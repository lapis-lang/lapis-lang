/**
 * LC Law Checking — the regime-based pass that admits laws into `E`.
 *
 * See _docs/theory/semantics.md §5.4 (regime-based checking) and
 * _docs/theory/elaboration.md §6.1 (the provenance chain).
 *
 * Two regimes share this module's schema machinery (schema instantiation,
 * the assignment sweep, the instance check), differing in sampler and in
 * what a passing check claims:
 *
 * - **The residual screen** (`screenLaw`) — best-effort falsification over
 *   bounded-depth samples (lc.md §7.2 schema instantiation; the sample
 *   budget is depth-capped). It *rejects* declarations it can falsify; it
 *   never *establishes* — passing is evidence, not proof (Model A
 *   authority), which is why a law admitted through the screen carries
 *   provenance `asserted`.
 * - **The finite-regime exhaustion** (`exhaustLaw`) — the ENTIRE inhabitant
 *   space of a bounded carrier is enumerated and checked, so passing is a
 *   **proof**: provenance `discharged`.
 *
 * `declareCheckedLaw` is the all-in-one entry (elaboration.md §6.1 steps
 * 1–4): structural validation, regime dispatch, the check, and the
 * provenance-tagged installation.
 *
 * Both mechanisms are total: evaluation is total (structural recursion), so
 * both sides of every instance terminate — no timeouts, no divergence.
 *
 * Scope (first cut): laws over operations whose parameters are **data
 * types** (μ-types). The residual screen samples variants to a bounded
 * depth; the finite regime requires a bounded inhabitant space (see
 * `finiteInhabitants`). Higher-order parameters (functions) have no finite
 * sample vocabulary — such a law declares but is installed `asserted`
 * unscreened (the residual's honest risk, semantics.md §7.4).
 *
 * Heterogeneous parameter types are checked position-wise: schema operand i
 * draws from the space of parameter type i, so every position sweeps its
 * own type's space. An instance whose evaluation hits an error sentinel is
 * a hole: the screen skips it (evidence, not proof — the count is the
 * honest coverage measure), while exhaustion rejects the declaration (a
 * `discharged` tag must mean full coverage).
 */

import {
    ARGUMENT_KINDS,
    type LawDecl,
    LawDeclarationError,
    LawError,
    type LawKind,
    type LawProvenance,
    LawRegistry,
    type LawTypeChecker,
    RELATIONAL_KINDS,
    screenableDomain,
} from "./laws.ts"

import { type CheckedOpSig, type OpRegistry } from "./ops.ts"

import { Value, ValueEnv, valueEquals, VariantVal } from "./values.ts"

import { EvalErrorValue } from "./eval_grammar.ts"

import { AnyType, DataType, type Type } from "./types.ts"

// ── Sampling ──────────────────────────────────────────────────────────────────

/**
 * The screen's sample depth: recursive variants recurse up to this many
 * levels (a `Succ` chain of length ≤ depth; depth 0 = the base cases only).
 * Per semantics.md §5.4 the residual samples "singleton variants one each;
 * primitive-field variants up to three combinations; recursive-field
 * variants one shallow sample" — a small bounded space that reaches the
 * interesting folds (nonempty scrutinees) without combinatorial growth.
 */
const MAX_SAMPLE_DEPTH = 2

/**
 * Generate sample values for one parameter type by walking its variants
 * (comb inheritance: a type's own variants plus its parent chain's).
 *
 * Depth 0 produces the depth-0 samples (variants without recursive fields);
 * each higher depth adds one level of recursion — one sample per recursive
 * variant per shallower sample, capped by the depth bound. Variants whose
 * non-recursive fields have no sample vocabulary (function types,
 * `Any`-typed fields, empty variant sets) are dropped — the remaining space
 * is what the screen can honestly sweep.
 */
function samplesFor(type: DataType, depth: number, eval_: EvalTerm): VariantVal[] {
    if (depth < 0) return []
    const all = type.allVariants()
    if (depth === 0) {
        return all
            .filter((variant) => !variant.fields.some((field) => field.isRecursive))
            .flatMap((variant) => {
                const sample = construct(variant, [], eval_, depth)
                return sample ? [sample] : []
            })
    }
    const shallower = samplesFor(type, depth - 1, eval_)
    const result: VariantVal[] = [...shallower]
    for (const variant of all) {
        const recursiveCount = variant.fields.filter((field) => field.isRecursive).length
        if (recursiveCount === 0) continue
        // One sample per recursive variant per shallower sample: recursive
        // fields draw from the shallower space (the last recursive position
        // takes the advancing sample) — enough to reach the fold's recursion
        // without the full product. Variants with unsampleable fields drop.
        for (const sample of shallower) {
            const built = construct(variant, shallower, eval_, depth, sample)
            if (built) result.push(built)
        }
    }
    return result
}

/**
 * Construct a variant value by evaluating its constructor form under a
 * scratch environment — construction goes through the evaluator so the
 * value's `dataType` is resolved by the same registry rules evaluation uses.
 *
 * `shallow` supplies the previous depth's samples for recursive fields; when
 * `sample` is given it is pinned to the LAST recursive field (the one a
 * fold's recursion descends through in the common single-recursive-field
 * shape), earlier recursive fields take the first shallow sample.
 * Non-recursive fields get their own typed samples (a nested recursive-field
 * sample of the field's type, or a depth-0 sample of that type) — the field's
 * declared type determines what the fold's handlers may pattern-match, so a
 * non-value sentinel would make samples that folds inspect fail. A field
 * type with NO generatable samples (function types, empty variant sets)
 * makes the whole variant unsampleable — returns `undefined`.
 *
 * A variant whose constructor fails to evaluate (unknown variant, failed
 * field construction) also yields `undefined` — the sampler drops it.
 */
function construct(
    variant: {
        name: string
        fields: readonly { name: string; type: Type; isRecursive: boolean }[]
    },
    shallow: readonly VariantVal[],
    eval_: EvalTerm,
    depth: number,
    sample?: VariantVal,
): VariantVal | undefined {
    const argNames = variant.fields.map((_, i) => `f${i}`)
    const bindings = new Map<string, Value>()
    const recursiveTotal = variant.fields.filter((field) => field.isRecursive).length
    let recursiveSeen = 0
    for (let i = 0; i < variant.fields.length; i++) {
        const field = variant.fields[i]!
        if (field.isRecursive) {
            const isLast = ++recursiveSeen === recursiveTotal
            const value = isLast && sample ? sample : shallow[0]
            if (value === undefined) return undefined
            bindings.set(argNames[i]!, value)
        } else {
            // Non-recursive fields: a typed sample of the field's own type —
            // the shallowest sample of a data type; `undefined` (no sample
            // vocabulary) when the field type is not sampleable. `Any`-typed
            // fields have no declared sample vocabulary either — unsampleable.
            const fieldSamples = field.type instanceof DataType
                ? samplesFor(field.type, Math.min(depth, 1), eval_)
                : []
            const value = fieldSamples[0]
            if (value === undefined) return undefined
            bindings.set(argNames[i]!, value)
        }
    }
    const source = `${variant.name}(${argNames.join(", ")})`
    const results = eval_(source, new ValueEnv(bindings))
    const value = results[0]
    // Unknown variant / failed construction: no usable sample.
    return value instanceof VariantVal ? value : undefined
}

/**
 * The evaluation primitive the screen uses: parse LC source under a value
 * environment and produce the resulting values (usually one; an empty array
 * = the instance did not evaluate — a sampling artifact, not evidence about
 * the axiom). Backed by `LCEval.parseWith` — total evaluation, so every
 * instance terminates.
 */
export type EvalTerm = (source: string, rho: ValueEnv) => readonly Value[]

// ── Schema instantiation ──────────────────────────────────────────────────────

/** A schema instance: the two sides as LC source, and the binding environment. */
interface LawInstance {
    readonly left: string
    readonly right: string
    readonly rho: ValueEnv
    /** The bindings, as rendered `name = term` pairs (for `LawError`). */
    readonly bindings: string[]
}

/** Per-kind schema variable names, in operand order (lc.md §7.2). */
const SCHEMA_NAMES: Record<LawKind, readonly string[]> = {
    associative: ["a", "b", "c"],
    commutative: ["a", "b"],
    identity: ["a"],
    idempotent: ["a"],
    involutory: ["a"],
    absorbing: ["a"],
    distributive: ["a", "b", "c"],
}

/**
 * Instantiate a law's axiom schema over a binding assignment (`bindings`:
 * schema variable name ↦ sample). The argument variable (`e` for identity,
 * `z` for absorbing) is pinned to the declared argument's evaluated value.
 *
 * Argument-taking kinds contribute TWO axiom instances per assignment —
 * lc.md §7.2 defines `identity: e` as both `⊕(e, a) ≡ a` and `⊕(a, e) ≡ a`
 * (and `absorbing: z` as both `⊗(z, a) ≡ z` and `⊗(a, z) ≡ z`). Screening
 * only the left direction would pass an operation with a one-sided identity
 * — a false axiom in `E` licensing a corrupting rewrite (`op(t, e) ↝ e`).
 */
function instantiate(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    bindings: readonly (readonly [string, VariantVal])[],
    argumentValue: Value | undefined,
): LawInstance[] {
    const opName = op.name
    let rho = new ValueEnv()
    const rendered: string[] = []
    for (const [name, value] of bindings) {
        rho = rho.extend(name, value)
        rendered.push(`${name} = ${renderValue(value)}`)
    }
    if (argumentValue !== undefined) {
        rho = rho.extend("e", argumentValue)
        rho = rho.extend("z", argumentValue)
        rendered.push(`argument = ${renderValue(argumentValue)}`)
    }
    const bindingsRendered = rendered

    switch (law.kind) {
        case "associative":
            return [{
                left: `${opName}(${opName}(a, b), c)`,
                right: `${opName}(a, ${opName}(b, c))`,
                rho,
                bindings: bindingsRendered,
            }]
        case "commutative":
            return [{
                left: `${opName}(a, b)`,
                right: `${opName}(b, a)`,
                rho,
                bindings: bindingsRendered,
            }]
        case "identity":
            // Both directions: ⊕(e, a) ≡ a (left) AND ⊕(a, e) ≡ a (right).
            return [
                { left: `${opName}(e, a)`, right: `a`, rho, bindings: bindingsRendered },
                { left: `${opName}(a, e)`, right: `a`, rho, bindings: bindingsRendered },
            ]
        case "idempotent":
            return [{ left: `${opName}(a, a)`, right: `a`, rho, bindings: bindingsRendered }]
        case "involutory":
            return [{
                left: `${opName}(${opName}(a))`,
                right: `a`,
                rho,
                bindings: bindingsRendered,
            }]
        case "absorbing":
            // Both directions: ⊗(z, a) ≡ z (left) AND ⊗(a, z) ≡ z (right).
            return [
                { left: `${opName}(z, a)`, right: `z`, rho, bindings: bindingsRendered },
                { left: `${opName}(a, z)`, right: `z`, rho, bindings: bindingsRendered },
            ]
        case "distributive": {
            const g = law.argument!
            return [{
                left: `${opName}(a, ${g}(b, c))`,
                right: `${g}(${opName}(a, b), ${opName}(a, c))`,
                rho,
                bindings: bindingsRendered,
            }]
        }
    }
}

/**
 * Render a value as an LC-like term (for `LawError` and dedup keys).
 */
function renderValue(value: Value): string {
    if (value instanceof VariantVal) {
        const fields = [...value.fields.values()].map(renderValue)
        return fields.length > 0
            ? `${value.variantName}(${fields.join(", ")})`
            : `${value.variantName}()`
    }
    return `<${value.kind}>`
}

// ── The screen ────────────────────────────────────────────────────────────────

/**
 * Screen one law: instantiate its schema over bounded samples of the
 * operation's domain and evaluate both sides. The **first** falsifying
 * sample wins; the thrown `LawError` carries the counterexample.
 *
 * Returns the number of instances checked (evidence of coverage; passing is
 * still only evidence, never proof). The caller installs the law `asserted`
 * on a passing screen — `LawRegistry.declareLaw`, or the all-in-one
 * `declareCheckedLaw` (which routes `finite`-regime laws to exhaustion
 * instead — this function is the residual regime's mechanism).
 *
 * @param law      the law declaration — structurally pre-validated by
 *                 `LawRegistry.validateLaw` in the `declareCheckedLaw`
 *                 entry; a raw call must supply a well-formed claim (an
 *                 unknown kind reaching the schema table is a caller bug).
 * @param op       the target operation (from `Ω`).
 * @param omega    the operation registry — `distributive`'s argument
 *                 operation is looked up here.
 * @param eval_    the evaluation primitive (see `makeEvalTerm`).
 * @param maxDepth the sample depth bound (default 2).
 *
 * @throws LawError when a sample falsifies the law.
 */
export function screenLaw(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    omega: OpRegistry,
    eval_: EvalTerm,
    maxDepth: number = MAX_SAMPLE_DEPTH,
): number {
    // Higher-order parameters: no finite sample vocabulary — the screen
    // declines (checked = 0; the caller installs the law unscreened).
    if (!screenableDomain(op)) return 0

    // The argument value for argument-taking kinds (shared precondition with
    // exhaustion — see `evalArgument`): a non-evaluating argument rejects
    // the declaration outright, so an argument that parses but evaluates to
    // nothing cannot slip through a raw `screenLaw` call and silently
    // produce zero coverage.
    const argumentValue = ARGUMENT_KINDS.includes(law.kind)
        ? evalArgument(law, op, eval_)
        : undefined

    // Distributive's relational operand operation must be screenable too.
    if (RELATIONAL_KINDS.includes(law.kind)) {
        const other = omega.lookup(law.argument!)
        if (!other || !screenableDomain(other)) return 0
    }

    // Per-position samples: schema operand i draws from the samples of the
    // parameter type at position i (mod the parameter count). Drawing from
    // the union across positions would put a Nat value in a Bool position —
    // the instance fails to evaluate and is silently skipped, losing
    // coverage. Heterogeneous types still share a position's samples with
    // the operation's actual signature (each position sweeps ITS OWN type).
    const positionSamples: VariantVal[][] = op.paramTypes.map((
        type,
    ) => [...dedupe(samplesFor(type as DataType, maxDepth, eval_))])
    if (positionSamples.some((s) => s.length === 0)) return 0

    let checked = 0
    // Enumerate assignments over the schema variables: every combination of
    // per-position samples the schema names (Cartesian across distinct
    // variables). Cyclic reuse would make some schemas vacuous — commutative
    // on a homogeneous op would degenerate to `op(a, a) ≡ op(a, a)`, passing
    // a non-commutative operation. Bounded sample spaces keep the product
    // small (depth ≤ 2 ⇒ a handful of samples per position).
    for (
        const bindings of assignments(
            SCHEMA_NAMES[law.kind]!,
            positionSamples,
            op.paramTypes.length,
        )
    ) {
        for (const instance of instantiate(law, op, bindings, argumentValue)) {
            const outcome = checkInstance(instance, law, op, eval_)
            if (outcome === "nonEval") {
                // Not a falsification — the schema may not apply to this
                // sample mix. Skipped, and NOT counted: the count is the
                // honest coverage measure (instances actually checked).
                continue
            }
            checked++
        }
    }
    return checked
}

/**
 * Evaluate one law instance's two sides and compare: returns `"nonEval"`
 * when either side does not evaluate (an error sentinel or an empty parse
 * forest), and `"holds"` when both sides evaluate and agree. Divergence
 * THROWS `LawError` — a falsified claim never flows back as a value.
 *
 * Shared by the residual screen (which SKIPS non-evaluating instances —
 * the schema may not apply to the sample mix) and the exhaustion engine
 * (which REJECTS the declaration on one — a discharged law must mean full
 * coverage, not a proof with holes).
 */
function checkInstance(
    instance: LawInstance,
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    eval_: EvalTerm,
): "holds" | "nonEval" {
    const left = eval_(instance.left, instance.rho)[0]
    const right = eval_(instance.right, instance.rho)[0]
    if (
        left === undefined || right === undefined ||
        left instanceof EvalErrorValue || right instanceof EvalErrorValue
    ) {
        // An instance that does not evaluate (or evaluates to an error
        // sentinel) is not a falsification — the schema may not apply to
        // this sample mix.
        return "nonEval"
    }
    if (!valueEquals(left, right)) {
        throw new LawError(op.name, law, instance.bindings, renderValue(left), renderValue(right))
    }
    return "holds"
}

/**
 * Enumerate the schema's variable assignments as a STREAM: variable i draws
 * from the iterator of the operand position it instantiates (position i, mod
 * the operation's parameter count — schemas instantiate fewer variables than
 * positions on some shapes). The sweep is the Cartesian product across
 * variables, so every variable takes independent values — a falsifying
 * pair like `op(a, b)` with `a ≠ b` is reachable for commutative.
 *
 * Laziness matters for the finite regime: an at-ceiling sweep (2²⁰
 * assignments) is produced one binding at a time — the full product is
 * never materialized. Position iterators are REWOUND per outer iteration by
 * the caller (they are cached, restartable iterators — see
 * `positionSpace`), so the product is correct without array materialization.
 */
function* assignments(
    names: readonly string[],
    positionSamples: readonly (readonly VariantVal[])[],
    paramCount: number,
    variableIndex: number = 0,
): Generator<(readonly [string, VariantVal])[]> {
    if (names.length === 0) {
        yield []
        return
    }
    const [head, ...rest] = names
    const position = variableIndex % paramCount
    for (const sample of positionSamples[position]!) {
        for (const tail of assignments(rest, positionSamples, paramCount, variableIndex + 1)) {
            yield [[head!, sample] as const, ...tail]
        }
    }
}

/**
 * Dedupe samples structurally (the sweep sees each distinct value once).
 * Wraps an ITERATOR: the dedup key set grows with the space, but the values
 * themselves are not re-materialized — the exhaustion engine pulls through
 * this lazily.
 */
function* dedupe(samples: Iterable<VariantVal>): Generator<VariantVal> {
    const seen = new Set<string>()
    for (const sample of samples) {
        const key = renderValue(sample)
        if (!seen.has(key)) {
            seen.add(key)
            yield sample
        }
    }
}

/**
 * Build an `EvalTerm` from an `LCEval`: extracts the values of each parse,
 * treating an empty forest (eval error, unknown variant) as "no result" —
 * the screen skips such instances rather than rejecting the law.
 */
export function makeEvalTerm(
    evalGrammar: { parseWith(input: string, rho: ValueEnv): Set<Value> },
): EvalTerm {
    return (source, rho) => [...evalGrammar.parseWith(source, rho)]
}

// ── The screening regime (semantics.md §5.4) ─────────────────────────────────

/**
 * The checking regime the law-checking pass applies (semantics.md §5.4):
 *
 * - **`finite`** — the operand carrier has a bounded inhabitant space
 *   (≤ `MAX_FINITE_INHABITANTS`) and the law's schema sweep over it stays
 *   within budget, so the law can be checked exhaustively — a passing
 *   exhaustion establishes it (`discharged` provenance).
 * - **`residual`** — everything else (unbounded-depth μ-types, or a space
 *   beyond the budget): the bounded-depth screen applies, falsifying only —
 *   `asserted` provenance.
 *
 * `machineFinite` (fixed encodings — binary64, Char alphabets) is not yet
 * a regime: those encodings are not declared in the type system, so the
 * exhaustion bound would be an implementation accident, not spec-able
 * (semantics.md §5.4). `derivable` (fold-induction from primitive laws)
 * likewise awaits a characterization of the derivable handler fragment.
 */
export type ScreeningRegime = "finite" | "residual"

/**
 * The inhabitant ceiling for the `finite` regime (semantics.md §5.4: "Bool,
 * enums, records of finites (< ~2²⁰ inhabitants)" — the ceiling is set
 * below the doc's upper edge: exhaustion MEMOIZES each distinct type's
 * deduped space as real `VariantVal`s, and the memory cost is the honest
 * price of full enumeration. 2¹⁶ × ~1.5KB/value ≈ 100MB per distinct
 * carrier — the practical bound measured on the default heap; a 2²⁰-space
 * record type exhausts it (OOM, measured ~1.8GB).) A data type whose
 * inhabitant count is at or below this bound is exhaustible: the entire
 * input space is checked, making a passing check a proof. Bumping this
 * ceiling requires a heap headroom check or an external-memory sweep.
 */
const MAX_FINITE_INHABITANTS = 2 ** 17

/**
 * The instance ceiling for a full exhaustion sweep. A schema over an arity-2
 * operation quantifies over PAIRS of inhabitants, so a type at the
 * inhabitant ceiling alone could demand up to 2¹⁷ × 2¹⁷ instances — the
 * per-type bound does not bound the sweep. The regime is `finite` only when
 * the actual schema sweep (inhabitants^schema variables × instances per
 * assignment) stays within this budget. Each instance evaluates both axiom
 * sides through the evaluator; 2¹⁷ keeps a full passing sweep in seconds
 * (measured) while remaining far above any realistic finite carrier's
 * meaningful schema sweep.
 */
const MAX_EXHAUSTION_INSTANCES = 2 ** 20

/**
 * Count the inhabitants of a data type, or `undefined` when the type is not
 * finitely inhabitable.
 *
 * The space of a μ-type is finite exactly when every variant field is:
 * a recursive field makes the type unbounded (a value may nest arbitrarily
 * deep), a function-typed field has no finite vocabulary, and `Any`-typed
 * fields are equally unbounded (the top type subsumes every type). A field
 * referencing another data type contributes that type's count (the product
 * through the variant's fields); parent-chain variants are summed in via
 * comb inheritance.
 *
 * Counts are saturated: any component exceeding the ceiling returns one
 * past it, so deep record chains cannot overflow the number range while the
 * caller's comparison against the ceiling still decides enumerability — a
 * value past the ceiling means "finite but not exhaustible here".
 */
export function finiteInhabitants(type: DataType): number | undefined {
    // The cache maps data types to their count-or-not-finite verdict;
    // `inProgress` marks types on the current traversal path — a cycle means
    // a recursive field, hence unbounded. (The μ-bound α is spelled as the
    // type itself: a self-referential field's type IS the μ-type.)
    const count = (
        type: DataType,
        cache: Map<DataType, number | undefined>,
        inProgress: Set<DataType>,
    ): number | undefined => {
        const cached = cache.get(type)
        if (cached !== undefined || cache.has(type)) return cached
        if (inProgress.has(type)) return undefined
        inProgress.add(type)
        let total = 0
        for (const variant of type.allVariants()) {
            let product = 1
            for (const field of variant.fields) {
                if (field.isRecursive) {
                    inProgress.delete(type)
                    cache.set(type, undefined)
                    return undefined
                }
                const fieldType = field.type
                if (fieldType instanceof AnyType) {
                    inProgress.delete(type)
                    cache.set(type, undefined)
                    return undefined
                }
                if (!(fieldType instanceof DataType)) {
                    // Function types (and any other non-data type) have no
                    // finite sample vocabulary.
                    inProgress.delete(type)
                    cache.set(type, undefined)
                    return undefined
                }
                const sub = count(fieldType, cache, inProgress)
                if (sub === undefined) {
                    inProgress.delete(type)
                    cache.set(type, undefined)
                    return undefined
                }
                product *= sub
                if (product > MAX_FINITE_INHABITANTS) {
                    inProgress.delete(type)
                    cache.set(type, MAX_FINITE_INHABITANTS + 1)
                    return MAX_FINITE_INHABITANTS + 1
                }
            }
            total += product
            if (total > MAX_FINITE_INHABITANTS) {
                inProgress.delete(type)
                cache.set(type, MAX_FINITE_INHABITANTS + 1)
                return MAX_FINITE_INHABITANTS + 1
            }
        }
        inProgress.delete(type)
        cache.set(type, total)
        return total
    }
    return count(type, new Map(), new Set())
}

/**
 * The regime for checking a law on the given operation (semantics.md §5.4
 * regime table, first cut). The sweep size is the exact count the schema
 * machinery would enumerate: schema variable i instantiates operand position
 * `i % paramCount` (see `assignments`), so each position's exponent is the
 * number of variables landing on it, and the sweep is
 * `Π inhabitants(position)^exponent(position)` — an exact estimate, not a
 * per-position worst case. `finite` requires every carrier exhaustible and
 * the sweep within the instance budget; everything else falls to the
 * residual's bounded-depth screen.
 */
export function screeningRegime(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
): ScreeningRegime {
    // The module's scope is laws over data-typed parameters: a function-typed
    // parameter has no inhabitant vocabulary at all. Even a position with
    // exponent 0 must disqualify — an argument-taking schema (identity:
    // e / absorbing: z) is well-posed only against a data carrier, and the
    // check below would otherwise route to exhaustion while the argument's
    // validity for the skipped slot was never established.
    if (!screenableDomain(op)) return "residual"

    // Per-position exponents: schema variable i maps to position i (mod the
    // parameter count) — the same mapping `assignments` enumerates, so the
    // estimate here IS the sweep the check will run.
    const exponents = new Array<number>(op.paramTypes.length).fill(0)
    for (let i = 0; i < SCHEMA_NAMES[law.kind]!.length; i++) {
        exponents[i % op.paramTypes.length]!++
    }
    const instancesPerAssignment = ARGUMENT_KINDS.includes(law.kind) ? 2 : 1

    let sweep = instancesPerAssignment
    for (let position = 0; position < op.paramTypes.length; position++) {
        // A position no variable lands on is never swept: its carrier's
        // size is irrelevant (this is what keeps an identity claim over
        // (Bool, 2¹⁸) exhaustible — only position 0 is ever enumerated).
        if (exponents[position] === 0) continue
        if (!(op.paramTypes[position]! instanceof DataType)) return "residual"
        const inhabitants = finiteInhabitants(op.paramTypes[position]! as DataType)
        if (inhabitants === undefined) return "residual"
        // Saturated count = "finite but at or past the ceiling" — the true
        // count is larger than reported, so the sweep estimate would be a
        // LIE if multiplied in (an 18-Bool record space saturating to 2¹⁷+1
        // could pass an instance budget of 2²⁰ and route to exhaustion over
        // a space it cannot hold). Past-ceiling positions route residual.
        if (inhabitants > MAX_FINITE_INHABITANTS) return "residual"
        // Saturated multiplication: past the budget the exact count no
        // longer matters — the regime is residual either way, and staying
        // below 2⁵³ keeps the arithmetic honest for extreme products.
        sweep *= inhabitants ** exponents[position]!
        if (sweep > MAX_EXHAUSTION_INSTANCES) return "residual"
    }
    return "finite"
}

/**
 * The screen's all-in-one entry (elaboration.md §6.1 steps 1–4): validate
 * the claim structurally against `Ω` (`LawRegistry.validateLaw` — vocabulary,
 * argument shape, relational arity, schema typing), then run the
 * **regime-based check** (semantics.md §5.4) and install the law in `E` with
 * the provenance the regime's outcome establishes:
 *
 * - `finite` regime → `exhaustLaw` (the entire input space is checked) →
 *   installed **`discharged`** on a full-coverage pass.
 * - `residual` regime → `screenLaw` (bounded-depth samples) → installed
 *   **`asserted`** on a passing screen (evidence, not proof).
 *
 * Validation runs BEFORE the check: a vocabulary/argument/arity/typing
 * error surfaces as `LawDeclarationError` — never as a screen artifact (a
 * `TypeError` from an unknown kind, or zero-coverage silence). The check
 * runs second, so a falsified claim never enters `E`.
 *
 * Returns `{ law, instances, regime }` — the installed declaration, the
 * number of instances checked, and the regime that produced it.
 *
 * @throws LawError when the check falsifies the law (nothing is installed).
 * @throws LawDeclarationError when the claim is not in the closed vocabulary,
 * is structurally ill-formed (from `LawRegistry.validateLaw`), or — in the
 * `finite` regime — an instance of the axiom fails to evaluate (a
 * `discharged` tag must mean full coverage; holes in the sweep are a
 * rejected declaration, not silent under-coverage).
 */
export function declareCheckedLaw(
    law: Omit<LawDecl, "provenance">,
    omega: OpRegistry,
    laws: LawRegistry,
    eval_: EvalTerm,
    checker?: LawTypeChecker,
    maxDepth: number = MAX_SAMPLE_DEPTH,
): { law: LawDecl; instances: number; regime: ScreeningRegime } {
    const op = omega.lookup(law.target)
    if (!op) {
        throw new LawDeclarationError(law.target, "the target operation is not declared in Ω")
    }
    // Structural validation FIRST (loud, typed errors), then the regime check.
    const structuralReason = laws.validateLaw(law, omega, checker)
    if (structuralReason !== undefined) {
        throw new LawDeclarationError(law.target, structuralReason)
    }
    // Regime dispatch (semantics.md §5.4): finite → exhaustive discharge;
    // residual → the bounded-depth screen. The check runs BEFORE installing:
    // a falsified claim never enters E.
    const regime = screeningRegime(law, op)
    const instances = regime === "finite"
        ? exhaustLaw(law, op, eval_)
        : screenLaw(law, op, omega, eval_, maxDepth)
    const provenance: LawProvenance = regime === "finite" ? "discharged" : "asserted"
    laws.declareLaw(law, omega, provenance, checker)
    const decl: LawDecl = { ...law, provenance }
    return { law: decl, instances, regime }
}

// ── Exhaustion (the finite regime — semantics.md §5.4) ───────────────────────

/**
 * Evaluate a law's declared argument term (identity: e / absorbing: z) in a
 * fresh environment. A non-evaluating argument throws `LawError` — the claim
 * is not even well-posed (both regimes share this precondition; the
 * argument's TYPE was validated against the carrier at declaration,
 * `LawRegistry.validateLaw`, but only evaluation proves the term inhabits
 * it).
 */
function evalArgument(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    eval_: EvalTerm,
): Value {
    const value = eval_(law.argument!, new ValueEnv())[0]
    // BOTH failure shapes reject: an empty result (the argument did not
    // parse/evaluate) AND an `EvalErrorValue` sentinel (the argument parsed
    // but evaluation failed — an unknown variant, a failed subterm). Binding
    // a sentinel as `e`/`z` would poison the sweep: over an empty finite
    // domain it could even install a `discharged` law with zero checked
    // instances, and residual checks would silently skip every instance.
    if (value === undefined || value instanceof EvalErrorValue) {
        const reason = value instanceof EvalErrorValue
            ? "evaluated to an error sentinel"
            : "did not evaluate"
        throw new LawError(op.name, law, [`argument = ${reason}`], "—", "—")
    }
    return value
}

/**
 * Exhaustively check a law: enumerate the ENTIRE inhabitant space of each
 * parameter type and evaluate the axiom schema over every assignment. Unlike
 * the residual screen, a passing sweep is a **proof** — no inhabitant was
 * left unchecked — so the caller installs the law `discharged`.
 *
 * Full enumeration reuses the screen's schema machinery (`assignments`,
 * `instantiate`) but not its sampler: `samplesFor` deliberately samples one
 * value per non-recursive field (bounded depth, bounded breadth) — the
 * residual's bounded budget. Exhaustion needs the full product: every
 * variant, every field combination, across the type's whole (finite) space.
 *
 * Coverage honesty: an instance that fails to evaluate REJECTS the
 * declaration (`LawDeclarationError`) rather than being skipped. A
 * `discharged` tag claims every inhabitant was checked — a hole in the
 * sweep would make that claim false; the screen's skip-and-continue is
 * honest only because it claims evidence, not proof.
 *
 * An operand type with NO inhabitants makes the claim **vacuously true** —
 * every assignment over the empty space holds without evaluation. The
 * discharge is honest (the sweep is complete), and the count records the
 * shape: argument-taking schemas still evaluate their argument, so such a
 * claim carries `instances = 0` and provenance `discharged` (semantics.md
 * §5.4: the finite regime's result is a proof — a vacuous one is still
 * established, though the caller may choose to warn on zero coverage).
 *
 * @throws LawError when any inhabitant falsifies the law, or a declared
 * argument does not evaluate.
 * @throws LawDeclarationError when an axiom instance over real inhabitants
 * fails to evaluate (a hole in the sweep — the claim is not checkable on
 * this signature to proof standard).
 */
function exhaustLaw(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    eval_: EvalTerm,
): number {
    // The argument value for argument-taking kinds (shared with the screen).
    const argumentValue = ARGUMENT_KINDS.includes(law.kind)
        ? evalArgument(law, op, eval_)
        : undefined

    // Lazy per-position inhabitant spaces: a position's full space is only
    // ever materialized if the schema actually binds that position, and a
    // space shared across positions (homogeneous ops) or reused across
    // variant fields of the same type is enumerated ONCE (the memo is
    // shared with `inhabitantsOf`'s field lookups). At the ceiling this is
    // the difference between ~1.8GB of resident values (OOM, measured) and
    // a footprint of the distinct field types' spaces.
    const spaces = new Map<DataType, readonly VariantVal[]>()

    // Positions whose type has no inhabitants make the claim VACUOUSLY true
    // when a variable lands on them: `assignments` yields nothing (the
    // product with an empty factor is empty), the sweep completes with zero
    // instances, and the discharge is honest — every inhabitant (∅) was
    // checked. Positions with exponent 0 are never enumerated at all: an
    // identity claim over (Bool, 2²⁰) must not build the 2²⁰-value space it
    // never binds (memoized per type, so a shared carrier enumerates once).
    const exponents = new Array<number>(op.paramTypes.length).fill(0)
    for (let i = 0; i < SCHEMA_NAMES[law.kind]!.length; i++) {
        exponents[i % op.paramTypes.length]!++
    }
    const positionSamples: readonly (readonly VariantVal[])[] = op.paramTypes
        .map((type, position) => {
            if (exponents[position] === 0) return [] as readonly VariantVal[]
            return spaceOf(type as DataType, eval_, spaces)
        })

    let checked = 0
    for (
        const bindings of assignments(
            SCHEMA_NAMES[law.kind]!,
            positionSamples,
            op.paramTypes.length,
        )
    ) {
        for (const instance of instantiate(law, op, bindings, argumentValue)) {
            const outcome = checkInstance(instance, law, op, eval_)
            if (outcome === "nonEval") {
                // Full coverage is the discharge contract: an instance that
                // does not evaluate is a hole in the proof, so the
                // declaration is rejected rather than silently under-covered.
                throw new LawDeclarationError(
                    op.name,
                    `exhaustion instance did not evaluate (under: ${
                        instance.bindings.join(", ")
                    }) — ` +
                        `the law cannot be discharged on this signature`,
                )
            }
            checked++
        }
    }
    return checked
}

/**
 * Enumerate ALL inhabitants of a finite data type, LAZILY: a generator over
 * every variant, with every combination of field values (fields of other
 * finite data types recurse into their own full space — the true product,
 * unlike the screen's one sample per field). Field spaces are pulled from a
 * shared memo (`spaces`): a type's space is enumerated once per check and
 * REUSED — both for variant fields that repeat a carrier and for repeated
 * operand positions (see `exhaustLaw`). Within one variant, the field
 * spaces must be materialized arrays before the product streams: a
 * single-pass generator consumed once by the product's inner loop would
 * leave later combinations with an exhausted iterator (a silent coverage
 * hole). Per-type memoization bounds that materialization: each DISTINCT
 * data type's space is resident at most once, so the footprint is the sum
 * of distinct field types' spaces, not the product. Requires
 * `finiteInhabitants(type)` to be defined and within the ceiling; the
 * caller (regime dispatch) guarantees both.
 *
 * **Completeness is the discharge contract**: a variant whose constructor
 * form fails to evaluate (unknown variant, failed field construction) is a
 * hole in the sweep, not a droppable sample — the enumeration THROWS
 * `LawDeclarationError` rather than returning a shrunken space that the
 * caller would pass as full coverage. (The residual screen's sampler may
 * drop failed constructions: its claim is bounded evidence, not a proof.)
 */
function* inhabitantsOf(
    type: DataType,
    eval_: EvalTerm,
    spaces: Map<DataType, readonly VariantVal[]>,
): Generator<VariantVal> {
    for (const variant of type.allVariants()) {
        // Zero-inhabitant fields kill the variant: a single field with an
        // empty space (an empty variant set, an `Empty`-typed field) makes
        // the variant contribute NO values. Detected via the pure classifier
        // BEFORE any field's space is materialized — a valid finite type
        // such as `Dead(Big, Empty) | Live()` must not enumerate `Big` (or
        // throw on an unregistered `Big`) just because `Dead` is dead. (A
        // recursive/unbounded field type reaching here is unreachable under
        // the finite regime; treat it conservatively as non-dead and let
        // the completeness check below surface the truth.)
        const hasEmptyField = variant.fields.some((field) => {
            const fieldType = field.type
            return fieldType instanceof DataType && finiteInhabitants(fieldType) === 0
        })
        if (hasEmptyField) continue
        // The field-value spaces, in field order: each field's full space,
        // enumerated ONCE through the shared memo (repeated field types —
        // two Bool fields, a Bool-Field record — enumerate once).
        const fieldSpaces: readonly (readonly VariantVal[])[] = variant.fields
            .map((field) => {
                const fieldType = field.type
                if (fieldType instanceof DataType) return spaceOf(fieldType, eval_, spaces)
                // Unreachable under the finite regime (the classifier rejects
                // non-data, `Any`, and recursive fields) — an empty space
                // yields an unsampleable variant, which the completeness
                // check below surfaces as a rejected declaration rather than
                // a hole.
                return [] as readonly VariantVal[]
            })
        // The Cartesian product across the variant's fields, streamed.
        for (const combo of cartesian(fieldSpaces)) {
            const argNames = variant.fields.map((_, i) => `f${i}`)
            const bindings = new Map<string, Value>()
            combo.forEach((value, i) => bindings.set(argNames[i]!, value))
            const source = `${variant.name}(${argNames.join(", ")})`
            const value = eval_(source, new ValueEnv(bindings))[0]
            // Construction goes through the evaluator (as in the screen's
            // `construct`) so the value's `dataType` resolves by the same
            // registry rules evaluation uses. A failed construction is NOT
            // silently dropped: the sweep's completeness is the discharge
            // contract, so a hole rejects the declaration outright.
            if (!(value instanceof VariantVal)) {
                throw new LawDeclarationError(
                    type.name,
                    `exhaustion could not construct an inhabitant: "${source}" did not evaluate — the finite regime cannot sweep this type`,
                )
            }
            yield value
        }
    }
}

/**
 * Stream the Cartesian product across materialized field spaces,
 * innermost-last (field order preserved in each emitted combo).
 */
function* cartesian(spaces: readonly (readonly VariantVal[])[]): Generator<Value[]> {
    if (spaces.length === 0) {
        yield []
        return
    }
    const [head, ...rest] = spaces
    for (const value of head!) {
        for (const tail of cartesian(rest)) {
            yield [value, ...tail]
        }
    }
}

/**
 * A type's deduped inhabitant space, materialized at most once per check
 * (the memo is shared across operand positions and variant fields — a
 * carrier appearing in several places is enumerated a single time).
 */
function spaceOf(
    type: DataType,
    eval_: EvalTerm,
    spaces: Map<DataType, readonly VariantVal[]>,
): readonly VariantVal[] {
    const cached = spaces.get(type)
    if (cached) return cached
    const space = [...dedupe(inhabitantsOf(type, eval_, spaces))]
    spaces.set(type, space)
    return space
}
