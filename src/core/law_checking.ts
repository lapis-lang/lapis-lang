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
 *   certified size-≤ k prefixes (lc.md §7.2 schema instantiation; the
 *   certificate is per-position, `type-algebra.md` §3). It *rejects*
 *   declarations it can falsify; it never *establishes* — passing is
 *   evidence, not proof (Model A authority), which is why a law admitted
 *   through the screen carries provenance `asserted`.
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
 * types** (μ-types). The residual screen sweeps certified size prefixes;
 * the finite regime requires a bounded inhabitant space (see
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
    type SubSpaceSpec,
} from "./laws.ts"

import { type CheckedOpSig, type OpRegistry } from "./ops.ts"

import { TypeRegistry } from "./grammar.ts"

import { TokenVal, Value, ValueEnv, VariantVal } from "./values.ts"

import { EvalErrorValue } from "./eval_grammar.ts"

import {
    coefficients,
    finiteInhabitants as finiteInhabitantsFromAlgebra,
    MAX_FINITE_INHABITANTS,
} from "./type_algebra.ts"

import { DataType, FamilyType, isPatternCarrierType, type Type, Variant } from "./types.ts"

import { enumeratePattern, makePatternCountEnv, typeUnionStrings } from "./pattern_lang.ts"

import { setPatternLookup } from "./type_algebra.ts"

import { derivableFragment, type DerivationCertificate, deriveLaw } from "./derivation.ts"

// ── Sampling ──────────────────────────────────────────────────────────────────

/**
 * Generate sample values for one parameter type by walking its variants
 * (comb inheritance: a type's own variants plus its parent chain's).
 *
 * Depth 0 produces the depth-0 samples (variants without recursive fields);
 * each higher depth adds one level of recursion — one sample per recursive
 * variant per shallower sample, capped by the depth bound. Variants whose
 * non-recursive fields have no sample vocabulary (function types,
 * `Any`-typed fields, empty variant sets) are dropped — the remaining space
 * is what the shrinker can honestly plug.
 *
 * Exported for the ∂T shrinker (`law_testing.ts`): filler candidates for a
 * hole are the hole type's sampled vocabulary — the same sampler, so the
 * two mechanisms agree on what a carrier's values look like.
 */
export function samplesFor(type: DataType, depth: number, eval_: EvalTerm): VariantVal[] {
    if (depth < 0) return []
    const all = type.allVariants()
    if (depth === 0) {
        return all
            .filter((variant) => !variant.fields.some((field) => field.type instanceof FamilyType))
            .flatMap((variant) => {
                const sample = construct(variant, [], eval_, depth)
                return sample ? [sample] : []
            })
    }
    const shallower = samplesFor(type, depth - 1, eval_)
    const result: VariantVal[] = [...shallower]
    for (const variant of all) {
        const recursiveCount = variant.fields.filter((field) =>
            field.type instanceof FamilyType
        ).length
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
        fields: readonly { name: string; type: Type }[]
    },
    shallow: readonly VariantVal[],
    eval_: EvalTerm,
    depth: number,
    sample?: VariantVal,
): VariantVal | undefined {
    const argNames = variant.fields.map((_, i) => `f${i}`)
    const bindings = new Map<string, Value>()
    const recursiveTotal = variant.fields.filter((field) => field.type instanceof FamilyType).length
    let recursiveSeen = 0
    for (let i = 0; i < variant.fields.length; i++) {
        const field = variant.fields[i]!
        if (field.type instanceof FamilyType) {
            const isLast = ++recursiveSeen === recursiveTotal
            const value = isLast && sample ? sample : shallow[0]
            if (value === undefined) return undefined
            bindings.set(argNames[i]!, value)
        } else {
            // Non-recursive fields: a typed sample of the field's own type —
            // the shallowest sample of a data carrier WITH variants, or a
            // matched token for a pattern-bearing field (see
            // `patternSamples`); `undefined` (no sample vocabulary) when the
            // field type is not sampleable. `Any`-typed fields have no
            // declared sample vocabulary either — unsampleable.
            const fieldSamples = field.type instanceof DataType
                ? field.type.variants.length > 0
                    ? samplesFor(field.type, Math.min(depth, 1), eval_)
                    : field.type.patterns.length > 0
                    ? patternSamples(field.type, eval_)
                    : []
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
    bindings: readonly (readonly [string, Value])[],
    argumentValue: Value | undefined,
): LawInstance[] {
    const opName = op.name
    let rho = new ValueEnv()
    const rendered: string[] = []
    for (const [name, value] of bindings) {
        rho = rho.extend(name, value)
        rendered.push(`${name} = ${value.renderDisplay()}`)
    }
    if (argumentValue !== undefined) {
        rho = rho.extend("e", argumentValue)
        rho = rho.extend("z", argumentValue)
        rendered.push(`argument = ${argumentValue.renderDisplay()}`)
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
 *
 * The per-kind arms live on the value subclasses as the virtual
 * `Value.renderDisplay` — a variant renders as `Name(field, …)` recursively,
 * a token renders as `Type"text"` (quoted), and kinds without a term reading
 * fall back to `<kind>` (display never declines where the source form does).
 * This module's output is the LawError text AND the exhaustion sweep's dedup
 * key.
 */

// ── The screen ────────────────────────────────────────────────────────────────

/**
 * The machineFinite sweep's VISIBLE EXTENT — the certificate of what the
 * `discharged` tag covers for a scoped claim. The scope's predicate is the
 * claim's domain, but the sweep certifies only the strings the
 * length-bounded enumeration reached: the certificate states that extent
 * (the length bound) and each scoped position's admitted cardinality, so
 * a consumer of the declaration sees "discharged on strings of length ≤ N
 * matching the scope" rather than an unqualified `discharged`.
 */
export interface SubSpaceSweep {
    /** The string-length bound the enumeration reached (MAX_PATTERN_LENGTH). */
    readonly maxLength: number
    /** Per scoped position: the predicate's source and the admitted count. */
    readonly positions: readonly {
        readonly position: number
        readonly where: string
        /** The admitted tokens' count (the sweep's space at this position). */
        readonly admitted: number
    }[]
}

/**
 * The screen's outcome: `"declined"` (the screen has no sample vocabulary
 * for this claim — coverage 0 is a HOLE, not evidence) or `"passed"` with
 * the number of instances actually checked and the **certified coverage**
 * report (per-position certificates + the rendered claim). Falsification
 * throws `LawError` and never returns.
 */
export type ScreenOutcome =
    | { outcome: "declined" }
    | { outcome: "passed"; checked: number; coverage: CertifiedCoverage }

/**
 * Screen one law: instantiate its schema over the **certified size-≤ kᵢ
 * prefix** of each operand position and evaluate both sides. The **first**
 * falsifying sample wins; the thrown `LawError` carries the counterexample.
 *
 * Coverage is a theorem, not a vibe: each position's sample space is its
 * type's complete size-≤ kᵢ class set — enumerated by `inhabitantsUpToSize`
 * and asserted against `coefficients` — so the coverage report states "all
 * inhabitants of size ≤ kᵢ per operand position — exactly N, verified". A
 * sweep/coefficient mismatch rejects the declaration loudly (an enumeration
 * hole must not masquerade as coverage); so does a projected sweep past the
 * budgets — today such a law would install `asserted` on ~1 masquerading
 * instance.
 *
 * Returns the screen outcome: `"declined"` when the screen has no sample
 * vocabulary for the claim (unscreenable domain, unscreenable relational
 * operand — the claim was exercised ZERO times); `"passed"` with the
 * instance count and the certificate when the sweep ran (evidence of
 * coverage; passing is still only evidence, never proof — the provenance
 * ladder is unchanged). The caller installs the law `asserted` on a
 * passed screen — `LawRegistry.declareLaw`, or the all-in-one
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
 *
 * @throws LawError when a sample falsifies the law.
 * @throws LawDeclarationError when a position's certification declines or
 *         mismatches (see `certifyPosition`/`certifyCoverage`).
 */
export function screenLaw(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    omega: OpRegistry,
    eval_: EvalTerm,
): ScreenOutcome {
    // Higher-order parameters: no finite sample vocabulary — the screen
    // declines (the caller rejects a zero-coverage claim; installing an
    // `asserted` law the screen never exercised would be silent under-
    // coverage). See `declareCheckedLaw`.
    if (!screenableDomain(op)) return { outcome: "declined" }

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
        if (!other || !screenableDomain(other)) return { outcome: "declined" }
    }

    // Per-position exponents: schema variable i maps to position i (mod the
    // parameter count) — the same mapping `assignments` enumerates, so the
    // certification's projection IS the sweep the check will run.
    const exponents = new Array<number>(op.paramTypes.length).fill(0)
    for (let i = 0; i < SCHEMA_NAMES[law.kind]!.length; i++) {
        exponents[i % op.paramTypes.length]!++
    }
    const instancesPerAssignment = ARGUMENT_KINDS.includes(law.kind) ? 2 : 1

    // CERTIFY FIRST (fail fast at sample generation): each swept position's
    // size bound, its enumerated prefix, and the coefficient assertion. The
    // certified samples ARE the screen's sweep space.
    const { coverage, positionSamples } = certifyCoverage(
        op,
        exponents,
        instancesPerAssignment,
        eval_,
    )
    // Zero sample vocabulary on a SWEPT position (an exponent > 0): the
    // claim was exercised zero times. Positions with exponent 0 have empty
    // sample arrays by construction (`certifyCoverage` never certifies
    // them — the assignments generator never reads them) and must NOT trip
    // this guard: an identity claim over (Nat, Big) sweeps position 0 only.
    if (
        positionSamples.some((samples, position) =>
            exponents[position]! > 0 && samples.length === 0
        )
    ) {
        return { outcome: "declined" }
    }

    let checked = 0
    // Enumerate assignments over the schema variables: every combination of
    // per-position samples the schema names (Cartesian across distinct
    // variables). Cyclic reuse would make some schemas vacuous — commutative
    // on a homogeneous op would degenerate to `op(a, a) ≡ op(a, a)`, passing
    // a non-commutative operation. The certified prefixes bound the product
    // (the sweep projection was checked against SWEEP_BUDGET above).
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
    return { outcome: "passed", checked, coverage }
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
    if (!left.equals(right)) {
        throw new LawError(
            op.name,
            law,
            instance.bindings,
            left.renderDisplay(),
            right.renderDisplay(),
        )
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
    positionSamples: readonly (readonly Value[])[],
    paramCount: number,
    variableIndex: number = 0,
): Generator<(readonly [string, Value])[]> {
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
        const key = sample.renderDisplay()
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
 * Sample values for a pattern-matched type: the pattern language's
 * enumerated tokens, evaluated through the evaluator so they become real
 * `TokenVal`s (the same construction path evaluation uses).
 *
 * The pattern universe is unbounded IN TOTAL (type-algebra.md §2.3: a
 * pattern type's generating function is rational, never polynomial) — but a
 * **certified prefix** is checkable, and with the language-equation reading
 * the certified prefix is the TRUE size-≤ MAX_SCREEN_SIZE
 * token set: each matched string of length ≤ MAX_SCREEN_SIZE becomes a
 * token via the evaluator (`TokenVal(text)` — the token is an axiom of the
 * operational semantics, its text is carried directly). A type with no
 * declared patterns has NO inhabitants — the empty space declines the
 * screen (zero-coverage honesty, `declareCheckedLaw`).
 *
 * (The size measure is TEXT LENGTH — `Value.size`'s token arm — so the
 * prefix and the coefficients agree.)
 */
function patternSamples(type: DataType, eval_: EvalTerm): Value[] {
    if (type.patterns.length === 0) return []
    // The token atom evaluates via the evaluator's `matchedToken` (a
    // `TokenVal` of the pattern type) — construction goes through the
    // evaluator so the value's type resolution follows the same registry
    // rules as every other value.
    //
    // The evaluator's result is validated EXPLICITLY, not indexed blindly:
    // 0 results and >1 results are distinct failure shapes with distinct
    // meanings, and neither may masquerade as "no vocabulary":
    //
    // - **0 results** — the token atom did not parse/evaluate (the registry
    //   entry and the evaluator's registry disagree, or evaluation broke):
    //   this is an EVALUATOR inconsistency, not a legitimate empty space
    //   (the empty space is the `patterns.length === 0` case above, already
    //   handled). Throwing surfaces the breakage; a silent decline would
    //   misreport it as a sample-space shape.
    // - **>1 results**: the evaluator's determinism policy treats an
    //   ambiguous internal parse as an error (`evalOp` fails loudly rather
    //   than first-picking). A token atom whose parse yields multiple
    //   `TokenVal`s is the same defect shape — report it as an error, don't
    //   sweep an arbitrary first pick.
    // - **a non-token result** (a variant, a closure): the name resolved to
    //   something else entirely — also an evaluator/registry inconsistency
    //   (the gate checked a `DataType`; the evaluator should agree).
    //   Same loud failure.
    const results = [...eval_(type.name, new ValueEnv())]
    const tokens = results.filter((r): r is TokenVal => r instanceof TokenVal)
    if (results.length === 0) {
        // A declaration failure, not a falsification: the message names the
        // broken sampling, not a counterexample (LawError's contract).
        throw new LawDeclarationError(
            type.name,
            `pattern type ${type.name}: the token atom did not evaluate — ` +
                `the evaluator and the type registry disagree`,
        )
    }
    if (tokens.length !== 1 || results.length !== 1) {
        throw new LawDeclarationError(
            type.name,
            `pattern type ${type.name}: the token atom's parse yielded ` +
                `${results.length} results (${tokens.length} tokens) — ` +
                `expected exactly one TokenVal`,
        )
    }
    return tokens
}

/**
 * The pattern language's registry hook: a type reference `<T>` in a pattern
 * resolves through the type registry (the same registry the evaluator and
 * the token gate consult). The hook returns any registered type; the
 * PATTERN-CARRIER narrowing happens at consumption (`patternTypeLookup` —
 * a `<T>` naming a variant-only carrier is not a pattern language, and
 * resolving it would silently count an empty language).
 *
 * The hook is installed by `LawTypeChecker`-carrying check entries: the
 * checker's registry is the language's type registry, and the law checker
 * wires it in once per registry identity (memoized — the hook follows the
 * LAST installed registry, which is correct because a check consults only
 * the registry its own law's checker carries).
 */
let typeRegistryLookup: (name: string) => Type | undefined = () => undefined

/**
 * The pattern language's counting lookup: resolves a type reference name
 * through the installed registry hook (only PATTERN CARRIERS — a `<T>`
 * naming a variant-only carrier (no pattern members) resolves to an EMPTY
 * pattern language, whose counts would read all zero — a silently
 * mis-typed reference; the shared member-shape guard rejects it here so
 * the counting env's own loud "does not resolve to a registered pattern
 * type" error surfaces instead).
 */
function patternTypeLookup(name: string): DataType | undefined {
    const resolved = typeRegistryLookup(name)
    return isPatternCarrierType(resolved) ? resolved : undefined
}

/**
 * Install the type registry for pattern-language type references. Idempotent
 * per registry identity; returns the prior hook for restoration in tests.
 */
export function installPatternLookup(
    lookup: (name: string) => Type | undefined,
): (name: string) => Type | undefined {
    const prior = typeRegistryLookup
    typeRegistryLookup = lookup
    return prior
}

/**
 * The registry-driven law-check entry: installs BOTH pattern-counting hooks
 * (this module's registry lookup and `type_algebra.ts`'s `setPatternLookup`)
 * from the caller's `TypeRegistry` — the SAME registry the evaluator and the
 * checker are bound to — runs `declareCheckedLaw`, and restores the prior
 * hooks after (a check must not leak its registry into a later, differently-
 * bound check).
 *
 * Without this wiring, a pattern containing `<T>` reaches the DEFAULT
 * throwing hooks during `coefficients`/enumeration — screening a referenced
 * pattern type would reject with a `TypeError` instead of resolving the
 * registered type. This is the ONLY entry a checker-carrying declaration
 * needs; `declareCheckedLaw` stays hook-free for callers that pre-install
 * (tests) or never touch type references.
 *
 * @param registry the language's type registry (the one the evaluator and
 *                 the checker carry — the same object identity the token
 *                 gate consults).
 */
export function declareCheckedLawWithRegistry(
    law: Omit<LawDecl, "provenance">,
    omega: OpRegistry,
    laws: LawRegistry,
    registry: TypeRegistry,
    eval_: EvalTerm,
    checker?: LawTypeChecker,
): ReturnType<typeof declareCheckedLaw> {
    const lookup = (name: string): Type | undefined => registry.lookup(name)
    const priorLawChecking = installPatternLookup(lookup)
    const priorTypeAlgebra = setPatternLookup(patternTypeLookup)
    try {
        return declareCheckedLaw(law, omega, laws, eval_, checker, { registry })
    } finally {
        installPatternLookup(priorLawChecking)
        setPatternLookup(priorTypeAlgebra)
    }
}

/**
 * A pattern type's sub-space sweep space: the matched strings' tokens, up to
 * the length bound, optionally filtered by the sub-space predicate.
 *
 * The machineFinite arm's sweep space: each string in the
 * language's enumeration becomes a `TokenVal(text)` — the token is an axiom
 * of the operational semantics, so construction is DIRECT (no evaluator
 * round-trip: the token has no evaluation rule; the evaluator's
 * `matchedToken` is itself this constructor). The enumeration is bounded by
 * `MAX_FINITE_INHABITANTS` (the exhaustion ceiling) and by
 * `MAX_PATTERN_LENGTH` (the string-length reach — the claim the sweep
 * actually certifies is the sub-space ∩ {length ≤ MAX_PATTERN_LENGTH}, so
 * the bound is RECORDED on the returned sweep and carried to the
 * declaration's certificate: a scope whose predicate admits only strings
 * longer than the bound discharges vacuously, and the certificate says so
 * loudly rather than letting the scope masquerade as full sub-space
 * coverage).
 *
 * A sub-space spec filters the enumerated tokens by the predicate (the
 * same `filterSubSpace` contract: a predicate error rejects loudly — a
 * hole cannot shrink a certified space silently). The filter runs BEFORE
 * the budget check: a huge full language with a tiny sub-space is still
 * exhaustible (the scope is the point), so the enumeration materializes
 * per-length up to the exhaustion budget and the FILTERED result must fit
 * `MAX_FINITE_INHABITANTS`.
 *
 * @returns the filtered token space (each element a `TokenVal` of
 *          `type`) WITH the length bound the sweep reached — the
 *          certificate states the sub-space's visible extent, not just
 *          its cardinality.
 *
 * @throws LawDeclarationError when the filtered space is EMPTY (a ∅
 *         sub-space discharge is almost never what the scope's author
 *         meant — the honest reading of a filtered-away scope is a
 *         rejected claim, not a vacuous proof).
 */
function patternSpaceOf(
    type: DataType,
    law: Omit<LawDecl, "provenance">,
    spec: SubSpaceSpec | undefined,
    eval_: EvalTerm,
): readonly TokenVal[] {
    if (type.patterns.length === 0) return []
    const env = makePatternCountEnv(patternTypeLookup)
    // The sweep space: the enumeration's COUNT must fit the exhaustion
    // ceiling — with a scope, the FILTERED result must fit (a huge full
    // language with a tiny sub-space is still exhaustible: the scope is
    // the point).
    const budget = MAX_FINITE_INHABITANTS
    const seen = new Set<string>()
    for (const ast of type.patterns) {
        const strings = enumeratePattern(ast, MAX_PATTERN_LENGTH, env, budget)
        if (strings === undefined) {
            throw new LawDeclarationError(
                law.target,
                `pattern type ${type.name}: the sub-space enumeration exceeds the exhaustion budget — the scope cannot certify the space`,
            )
        }
        for (const text of strings) seen.add(text)
        if (seen.size > budget) {
            throw new LawDeclarationError(
                law.target,
                `pattern type ${type.name}: the sub-space enumeration exceeds the exhaustion budget — the scope cannot certify the space`,
            )
        }
    }
    let enumerated: readonly TokenVal[] = [...seen].map((text) => new TokenVal(type.name, text))
    if (spec) {
        enumerated = filterTokenSubSpace(enumerated, spec, law.target, type.name, eval_)
        if (enumerated.length === 0) {
            throw new LawDeclarationError(
                law.target,
                `pattern type ${type.name}: the sub-space predicate "${spec.where}" (position ${spec.position}) admits NO string of length ≤ ${MAX_PATTERN_LENGTH} — an empty sub-space discharges vacuously, which is almost never the scoped claim the author meant; the declaration is rejected (state the intended range in the scope predicate)`,
            )
        }
    }
    return enumerated
}

/*
 * The string-length bound for the machineFinite arm's enumeration: the
 * sub-space sweep is a DECIDABLE-BOUNDED space — the scope's predicate
 * restricts membership, and the enumeration materializes strings up to this
 * length (the length bound rides on sized types; the exhaustion ceiling
 * bounds the COUNT). A scope whose filtered space fits the ceiling is
 * exhaustible even over a huge language (e.g. a length predicate on
 * `[0-9]+`): the enumeration walks per-length classes and declines only
 * when the length reach itself is past the budget.
 */
const MAX_PATTERN_LENGTH = 4

/**
 * Filter enumerated tokens by a sub-space predicate (the token-carried
 * variant of `filterSubSpace` — the predicate binds `a` to the token).
 */
function filterTokenSubSpace(
    tokens: readonly TokenVal[],
    spec: SubSpaceSpec,
    opName: string,
    typeName: string,
    eval_: EvalTerm,
): readonly TokenVal[] {
    const kept: TokenVal[] = []
    for (const token of tokens) {
        const rho = new ValueEnv(new Map([["a", token as Value]]))
        const results = [...eval_(spec.where, rho)]
        const verdict = results[0]
        if (
            results.length !== 1 || verdict === undefined ||
            verdict instanceof EvalErrorValue
        ) {
            throw new LawDeclarationError(
                opName,
                `sub-space predicate "${spec.where}" on ${typeName} did not evaluate to a single verdict — the scope cannot certify the space`,
            )
        }
        if (verdict.equals(TRUE_VALUE)) kept.push(token)
    }
    return kept
}

// ── The certified prefix (the size-bounded enumerator) ───────────────────────

/**
 * The certified screen's size bound: positions certify their full size-≤ k
 * classes up to this size (parity with the ∂T shrinker's chain reach:
 * `sampleDepth = 2` ⇒ sizes ≤ 3 for chain carriers — chain-carrier sweeps
 * keep their shrinker-compatible reach).
 */
const MAX_SCREEN_SIZE = 3

/**
 * The per-position instance ceiling for the certified prefix: a position's
 * certified space (the size-≤ kᵢ class set) must stay within this budget,
 * or the certification declines. Bounds the enumerator's footprint (real
 * `VariantVal`s, memoized per distinct type — the same discipline as
 * exhaustion's `MAX_FINITE_INHABITANTS`).
 */
const PREFIX_BUDGET = 2 ** 8

/**
 * The sweep ceiling across ALL positions (the projected assignment count ×
 * instances per assignment): the certified sweep must stay within this
 * budget, or the certification declines. Mirrors `MAX_EXHAUSTION_INSTANCES`
 * at a tighter bound (the screen runs on every residual declaration).
 */
const SWEEP_BUDGET = 2 ** 16

/**
 * The floor-raise probe's degree ceiling: how far the minimum-nonempty-class
 * search grows past `MAX_SCREEN_SIZE` before declaring the carrier
 * uninhabited. Bounded by the exhaustion budget's spirit — a record wider
 * than ~2⁰ Bool fields per class step is unreachable in practice, and the
 * prefix budget's own excess check declines earlier for genuinely wide
 * carriers. Generous enough that any realistic record width is reached
 * (an n-Bool flat record's min class is n+1; 18 Bools → 19, well within).
 */
const MAX_PROBE_DEGREE = 32

/**
 * A position's certified coverage: the size bound and the two sides of the
 * certificate (expected from the coefficients, actual from the sweep).
 */
export interface CertifiedPosition {
    /** The certified size bound (all inhabitants of size ≤ k). */
    readonly k: number
    /** The type's name (for the report). */
    readonly typeName: string
    /** The coefficient count: exactly how many inhabitants size ≤ k holds. */
    readonly expected: number
    /** How many distinct samples the sweep actually produced. */
    readonly actual: number
}

/**
 * The certified-coverage report the screen's outcome carries: per-position
 * certificates plus the rendered claim. Evidence, never proof — the
 * provenance ladder is unchanged (certification upgrades the claim's
 * precision, not its authority tier); this upgrades WHAT the screen's
 * evidence claims, from "N instances" to a verified prefix.
 */
export interface CertifiedCoverage {
    readonly positions: readonly CertifiedPosition[]
    /** The rendered theorem: "all inhabitants of size ≤ k per position — exactly N, verified". */
    readonly claim: string
}

/**
 * Enumerate ALL inhabitants of a data type up to a size bound, LAZILY and
 * COMPLETELY: the size-≤ k class set, bottom-up over (type, size) so
 * subvalue spaces are shared (the same per-type memo discipline as
 * exhaustion's `spaceOf`).
 *
 * The result is exactly what `coefficients(type, k)`'s prefix counts: a
 * pattern type yields its singleton name-token only when k ≥ 1 (the token
 * is a size-1 inhabitant; a size-≤ 0 prefix is EMPTY, matching c₀ = 0); a
 * data type's walk covers every size class 1..k.
 *
 * This is the upgrade the certification requires: a depth-bounded sampler
 * is NOT a size prefix for branching or wide carriers — it takes one field
 * sample per variant (`construct` binds `fieldSamples[0]`), so
 * `One(False())` is never sampled and a depth-2 Tree sweep contains one
 * size-5 tree while omitting the other. A size-indexed sweep is complete
 * WITHIN each size class: every combination of field values whose total
 * node count is ≤ k is produced exactly once.
 *
 * Field spaces follow the coefficient reading's own table (type-algebra.md
 * §3): a recursive field draws from the CARRIER's smaller sizes (the comb's
 * algebra is the carrier — even for inherited variants); a data field from
 * that type's space; a pattern field is the singleton token; a variant with
 * an unsampleable field (function/`Any`/pattern/token/`Nothing`) contributes
 * nothing (the same unsampleable rule everywhere).
 *
 * Construction goes through the evaluator (as everywhere else): a variant
 * whose constructor form fails to evaluate is a HOLE in the certificate —
 * the enumerated count would fall short of the coefficient count, so the
 * caller rejects the declaration loudly (completeness is the certified
 * contract; the screen's skip only ever applied to instance evaluation,
 * never to sample construction).
 *
 * @param type the carrier (μ data type, or a pattern type for the declared
 *             fallback)
 * @param k    the certified size bound (all inhabitants of size ≤ k); a
 *             NEGATIVE bound is a caller bug — a `RangeError` surfaces it
 *             (k = 0 is valid: the size-≤ 0 prefix is empty, c₀ = 0)
 * @param eval_ the evaluation primitive (see `makeEvalTerm`)
 * @returns the deduped size-≤ k inhabitants; the count is what the
 *          certificate asserts (and what the caller asserts against
 *          `coefficients`).
 *
 * @throws RangeError when k < 0 (an invalid bound — the coefficients
 *         reading rejects it the same way).
 */
export function inhabitantsUpToSize(
    type: DataType,
    k: number,
    eval_: EvalTerm,
): readonly Value[] {
    if (k < 0) {
        throw new RangeError(`inhabitantsUpToSize(${type.name}): the size bound k must be ≥ 0`)
    }
    if (type instanceof DataType && type.patterns.length > 0) {
        // The language-equation enumeration: the carrier's PATTERN members'
        // size-≤ k token set — every matched string of length ≤ k becomes a
        // token (`TokenVal(type, text)`; the token is an axiom of the
        // operational semantics, its text carried directly), INCLUDING the
        // ε string when the language is nullable (`a*`, `a?`): its size is
        // 0, so it is the size-0 class's sole member — c₀ counts it, and
        // the size-≤ k prefix must hold it or the enumerator under-reports
        // the coefficient count. The read goes through the type's UNION
        // (`typeUnionStrings` — variants may overlap; one merged set), so
        // the enumerator and the coefficients read the same language. A
        // prefix past the budget is a DECLINE (the caller rejects loudly —
        // an enumeration hole must not masquerade as coverage).
        const strings = typeUnionStrings(type, k, PREFIX_BUDGET)
        if (strings === undefined) {
            throw new LawDeclarationError(
                type.name,
                `the size-≤ ${k} enumeration exceeds the prefix budget — the certificate declines (an enumeration hole must not masquerade as coverage)`,
            )
        }
        const tokens: Value[] = [...strings]
            .map((text) => new TokenVal(type.name, text))
        if (type.variants.length === 0) {
            // A pattern-ONLY carrier's space is exactly the token set —
            // sort to the certificate's per-length order and return.
            return tokens.sort((a, b) => a.size() - b.size())
        }
        // A MIXED carrier's space is the UNION of both member kinds — the
        // token walk above PLUS the variant-system walk below (the same
        // composition `coefficients` runs: variant inhabitants are
        // `VariantVal`s, pattern inhabitants are tokens, kind-disjoint
        // universes whose prefixes merge). Omitting either kind would make
        // the certified sweep under-cover the space the coefficients
        // count — the certificate's mismatch check would reject (or worse,
        // a field-space read would silently shrink).
        const variantSpace = spaceUpToSize(
            type,
            k,
            eval_,
            new Map(),
            new Map(),
        )
        return [...variantSpace, ...tokens].sort((a, b) => a.size() - b.size())
    }
    const spaces = new Map<DataType, readonly VariantVal[]>()
    const degrees = new Map<DataType, number>()
    return spaceUpToSize(type, k, eval_, spaces, degrees)
}

/**
 * A type's deduped size-≤ k space, materialized at most once per
 * certification (the memo is shared across operand positions and variant
 * fields — a carrier appearing in several places is enumerated a single
 * time).
 *
 * The walk is BOTTOM-UP over size classes: a size-n value is a variant node
 * plus field combinations of total size n−1, so class n is built only after
 * all smaller classes of the SAME carrier are complete — the same fixpoint
 * shape the coefficient reading's `currentFor` applies (a recursive field
 * reads the carrier's SMALLER-size space through the memo; the memo grows
 * with each completed class). A data field's space is that type's ≤ n−1
 * space, grown through the same memo discipline (an inner type's walk
 * registers its own completed degree).
 *
 * The memo (`spaces` + `degrees`) is PER-CERTIFICATION, and its two maps
 * move together: degree metadata next to the values it describes. A
 * module-global degree map would outlive its walk and VOUCH FOR A PREFIX
 * THE CURRENT MEMO NEVER BUILT — a later certification (a fresh `spaces`)
 * would read a stale completed degree and trust an empty array as a full
 * prefix.
 *
 * **Re-entrancy.** A field can name its own carrier WITHOUT the recursive
 * flag (a data field typed as the carrier itself), and mutual systems
 * (A's field references B, B's references A) re-enter the walk mid-build.
 * An IN-PROGRESS type (seeded in the memo, degree 0 — not yet complete) is
 * served its PARTIAL prefix and is NOT rebuilt: the re-entrant reader needs
 * exactly the smaller classes the outer walk has already completed, and
 * clearing the memo would silently DROP them. The outer walk reads its own
 * partial prefix the same way (the recursive-field branch), so both
 * re-entrancy shapes extend rather than reset.
 */
function spaceUpToSize(
    type: DataType,
    k: number,
    eval_: EvalTerm,
    spaces: Map<DataType, readonly VariantVal[]>,
    degrees: Map<DataType, number>,
): readonly VariantVal[] {
    // A previous walk (within this same certification) that already
    // completed degree ≥ k has the full prefix in the memo — reuse it (a
    // completed degree is the certificate's contract: classes 1..degree
    // are complete).
    const cached = spaces.get(type)
    const cachedDegree = degrees.get(type) ?? -2
    if (cached && cachedDegree >= k) return cached
    // An IN-PROGRESS entry (seeded by an outer walk of THIS type — marker
    // degree −1, never yet completed) serves its PARTIAL prefix: the caller
    // needs exactly the smaller-size space the outer walk has built so far.
    // Rebuilding here would re-enter the running walk; clearing the memo
    // would drop its already-enumerated classes — a silent loss the
    // certificate would then miscount as an enumeration hole. The marker is
    // −1, NOT 0: a COMPLETED k=0 walk also carries degree 0 (its empty
    // prefix is a real, complete result) and must be distinguishable from
    // the seed — otherwise an inner k=0 walk (a data field whose space is
    // empty at this size) would mark its type in-progress forever, and the
    // NEXT size class would read that type's field space as the stale empty
    // array instead of re-walking at the new degree.
    if (cached && cachedDegree === -1) return cached
    // Seed the memo BEFORE the walk: a re-entrant request for this type
    // (through a self-typed non-Family data field, or a mutual pair) sees
    // the in-progress marker (degree −1) and never rebuilds. The empty
    // prefix is CORRECT at the walk's start — class 1's Family fields
    // read exactly this empty array.
    spaces.set(type, [])
    degrees.set(type, -1)
    // Productive variants: those whose every field has sample vocabulary.
    // A variant with an unsampleable field contributes nothing — matched by
    // the zero polynomial in `coefficients` (the same unsampleable rule
    // everywhere). A pattern-BEARING field carrier is NOT unsampleable: its
    // space is the token classes (the language-equation enumeration), even
    // though `finiteInhabitants`' variant-system count reads 0 for it — the
    // field's token walk below enumerates its members. Stage 5's
    // member-shape counting replaces this interim exception.
    const variants = type.allVariants().filter((variant) => {
        const fieldTypes = variant.fields.map((field) => field.type)
        if (
            fieldTypes.some((t) =>
                t instanceof DataType && t.patterns.length === 0 &&
                (finiteInhabitants(t) ?? 1) === 0
            )
        ) {
            return false
        }
        return variant.fields.every((field) => {
            const fieldType = field.type
            if (fieldType instanceof FamilyType) return true
            // A data field is sampleable iff the carrier carries members:
            // variants (the space walk) or patterns (the token read) — a
            // bare carrier (no members) is a zero-inhabitant field, caught
            // by the empty-field filter above.
            if (fieldType instanceof DataType) {
                return fieldType.variants.length > 0 || fieldType.patterns.length > 0
            }
            return false
        })
    })
    for (let size = 1; size <= k; size++) {
        const classValues: VariantVal[] = []
        for (const variant of variants) {
            // Each field's space at this size: recursive → the carrier's
            // ≤ size−1 space (the memo's completed prefix); data field →
            // that type's ≤ size−1 space (grown through the shared memo);
            // pattern field → the singleton token; unsampleable → empty.
            const fieldSpaces: readonly (readonly Value[])[] = variant.fields.map((
                field,
            ) => {
                const fieldType = field.type
                if (fieldType instanceof FamilyType) return spaces.get(type) ?? []
                if (fieldType instanceof DataType && fieldType.variants.length > 0) {
                    // The field carrier's variant-member space at this size
                    // (the ≤ size−1 prefix, grown through the shared memo).
                    const variantSpace = spaceUpToSize(fieldType, size - 1, eval_, spaces, degrees)
                    if (fieldType.patterns.length === 0) {
                        // A variants-only field carrier's space is exactly
                        // the walk's result.
                        return variantSpace
                    }
                    // A MIXED field carrier's space unions BOTH kinds: the
                    // variant walk's values PLUS the field's own per-length
                    // tokens (the same composition the coefficients' token
                    // arm runs — omitting the token members would shrink a
                    // With(p)-shaped mixed field's space and the class
                    // filter would silently drop constructions the
                    // coefficients count).
                    const tokenLen = size - 1
                    const strings = typeUnionStrings(fieldType, tokenLen, PREFIX_BUDGET)
                    const fieldTokens: readonly Value[] = strings === undefined ? [] : [...strings]
                        .filter((text) => text.length === tokenLen)
                        .map((text) => new TokenVal(fieldType.name, text))
                    return [...variantSpace, ...fieldTokens]
                }
                if (fieldType instanceof DataType && fieldType.patterns.length > 0) {
                    // The pattern field's space at this size: the TRUE
                    // size-EXACT (size−1) token set from the field type's
                    // UNION (`typeUnionStrings` — the field's language is
                    // the union of ALL its declared patterns; enumerating
                    // `patterns[0]` alone would drop every later variant's
                    // strings and silently shrink a With(p) carrier's
                    // space) — the size measure is TEXT LENGTH
                    // (`Value.size`'s token arm), so the field's space and
                    // the coefficients agree: a size-n With(p) needs a
                    // token of EXACTLY length n−1 (the class filter below
                    // enforces the total, so the field space must be
                    // per-length, not per-prefix). Budget-capped; an
                    // over-budget pattern field contributes nothing (the
                    // variant is dropped, and the certificate's mismatch
                    // check surfaces the hole loudly if it mattered).
                    const strings = typeUnionStrings(fieldType, size - 1, PREFIX_BUDGET)
                    const tokenLen = size - 1
                    return strings === undefined ? [] : [...strings]
                        .filter((text) => text.length === tokenLen)
                        .map((text) => new TokenVal(fieldType.name, text))
                }
                return [] as readonly Value[]
            })
            for (const combo of cartesian(fieldSpaces)) {
                const totalSize = 1 + combo.reduce((sum, v) => sum + v.size(), 0)
                if (totalSize !== size) continue
                const argNames = variant.fields.map((_, i) => `f${i}`)
                const bindings = new Map<string, Value>()
                combo.forEach((value, i) => bindings.set(argNames[i]!, value))
                const source = `${variant.name}(${argNames.join(", ")})`
                // The construction's result is validated EXPLICITLY — not
                // indexed blindly and not trusted because it is *a* value:
                //
                // - **exactly one result** — the evaluator's determinism
                //   policy treats an ambiguous internal parse as an error
                //   (`evalOp` fails loudly rather than first-picking). A
                //   constructor form whose parse yields multiple results is
                //   the same defect shape — report it, never sweep an
                //   arbitrary first pick.
                // - **the carrier matches** — the value's stamped `dataType`
                //   must be THIS carrier (identity, not name: two distinct
                //   DataType instances can share a name). A registry
                //   collision (two carriers registering the same variant
                //   name) makes the evaluator resolve the source to the
                //   WRONG carrier's variant — a value that does not belong
                //   in this prefix would pass the coefficient equality
                //   while corrupting the sweep.
                // - **the variant name and field shape match** — the value
                //   must be THIS variant with exactly the declared fields'
                //   arity (a registry collision can return another
                //   carrier's same-named variant with different fields).
                // Any other shape is a hole in the certificate: the
                // enumerated count would silently diverge from what the
                // coefficients count, so the hole rejects loudly instead of
                // masquerading as coverage.
                const results = eval_(source, new ValueEnv(bindings))
                if (results.length !== 1) {
                    throw new LawDeclarationError(
                        type.name,
                        `certification could not construct an inhabitant: "${source}" ` +
                            `yielded ${results.length} results — the certified ` +
                            `prefix requires exactly one (an ambiguous parse is ` +
                            `an evaluator inconsistency, never swept)`,
                    )
                }
                const value = results[0]
                if (
                    !(value instanceof VariantVal) || value.dataType !== type ||
                    value.variantName !== variant.name ||
                    value.fields.size !== variant.fields.length
                ) {
                    throw new LawDeclarationError(
                        type.name,
                        `certification could not construct an inhabitant: "${source}" ` +
                            `did not evaluate to this carrier's variant — the ` +
                            `evaluator and the type registry disagree (a registry ` +
                            `collision would put a foreign value in the certified ` +
                            `prefix)`,
                    )
                }
                classValues.push(value)
            }
        }
        // Extend the memo with the completed class (deduped against
        // everything so far — the sweep sees each distinct value once).
        const grown = [...dedupe([...(spaces.get(type) ?? []), ...classValues])]
        spaces.set(type, grown)
    }
    // The completed degree registers the certificate's coverage: later
    // readers at degree ≤ k reuse this space; a HIGHER degree re-walks
    // (the classes beyond k are built then).
    degrees.set(type, k)
    return spaces.get(type) ?? []
}

// ── The certification (the per-position kᵢ policy) ─────────────────────────

/**
 * Certify one operand position: choose its size bound kᵢ, enumerate the
 * full size-≤ kᵢ prefix, and assert the count against `coefficients` —
 * the theorem, machine-checked.
 *
 * The kᵢ policy:
 * 1. The smallest nonempty size class min S(T) (from the coefficients).
 * 2. Candidate kᵢ = min(MAX_SCREEN_SIZE, max { k | prefix(k) ≤ PREFIX_BUDGET }),
 *    RAISED to min S(T) when min S(T) > MAX_SCREEN_SIZE (the wide-record
 *    escape: without it every record wider than three fields would decline
 *    — a Triple(a, b, c) has no inhabitants below size 4).
 * 3. If the raised kᵢ's prefix exceeds PREFIX_BUDGET, the certification
 *    declines loudly (LawDeclarationError naming the blocking class).
 *
 * @returns the position's certificate; the enumeration is a side effect
 *          (the certified samples ARE the screen's sweep space).
 *
 * @throws LawDeclarationError when the smallest nonempty class exceeds the
 *         prefix budget (the certificate cannot be swept), or when the
 *         enumerated count mismatches the coefficient count (a hole in the
 *         sweep — the loud error the certificate requires).
 */
function certifyPosition(
    type: DataType,
    eval_: EvalTerm,
): CertifiedPosition {
    const coeffs = coefficients(type, MAX_SCREEN_SIZE)
    // The smallest nonempty size class (the prefix's floor).
    const minClass = coeffs.findIndex((c) => c > 0)
    if (minClass < 0) {
        // No inhabitants up to MAX_SCREEN_SIZE: either the carrier's
        // smallest class is beyond the range (the wide-record escape —
        // raised below), or it is uninhabited. DERIVE the minimum nonempty
        // degree by growing the probe one class at a time — a fixed guess
        // cannot reach every record width (a 7-Bool record's first
        // inhabitant is size 8: the constructor plus seven fields; an
        // 18-Bool record's is size 19). The growth is bounded by the prefix
        // budget itself: the probe stops as soon as a single class exceeds
        // PREFIX_BUDGET (a wider class only holds more, so a later class
        // cannot fit either — the certification would decline there
        // anyway), and a probe that grows PAST the budget without ever
        // finding a nonzero class means the carrier is genuinely
        // uninhabited (StreamLike: its only variant is recursive with no
        // base case — no class exists at ANY size).
        let probeDegree = MAX_SCREEN_SIZE
        let probeMin = -1
        let probeCoeff = 0
        while (true) {
            probeDegree++
            const probe = coefficients(type, probeDegree)
            probeCoeff = probe[probeDegree]!
            if (probeCoeff > 0) {
                probeMin = probeDegree
                break
            }
            // A single class larger than the budget certifies nothing —
            // growing further only finds bigger classes (the coefficient
            // sequence is nondecreasing in class width for these shapes...).
            // Not true in general (coefficients can dip), but a class past
            // the budget cannot be certified, and SMALLER classes between
            // here and there would have appeared already; keep probing only
            // while the class stays within budget.
            if (probeCoeff > PREFIX_BUDGET) {
                throw new LawDeclarationError(
                    type.name,
                    `certification declined: the smallest nonempty size class ` +
                        `holds ${probeCoeff} inhabitants at size ${probeDegree} ` +
                        `— past the prefix budget (${PREFIX_BUDGET}); the screen ` +
                        `cannot certify this carrier`,
                )
            }
            if (probeDegree >= MAX_PROBE_DEGREE) {
                throw new LawDeclarationError(
                    type.name,
                    `certification declined: the type has NO inhabitants in the ` +
                        `certified size range (c₁..c${probeDegree} are all 0) — ` +
                        `zero coverage, nothing installed`,
                )
            }
        }
        // The smallest class is at probeMin > MAX_SCREEN_SIZE: certify
        // exactly that class (the floor raise), if it fits the budget.
        const raisedPrefix = probeCoeff
        if (raisedPrefix > PREFIX_BUDGET) {
            throw new LawDeclarationError(
                type.name,
                `certification declined: the smallest nonempty size class ` +
                    `${probeMin} holds ${raisedPrefix} inhabitants — past ` +
                    `the prefix budget (${PREFIX_BUDGET}); the screen cannot ` +
                    `certify this carrier`,
            )
        }
        const samples = inhabitantsUpToSize(type, probeMin, eval_)
        if (samples.length !== raisedPrefix) {
            throw new LawDeclarationError(
                type.name,
                `certification MISMATCH: the size-≤ ${probeMin} sweep produced ` +
                    `${samples.length} samples but the type equation counts ` +
                    `${raisedPrefix} — an enumeration hole would masquerade as ` +
                    `coverage, so the declaration is rejected (check the ` +
                    `registry/evaluator consistency)`,
            )
        }
        return {
            k: probeMin,
            typeName: type.name,
            expected: raisedPrefix,
            actual: samples.length,
        }
    }
    // The largest k whose prefix fits the per-position budget (candidates
    // only above the floor — sizes below minClass contribute nothing).
    let k = 0
    let prefix = 0
    for (let n = minClass; n <= MAX_SCREEN_SIZE; n++) {
        const next = prefix + coeffs[n]!
        if (next > PREFIX_BUDGET) break
        prefix = next
        k = n
    }
    const samples = inhabitantsUpToSize(type, k, eval_)
    if (samples.length !== prefix) {
        throw new LawDeclarationError(
            type.name,
            `certification MISMATCH: the size-≤ ${k} sweep produced ` +
                `${samples.length} samples but the type equation counts ` +
                `${prefix} — an enumeration hole would masquerade as ` +
                `coverage, so the declaration is rejected (check the ` +
                `registry/evaluator consistency)`,
        )
    }
    return { k, typeName: type.name, expected: prefix, actual: samples.length }
}

/**
 * Certify the screen's per-position coverage and return the report:
 * per-position certificates plus the rendered claim. The sweep projection
 * (the same exponent arithmetic `screeningRegime` runs) must stay within
 * `SWEEP_BUDGET` — a projected sweep past the budget declines loudly (the
 * screen would otherwise silently sweep a space it cannot hold).
 *
 * @throws LawDeclarationError from any position's certification (see
 *         `certifyPosition`), or when the projected sweep exceeds the
 *         budget.
 */
function certifyCoverage(
    op: CheckedOpSig,
    exponents: readonly number[],
    instancesPerAssignment: number,
    eval_: EvalTerm,
): { coverage: CertifiedCoverage; positionSamples: Value[][] } {
    const positions: CertifiedPosition[] = []
    const positionSamples: Value[][] = []
    let sweep = instancesPerAssignment
    for (let position = 0; position < op.paramTypes.length; position++) {
        const type = op.paramTypes[position]!
        // A position no schema variable lands on is never swept: its
        // certification is irrelevant (and its samples are empty — the
        // assignments generator never reads them).
        if (exponents[position] === 0) {
            positionSamples.push([])
            continue
        }
        const certified = certifyPosition(type as DataType, eval_)
        positions.push(certified)
        const samples = inhabitantsUpToSize(
            type as DataType,
            certified.k,
            eval_,
        )
        positionSamples.push([...samples])
        sweep *= certified.actual ** exponents[position]!
        if (sweep > SWEEP_BUDGET) {
            throw new LawDeclarationError(
                op.name,
                `certification declined: the certified sweep exceeds the ` +
                    `sweep budget (${SWEEP_BUDGET}) — position ${position} ` +
                    `(${certified.typeName}) certifies ${certified.actual} ` +
                    `samples at exponent ${exponents[position]}`,
            )
        }
    }
    const total = positions.reduce((sum, p) => sum + p.expected, 0)
    const bounds = positions.map((p) => `size ≤ ${p.k} (${p.typeName})`).join(" × ")
    const claim = `all inhabitants of ${bounds} per operand position — exactly ${total} verified`
    return { coverage: { positions, claim }, positionSamples }
}

/**
 * The checking regime the law-checking pass applies (semantics.md §5.4):
 *
 * - **`finite`** — the operand carrier has a bounded inhabitant space
 *   (≤ `MAX_FINITE_INHABITANTS`) and the law's schema sweep over it stays
 *   within budget, so the law can be checked exhaustively — a passing
 *   exhaustion establishes it (`discharged` provenance).
 * - **`machineFinite`** — a pattern carrier (or a data carrier over
 *   pattern-typed fields) WITH a sub-space spec on every swept position:
 *   structural exhaustion is permanently unavailable to pattern types
 *   (type-algebra.md §2.3 — their generating functions are rational), but a
 *   law scoped to a decidable sub-space ("all Ints with |x| ≤ 2³¹") can be
 *   exhausted WITHIN it — a passing scoped sweep establishes the SCOPED claim
 *   (`discharged` provenance; the scope rides on the declaration as visible
 *   provenance, and the claim is `asserted` beyond the range by the same
 *   honesty that scoped any claim). The restricted sweep must fit
 *   `MAX_EXHAUSTION_INSTANCES`.
 * - **`residual`** — everything else (unbounded-depth μ-types, pattern
 *   carriers without a total sub-space spec, or a space beyond the budget):
 *   the certified screen applies, falsifying only — `asserted` provenance.
 * - **`derivable`** — a residual-shaped claim whose target operation's
 *   definition is in the derivable handler fragment (a fold-built lambda
 *   chain over a parameter — the recursion axis; `derivation.ts`'s
 *   characterization): the BMF derivation engine attempts a bounded,
 *   search-free induction over the fold schema from the called ops'
 *   primitive/discharged laws. A closing derivation is a PROOF
 *   (`discharged` provenance, with the derivation certificate); a claim
 *   the engine cannot close falls back to the residual screen (falsifying
 *   only — the honest residual, unchanged).
 */
export type ScreeningRegime = "finite" | "machineFinite" | "residual" | "derivable"

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
 * The counting judgment lives on `type_algebra.ts`'s `TypeAlgebra` class
 * (the counting classifier is the third reading of the same type equations
 * `derivative` and `coefficients` read); this module re-exports the
 * free-function surface its consumers and tests use, delegating to the
 * module default instance. The full contract (the field-kind rules, the
 * saturation arithmetic, the persistent identity-keyed memo) lives on
 * `TypeAlgebra.inhabitants`.
 */
export function finiteInhabitants(type: DataType): number | undefined {
    return finiteInhabitantsFromAlgebra(type)
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
 * residual's certified screen.
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
    let patternCarrierPositions = 0
    for (let position = 0; position < op.paramTypes.length; position++) {
        // A position no variable lands on is never swept: its carrier's
        // size is irrelevant (this is what keeps an identity claim over
        // (Bool, 2¹⁸) exhaustible — only position 0 is ever enumerated).
        if (exponents[position] === 0) continue
        if (isPatternCarrierType(op.paramTypes[position])) {
            // A pattern carrier routes machineFinite ONLY when the law
            // scopes it: structural exhaustion is never honest for one
            // (type-algebra.md §2.3 — a pattern type's generating function
            // is rational, unbounded in total), but a sub-space spec makes
            // the SWEPT space finite and spec-able. An unscoped pattern
            // carrier routes residual (the certified screen's token
            // samples cover a certified prefix instead).
            //
            // The MIXED refinement: a carrier with BOTH member kinds is
            // not fully swept by the sub-space machinery
            // (`patternSpaceOf` enumerates the token language only — the
            // variant members' space is outside its reach, and may be
            // unbounded). Its certified screen composes both kinds (see
            // `inhabitantsUpToSize`), so a mixed carrier routes residual
            // — scoped or not — and the machineFinite arm stays
            // pattern-only carriers (patterns > 0, variants = 0).
            const carrier = op.paramTypes[position]! as DataType
            if (
                carrier.variants.length === 0 &&
                law.subSpace?.some((spec) => spec.position === position)
            ) {
                patternCarrierPositions++
                continue
            }
            return "residual"
        }
        if (!(op.paramTypes[position]! instanceof DataType)) {
            return "residual"
        }
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
    if (patternCarrierPositions > 0) return "machineFinite"
    return "finite"
}

/**
 * Upgrade a residual-routed claim to `derivable` when the target operation's
 * definition passes the derivable fragment's cheap syntactic gate
 * (semantics.md §5.4's `derivable` row: "Any type, if the fold's handler
 * bodies fall in the primitive-law derivation fragment").
 *
 * The gate is budget-free and syntactic (a lambda chain over the declared
 * parameters whose body is a fold over one of the parameters — the
 * recursion axis — one handler per axis variant): it admits nothing about
 * CLOSURE (the derivation's own outcome); it only decides whether the
 * derivable regime's engine gets its attempt. A gate failure routes
 * residual — the additive-union discipline: a routing outcome is only ever
 * refined, never re-routed, when the gate declines.
 */
function upgradeToDerivable(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    registry: TypeRegistry,
    omega: OpRegistry,
): ScreeningRegime {
    return derivableFragment(law, op, registry, omega) ? "derivable" : "residual"
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
 * - `residual` regime → `screenLaw` (certified size prefixes) → installed
 *   **`asserted`** on a passing screen (evidence, not proof).
 * - `machineFinite` regime → `exhaustLaw` (the sub-space-scoped sweep) →
 *   installed **`discharged`** on a full-coverage pass over the
 *   certified sub-space; the scope rides on the declaration as the visible
 *   provenance of what the tag covers (`asserted` beyond the range is the
 *   honest reading of any scoped claim).
 *
 * Validation runs BEFORE the check: a vocabulary/argument/arity/typing
 * error surfaces as `LawDeclarationError` — never as a screen artifact (a
 * `TypeError` from an unknown kind, or zero-coverage silence). The check
 * runs second, so a falsified claim never enters `E`.
 *
 * **Zero-coverage rejection:** a `residual`-regime law whose screen yielded
 * zero evidence — EITHER because it *declined* (no sample vocabulary; the
 * domain is unscreenable) OR because the sweep *passed with 0 checked*
 * instances (every drawn sample was a hole) — is REJECTED, not installed:
 * `asserted` means "the screen found no counterexample", and a claim the
 * screen never exercised carries no such evidence. (Exhaustion's
 * zero-coverage case — a vacuous claim over an empty carrier — stays
 * honest: there the count 0 records a *complete* sweep over ∅, a real
 * proof shape.)
 *
 * Returns `{ law, instances, regime, coverage, subSpaceSweep, derivation }`
 * — the installed declaration, the number of instances checked, the regime
 * that produced it, and the COVERAGE certificate: for the residual regime
 * the screen's certified-coverage report; for the machineFinite regime the
 * sub-space sweep's shape (`subSpaceSweep` — the length bound the sweep
 * reached and each scoped position's admitted cardinality; the visible
 * extent of what `discharged` covers, since the scope's predicate is the
 * claim's domain but the sweep certifies only the strings the
 * length-bounded enumeration reached); for the derivable regime the
 * derivation certificate (`derivation` — which cases closed how and which
 * axioms the proof consumed). Undefined for the plain finite regime (a
 * discharged law's coverage is the full space, which the regime itself
 * already certifies).
 *
 * @throws LawError when the check falsifies the law (nothing is installed).
 * @throws LawDeclarationError when the claim is not in the closed vocabulary,
 * is structurally ill-formed (from `LawRegistry.validateLaw`) — in the
 * `finite` regime — an instance of the axiom fails to evaluate (a
 * `discharged` tag must mean full coverage; holes in the sweep are a
 * rejected declaration, not silent under-coverage), or — in the `residual`
 * regime — the screen exercised the claim zero times (declined: an
 * unscreenable domain or an empty sample space; or passed with 0 checked:
 * every drawn sample was a hole).
 */
export function declareCheckedLaw(
    law: Omit<LawDecl, "provenance">,
    omega: OpRegistry,
    laws: LawRegistry,
    eval_: EvalTerm,
    checker?: LawTypeChecker,
    registries?: { readonly registry: TypeRegistry },
): {
    law: LawDecl
    instances: number
    regime: ScreeningRegime
    coverage: CertifiedCoverage | undefined
    /** The machineFinite sweep's visible extent (undefined off that regime). */
    subSpaceSweep: SubSpaceSweep | undefined
    /** The derivation certificate (defined only on the derivable regime). */
    derivation: DerivationCertificate | undefined
} {
    const op = omega.lookup(law.target)
    if (!op) {
        throw new LawDeclarationError(law.target, "the target operation is not declared in Ω")
    }
    // Structural validation FIRST (loud, typed errors), then the regime check.
    const structuralReason = laws.validateLaw(law, omega, checker)
    if (structuralReason !== undefined) {
        throw new LawDeclarationError(law.target, structuralReason)
    }
    // Regime dispatch (semantics.md §5.4): finite/machineFinite → exhaustive
    // discharge (the latter over the sub-space); residual → the certified
    // screen. A residual-shaped claim whose definition passes the derivable
    // fragment's gate upgrades to `derivable` (the registries threaded from
    // the registry-carrying entry; a registry-free caller — tests that
    // pre-install hooks — routes residual as always). The check runs BEFORE
    // installing: a falsified claim never enters E.
    let regime = screeningRegime(law, op)
    if (regime === "residual" && registries !== undefined) {
        regime = upgradeToDerivable(law, op, registries.registry, omega)
    }

    // The derivable arm: attempt the derivation. A closing derivation is a
    // PROOF (discharged, with the certificate); the belt-and-braces screen
    // certification runs before installation — an engine bug that fabricates a bogus
    // proof becomes a loud LawError on concrete instances. A non-closing
    // derivation is a DECLINE, not a falsification: the claim falls through
    // to the residual screen, and the returned regime names the mechanism
    // that produced the outcome ("residual" — the screen established the
    // provenance).
    let derivation: DerivationCertificate | undefined
    if (regime === "derivable") {
        if (registries === undefined) {
            // A registry-free caller cannot reach the gate (the upgrade above
            // needs it); this arm is unreachable through the public entries.
            regime = "residual"
        } else {
            const result = deriveLaw(law, op, registries.registry, omega, laws)
            if ("derivable" in result) {
                // Not-derivable: fall back to the residual screen (the
                // claim proceeds to screening).
                regime = "residual"
            } else {
                // The belt-and-braces screen: the certified prefix sweep
                // runs exactly as for the residual. A falsifying sample
                // throws — nothing installs (the screen wins over a bogus
                // proof). A DECLINING screen (no sample vocabulary) skips
                // the guard: decline is not falsification.
                const guardScreen = screenLaw(law, op, omega, eval_)
                const screened = guardScreen.outcome === "passed" ? guardScreen.checked : undefined
                if (guardScreen.outcome === "passed" && guardScreen.checked === 0) {
                    throw new LawDeclarationError(
                        law.target,
                        "the belt-and-braces screen exercised zero instances: the " +
                            "derivation's claim never evaluated on concrete samples " +
                            "— a derivation whose claim the evaluator cannot exercise " +
                            "is not installable (check the operation's definition/evaluator)",
                    )
                }
                derivation = { ...result, screened }
            }
        }
    }

    // By here a derivable-routed claim is either discharged (with the
    // certificate — the belt-and-braces screen already ran inside the arm)
    // or downgraded to residual for the screen below.
    const screen: ScreenOutcome | undefined = regime === "residual" && derivation === undefined
        ? screenLaw(law, op, omega, eval_)
        : undefined
    // Exhaustion is the FINITE/MACHINE-FINITE regimes' evidence — the whole
    // inhabitant space is checked. A derivable-routed claim's evidence is
    // the derivation plus the belt-and-braces screen (a sweep here would
    // enumerate an UNBOUNDED carrier — the gate routes residual precisely
    // when the space is not finite), and a residual claim's evidence is the
    // screen — neither runs exhaustion.
    const exhaustion = (screen !== undefined || derivation !== undefined)
        ? undefined
        : exhaustLaw(law, op, eval_)
    const instances = screen
        ? screen.outcome === "passed" ? screen.checked : 0
        : derivation !== undefined
        // The derivable regime's instance count: the belt-and-braces
        // screen's checked count (the concrete redundancy), or 0 when the
        // guard screen declined (the proof is the evidence).
        ? (derivation.screened ?? 0)
        : exhaustion!.checked
    // Zero-coverage honesty — BOTH zero-coverage shapes reject:
    //
    // - **Declined** (unscreenable domain, empty sample space, unscreenable
    //   relational operand): the screen never exercised the claim — zero
    //   evidence, nothing installed.
    // - **Passed with 0 checked** (the sweep ran but EVERY instance was a
    //   hole — an error sentinel or a failed evaluation): the samples were
    //   drawn, but the claim was exercised zero times. "No counterexample
    //   found" over an all-holes sweep is no evidence either — an operation
    //   whose every law instance errors would otherwise install `asserted`
    //   on zero checked instances. Distinct diagnostic so the caller can
    //   tell a broken evaluator from an unscreenable domain.
    //
    // Exhaustion's zero-coverage case — a vacuous claim over an empty
    // carrier — stays honest: there the count 0 records a *complete* sweep
    // over ∅, a real proof shape (not a screen artifact).
    if (screen?.outcome === "declined") {
        throw new LawDeclarationError(
            law.target,
            "the screen declined: no sample vocabulary for this claim's domain " +
                "(higher-order or empty sample space) — zero coverage, nothing installed",
        )
    }
    if (screen?.outcome === "passed" && screen.checked === 0) {
        throw new LawDeclarationError(
            law.target,
            "the screen exercised zero instances: every drawn sample failed to " +
                "evaluate — a passing sweep over all-holes samples is no evidence, " +
                "nothing installed (check the operation's definition/evaluator)",
        )
    }
    const provenance: LawProvenance =
        regime === "finite" || regime === "machineFinite" || derivation !== undefined
            ? "discharged"
            : "asserted"
    laws.declareLaw(law, omega, provenance, checker)
    const decl: LawDecl = { ...law, provenance }
    return {
        law: decl,
        instances,
        regime: derivation !== undefined ? "derivable" : regime,
        coverage: screen?.outcome === "passed" ? screen.coverage : undefined,
        subSpaceSweep: exhaustion?.sweep,
        derivation,
    }
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
 * `instantiate`) but not its enumerator: the certified screen sweeps a
 * size-≤ k prefix (bounded by the budget constants); exhaustion needs the
 * full product — every variant, every field combination, across the type's
 * whole (finite) space.
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
 * this signature to proof standard), or when a scoped pattern position's
 * sub-space is empty (a vacuous discharge is rejected — see
 * `patternSpaceOf`).
 */
function exhaustLaw(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    eval_: EvalTerm,
): { checked: number; sweep: SubSpaceSweep | undefined } {
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
    // The machineFinite arm: a scoped position's space is
    // FILTERED by its sub-space predicate BEFORE the product — the sweep is
    // over the sub-space, so the full-coverage contract (every instance
    // must evaluate; a hole rejects) carries over untouched, now over the
    // scoped space. The predicate is user code evaluated by the same total
    // evaluator: a predicate error on a sample is an EVALUATION HOLE (the
    // filter cannot decide membership) — the declaration is rejected, not
    // the sample silently dropped (a silent drop would shrink the certified
    // space the discharge claims).
    const predicates = new Map<number, SubSpaceSpec>(
        (law.subSpace ?? []).map((spec) => [spec.position, spec]),
    )
    // Per-position admitted cardinalities (the sweep certificate's data —
    // the space each scoped position contributes AFTER filtering).
    const sweepSpaces = new Map<number, number>()
    const positionSamples: Array<ReadonlyArray<VariantVal | TokenVal>> = op.paramTypes
        .map((type, position): ReadonlyArray<VariantVal | TokenVal> => {
            if (exponents[position] === 0) return []
            const spec = predicates.get(position)
            if (isPatternCarrierType(type)) {
                // The pattern carrier's sub-space: enumerate the matched
                // strings' tokens (the true size-≤ bound space from the
                // language equation) — this is the sub-space exhaustion's
                // sweep space; `MAX_FINITE_INHABITANTS` bounds it (the
                // regime's routing already guaranteed the fit). The
                // member-shape gate: a variants-only carrier falls through
                // to the full variant space below.
                const space = patternSpaceOf(type, law, spec, eval_)
                if (spec) sweepSpaces.set(position, space.length)
                return space
            }
            const full = spaceOf(type as DataType, eval_, spaces)
            if (!spec) return full
            const filtered = filterSubSpace(full, spec, eval_, op.name, position)
            sweepSpaces.set(position, filtered.length)
            return filtered
        })

    let checked = 0
    for (
        const bindings of assignments(
            SCHEMA_NAMES[law.kind]!,
            positionSamples as unknown as readonly (readonly Value[])[],
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
    // The sweep's visible extent (the machineFinite certificate): scoped
    // positions state their admitted cardinality, and the length bound
    // states how far the enumeration reached. Recorded ONLY for the
    // pattern-typed scoped positions (a finite data carrier's full space
    // needs no extent note — the regime itself certifies it).
    const sweepPositions = (law.subSpace ?? [])
        .filter((spec) => op.paramTypes[spec.position] instanceof DataType)
        .map((spec) => ({
            position: spec.position,
            where: spec.where,
            admitted: sweepSpaces.get(spec.position) ?? 0,
        }))
    const sweep: SubSpaceSweep | undefined = sweepPositions.length > 0
        ? { maxLength: MAX_PATTERN_LENGTH, positions: sweepPositions }
        : undefined
    return { checked, sweep }
}

/**
 * A scoped position's filtered space: the samples satisfying the sub-space
 * predicate. The predicate is evaluated per sample through the evaluator
 * (`where` is an LC boolean term over the bound variable `a`); a sample the
 * predicate rejects is OUT of the sub-space — excluded from the sweep (the
 * claim is scoped, so exclusion is the honest certification, not under-
 * coverage).
 *
 * A predicate ERROR on a sample is an evaluation hole: the filter cannot
 * decide membership, and a hole inside the certified space would shrink it
 * silently. Rejected loudly (the same completeness contract exhaustion
 * applies to constructions).
 */
function filterSubSpace(
    samples: readonly VariantVal[],
    spec: SubSpaceSpec,
    eval_: EvalTerm,
    opName: string,
    position: number,
): readonly VariantVal[] {
    const kept: VariantVal[] = []
    for (const sample of samples) {
        const rho = new ValueEnv(new Map([["a", sample as Value]]))
        const results = [...eval_(spec.where, rho)]
        const verdict = results[0]
        if (
            results.length !== 1 || verdict === undefined ||
            verdict instanceof EvalErrorValue
        ) {
            throw new LawDeclarationError(
                opName,
                `sub-space predicate "${spec.where}" (position ${position}) did not evaluate to a single verdict — the scope cannot certify the space`,
            )
        }
        if (verdict.equals(TRUE_VALUE)) kept.push(sample)
    }
    return kept
}

/** The `True` variant value (predicate verdicts compare against it). */
const TRUE_VALUE: VariantVal = makeTrueValue()

function makeTrueValue(): VariantVal {
    // `True()` — the Bool variant, constructed without the evaluator (the
    // verdict comparison is a structural equality against the known shape;
    // the evaluator is for CONSTRUCTION of samples, and predicate verdicts
    // come back as values from `eval_`, already resolved).
    const boolType = DataType.define("Bool")
        .addVariant(new Variant("True", []), new Variant("False", []))
        .build()
    return new VariantVal("True", boolType, new Map())
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
 * caller would pass as full coverage. (The certified screen's construction
 * failures reject the declaration outright — see `inhabitantsUpToSize`.)
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
            // A pattern-BEARING field carrier is NOT empty: its space is
            // the token classes (the language-equation enumeration) —
            // `finiteInhabitants`' variant-system count reads 0 for it (no
            // variants), but the carrier's members are pattern
            // constructors, and the field's space walk below enumerates
            // them. Stage 5's member-shape counting replaces this interim
            // exception (a finite-language pattern carrier then reports a
            // real count).
            if (fieldType instanceof DataType && fieldType.patterns.length > 0) {
                return false
            }
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
 * innermost-last (field order preserved in each emitted combo). Spaces may
 * be readonly (the certified enumerator's memoized spaces are shared).
 */
function* cartesian(spaces: readonly (readonly Value[])[]): Generator<Value[]> {
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
