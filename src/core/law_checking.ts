/**
 * LC Law Screening — the residual screen for asserted laws.
 *
 * See _docs/theory/semantics.md §5.4 (regime-based checking) and
 * _docs/theory/elaboration.md §6.1 (the provenance chain).
 *
 * The screen is **best-effort falsification**: it instantiates a law's axiom
 * schema (lc.md §7.2) over bounded-depth samples of the operation's domain,
 * evaluates both sides, and throws `LawError` on the first divergence. It
 * *rejects* declarations it can falsify; it never *establishes* — passing is
 * evidence, not proof (Model A authority). That is why every law entering
 * `E` through the screen carries provenance `asserted`.
 *
 * The screen is total: evaluation is total (structural recursion), so both
 * sides of every instance terminate — no timeouts, no divergence. Bounded
 * depth additionally caps the sample space.
 *
 * Scope (first cut): laws over operations whose parameters are **data types**
 * (μ-types). Sampling walks the variants of each parameter type; recursive
 * variants recurse to a bounded depth. Higher-order parameters (functions)
 * have no finite sample vocabulary — such a law declares but is installed
 * `asserted` unscreened (the residual's honest risk, semantics.md §7.4).
 *
 * Heterogeneous parameter types are screened position-wise: schema operand i
 * draws from the samples of parameter type i, so every position sweeps its
 * own type's space. When an op has several parameter types, coverage is the
 * per-position sweep — an instance the operation's signature itself rejects
 * (none here: positions match the signature) or one whose evaluation hits an
 * error sentinel is skipped, not counted; the returned instance count is the
 * honest coverage measure.
 */

import {
    ARGUMENT_KINDS,
    type LawDecl,
    LawDeclarationError,
    LawError,
    type LawKind,
    LawRegistry,
    type LawTypeChecker,
    RELATIONAL_KINDS,
    screenableDomain,
} from "./laws.ts"

import { type CheckedOpSig, type OpRegistry } from "./ops.ts"

import { Value, ValueEnv, valueEquals, VariantVal } from "./values.ts"

import { EvalErrorValue } from "./eval_grammar.ts"

import { DataType, type Type } from "./types.ts"

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
    law: LawDecl,
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
 * `declareScreenedLaw`.
 *
 * @param law      the law declaration — structurally pre-validated by
 *                 `LawRegistry.validateLaw` in the `declareScreenedLaw`
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
    law: LawDecl,
    op: CheckedOpSig,
    omega: OpRegistry,
    eval_: EvalTerm,
    maxDepth: number = MAX_SAMPLE_DEPTH,
): number {
    // Higher-order parameters: no finite sample vocabulary — the screen
    // declines (checked = 0; the caller installs the law unscreened).
    if (!screenableDomain(op)) return 0

    // The argument value for argument-taking kinds: evaluate the declared
    // argument term once, in a fresh environment. A non-evaluating argument
    // rejects the declaration outright (the claim is not even well-posed).
    // The argument's TYPE was validated against the carrier at declaration
    // (`LawRegistry.validateLaw`); the screen re-checks evaluation so an
    // argument that parses but evaluates to nothing cannot slip through a
    // raw `screenLaw` call and silently produce zero coverage.
    let argumentValue: Value | undefined
    if (ARGUMENT_KINDS.includes(law.kind)) {
        argumentValue = eval_(law.argument!, new ValueEnv())[0]
        if (argumentValue === undefined) {
            throw new LawError(op.name, law, ["argument = (did not evaluate)"], "—", "—")
        }
    }

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
    const positionSamples: VariantVal[][] = op.paramTypes.map((type) =>
        dedupe(samplesFor(type as DataType, maxDepth, eval_))
    )
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
            const left = eval_(instance.left, instance.rho)[0]
            const right = eval_(instance.right, instance.rho)[0]
            if (
                left === undefined || right === undefined ||
                left instanceof EvalErrorValue || right instanceof EvalErrorValue
            ) {
                // An instance that does not evaluate (or evaluates to an
                // error sentinel) is not a falsification — the schema may
                // not apply to this sample mix. Skip it.
                continue
            }
            if (!valueEquals(left, right)) {
                throw new LawError(
                    op.name,
                    law,
                    instance.bindings,
                    renderValue(left),
                    renderValue(right),
                )
            }
            checked++
        }
    }
    return checked
}

/**
 * Enumerate the schema's variable assignments: variable i draws from the
 * samples of the operand position it instantiates (position i, mod the
 * operation's parameter count — schemas instantiate fewer variables than
 * positions on some shapes). The sweep is the Cartesian product across
 * variables, so every variable takes independent values — a falsifying
 * pair like `op(a, b)` with `a ≠ b` is reachable for commutative.
 */
function assignments(
    names: readonly string[],
    positionSamples: readonly VariantVal[][],
    paramCount: number,
): (readonly [string, VariantVal])[][] {
    let combos: (readonly [string, VariantVal])[][] = [[]]
    for (let i = 0; i < names.length; i++) {
        const samples = positionSamples[i % paramCount]!
        const next: (readonly [string, VariantVal])[][] = []
        for (const combo of combos) {
            for (const sample of samples) {
                next.push([...combo, [names[i]!, sample]])
            }
        }
        combos = next
    }
    return combos
}

/** Dedupe samples structurally (the sweep sees each distinct value once). */
function dedupe(samples: VariantVal[]): VariantVal[] {
    const seen = new Set<string>()
    const result: VariantVal[] = []
    for (const sample of samples) {
        const key = renderValue(sample)
        if (!seen.has(key)) {
            seen.add(key)
            result.push(sample)
        }
    }
    return result
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

/**
 * The screen's all-in-one entry: validate the claim structurally against
 * `Ω` (`LawRegistry.validateLaw` — vocabulary, argument shape, relational
 * arity, schema typing), screen it, and on a passing screen install it in
 * `E` with provenance `asserted`.
 *
 * Validation runs BEFORE the screen: a vocabulary/argument/arity/typing
 * error surfaces as `LawDeclarationError` — never as a screen artifact (a
 * `TypeError` from an unknown kind, or zero-coverage silence). The screen
 * runs second, so a falsified claim never enters `E`.
 *
 * Returns `{ law, instances }` — the installed declaration and the number
 * of instances the screen checked. This is the elaboration-time sequence of
 * elaboration.md §6.1 steps 1–4, for one law.
 *
 * @throws LawError when the screen falsifies the law (nothing is installed).
 * @throws LawDeclarationError when the claim is not in the closed vocabulary
 * or is structurally ill-formed (from `LawRegistry.validateLaw`).
 */
export function declareScreenedLaw(
    law: Omit<LawDecl, "provenance">,
    omega: OpRegistry,
    laws: LawRegistry,
    eval_: EvalTerm,
    checker?: LawTypeChecker,
    maxDepth: number = MAX_SAMPLE_DEPTH,
): { law: LawDecl; instances: number } {
    const op = omega.lookup(law.target)
    if (!op) {
        throw new LawDeclarationError(law.target, "the target operation is not declared in Ω")
    }
    // Structural validation FIRST (loud, typed errors), then the screen.
    const structuralReason = laws.validateLaw(law, omega, checker)
    if (structuralReason !== undefined) {
        throw new LawDeclarationError(law.target, structuralReason)
    }
    // Screen BEFORE installing: a falsified claim never enters E.
    const decl: LawDecl = { ...law, provenance: "asserted" }
    const instances = screenLaw(decl, op, omega, eval_, maxDepth)
    laws.declareLaw(law, omega, "asserted", checker)
    return { law: decl, instances }
}
