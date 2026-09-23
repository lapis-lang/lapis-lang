/**
 * LC Cost Algebra — static cost/depth analysis over LC terms.
 *
 * See _docs/theory/semantics.md §5.5 (The Cost Algebra) and
 * _docs/issue52-plan.md (the implementation plan this module follows).
 *
 * Totality guarantees that programs terminate; it does not guarantee that they
 * terminate _feasibly_. The cage makes cost analysis unusually tractable — a
 * fold's recursion tree is **isomorphic to its input structure**
 * (container-shaped recursion: `fold [μF]` over a value with _n_ constructor
 * nodes performs exactly _n_ recursive invocations, independent of handler
 * bodies), so a cost/depth algebra over terms is mechanically computable, and
 * a decidable criterion separates the certified fragment from the flagged
 * residual — the same certified/flagged split as law provenance
 * (semantics.md §5.4).
 *
 * The algebra decomposes cost/depth per node:
 *
 *   cost(Cᵢ(tⱼ))      = 1 + Σⱼ cost(tⱼ)               (constructor is O(1))
 *   cost(app t u)     = cost(t) + cost(u) + body(u)   (closure composition)
 *   cost(op(tⱼ))      = the callee's memoized summary,
 *                       instantiated at the arguments' sizes
 *   cost(fold [T] s)  = Σ over s's nodes of the per-node handler work
 *   latency(e.oₖ)     = cost of gₖ on the seed        (the codata dual, §2.4)
 *
 * Only handler-body costs recurse into the analysis; structure contributes a
 * known skeleton. Folds are NOT monotone as functions — what is rigid is the
 * _call-shape_: the recursion profile is fixed by the input's shape.
 *
 * ## The criterion: cycles × value growth
 *
 * Unsafe (hyper-growth, "busy-beaver"-style) computation requires both cycles
 * and unbounded value growth. `Ω` is acyclic by construction (the
 * declaration-order stratification in `ops.ts` — an operation may only
 * reference operations declared earlier), so the remaining analysis axis is
 * **value-size feedback**: a fold's result flowing back as another fold's
 * input without a static size bound on the intermediate.
 *
 * A **size-sensitive position** is where a value's size drives cost: a fold's
 * scrutinee (the invocation count is the input's node count), an operation
 * application's argument positions (the callee's cost is driven by its
 * parameters' sizes), an application's function position (the applied body's
 * cost is consumed per application), and an observation's generator (the
 * codata dual — the latency).
 *
 * The **flag** fires iff the producer's result-size is opaque — a
 * function-typed value flowing into a size-sensitive position. First-order
 * data always admits a closed size expression (the algebra closes every
 * data-valued term), so every first-order feedback edge certifies (the affine
 * shape — e.g. `map` feeding a fold), while a fold whose recursion threads
 * functions (the Ackermann shape: a fold over Nat producing Nat → Nat, whose
 * handler applies the recursion result) has an opaque producer at the
 * application's function position and is flagged. Flags are **diagnostics,
 * never errors** — the report carries them; nothing throws.
 *
 * ## Two vehicles, one algebra
 *
 * - **`CostEngine extends AbstractLC`** — the evaluator's architecture: a
 *   denotation environment threaded through the productions (`extendCtx`),
 *   each production building the sub-summary. Capture-safe by construction
 *   (the same reason `LCEval` threads `ρ`): a shadowing binder extends the
 *   environment rather than mutating it, so a body's denotations are exactly
 *   what its binders denote. The engine analyzes **op definitions** (Ω
 *   entries are LC source strings with no derivation tree) and direct terms
 *   (`analyzeTerm`).
 * - **`CostPass extends SemanticPass`** — the `DerivationTree`-consuming
 *   entry. The tree supplies structure (labels + spans + source); the pass's
 *   per-production methods return **deferred summaries** — thunks over the
 *   denotation environment — so the parent, which knows the bindings, builds
 *   the handler environments and applies the child thunks under them.
 *   Inherited-attribute flow through deferred application: bottom-up
 *   evaluation with the environment threaded where it is constructed.
 *
 * Both vehicles share the summary algebra and the fold recurrence; they differ
 * only in how structure arrives (a parse vs a tree walk).
 *
 * ## What the analysis does NOT claim
 *
 * - The conservative fold bound (invocations = the scrutinee's node count ×
 *   the SUM of the handlers' costs — a safe over-approximation of the exact
 *   Σ_nodes decomposition, since only one handler runs per node) is within a
 *   constant factor for uniform handlers (the common case, where the sum IS
 *   the max — e.g. every linear fold); the certificate states the bound's
 *   shape, never an exact count. Scrutinees that are constructor literals
 *   give exact node counts (the per-node work stays the handlers' sum).
 * - Super-affine structural growth (a handler body growing geometrically in
 *   the recursion result) reports the coarse
 *   `exponential (primitive-recursive)` class with the recurrence stated —
 *   certified but coarse. The busy-beaver criterion is about _feedback_, not
 *   structural growth: structural growth is primitive-recursive by
 *   construction (structural recursion over a μ-type), so it is never flagged.
 * - The flagged fragment's exact cost is undecidable in general — the
 *   correctly-stated Rice wall bounds the analysis fragment, it does not
 *   erase it. Runtime profiling (the flag's suggested observation) is the
 *   live-image mode's channel and lands with that work.
 */

import {
    type DerivationNode,
    type DerivationTree,
    type Parser,
    SemanticPass,
} from "@lapis-lang/lang-forma"

import {
    CodataType,
    DataType,
    FamilyType,
    Field,
    type RequiredCases,
    Type,
    type TypeCases,
} from "./types.ts"

import { AbstractLC, type LCShape, TypeRegistry } from "./grammar.ts"

import { type CheckedOpSig, OpRegistry } from "./ops.ts"

// ── The size/cost expression algebra ─────────────────────────────────────────

/**
 * The saturation ceiling for size/cost coefficients: past it, the arithmetic
 * saturates (a bound past `Number.MAX_SAFE_INTEGER` is meaningless at
 * runtime — saturating at the language-defined safe bound keeps the
 * arithmetic honest and the expressions finite).
 */
export const COST_CEILING = Number.MAX_SAFE_INTEGER

/** Saturating addition: never past the ceiling. */
function satAdd(a: number, b: number): number {
    const sum = a + b
    return sum > COST_CEILING ? COST_CEILING : sum
}

/** Saturating multiplication: any zero operand zeroes; else saturate. */
function satMul(a: number, b: number): number {
    if (a === 0 || b === 0) return 0
    const product = a * b
    return product > COST_CEILING ? COST_CEILING : product
}

/** A monomial: `coefficient × ∏ var^exponent` over named size variables. */
export interface Monomial {
    readonly coefficient: number
    /** var name → exponent (≥ 1; saturated). */
    readonly factors: ReadonlyMap<string, number>
}

/**
 * The SAFE ALPHABET for a size-variable name — the character set the
 * algebra's internal name machinery assumes. Two consumers parse names
 * structurally, and both assume a restricted character set:
 *
 * - `monomialKey` joins factors with `,` and appends `^e`; `fromMerged`
 *   reconstructs the factors by `split(",")` then `split("^")` — so a name
 *   containing `,` or `^` would be MIS-PARSED back (a `,` splits one name
 *   into two factors; a `^` splits it into a truncated name and an
 *   exponent), silently corrupting the merge and the substitution.
 * - `renderMonomial` wraps the name in `|…|` — a `|` in the name makes the
 *   rendered certificate ambiguous to read.
 *
 * Everything else (`:` separators, `(` `)` groupings, whitespace, control
 * characters, quotes, backslashes) is unsafe for one consumer or another —
 * or merely unreadable in a report. The sanitizer below escapes every
 * character OUTSIDE the safe set to `\xHH`, so any input string becomes a
 * valid, unambiguous, round-trippable variable name.
 */
const SAFE_NAME_CHARS = /^[A-Za-z0-9_.\-+#]*$/

/**
 * Sanitize one component of a variable name into the safe alphabet: every
 * character outside it (see `SAFE_NAME_CHARS`) is hex-escaped (`\xNN`), so
 * the result is always a valid, unambiguous, and round-trippable name —
 * `unescapeNameComponent` reconstructs the original.
 *
 * Deterministic and injective (the escape alphabet `\x` + hex digits cannot
 * collide with an unescaped safe string, since raw `\` is itself escaped),
 * so `substitute`'s exact-match discipline and the monomial merge keys stay
 * correct for any input.
 */
export function sanitizeNameComponent(raw: string): string {
    return [...raw]
        .map((c) =>
            SAFE_NAME_CHARS.test(c) ? c : `\\x${c.charCodeAt(0).toString(16).padStart(2, "0")}`
        )
        .join("")
}

/**
 * The inverse of `sanitizeNameComponent` (diagnostics: a sanitized name read
 * back to the component that produced it). Not used by the algebra itself —
 * the algebra never parses names back — but exported so report consumers can
 * recover the readable form.
 */
export function unescapeNameComponent(safe: string): string {
    return safe.replace(
        /\\x([0-9a-f]{2})/g,
        (_m, h: string) => String.fromCharCode(parseInt(h, 16)),
    )
}

/** A monomial's canonical merge key (coefficient-independent). */
function monomialKey(m: Monomial): string {
    if (m.factors.size === 0) return ":"
    return [...m.factors.entries()].map(([v, e]) => `${v}^${e}`).sort().join(",")
}

/** A merge key's factor part (empty for the constant key ":"). */
function keyFactors(key: string): string {
    return key === ":" ? "" : key
}

/** Render one monomial: `c·|v|^e·…` or `c` for constants. */
function renderMonomial(m: Monomial): string {
    if (m.factors.size === 0) return `${m.coefficient}`
    const factors = [...m.factors.entries()]
        .sort(([a], [b]) => a.localeCompare(b))
        .map(([v, e]) => e === 1 ? `|${v}|` : `|${v}|^${e}`)
        .join("·")
    return m.coefficient === 1 ? factors : `${m.coefficient}·${factors}`
}

/**
 * A polynomial-form size/cost expression: Σ monomials over named size
 * variables, saturating. `opaque` marks the absence of an expression: the
 * value is **function-typed** (a closure, a function-typed parameter or
 * result) and has no size algebra — the opacity that drives the feedback
 * flag.
 */
export class SizeExpr {
    private constructor(
        readonly monomials: readonly Monomial[],
        readonly opaque: boolean,
        /** Why the expression is opaque (empty when it is not). */
        readonly opaqueReason: string = "",
    ) {}

    /** The zero expression (an empty sum). */
    static readonly ZERO = new SizeExpr([], false)

    /** The constant 1 (a single node). */
    static readonly ONE = SizeExpr.constant(1)

    /** The opaque marker: no size algebra exists for this value. */
    static opaque(reason: string): SizeExpr {
        return new SizeExpr([], true, reason)
    }

    /** A constant expression. */
    static constant(c: number): SizeExpr {
        return c === 0
            ? SizeExpr.ZERO
            : new SizeExpr([{ coefficient: c, factors: new Map() }], false)
    }

    /** A single variable, exponent 1, coefficient 1: `|name|`. */
    static variable(name: string): SizeExpr {
        return new SizeExpr([{ coefficient: 1, factors: new Map([[name, 1]]) }], false)
    }

    /** A variable with an explicit exponent: `|name|^e` (0 → the constant 1). */
    static variablePow(name: string, e: number): SizeExpr {
        return e === 0
            ? SizeExpr.ONE
            : new SizeExpr([{ coefficient: 1, factors: new Map([[name, e]]) }], false)
    }

    /** The is-opaque query. */
    get isOpaque(): boolean {
        return this.opaque
    }

    /** Whether the expression is the (syntactic) zero. */
    get isZero(): boolean {
        return !this.opaque && this.monomials.length === 0
    }

    /** Saturating pointwise sum. */
    plus(other: SizeExpr): SizeExpr {
        if (this.opaque) return this
        if (other.opaque) return other
        const merged = new Map<string, number>()
        for (const m of [...this.monomials, ...other.monomials]) {
            const key = monomialKey(m)
            merged.set(key, satAdd(merged.get(key) ?? 0, m.coefficient))
        }
        return SizeExpr.fromMerged(merged)
    }

    /** Saturating pointwise product (distributing over the monomial lists). */
    times(other: SizeExpr): SizeExpr {
        if (this.opaque) return this
        if (other.opaque) return other
        const merged = new Map<string, number>()
        for (const a of this.monomials) {
            for (const b of other.monomials) {
                const factors = new Map<string, number>(a.factors)
                for (const [v, e] of b.factors) {
                    factors.set(v, satAdd(factors.get(v) ?? 0, e))
                }
                const m: Monomial = { coefficient: satMul(a.coefficient, b.coefficient), factors }
                const key = monomialKey(m)
                merged.set(key, satAdd(merged.get(key) ?? 0, m.coefficient))
            }
        }
        return SizeExpr.fromMerged(merged)
    }

    /** Raise to a power (exponents stay small; saturating). */
    pow(e: number): SizeExpr {
        if (this.opaque) return this
        if (e === 0) return SizeExpr.ONE
        let result = SizeExpr.ONE
        for (let i = 0; i < e; i++) result = result.times(this)
        return result
    }

    /**
     * Substitute one variable with an expression (the recurrence driver: a
     * recursive binding's size variable becomes the recursion's symbolic
     * result at the subterm's size).
     */
    substitute(name: string, replacement: SizeExpr): SizeExpr {
        if (this.opaque) return this
        if (replacement.opaque) return replacement
        const merged = new Map<string, number>()
        for (const m of this.monomials) {
            const factorE = m.factors.get(name)
            if (factorE === undefined) {
                const key = monomialKey(m)
                merged.set(key, satAdd(merged.get(key) ?? 0, m.coefficient))
                continue
            }
            const rest = new Map<string, number>()
            for (const [v, e] of m.factors) {
                if (v !== name) rest.set(v, e)
            }
            const replaced = replacement.pow(factorE)
            for (const rm of replaced.monomials) {
                const factors = new Map<string, number>(rest)
                for (const [v, e] of rm.factors) {
                    factors.set(v, satAdd(factors.get(v) ?? 0, e))
                }
                const m2: Monomial = {
                    coefficient: satMul(m.coefficient, rm.coefficient),
                    factors,
                }
                const key = monomialKey(m2)
                merged.set(key, satAdd(merged.get(key) ?? 0, m2.coefficient))
            }
        }
        return SizeExpr.fromMerged(merged)
    }

    /** The expression's total degree (∞ for opaque). */
    degree(): number {
        if (this.opaque) return Number.POSITIVE_INFINITY
        let max = 0
        for (const m of this.monomials) {
            let degree = 0
            for (const e of m.factors.values()) degree += e
            if (degree > max) max = degree
        }
        return max
    }

    /** The expression without any monomial mentioning `name`. */
    without(name: string): SizeExpr {
        if (this.opaque) return this
        const merged = new Map<string, number>()
        for (const m of this.monomials) {
            if (m.factors.has(name)) continue
            const key = monomialKey(m)
            merged.set(key, satAdd(merged.get(key) ?? 0, m.coefficient))
        }
        return SizeExpr.fromMerged(merged)
    }

    /** Render for reports and test assertions. */
    render(): string {
        if (this.opaque) return `opaque(${this.opaqueReason})`
        if (this.monomials.length === 0) return "0"
        return this.monomials.map(renderMonomial).join(" + ")
    }

    private static fromMerged(merged: Map<string, number>): SizeExpr {
        const monomials: Monomial[] = []
        for (const [key, coefficient] of merged) {
            if (coefficient === 0) continue
            const factors = new Map<string, number>()
            const factorPart = keyFactors(key)
            if (factorPart.length > 0) {
                for (const pair of factorPart.split(",")) {
                    const [v, e] = pair.split("^")
                    factors.set(v!, Number(e))
                }
            }
            monomials.push({ coefficient, factors })
        }
        monomials.sort((a, b) => monomialKey(a).localeCompare(monomialKey(b)))
        return new SizeExpr(monomials, false)
    }
}

// ── Depth expressions (max-form) ──────────────────────────────────────────────

/**
 * A depth expression: max-form over component depths. Depth is the longest
 * sequential chain in the evaluation (stack depth): a constructor adds 1 over
 * its deepest field; a fold's depth is the scrutinee's traversal plus the
 * worst handler-body depth; independent fields take the MAX, not the sum.
 */
export class DepthExpr {
    private constructor(
        readonly components: readonly SizeExpr[],
        readonly opaque: boolean,
        readonly opaqueReason: string = "",
    ) {}

    static readonly ZERO = new DepthExpr([], false)

    /** The opaque marker (a function-typed value's depth is its runtime's). */
    static opaque(reason: string): DepthExpr {
        return new DepthExpr([], true, reason)
    }

    static of(expr: SizeExpr): DepthExpr {
        return new DepthExpr([expr], false)
    }

    static constant(c: number): DepthExpr {
        return new DepthExpr([SizeExpr.constant(c)], false)
    }

    get isOpaque(): boolean {
        return this.opaque
    }

    /** Parallel composition: the max of the component depths. */
    max(other: DepthExpr): DepthExpr {
        if (this.opaque) return this
        if (other.opaque) return other
        return new DepthExpr([...this.components, ...other.components], false)
    }

    /** Sequential composition: add a size expression to every component. */
    plus(expr: SizeExpr): DepthExpr {
        if (this.opaque) return this
        if (expr.isOpaque) return DepthExpr.opaque(expr.opaqueReason)
        return new DepthExpr(this.components.map((c) => c.plus(expr)), false)
    }

    /** Substitute a variable in every component. */
    substitute(name: string, replacement: SizeExpr): DepthExpr {
        if (this.opaque) return this
        if (replacement.isOpaque) return DepthExpr.opaque(replacement.opaqueReason)
        return new DepthExpr(this.components.map((c) => c.substitute(name, replacement)), false)
    }

    /** The depth expression's degree (the max component's). */
    degree(): number {
        if (this.opaque) return Number.POSITIVE_INFINITY
        return this.components.reduce((max, c) => Math.max(max, c.degree()), 0)
    }

    /**
     * The depth collapsed to a size expression (Σ components — an upper bound
     * on the max, exact when one component dominates).
     */
    toSize(): SizeExpr {
        if (this.opaque) return SizeExpr.opaque(this.opaqueReason)
        return this.components.reduce((sum, c) => sum.plus(c), SizeExpr.ZERO)
    }

    render(): string {
        if (this.opaque) return `opaque(${this.opaqueReason})`
        if (this.components.length === 0) return "0"
        return this.components.map((c) => c.render()).join(" ⊔ ")
    }
}

// ── Growth classes ────────────────────────────────────────────────────────────

/**
 * The growth class a closed expression (or stated recurrence) places a bound
 * in. `exponential (primitive-recursive)` is the coarse class for super-affine
 * structural growth: the bound does not close to a polynomial, but the
 * recursion is structural (over a μ-type), so it terminates primitive-
 * recursively — certified, coarsely stated, never flagged (the busy-beaver
 * criterion is about feedback, not structural growth).
 */
export type GrowthClass =
    | "constant"
    | "linear"
    | "polynomial"
    | "exponential (primitive-recursive)"
    | "unbounded"

/** Classify a size expression by its degree (opaque → unbounded). */
function classifyExpr(expr: SizeExpr): GrowthClass {
    if (expr.isOpaque) return "unbounded"
    if (expr.isZero || expr.degree() === 0) return "constant"
    const degree = expr.degree()
    if (degree === 1) return "linear"
    if (degree <= 8) return "polynomial"
    return "exponential (primitive-recursive)"
}

// ── Provenance ────────────────────────────────────────────────────────────────

/**
 * What produced a value — provenance on every summary, so a feedback edge
 * names both of its ends (the named form is what makes an edge statement
 * meaningful; the identity-survival property of `opProd` is the payoff).
 *
 * The codata constructs keep their own kinds: `unfold` names a codata
 * VALUE (the `unfold [T] s` form — O(1) to produce), `cofold` names a
 * codata ELIMINATION (the `cofold [T] e` form). Neither is a fold's
 * recursion result — conflating them with `fold` would mislabel the
 * flag's producer end (an application of an unfold's result is an
 * ordinary first-order data flow, not the flagged recursion shape).
 */
export type Provenance =
    | { readonly kind: "param"; readonly name: string }
    | { readonly kind: "op"; readonly name: string }
    | { readonly kind: "fold"; readonly name: string }
    | { readonly kind: "unfold"; readonly name: string }
    | { readonly kind: "cofold"; readonly name: string }
    | { readonly kind: "constructor"; readonly name: string }
    | { readonly kind: "closure"; readonly name: string }
    | { readonly kind: "token"; readonly name: string }
    | { readonly kind: "unknown" }

/** A provenance's readable name (reports, edges). */
export function provenanceName(p: Provenance): string {
    return p.kind === "unknown" ? "?" : p.name
}

// ── Feedback edges, flags, reports ────────────────────────────────────────────

/**
 * A feedback edge: a value flowing into a size-sensitive position. The edge
 * records both ends (the named form), the position kind, and the producer's
 * bound when one exists.
 */
export interface CostEdge {
    /** What produced the value (which op/fold/parameter/constructor). */
    readonly producer: Provenance
    /** The consumer site (which op/fold/application/observation). */
    readonly consumer: Provenance
    /** The position kind at the consumer. */
    readonly position:
        | "fold scrutinee"
        | "op argument"
        | "application function"
        | "observation generator"
    /** The position's name where applicable (the op name, the observer). */
    readonly consumerSite: string
    /** The producer's closed result-size bound, when one exists. */
    readonly bound: SizeExpr | undefined
    /** Whether the producer's size is opaque (the flag's condition). */
    readonly isFlagged: boolean
}

/**
 * A flag: the diagnostic (never an error) on value-size feedback without a
 * static bound — the busy-beaver candidate. The payload is the issue's
 * acceptance item: the feedback edge, the missing bound, and the suggested
 * runtime profile.
 */
export interface CostFlag {
    /** The feedback edge that has no static bound. */
    readonly edge: CostEdge
    /** The missing bound: the size relationship that cannot be stated. */
    readonly missingBound: string
    /** The runtime observation to attach (the profiling design note). */
    readonly suggestedProfile: string
}

/** Build the flag payload for one flagged edge. */
function flagOf(edge: CostEdge): CostFlag {
    const producer = edge.producer.kind === "unknown"
        ? "an unclassified value"
        : `"${provenanceName(edge.producer)}"`
    return {
        edge,
        missingBound:
            `the value at ${edge.consumerSite} (${edge.position}) is produced by ${producer} ` +
            `and is function-typed — its size has no static algebra, so the consumer's ` +
            `cost at this position has no closed bound (the hyper-growth candidate: ` +
            `a result re-entering as input through a function value)`,
        suggestedProfile: `observe at runtime: sample the input sizes and invocation counts at ` +
            `"${edge.consumerSite}", accumulate the samples against this flag, and alert ` +
            `when the observed profile exceeds the certified programs' envelope ` +
            `(withdrawal-style, mirroring law observation)`,
    }
}

/**
 * A cost contribution the analysis could not bound: applying a function-typed
 * parameter whose body is unknown. Recorded so the certificate states exactly
 * what closed and what did not; unresolved atoms flag nothing by themselves.
 */
export interface UnresolvedCost {
    /** The application site's provenance. */
    readonly site: Provenance
    /** The applied function's provenance (whose body is unknown). */
    readonly applied: Provenance
    /** Why the contribution is unresolved. */
    readonly reason: string
}

/**
 * An observation's latency (the codata dual): the generator body's cost on
 * the seed. Productivity guarantees each observation is produced after
 * _finite_ work — not _small_ work; this is the codata-side unbounded cost.
 */
export interface LatencyReport {
    /** The observer observed. */
    readonly observer: string
    /** The generator body's cost on the seed (symbolic in the seed's size). */
    readonly latency: SizeExpr
}

/** The verdict the classifier assigns a report. */
export type CostVerdict = "certified" | "flagged"

/**
 * A term's symbolic summary: cost, depth, result size — each a symbolic
 * expression over the named size variables of the term's free values, plus
 * the result's provenance and the feedback/latency records the analysis
 * accumulated.
 */
export interface CostSummary {
    /** The total work: node visits + per-node handler work, symbolic. */
    readonly cost: SizeExpr
    /** The longest sequential chain (stack depth), max-form. */
    readonly depth: DepthExpr
    /** The result's size expression (opaque for function-typed results). */
    readonly resultSize: SizeExpr
    /** What produced the result value (the feedback edge's producer end). */
    readonly provenance: Provenance
    /** The result's type classification (data vs function-typed). */
    readonly resultKind: "data" | "function" | "unknown"
    /**
     * For a closure: the deferred full-application cost — the chain of
     * per-application stages consumed at application sites (the
     * lambda-chain propagation that gives op summaries their fold work).
     */
    readonly bodyChain?: ClosureChain
    /**
     * A super-affine structural recurrence, stated when the summary's size
     * bound did not close (the certificate states it; the report surfaces it).
     */
    readonly recurrence?: string
    /**
     * Feedback edges observed: a value flowing into a size-sensitive
     * position, with the bound (the producer's closed result size) when one
     * exists.
     */
    readonly edges: readonly CostEdge[]
    /**
     * Cost contributions the analysis could not bound — applying a
     * function-typed parameter (e.g. `map`'s `f h`) whose body is unknown.
     * Recorded, never flagged by themselves.
     */
    readonly unresolved: readonly UnresolvedCost[]
    /** Observation latencies (the codata dual), per observer. */
    readonly latencies: readonly LatencyReport[]
}

/** The analysis's identity summary (no work, no records). */
function emptySummary(): CostSummary {
    return {
        cost: SizeExpr.ZERO,
        depth: DepthExpr.ZERO,
        resultSize: SizeExpr.ZERO,
        provenance: { kind: "unknown" },
        resultKind: "unknown",
        edges: [],
        unresolved: [],
        latencies: [],
    }
}
/**
 * The analysis report for one term/op: the verdict, the bounds, the growth
 * class, the unresolved atoms, and the latencies.
 */
export interface CostReport {
    /** `certified` when every feedback edge has a closed bound; else `flagged`. */
    readonly verdict: CostVerdict
    /** The term's total cost expression. */
    readonly cost: SizeExpr
    /** The term's depth (max-form, collapsed to a size bound). */
    readonly depth: SizeExpr
    /** The result's size expression (opaque for function-typed results). */
    readonly resultSize: SizeExpr
    /** The result's growth class. */
    readonly growth: GrowthClass
    /** A super-affine structural recurrence, stated when the bound is coarse. */
    readonly recurrence: string | undefined
    /** All feedback edges observed. */
    readonly edges: readonly CostEdge[]
    /** The flags (a subset of the edges — the opaque producers). */
    readonly flags: readonly CostFlag[]
    /** The cost contributions the analysis could not bound. */
    readonly unresolved: readonly UnresolvedCost[]
    /** The observation latencies (codata dual). */
    readonly latencies: readonly LatencyReport[]
    /** For an op analysis: the op's name; for a term analysis, the source. */
    readonly subject: string
    /** `unanalyzed` when the subject could not be read at all. */
    readonly status: "analyzed" | "unanalyzed"
    /** The unanalyzability reason (when `status` is `unanalyzed`). */
    readonly unanalyzedReason?: string
}

/** Assemble a report from a summary (the classifier runs here). */
function reportOf(
    summary: CostSummary,
    subject: string,
    recurrence: string | undefined,
): CostReport {
    const flags = summary.edges.filter((e) => e.isFlagged).map(flagOf)
    return {
        verdict: flags.length > 0 ? "flagged" : "certified",
        cost: summary.cost,
        depth: summary.depth.toSize(),
        resultSize: summary.resultSize,
        growth: classifyExpr(summary.resultSize),
        recurrence,
        edges: summary.edges,
        flags,
        unresolved: summary.unresolved,
        latencies: summary.latencies,
        subject,
        status: "analyzed",
    }
}

/**
 * The fields `renderCostReport` reads — shared by `CostReport` (a term's
 * report) and `OpCostSummary` (an op's summary). The renderer states the
 * certificate's bounds and records for either subject.
 */
interface RenderableReport {
    readonly verdict?: CostVerdict
    readonly cost: SizeExpr
    readonly depth: SizeExpr
    readonly resultSize: SizeExpr
    readonly growth: GrowthClass
    readonly recurrence: string | undefined
    readonly edges: readonly CostEdge[]
    readonly flags: readonly CostFlag[]
    readonly unresolved: readonly UnresolvedCost[]
    readonly latencies: readonly LatencyReport[]
    /** The term's source (a `CostReport`); an op summary names itself via `op`. */
    readonly subject?: string
    /** The analyzed operation (an `OpCostSummary` names its subject here). */
    readonly op?: { readonly name: string }
    readonly status: "analyzed" | "unanalyzed"
    readonly unanalyzedReason?: string
}

/** Render the report as a human-readable certificate (tests, diagnostics). */
export function renderCostReport(report: RenderableReport): string {
    const lines: string[] = []
    const subject = report.subject ?? (report.op !== undefined ? report.op.name : "(unknown)")
    lines.push(`subject: ${subject} [${report.status}]`)
    if (report.verdict !== undefined) lines.push(`verdict: ${report.verdict}`)
    lines.push(`cost: ${report.cost.render()}`)
    lines.push(`depth: ${report.depth.render()}`)
    lines.push(`result size: ${report.resultSize.render()}`)
    lines.push(`growth: ${report.growth}`)
    if (report.recurrence !== undefined) lines.push(`recurrence: ${report.recurrence}`)
    for (const edge of report.edges) {
        const bound = edge.bound === undefined ? "none" : edge.bound.render()
        lines.push(
            `edge: ${provenanceName(edge.producer)} → ${edge.consumerSite} (${edge.position}) ` +
                `[bound: ${bound}]${edge.isFlagged ? " FLAGGED" : ""}`,
        )
    }
    for (const flag of report.flags) {
        lines.push(`flag: ${flag.missingBound}`)
        lines.push(`profile: ${flag.suggestedProfile}`)
    }
    for (const u of report.unresolved) {
        lines.push(`unresolved: ${u.reason}`)
    }
    for (const l of report.latencies) {
        lines.push(`latency(${l.observer}): ${l.latency.render()}`)
    }
    return lines.join("\n")
}

// ── The denotation environment ────────────────────────────────────────────────

/**
 * What one name denotes, cost-wise: the value's type classification (the
 * opacity driver), its size expression, and its provenance. This is the
 * inherited attribute the engine threads — the cost-side counterpart of the
 * evaluator's `ρ`.
 */
export interface Denotation {
    /** The denoted value's type (when statically known). */
    readonly type: Type | undefined
    /** Data vs function-typed — the opacity rule's input. */
    readonly kind: "data" | "function" | "unknown"
    /** The value's size expression (`opaque` for function-typed values). */
    readonly size: SizeExpr
    /** What produced the value. */
    readonly provenance: Provenance
}

/** The denotation environment: name ↦ denotation, threaded through binders. */
export class CostEnv {
    private constructor(private readonly bindings: ReadonlyMap<string, Denotation>) {}

    static empty(): CostEnv {
        return new CostEnv(new Map())
    }

    lookup(name: string): Denotation | undefined {
        return this.bindings.get(name)
    }

    extend(name: string, denotation: Denotation): CostEnv {
        const next = new Map(this.bindings)
        next.set(name, denotation)
        return new CostEnv(next)
    }
}

/**
 * Classify a type: function-typed (FunType) vs data vs unknown — routed
 * through `t.dispatch` (the Type universe's required-case dispatch), with the
 * classification degrading to `unknown` for any kind outside the core
 * universe (the engine's own marker types — `FoldRecType` — are deliberate
 * pass-local `Type` subclasses that never escape the module).
 *
 * The try/catch is the contract, not defense: classification is a TAG, not
 * a membership test (the membership boundary is `subtyping.ts`'s
 * `requireType`, which throws). A foreign subclass reaching a binder's
 * denotation must cost nothing and classify unknown — never crash the
 * analysis (`analyzeTerm` never throws). The interception in `extendCtx`
 * handles the engine's own marker; this keeps the classification robust
 * against future call sites that forget it.
 */
function typeKind(type: Type | undefined): "data" | "function" | "unknown" {
    if (type === undefined) return "unknown"
    try {
        return type.dispatch<"data" | "function" | "unknown">({
            fun: () => "function",
            intersection: () => "unknown",
            polymorphic: () => "unknown",
            typeVar: () => "unknown",
            family: () => "unknown",
            data: () => "data",
            patternData: () => "data",
            codata: () => "data",
            token: () => "unknown",
            any: () => "unknown",
            nothing: () => "unknown",
        })
    } catch {
        // An undeclared Type subclass (a pass-local marker that escaped its
        // producer's interception): classify unknown, never crash.
        return "unknown"
    }
}

/** The denotation for a binder at a declared type (the `extendCtx` hook's). */
function denotationFor(name: string, type: Type | undefined): Denotation {
    const kind = typeKind(type)
    return {
        type,
        kind,
        size: kind === "function"
            ? SizeExpr.opaque(`function-typed value "${name}"`)
            : SizeExpr.variable(name),
        provenance: { kind: "param", name },
    }
}

// ── The fold recurrence (the plan's D4) ───────────────────────────────────────

/**
 * The result-size recurrence's outcome: the closed bound, when the recurrence
 * closed to one; the stated recurrence when it did not (the honest residual);
 * the growth class the recurrence establishes.
 */
export interface RecurrenceResult {
    readonly closed: SizeExpr | undefined
    readonly recurrence: string | undefined
    readonly growth: GrowthClass
}

/**
 * Solve the chain recurrence: R = base (the base variants' result sizes) or
 * step (the recursive variant's body size with the recursive binding already
 * substituted by `R` itself). Solvable when `step` is affine in `R` in the
 * LFPL shape (bare R, coefficient ≤ 1, exponent 1): R closes to
 * base + |input|·(per-step growth), summed over the scrutinee's FULL size
 * expression. The discipline mirrors `coefficients`' truncated fixpoint — no
 * general equation solving (differentiate the equation directly):
 *
 * 1. **Affine closure (the Hofmann/LFPL shape).** Each recursive result feeds
 *    back at most itself — the recursion variable appears BARE in the step
 *    (exponent 1, no other factors in its monomial) with total coefficient
 *    ≤ 1. A symbolic factor riding alongside (`|y|·R`) is multiplicative
 *    feedback (geometric growth), not chain summation — it does not close.
 *    This certifies `map` → fold and every linear fold.
 * 2. **Chain summation.** R(n) = R(n−1) + g closes to base + |input|·g —
 *    symbolic summation of the R-free polynomial g over the scrutinee's
 *    FULL size expression (a multi-variable scrutinee sums over its whole
 *    size: the invocation count is the node count, however many names it
 *    takes).
 * 3. **Beyond affine** (geometric structural self-growth — a non-bare R
 *    monomial, a coefficient > 1, or an exponent > 1): the bound does not
 *    close to a polynomial. The verdict stays certified — the growth is
 *    primitive-recursive and the recurrence is mechanically computed — but
 *    the certificate states the recurrence and the coarse class, never a
 *    closed bound.
 */
function solveChainRecurrence(
    baseSize: SizeExpr,
    stepSize: SizeExpr,
    recursionVar: string,
    inputSize: SizeExpr,
): RecurrenceResult {
    if (baseSize.isOpaque || stepSize.isOpaque || inputSize.isOpaque) {
        return { closed: undefined, recurrence: undefined, growth: "unbounded" }
    }
    // Decompose step = (R-parts, each with the recursion variable factored
    // out) + rest (the R-free remainder). The R-parts must be the BARE
    // variable (no other factors in the monomial) — a symbolic factor riding
    // alongside is the multiplicative-feedback shape that must not close.
    let coefficient = 0
    let exponent = 0
    let bare = true
    for (const m of stepSize.monomials) {
        const e = m.factors.get(recursionVar)
        if (e === undefined) continue
        if (m.factors.size !== 1) bare = false
        coefficient = satAdd(coefficient, m.coefficient)
        exponent = Math.max(exponent, e)
    }
    const rest = stepSize.without(recursionVar)
    // Affine non-size-increasing (the LFPL shape): the recursion feeds back
    // at most itself, bare — R(n) = rest + R(n−1) closes to
    // base + |input|·rest over the scrutinee's FULL size expression (the
    // invocation count is the input's node count, whatever variables name
    // it). The per-step growth is the R-free part of the step body (a bare
    // recursion — the identity handler — contributes the constant 1 per
    // step).
    if (coefficient <= 1 && exponent <= 1 && bare) {
        const perStep = rest.isZero ? SizeExpr.ONE : rest
        const closed = baseSize.plus(inputSize.times(perStep))
        return { closed, recurrence: undefined, growth: classifyExpr(closed) }
    }
    // Super-affine: report the recurrence, coarsely (certified, not flagged).
    const inputName = inputSize.render()
    return {
        closed: undefined,
        recurrence:
            `R(${inputName}) = ${stepSize.render()} (recursion substituted), R(base) = ${baseSize.render()}`,
        growth: "exponential (primitive-recursive)",
    }
}

/**
 * The marker type for a fold handler's recursive field binding: the binder
 * denotes the fold's own recursion result — a symbolic quantity with fold
 * provenance (the flag's named producer), whose size has no static algebra
 * of its own (the recursion result's size is the fold's recurrence output).
 *
 * The engine's `foldFieldType` returns it for recursive fields; `extendCtx`
 * translates it into the fold-recursion denotation. It never escapes the
 * engine: the fold action consumes summaries only, and no report reads types.
 */
class FoldRecType extends Type {
    constructor(readonly carrierName: string) {
        super()
    }

    override equals(other: Type): boolean {
        return other instanceof FoldRecType && other.carrierName === this.carrierName
    }

    override toString(): string {
        return `⟨rec ${this.carrierName}⟩`
    }

    /**
     * The pass-local marker is OUTSIDE the core universe: a generic
     * dispatch arm would name an undeclared case, so the marker answers
     * itself — any case table it reaches throws with this type's name,
     * which the engine's classification degrades to `unknown` (the
     * try/catch contract in `typeKind`). `map` throws the same way: no
     * structural reading of a marker exists, so there is no traversal
     * to run.
     */
    override dispatch<T>(_cases: RequiredCases<T>): T {
        throw new TypeError(
            `FoldRecType (${this.carrierName}) is a cost-engine marker outside ` +
                `the core Type universe — no generic case table answers for it`,
        )
    }

    override map(_cases: TypeCases<Type>): Type {
        throw new TypeError(
            `FoldRecType (${this.carrierName}) is a cost-engine marker outside ` +
                `the core Type universe — no structural map answers for it`,
        )
    }

    override resolveFamily(_carrier: DataType): Type {
        throw new TypeError(
            `FoldRecType (${this.carrierName}) is a cost-engine marker outside ` +
                `the core Type universe — no μ-bound to resolve`,
        )
    }
}

/**
 * The denotation for a fold's recursive field binding: the recursion result
 * — FOLD provenance (the flag's producer end names the fold, which is what
 * makes a handler-internal application of the recursion result — the
 * Ackermann shape — flaggable), function classification (an applied
 * recursion result is the flagged higher-order composition), and a
 * SYMBOLIC size: the binding's own name. The fold's action substitutes that
 * variable by the recursion result at the subtree (the recurrence's R), so
 * first-order handler work stays symbolic and closable — while an
 * APPLICATION of the binding hits the flagged arm (a function-typed value
 * whose per-application cost has no static algebra).
 */
function foldRecDenotation(carrierName: string, name: string): Denotation {
    return {
        type: undefined,
        kind: "function",
        size: SizeExpr.variable(name),
        provenance: { kind: "fold", name: carrierName },
    }
}

// ── The cost engine (the grammar-subclass vehicle) ────────────────────────────

/** The engine's parse shape: expr = CostSummary, atom = CostSummary. */
interface CostShape extends LCShape {
    expr: CostSummary
    atom: CostSummary
    type: Type
}

/**
 * The deferred full-application cost of a closure chain (λx₁. … .λxₖ. body).
 *
 * `cost` is the body's FULL production cost — symbolic in the chain's binder
 * names (`params`, outermost first) — consumed when the chain has been
 * applied to all its arguments: each application substitutes one binder by
 * the argument's size; the last one exposes the body's cost as the
 * application's own. `resultSize`/`provenance`/`resultKind` describe the
 * fully-applied body's outcome.
 *
 * This is what makes an op summary reflect its fold's work: the definition
 * `\\x. \\y. fold [T] x {...}` carries the fold's cost over `|x|`; an
 * `opApp` instantiating the summary at `|a|`, `|b|` yields the recursion's
 * shape — not the constant closure cost. `undefined` when the body could not
 * be bounded (an opaque body — a function-typed value applied inside):
 * application sites record an unresolved contribution instead of a false
 * bound.
 */
interface ClosureChain {
    readonly params: readonly string[]
    readonly cost: SizeExpr
    readonly bodyDepth: DepthExpr
    readonly resultSize: SizeExpr
    readonly provenance: Provenance
    readonly resultKind: "data" | "function" | "unknown"
}

/** Compose two summaries sequentially: costs add, depths compose, records union. */
function summaryPlus(a: CostSummary, b: CostSummary): CostSummary {
    return {
        cost: a.cost.plus(b.cost),
        depth: b.depth.max(a.depth),
        resultSize: b.resultSize,
        provenance: b.provenance,
        resultKind: b.resultKind,
        edges: [...a.edges, ...b.edges],
        unresolved: [...a.unresolved, ...b.unresolved],
        latencies: [...a.latencies, ...b.latencies],
    }
}

/**
 * The cost engine: the LC grammar's concrete syntax with cost-summary
 * semantic actions, threading a denotation environment (`CostEnv`) through
 * the productions — the evaluator's architecture, cost-side.
 *
 * The engine needs only enough typing to classify function-typed values (the
 * opacity rule): Ω's declared signatures, the registry's variant fields,
 * lambda annotations in the source, and the fold's own handler structure. It
 * does NOT consume the type checker's per-node types (the analysis is
 * independent of `LCTypeCheck` — see the plan's D7).
 *
 * **Closure body costs.** A lambda's summary is O(1) to *produce*, and it
 * carries the body's cost as the **deferred per-application cost** (`bodyCost`)
 * — the work one application of the closure performs, symbolic in the
 * parameter's size variable. Application sites consume it: `app` adds the
 * closure's `bodyCost` (with the parameter substituted by the argument's size)
 * to the composition. This is what makes an op summary reflect its fold's
 * work: the definition `\x. \y. fold [T] x {...}` summarizes as the fold's
 * cost over `|x|`, not the constant closure cost — and a caller instantiating
 * the summary at `|a|`, `|b|` gets the recursion's shape, not `1`.
 *
 * An opaque body (the parameter applied inside — the Ackermann shape) records
 * the contribution as unresolved, flagged only when the applied value flows
 * from a *fold's recursion result* (the flagged feedback shape).
 */
class CostEngine extends AbstractLC<CostShape> {
    constructor(
        registry: TypeRegistry,
        private readonly omega: OpRegistry,
        private readonly store: OpSummaryStore,
    ) {
        super()
        this.setRegistry(registry)
        this.setOpRegistry(omega)
    }

    override start(): Parser<CostSummary> {
        return this.exprProd(CostEnv.empty())
    }

    /** Analyze one LC source fragment under a denotation environment. */
    analyze(source: string, env: CostEnv): CostSummary | undefined {
        const results = [...this._parseWith(source, this.exprProd(env))]
        return results.length === 1 ? results[0] : undefined
    }

    // ── Context extension: the binder hook ────────────────────────────────────

    protected override extendCtx(ctx: unknown, name: string, type: Type): unknown {
        if (ctx instanceof CostEnv) {
            // The fold-recursion marker: the binder denotes the fold's own
            // recursion result (opaque size, fold provenance — the flag's
            // named producer end).
            if (type instanceof FoldRecType) {
                return ctx.extend(name, foldRecDenotation(type.carrierName, name))
            }
            return ctx.extend(name, denotationFor(name, type))
        }
        return ctx
    }

    /**
     * The type a fold handler's field binding carries into `extendCtx`:
     * non-recursive fields at their declared type (data — the raw field
     * value's size variable); Family fields (the μ-bound) at the
     * fold-recursion marker (the denotation is the fold's own result —
     * opaque size, fold provenance). This is the cost-side mirror of
     * E-Fold's binding rule (a recursive field binds the folded result) and
     * the type checker's σ binding.
     */
    protected override foldFieldType(field: Field, dataType: DataType): Type {
        // Only the μ-bound occurrence (a Family-typed field) is the
        // fold-recursion denotation: resolveFamily translates Family → the
        // carrier, so the RESOLVED type is the carrier exactly when the field
        // was Family-typed; an ordinary data field stays itself. Distinguish
        // the two by the DECLARED field type: Family resolves to the carrier
        // (== dataType); a genuine data field names its own type.
        return field.type instanceof FamilyType ? new FoldRecType(dataType.name) : field.type
    }

    // ── Semantic actions ──────────────────────────────────────────────────────

    /**
     * λx:σ. t — the closure's summary. Producing the closure is O(1); the
     * body's cost rides along as the deferred per-application cost (its own
     * edges/unresolved/latencies ride along too — they materialize when the
     * closure is applied or when the summary's records are read). A
     * function-typed parameter is opaque: the body's cost under an opaque
     * parameter is not a closed bound, so `bodyCost` is undefined and the
     * application sites record the unresolved contribution instead.
     */
    protected override lam(param: string, type: Type, body: CostSummary): CostSummary {
        void type
        return closureSummary(param, body)
    }

    /** t u — application composition (see `applySummary`). */
    protected override app(fn: CostSummary, arg: CostSummary): CostSummary {
        return applySummary(fn, arg, { kind: "unknown" })
    }

    /**
     * let x:σ = t in u — the definition's cost + the body's cost. The binder
     * denotes the DEFINITION'S RESULT: the grammar extended the body's
     * context with the declared type, but the definition's summary carries
     * the tighter fact — its result size (and provenance/kind). The engine
     * threads it through the summary's records: the body saw the binder via
     * `extendCtx`'s declared-type denotation, so the records' size variables
     * under that name are substituted by the definition's result size here —
     * the same binding rule `CostPass.letProd` applies (the two vehicles
     * agree on `let`).
     */
    protected override let_(
        name: string,
        _type: Type,
        def: CostSummary,
        body: CostSummary,
    ): CostSummary {
        // The body was analyzed under the declared-type denotation: its
        // size variable for `name` is exactly `name` (see `denotationFor`).
        // Substitute it by the definition's result — the definition's
        // records ride along into the substitution so a fold over the
        // bound name reads its input's actual size.
        const substituteIn = (s: CostSummary): CostSummary => ({
            ...s,
            cost: s.cost.substitute(name, def.resultSize),
            depth: s.depth.substitute(name, def.resultSize),
            resultSize: s.resultSize.substitute(name, def.resultSize),
        })
        const defBound = substituteIn(def)
        const bodyBound = substituteIn(body)
        return summaryPlus(defBound, bodyBound)
    }

    /** x — a variable: its denotation (zero work; the size rides on the ref). */
    protected override varRef(name: string, ctx: unknown): CostSummary {
        const env = ctx as CostEnv
        const d = env.lookup(name)
        if (d === undefined) {
            // An unbound name under this environment: an honest size variable
            // (the caller's environment governs what it denotes).
            return {
                cost: SizeExpr.ZERO,
                depth: DepthExpr.ZERO,
                resultSize: SizeExpr.variable(name),
                provenance: { kind: "param", name },
                resultKind: "unknown",
                edges: [],
                unresolved: [],
                latencies: [],
            }
        }
        return {
            cost: SizeExpr.ZERO,
            depth: DepthExpr.ZERO,
            resultSize: d.size,
            provenance: d.provenance,
            resultKind: d.kind,
            edges: [],
            unresolved: [],
            latencies: [],
        }
    }

    protected override paren(e: CostSummary): CostSummary {
        return e
    }

    /** Cᵢ(tⱼ) — the constructor rule: work = Σⱼ (fields' work) + 1 node. */
    protected override variantCon(name: string, args: CostSummary[]): CostSummary {
        let summary = emptySummary()
        for (const arg of args) summary = summaryPlus(summary, arg)
        return {
            ...summary,
            cost: summary.cost.plus(SizeExpr.ONE),
            depth: summary.depth.plus(SizeExpr.ONE),
            resultSize: summary.resultSize.plus(SizeExpr.ONE),
            provenance: { kind: "constructor", name },
            resultKind: "data",
        }
    }

    /**
     * e.o — the observation: the codata dual. The observation's cost is the
     * generator body's cost on the seed — statically the seed-driven latency
     * (a named variable, bounded by the unfold site's generator analysis when
     * one is in scope), else an honest named atom.
     */
    protected override obs(scrutinee: CostSummary, observerName: string): CostSummary {
        const seedLatency = SizeExpr.variable(`latency(${observerName})`)
        return {
            cost: scrutinee.cost.plus(seedLatency),
            depth: scrutinee.depth.plus(seedLatency),
            resultSize: SizeExpr.variable(`obs(${observerName})`),
            provenance: { kind: "unknown" },
            resultKind: "unknown",
            edges: [
                ...scrutinee.edges,
                {
                    producer: scrutinee.provenance,
                    consumer: { kind: "unknown" },
                    position: "observation generator",
                    consumerSite: observerName,
                    bound: scrutinee.resultSize.isOpaque ? undefined : scrutinee.resultSize,
                    isFlagged: scrutinee.resultSize.isOpaque,
                },
            ],
            unresolved: scrutinee.unresolved,
            latencies: [
                ...scrutinee.latencies,
                { observer: observerName, latency: seedLatency },
            ],
        }
    }

    /**
     * fold [T] s {Cᵢ(xⱼ) → tᵢ} — the container-shaped core.
     *
     * The recursion tree is isomorphic to the scrutinee's structure: the
     * invocation count is the scrutinee's node count, independent of the
     * handler bodies. Per node, the work is the matching handler body's
     * cost. The handler environment binds non-recursive fields to their raw
     * sizes and RECURSIVE fields to the fold's own recursion result — the
     * symbolic quantity the fold's recurrence computes (the same binding
     * rule E-Fold applies on concrete values: a recursive field binds the
     * folded result).
     *
     * The handler bodies were analyzed under the production's environment;
     * the fold re-substitutes each binding's size variable: non-recursive
     * bindings keep their raw field sizes; recursive bindings take the
     * recursion result at the subtree.
     */
    protected override fold(
        dataType: DataType,
        scrutinee: CostSummary,
        handlers: { variantName: string; bindings: string[]; body: CostSummary }[],
        _resultType: Type,
    ): CostSummary {
        void _resultType
        // The scrutinee's records PLUS every handler body's records: a
        // handler-internal application of the recursion binding (the
        // Ackermann shape) records its flag edge inside the body — dropping
        // it would launder a flagged feedback into a certified report.
        const edges: CostEdge[] = [...scrutinee.edges]
        const unresolved: UnresolvedCost[] = [...scrutinee.unresolved]
        const latencies: LatencyReport[] = [...scrutinee.latencies]
        for (const handler of handlers) {
            edges.push(...handler.body.edges)
            unresolved.push(...handler.body.unresolved)
            latencies.push(...handler.body.latencies)
        }

        // The scrutinee's size drives the invocation count — a size-sensitive
        // position: record the edge (scrutinee → this fold).
        edges.push({
            producer: scrutinee.provenance,
            consumer: { kind: "fold", name: dataType.name },
            position: "fold scrutinee",
            consumerSite: `fold [${dataType.name}]`,
            bound: scrutinee.resultSize.isOpaque ? undefined : scrutinee.resultSize,
            isFlagged: scrutinee.resultSize.isOpaque,
        })

        // The recursion variable: the fold's result at a subtree. The `#`
        // prefix makes it untypable — a user binder named `foldRec` cannot
        // collide with the fold's own symbolic quantity under `substitute`.
        const RECURSION = "#foldRec"

        // Per-handler summaries with the bindings substituted.
        const perHandler = handlers.map((handler) => {
            const variant = dataType.findVariant(handler.variantName)
            let bodyCost = handler.body.cost
            let bodySize = handler.body.resultSize
            let bodyDepth = handler.body.depth
            if (variant !== undefined) {
                variant.fields.forEach((field: Field, i: number) => {
                    const binding = handler.bindings[i]
                    if (binding === undefined) return
                    if (field.type instanceof FamilyType) {
                        // The recursion result at the subtree.
                        const recResult = SizeExpr.variable(RECURSION)
                        bodyCost = bodyCost.substitute(binding, recResult)
                        bodySize = bodySize.substitute(binding, recResult)
                        bodyDepth = bodyDepth.substitute(binding, recResult)
                    }
                    // Non-recursive bindings keep their raw field sizes (the
                    // size variables the production bound them to).
                })
            }
            return {
                variantName: handler.variantName,
                cost: bodyCost,
                size: bodySize,
                depth: bodyDepth,
            }
        })

        // The per-node work: the pairing is invocations × (Σ handler costs)
        // — a safe OVER-APPROXIMATION of the exact Σ_nodes decomposition
        // (per node, only the matching handler's body runs; summing all
        // handlers charges every handler at every node, so non-uniform
        // handlers over-approximate by the handler-count factor). The sum
        // (not the max) is what the arithmetic supports: SizeExpr has no max
        // operator, and the sum stays sound for uniform handlers — where it
        // IS the max — while the recurrence solver consumes it directly.
        let perNodeWork = SizeExpr.ZERO
        let perNodeDepth = DepthExpr.ZERO
        let foldRecurrence: string | undefined
        for (const h of perHandler) {
            perNodeWork = perNodeWork.plus(h.cost)
            perNodeDepth = perNodeDepth.max(h.depth)
        }

        // The result-size recurrence: chain carriers (exactly one recursive
        // variant with exactly one recursive field) close via the solver;
        // everything else reports the conservative symbolic form.
        const allVariants = dataType.allVariants()
        const recursiveVariants = allVariants.filter((v) =>
            v.fields.some((f) => f.type instanceof FamilyType)
        )
        let resultSize: SizeExpr
        const isChain = recursiveVariants.length === 1 &&
            recursiveVariants[0]!.fields.filter((f) => f.type instanceof FamilyType).length === 1
        if (isChain) {
            const recVariant = recursiveVariants[0]!
            const baseVariants = allVariants.filter(
                (v) => !v.fields.some((f) => f.type instanceof FamilyType),
            )
            const baseSize = baseVariants.reduce<SizeExpr>(
                (sum, v) => {
                    const h = perHandler.find((ph) => ph.variantName === v.name)
                    return sum.plus(h ? h.size : SizeExpr.ZERO)
                },
                SizeExpr.ZERO,
            )
            const stepHandler = perHandler.find((ph) => ph.variantName === recVariant.name)
            const stepSize = stepHandler ? stepHandler.size : SizeExpr.ZERO
            // The recurrence's input is the scrutinee's FULL size expression
            // — the invocation count is the input's node count, whatever
            // variables name it (e.g. `|p0|` under an op definition's
            // environment, `|m| + |n|` for a sum-scrutinee, the literal's own
            // node count for a constructor literal). An opaque scrutinee
            // names itself honestly (`scrutinee` — the conservative fallback
            // the cost path below shares).
            const inputSize = scrutinee.resultSize.isOpaque
                ? SizeExpr.variable("#scrutinee")
                : scrutinee.resultSize
            const solved = solveChainRecurrence(baseSize, stepSize, RECURSION, inputSize)
            resultSize = solved.closed ?? SizeExpr.opaque("super-affine structural growth")
            foldRecurrence = solved.recurrence
        } else {
            resultSize = SizeExpr.variable(RECURSION)
        }

        // The cost: scrutinee evaluation + Σ over nodes of per-node work.
        // The invocation count is the scrutinee's node count — exact for a
        // literal scrutinee (its own size), else the scrutinee's OWN size
        // variable (e.g. |p0| under an op definition's parameter denotation —
        // the recurrence's input, named by the denotation the environment
        // bound; an unbound scrutinee falls back to its rendered form).
        const isLiteral = scrutinee.provenance.kind === "constructor"
        const invocations = isLiteral
            ? scrutinee.resultSize
            : scrutinee.resultSize.isOpaque
            ? SizeExpr.variable("#scrutinee")
            : scrutinee.resultSize
        const foldCost = invocations.times(perNodeWork)
        const foldDepth = scrutinee.depth.plus(invocations).max(perNodeDepth.plus(invocations))

        return {
            cost: scrutinee.cost.plus(foldCost),
            depth: foldDepth,
            resultSize,
            recurrence: foldRecurrence,
            provenance: { kind: "fold", name: dataType.name },
            resultKind: resultSize.isOpaque ? "unknown" : "data",
            edges,
            unresolved,
            latencies,
        }
    }

    /**
     * unfold [T] s {oⱼ → gⱼ} — the codata value (lazy: generators deferred).
     * The generators' WORK stays deferred into the latency entries (an
     * observation pays it); the generators' DIAGNOSTIC RECORDS — the flag
     * edges and unresolved contributions inside a generator body (an
     * Ackermann-shaped fold inside a generator, an unresolved higher-order
     * application) — are NOT deferred: they are part of the codata value's
     * own certificate, and deferring them would let an observation report
     * `certified` while a flagged feedback edge hides inside the generator.
     * Records ride along now; only the work lands in the latencies.
     */
    protected override unfold(
        codataType: CodataType,
        seed: CostSummary,
        generators: { observerName: string; body: CostSummary }[],
        _seedType: Type,
    ): CostSummary {
        // The per-observer work ledger (each observation pays its
        // generator's cost) plus the generators' own latencies (a
        // generator may itself observe another codata value).
        const latencies: LatencyReport[] = generators.flatMap((g) => [
            { observer: g.observerName, latency: g.body.cost },
            ...g.body.latencies,
        ])
        const edges: CostEdge[] = [...seed.edges]
        const unresolved: UnresolvedCost[] = [...seed.unresolved]
        for (const g of generators) {
            edges.push(...g.body.edges)
            unresolved.push(...g.body.unresolved)
        }
        return {
            cost: seed.cost.plus(SizeExpr.ONE),
            depth: seed.depth.plus(SizeExpr.ONE),
            resultSize: SizeExpr.constant(1),
            provenance: { kind: "unfold", name: codataType.name },
            resultKind: "data",
            edges,
            unresolved,
            latencies,
        }
    }

    /** ^α<:σ. t — type abstraction (erasure): the body's summary. */
    protected override typeAbs(_tyVar: string, _bound: Type, body: CostSummary): CostSummary {
        return body
    }

    /** t [τ] — type application (erasure): the body's summary. */
    protected override typeApp(body: CostSummary, _argType: Type): CostSummary {
        return body
    }

    /** cofold [T] e {o(xⱼ) → t} — codata elimination: the handler's work. */
    protected override cofold(
        codataType: CodataType,
        scrutinee: CostSummary,
        handler: { observerName: string; bindings: string[]; body: CostSummary },
        _resultType: Type,
    ): CostSummary {
        return {
            cost: scrutinee.cost.plus(handler.body.cost).plus(SizeExpr.ONE),
            depth: scrutinee.depth.max(handler.body.depth).plus(SizeExpr.ONE),
            resultSize: SizeExpr.constant(1),
            provenance: { kind: "cofold", name: codataType.name },
            resultKind: "data",
            edges: scrutinee.edges,
            unresolved: scrutinee.unresolved,
            latencies: scrutinee.latencies,
        }
    }

    /**
     * op(tⱼ) — the named application: the callee's memoized summary,
     * instantiated at the arguments' sizes. The `opProd` node's identity (the
     * registry gate recognized the name) is what makes the memoization
     * possible — the summary comes from Ω once.
     *
     * A name NOT in Ω is the honest residual: the application's work is not
     * counted (no summary exists) AND the result's size is opaque (the
     * result type is unknown — a closed size here would be a falsely precise
     * certificate). The unresolved record states the non-counting policy;
     * the classifier sees the opaque result, not a certified one.
     */
    protected override opApp(opName: string, args: CostSummary[]): CostSummary {
        const op = this.omega.lookup(opName)
        if (op === undefined) {
            const base = args.reduce(summaryPlus, emptySummary())
            return {
                ...base,
                resultSize: SizeExpr.opaque(`unresolvable op "${opName}"`),
                provenance: { kind: "op", name: opName },
                resultKind: "unknown",
                unresolved: [
                    ...base.unresolved,
                    {
                        site: { kind: "op", name: opName },
                        applied: { kind: "unknown" },
                        reason: `the source applies "${opName}", which is not declared in Ω ` +
                            `— no cost summary exists for it; its work is not counted`,
                    },
                ],
            }
        }
        const summary = this.store.summaryOf(this.omega, op)
        return instantiateOpSummary(op, summary, args)
    }

    /** match("p") — a matched token: a named size variable (the text is unknown). */
    protected override matchedToken(dataTypeName: string, _text: string): CostSummary {
        return {
            cost: SizeExpr.ONE,
            depth: DepthExpr.constant(1),
            resultSize: SizeExpr.variable(`token(${dataTypeName})`),
            provenance: { kind: "token", name: dataTypeName },
            resultKind: "data",
            edges: [],
            unresolved: [],
            latencies: [],
        }
    }

    /**
     * match("p") — pattern-matched construction: the same cost shape as the
     * bare token atom. Producing the token is O(1); the RESULT size is the
     * pattern's CANONICAL source length (the value's own size measure —
     * `TokenVal.size` is its text length, and the token's text is the
     * canonical source the gate resolves), a static quantity the declared
     * pattern fixes. No subterms, no edges, no recursion.
     *
     * The size variable is named per-pattern (`token(T:<p>)`, vs the bare
     * atom's `token(T)`): the two introduction routes carry DIFFERENT static
     * texts (the bare atom's text is the type name; the match form's text is
     * the pattern source), so the variables name the value the route fixes —
     * two routes producing one type's tokens do not share a size variable
     * because their `TokenVal.size` values differ (the name-lexed form's
     * length vs the pattern source's length). The canonical source — not the
     * caller's spelling — names the variable, so two spellings of one AST
     * share the variable (their tokens are equal, sizes included).
     *
     * The pattern source is ARBITRARY pattern text (metacharacters, quoted
     * literals, control characters), while every other variable name in the
     * algebra comes from a restricted grammar — and the algebra's internal
     * machinery parses names structurally (the monomial merge key splits on
     * `,`/`^`; the renderer wraps in `|…|`). The source is therefore
     * sanitized into the safe alphabet (`sanitizeNameComponent` — ASCII
     * pattern characters like `[0-9]+` pass through unescaped and stay
     * human-readable; quotes, backslashes, and control characters
     * hex-escape), so the name is unambiguous in the merge keys and the
     * rendered certificate whatever the pattern contains.
     */
    protected override matchedPattern(
        dataTypeName: string,
        patternSource: string,
        _rawSource: string,
    ): CostSummary {
        const source = sanitizeNameComponent(patternSource)
        return {
            cost: SizeExpr.ONE,
            depth: DepthExpr.constant(1),
            resultSize: SizeExpr.variable(`token(${dataTypeName}:${source})`),
            provenance: { kind: "token", name: dataTypeName },
            resultKind: "data",
            edges: [],
            unresolved: [],
            latencies: [],
        }
    }
}

/**
 * A closure's summary: producing it is O(1); the body's analysis rides along
 * as the deferred full-application cost (the `ClosureChain` — the body's
 * full cost over the chain's binders) and its records
 * (edges/unresolved/latencies) ride along too — they materialize when the
 * closure is applied or when the summary's records are read. A body whose
 * cost could not be bounded carries no chain: application sites record the
 * unresolved contribution instead of a false bound.
 */
function closureSummary(param: string, body: CostSummary): CostSummary {
    // Compose the chain: an inner closure's deferred chain (the rest of the
    // curried lambda chain) folds into this one — the params accumulate
    // (outermost first) and the cost/result stay the fully-applied body's.
    // The binders' names are distinct per binder (shadowing rebinds the
    // environment, never the same name twice in one chain's cost), so the
    // accumulated parameter list substitutes one-to-one at application.
    const inner = body.bodyChain
    const chain: ClosureChain = inner !== undefined
        ? {
            params: [param, ...inner.params],
            cost: inner.cost,
            bodyDepth: inner.bodyDepth,
            resultSize: inner.resultSize,
            provenance: inner.provenance,
            resultKind: inner.resultKind,
        }
        : {
            params: [param],
            cost: body.cost,
            bodyDepth: body.depth,
            resultSize: body.resultSize,
            provenance: { kind: "closure", name: param },
            resultKind: "function",
        }
    return {
        cost: SizeExpr.ONE,
        depth: DepthExpr.constant(1),
        resultSize: SizeExpr.opaque(`closure (λ${param})`),
        provenance: { kind: "closure", name: param },
        resultKind: "function",
        // The body's stated recurrence rides along — a super-affine fold
        // inside the closure is the op definition's own certificate note
        // (computeOpSummary reads it off the peeled summary).
        recurrence: body.recurrence,
        bodyChain: chain.cost.isOpaque ? undefined : chain,
        edges: body.edges,
        unresolved: body.unresolved,
        latencies: body.latencies,
    }
}

/**
 * Application composition: fn's summary applied to arg's summary.
 *
 * The application's cost is fn's + arg's + the applied body's next
 * contribution: a deferred chain substitutes its outermost binder by the
 * argument's size; when the chain has one binder left, the substitution IS
 * the body's cost at the argument and the body's result flows out (a
 * curried chain accumulates its body's work at the last application — the
 * composition an op summary's instantiation reads back). Partially-applied
 * chains keep the remaining cost deferred for the next application.
 *
 * When fn is a function-typed *value* with no deferred chain (a fold's
 * recursion result applied inside its own handler — the Ackermann shape),
 * the application contribution is unresolved AND the edge flags: the applied
 * value's size has no algebra, so the per-application cost has no static
 * bound. A closure whose chain was dropped (an opaque body) records the
 * unresolved contribution without flagging (the ordinary higher-order
 * composition).
 */
function applySummary(fn: CostSummary, arg: CostSummary, consumer: Provenance): CostSummary {
    const edges: CostEdge[] = [...fn.edges, ...arg.edges]
    const unresolved: UnresolvedCost[] = [...fn.unresolved, ...arg.unresolved]
    if (fn.resultKind === "function" || fn.resultSize.isOpaque) {
        // The application's function position is size-sensitive: the applied
        // function's per-application cost is consumed here. The flag fires
        // when the producer is a FOLD's recursion result (the Ackermann
        // shape) — a lambda's own application (the closure the analyst
        // wrote) consumes its deferred chain instead. An unfold/cofold
        // result is an ordinary first-order codata value (size 1) — never
        // the flagged recursion shape, never a flag producer here.
        const isFoldResult = fn.provenance.kind === "fold"
        edges.push({
            producer: fn.provenance,
            consumer,
            position: "application function",
            consumerSite: "apply",
            bound: undefined,
            isFlagged: isFoldResult,
        })
        if (isFoldResult) {
            unresolved.push({
                site: consumer,
                applied: fn.provenance,
                reason: `the applied value is a fold's recursion result ` +
                    `(${provenanceName(fn.provenance)}) — its per-application cost ` +
                    `has no static algebra (the flagged feedback shape)`,
            })
        }
        // The deferred chain: an analyzed closure contributes the next
        // binder's substitution; a fully-peeled chain exposes the body's
        // cost and result.
        let appliedCost = SizeExpr.ZERO
        let nextChain: ClosureChain | undefined
        let resultSize = SizeExpr.opaque("applied function's result — unknown body")
        let provenance: Provenance = { kind: "unknown" }
        let resultKind: CostSummary["resultKind"] = "unknown"
        const chain = fn.bodyChain
        if (chain !== undefined && chain.params.length > 0) {
            // Substitute the outermost binder by the argument's size.
            const substituted = chain.cost.substitute(chain.params[0]!, arg.resultSize)
            if (chain.params.length > 1) {
                // More binders pending: the cost stays deferred, one binder
                // shorter.
                appliedCost = SizeExpr.ZERO
                nextChain = {
                    params: chain.params.slice(1),
                    cost: substituted,
                    bodyDepth: chain.bodyDepth,
                    resultSize: chain.resultSize,
                    provenance: chain.provenance,
                    resultKind: chain.resultKind,
                }
            } else {
                // The last binder: the body's cost lands on this
                // application; its result flows out.
                appliedCost = substituted
                resultSize = chain.resultSize
                provenance = chain.provenance
                resultKind = chain.resultKind
            }
        } else if (!isFoldResult) {
            unresolved.push({
                site: consumer,
                applied: fn.provenance,
                reason: `the applied closure's body has no closed cost ` +
                    `(${provenanceName(fn.provenance)}) — the per-application ` +
                    `contribution is recorded, not bounded`,
            })
        }
        return {
            cost: fn.cost.plus(arg.cost).plus(appliedCost),
            depth: fn.depth.max(arg.depth).max(DepthExpr.of(appliedCost)),
            resultSize,
            provenance,
            resultKind,
            bodyChain: nextChain,
            edges,
            unresolved,
            latencies: [...fn.latencies, ...arg.latencies],
        }
    }
    return {
        cost: fn.cost.plus(arg.cost),
        depth: fn.depth.max(arg.depth),
        resultSize: SizeExpr.opaque("applied non-closure"),
        provenance: { kind: "unknown" },
        resultKind: "unknown",
        edges,
        unresolved,
        latencies: [...fn.latencies, ...arg.latencies],
    }
}

// ── Op summaries (the plan's D6: memoized, stratified, identity-bearing) ──────

/**
 * An operation's cost summary: the definition's summary with the parameters'
 * size variables as the free quantities, plus the report-level records the
 * analysis accumulated (the definition's own edges/unresolved/latencies).
 */
export interface OpCostSummary {
    /** The analyzed operation. */
    readonly op: CheckedOpSig
    /** The definition's cost, in terms of the parameters' size variables. */
    readonly cost: SizeExpr
    /** The definition's depth (collapsed to a size bound). */
    readonly depth: SizeExpr
    /** The result's size expression (in terms of the parameters' sizes). */
    readonly resultSize: SizeExpr
    /** The result's growth class. */
    readonly growth: GrowthClass
    /** A super-affine recurrence, stated when the bound is coarse. */
    readonly recurrence: string | undefined
    /** The definition's feedback edges. */
    readonly edges: readonly CostEdge[]
    /** The flags the definition itself carries. */
    readonly flags: readonly CostFlag[]
    /** The unresolved cost contributions. */
    readonly unresolved: readonly UnresolvedCost[]
    /** The observation latencies. */
    readonly latencies: readonly LatencyReport[]
    /** `unanalyzed` when the definition could not be read at all. */
    readonly status: "analyzed" | "unanalyzed"
    /** The unanalyzability reason (when `status` is `unanalyzed`). */
    readonly unanalyzedReason?: string
}

/**
 * The per-registry memo of op summaries: each `CheckedOpSig` analyzed once,
 * in Ω declaration order (the stratification order — an op's definition
 * references only earlier ops, so their summaries are already computed and
 * the analysis is well-founded by the same stratification that guarantees
 * termination).
 */
export class OpSummaryStore {
    private readonly byRegistry = new WeakMap<OpRegistry, Map<string, OpCostSummary>>()

    constructor(private readonly registry: TypeRegistry) {}

    summaryOf(omega: OpRegistry, op: CheckedOpSig): OpCostSummary {
        let memo = this.byRegistry.get(omega)
        if (memo === undefined) {
            memo = new Map()
            this.byRegistry.set(omega, memo)
        }
        const cached = memo.get(op.name)
        if (cached !== undefined) return cached
        // Cycle guard (defensive — Ω's acyclicity makes this unreachable): a
        // re-entrant request serves an opaque placeholder, never diverges.
        memo.set(op.name, unanalyzedSummary(op, "cyclic summary request"))
        const computed = computeOpSummary(omega, op, this.registry, this)
        memo.set(op.name, computed)
        return computed
    }
}

/** The `unanalyzed` summary shape (an honest residual, never a crash). */
function unanalyzedSummary(op: CheckedOpSig, reason: string): OpCostSummary {
    return {
        op,
        cost: SizeExpr.opaque("unanalyzed"),
        depth: SizeExpr.opaque("unanalyzed"),
        resultSize: SizeExpr.opaque("unanalyzed"),
        growth: "unbounded",
        recurrence: undefined,
        edges: [],
        flags: [],
        unresolved: [],
        latencies: [],
        status: "unanalyzed",
        unanalyzedReason: reason,
    }
}

/**
 * Compute one op's summary: analyze the definition source under an
 * environment binding the parameters to their size variables (named `p0`…
 * `p(n−1)` — the instantiation contract), with function-typed parameters
 * opaque. A definition the engine cannot read (an empty or ambiguous parse)
 * yields an `unanalyzed` summary — the cost pass never blocks a program.
 */
function computeOpSummary(
    omega: OpRegistry,
    op: CheckedOpSig,
    registry: TypeRegistry,
    store: OpSummaryStore,
): OpCostSummary {
    const engine = new CostEngine(registry, omega, store)
    let env = CostEnv.empty()
    op.paramTypes.forEach((paramType, i) => {
        env = env.extend(`p${i}`, denotationFor(`p${i}`, paramType))
    })
    const summary = engine.analyze(op.definition, env)
    if (summary === undefined) {
        return unanalyzedSummary(op, "the definition does not parse as LC source")
    }
    // Peel the definition's lambda chain: the summary is the FULLY-APPLIED
    // body's summary in terms of the parameters' size variables (`p0`…) —
    // not the outer closure's O(1) production. The chain's binders ARE the
    // parameters in order (the well-formedness check pins a definition to
    // the lambda chain over the declared parameters). The source's binder
    // names are local (the fixture's `\x. \y. …`); the summary is renamed to
    // the instantiation contract's (`p0…p(n−1)`) — what callers substitute.
    const chain = summary.bodyChain
    if (chain !== undefined) {
        let cost = chain.cost
        let depth = chain.bodyDepth
        let resultSize = chain.resultSize
        chain.params.forEach((binder, i) => {
            const paramName = `p${i}`
            cost = cost.substitute(binder, SizeExpr.variable(paramName))
            depth = depth.substitute(binder, SizeExpr.variable(paramName))
            resultSize = resultSize.substitute(binder, SizeExpr.variable(paramName))
        })
        const report = reportOf(
            {
                ...summary,
                cost,
                depth,
                resultSize,
                provenance: chain.provenance,
                resultKind: chain.resultKind,
            },
            op.name,
            summary.recurrence,
        )
        return {
            op,
            cost,
            depth: depth.toSize(),
            resultSize,
            growth: report.growth,
            recurrence: report.recurrence,
            edges: summary.edges,
            flags: report.flags,
            unresolved: summary.unresolved,
            latencies: summary.latencies,
            status: "analyzed",
        }
    }
    const { cost, depth, resultSize, provenance, resultKind, recurrence } = summary
    const report = reportOf(
        { ...summary, cost, depth, resultSize, provenance, resultKind },
        op.name,
        recurrence,
    )
    return {
        op,
        cost,
        depth: depth.toSize(),
        resultSize,
        growth: report.growth,
        recurrence: report.recurrence,
        edges: summary.edges,
        flags: report.flags,
        unresolved: summary.unresolved,
        latencies: summary.latencies,
        status: "analyzed",
    }
}

/**
 * Instantiate an op's summary at the actual argument summaries: the
 * parameters' size variables (`p0`…) become the arguments' size expressions,
 * the result's provenance names the op (the named form survives — the edge
 * statement's subject), and the definition's records ride along.
 *
 * The ARGUMENTS are part of the application's work too (E-OpArg evaluates
 * them eagerly, leftmost): their construction costs and records compose
 * with the instantiated callee summary — the callee's cost already reads
 * the arguments' sizes (the instantiation contract), but it does not
 * include the arguments' own construction. The result size/provenance stay
 * the callee's (the composition's last value), per the instantiation
 * contract.
 */
function instantiateOpSummary(
    op: CheckedOpSig,
    summary: OpCostSummary,
    args: CostSummary[],
): CostSummary {
    const base = args.reduce(summaryPlus, emptySummary())
    if (summary.status === "unanalyzed") {
        return {
            ...base,
            provenance: { kind: "op", name: op.name },
            resultKind: "unknown",
        }
    }
    let cost = summary.cost
    let depth: SizeExpr = summary.depth
    let resultSize = summary.resultSize
    op.paramTypes.forEach((_paramType, i) => {
        const arg = args[i]
        if (arg === undefined) return
        const paramName = `p${i}`
        cost = cost.substitute(paramName, arg.resultSize)
        depth = depth.substitute(paramName, arg.resultSize)
        resultSize = resultSize.substitute(paramName, arg.resultSize)
    })
    return {
        // The eager arguments compose in (their construction costs, edges,
        // latencies); the RESULT fields stay the callee's — the call's
        // outcome is what the callee produces, not the last argument's.
        cost: base.cost.plus(cost),
        depth: DepthExpr.of(depth).max(base.depth),
        resultSize,
        provenance: { kind: "op", name: op.name },
        resultKind: resultSize.isOpaque ? "unknown" : "data",
        edges: [...base.edges, ...summary.edges],
        unresolved: [...base.unresolved, ...summary.unresolved],
        latencies: [...base.latencies, ...summary.latencies],
    }
}

// ── The public entries ────────────────────────────────────────────────────────

/**
 * The module-level store cache, keyed by `(TypeRegistry, OpRegistry)`
 * identity: repeated public-entry calls on the same (registry, Ω) pair
 * share one `OpSummaryStore` — the memo survives across calls instead of
 * restarting per call. `WeakMap` throughout: a registry pair that falls
 * out of scope releases its summaries with it.
 */
const sharedStores = new WeakMap<TypeRegistry, WeakMap<OpRegistry, OpSummaryStore>>()

/** The shared store for a (registry, Ω) pair (created on first use). */
function sharedStore(registry: TypeRegistry, omega: OpRegistry): OpSummaryStore {
    let byOmega = sharedStores.get(registry)
    if (byOmega === undefined) {
        byOmega = new WeakMap()
        sharedStores.set(registry, byOmega)
    }
    let store = byOmega.get(omega)
    if (store === undefined) {
        store = new OpSummaryStore(registry)
        byOmega.set(omega, store)
    }
    return store
}

/**
 * Analyze one operation's definition: its cost/depth/result-size summary in
 * terms of the parameters' size variables (`p0`…), the feedback edges, and
 * the flags. Memoized per `(TypeRegistry, OpRegistry)` pair — the same
 * identity pair shares one module-level store across calls (the
 * stratification order makes the computation well-founded: an op's
 * definition references only earlier ops), so repeated analyses of the same
 * op re-serve the cached summary rather than re-parsing.
 *
 * @returns the op's cost summary (`status: "unanalyzed"` with a reason when
 *          the definition could not be read — never a throw).
 */
export function analyzeOp(
    op: CheckedOpSig,
    registry: TypeRegistry,
    omega: OpRegistry,
): OpCostSummary {
    return sharedStore(registry, omega).summaryOf(omega, op)
}

/**
 * Analyze a batch of operations in Ω declaration order — the stratified
 * computation the analysis is well-founded on. Returns one summary per op,
 * in the given order. The batch shares the (registry, Ω)-keyed store, so
 * `mul`'s analysis re-uses `add`'s cached summary when both are in the
 * batch.
 */
export function analyzeOps(
    ops: readonly CheckedOpSig[],
    registry: TypeRegistry,
    omega: OpRegistry,
): readonly OpCostSummary[] {
    const store = sharedStore(registry, omega)
    return ops.map((op) => store.summaryOf(omega, op))
}

/**
 * Analyze a standalone LC term under a denotation environment. Returns the
 * report, or `undefined` when the term does not parse (the caller decides
 * what an unparseable fragment means — the analysis never throws).
 *
 * The parameters' denotations come from `env` (name ↦ type); the analysis
 * classifies function-typed parameters as opaque (the flag's condition when
 * they reach a size-sensitive position). Op applications resolve through
 * the same (registry, Ω)-shared memo the op analyses use.
 */
export function analyzeTerm(
    source: string,
    registry: TypeRegistry,
    omega: OpRegistry,
    env: ReadonlyMap<string, Type> = new Map(),
): CostReport | undefined {
    const engine = new CostEngine(registry, omega, sharedStore(registry, omega))
    let costEnv = CostEnv.empty()
    for (const [name, type] of env) {
        costEnv = costEnv.extend(name, denotationFor(name, type))
    }
    const summary = engine.analyze(source, costEnv)
    if (summary === undefined) return undefined
    return reportOf(summary, source, undefined)
}

// ── CostPass: the DerivationTree-consuming vehicle (the plan's D2) ────────────

/**
 * The deferred-summary shape the pass's per-production methods return: a
 * thunk over the denotation environment. The parent — which knows the
 * bindings — builds the handler environments and applies the child thunks
 * under them. This is inherited-attribute flow through deferred application:
 * bottom-up evaluation with the environment threaded where it is constructed.
 */
export type DeferredSummary = (env: CostEnv) => CostSummary

/** The pass's shape: every production yields a deferred summary. */
interface CostPassShape {
    [k: string]: DeferredSummary
    expr: DeferredSummary
    atom: DeferredSummary
}

/**
 * `CostPass extends SemanticPass` — the `DerivationTree`-consuming entry the
 * issue mandates. The pass consumes the type checker's derivation trees
 * (`LCTypeCheck.parseToTree`) and composes the memoized op summaries at the
 * tree's `opProd` nodes (never re-reading a definition — the
 * identity-survival payoff: the tree names the op, the summary comes from Ω
 * once).
 *
 * **The division of labor.** The tree supplies STRUCTURE and IDENTITIES
 * (labels, spans, the source, the `opProd` names, the `spanFoldHandler`
 * records); the algebra supplies the semantics. The engine `CostEngine` is
 * the semantic source — the same parse the checker ran, over the same
 * source, threading the same denotation environment. The pass's walk is
 * LOAD-BEARING where the tree's information is unique:
 *
 * - **Op identities.** The walk records every `opProd` name's Ω-resolution
 *   (memoized at the tree's nodes — the identity-survival payoff: the tree
 *   names the op, the summary comes from Ω once).
 * - **Unknown-op residuals.** A tree whose `opProd` names an op the pass's Ω
 *   does not declare (a divergent registry — the tree was derived under a
 *   different Ω) is an honest structural residual: the report states it and
 *   that its work is not counted, never a crash.
 *
 * Because the checker's left-recursive productions duplicate the same term
 * across multiple derivation depths, a raw bottom-up walk would
 * multiply-count shared work — so the subject's SUMMARY comes from the
 * engine's single parse of the same source under the same environment. The
 * two vehicles agree by construction: the engine's productions ARE the
 * grammar's productions.
 *
 * The deferred-summary discipline stays (the pass's production methods are
 * thunks over `CostEnv`) so a handler body's summary depends on what its
 * bindings denote and only the fold — the parent — builds the handler
 * environments. Capture-safe by construction: the environment is threaded
 * where it is constructed, never mutated.
 */
export class CostPass extends SemanticPass<CostPassShape> {
    private readonly engine: CostEngine
    private readonly registry: TypeRegistry
    private readonly omega: OpRegistry
    /** The op names the current walk resolved in Ω (per-report, cleared). */
    private resolvedOps = new Set<string>()
    /** The op names the current walk could NOT resolve (the residuals). */
    private unresolvedOps = new Set<string>()

    constructor(
        registry: TypeRegistry,
        omega: OpRegistry,
        private readonly store: OpSummaryStore = new OpSummaryStore(registry),
    ) {
        super()
        this.registry = registry
        this.omega = omega
        this.engine = new CostEngine(registry, omega, store)
    }

    /**
     * Evaluate the pass over a derivation tree: the report for the term the
     * tree derives.
     *
     * The walk IS load-bearing — it is where the tree's unique information
     * reaches the report:
     *
     * - **Op identities.** The tree's `opProd` nodes name every applied op;
     *   the walk records which names resolved in Ω (the identity-survival
     *   property — the report's provenances name the ops) and which did not
     *   (the structural residual the engine's own parse silently drops — a
     *   name that is not in Ω parses as an application of an unbound
     *   variable, invisible to the algebra). The residuals surface in the
     *   report's `unresolved` records, never a crash.
     *
     * The summary itself is the engine's single parse of the same source
     * under the same denotation environment — the algebra's semantics,
     * immune to the checker's left-recursive derivation duplication (a raw
     * walk would multiply-count shared work).
     */
    evaluateReport(
        tree: DerivationTree,
        env: ReadonlyMap<string, Type> = new Map(),
    ): CostReport | undefined {
        const source = tree.source
        let costEnv = CostEnv.empty()
        for (const [name, type] of env) {
            costEnv = costEnv.extend(name, denotationFor(name, type))
        }
        return this.withSource(source, () => {
            // The memo and the identity sets are per-report: a long-lived
            // pass must not retain the nodes (or the names) of trees it has
            // already walked.
            this.deferMemo.clear()
            this.resolvedOps = new Set()
            this.unresolvedOps = new Set()
            // The walk: the tree's unique information — the op identities
            // (`opProd` records its Ω-resolution as the deferred thunks
            // apply) and the fold-handler structure. The root's deferred
            // summary applies under the CALLER'S environment (`costEnv`):
            // the fallback path's sizes must read the same bindings the
            // engine's parse would have (a free variable's size is its
            // denotation, not a fresh atom).
            const deferred = this.evaluate(tree) as DeferredSummary | undefined
            const walked = deferred !== undefined ? deferred(costEnv) : undefined
            // The semantics: the engine's single parse of the same source
            // under the same environment — the subject's summary, immune to
            // the tree's derivation duplication.
            const summary = this.engine.analyze(source, costEnv)
            if (summary === undefined) {
                // The engine cannot re-derive the semantics — a divergent Ω
                // (the tree's op names are not in the pass's Ω, so the
                // source's tight-paren forms do not parse). The WALK still
                // read the tree: its summary is the honest fallback (the
                // per-node work it composed from the tree's own records).
                if (walked === undefined) return undefined
                const walkedReport = reportOf(walked, source, walked.recurrence)
                return this.withResiduals(walkedReport)
            }
            const report = reportOf(summary, source, summary.recurrence)
            return this.withResiduals(report)
        })
    }

    /** Append the walk's unknown-op residuals to a report (never a crash). */
    private withResiduals(report: CostReport): CostReport {
        if (this.unresolvedOps.size === 0) return report
        return {
            ...report,
            unresolved: [
                ...report.unresolved,
                ...[...this.unresolvedOps].map((name) => ({
                    site: { kind: "op" as const, name },
                    applied: { kind: "unknown" as const },
                    reason: `the tree applies "${name}", which is not declared in Ω ` +
                        `— no cost summary exists for it; its work is not counted`,
                })),
            ],
        }
    }

    // ── Production methods (dispatch by label — the SemanticPass contract) ───

    /**
     * The generic production passthrough: a single child's thunk flows up
     * (the expr/obs/app/typeApp/atom wrapper chain), and a leaf or an
     * unrecognized node summarizes as the identity — the honest zero for a
     * wrapper the algebra reads through.
     */
    protected override defaultHandler(
        node: DerivationNode,
        childResults: readonly DeferredSummary[],
    ): DeferredSummary {
        if (childResults.length === 1) return childResults[0]!
        // Multi-child nodes with readable structure (the checker's appProd
        // wrapper: fn + ws + arg) compose their expr children in order.
        const exprs = node.children.filter((c) => c.label === "exprProd")
        if (exprs.length >= 2) {
            const parts = exprs.map((e) => this.defer(e))
            return (env) => {
                let summary = parts[0]!(env)
                for (let i = 1; i < parts.length; i++) {
                    summary = applySummary(summary, parts[i]!(env), { kind: "unknown" })
                }
                return summary
            }
        }
        return passthroughSummary
    }

    /**
     * atomProd → variantProd: C(tⱼ) — the constructor rule. The variant's
     * name is the `variantName` descendant's value; the args are the
     * `atomProd` descendants (the constructor's own — `variantProd`'s
     * direct atom children).
     */
    protected variantProd(
        node: DerivationNode,
        _children: readonly DeferredSummary[],
    ): DeferredSummary {
        const name = descendantValue<string>(node, "variantName") ?? ""
        const argNodes = directChildren(node, "atomProd")
        const args = argNodes.map((a) => this.defer(a))
        return (env) => {
            const argSummaries = args.map((d) => d(env))
            let summary = emptySummary()
            for (const arg of argSummaries) summary = summaryPlus(summary, arg)
            return {
                ...summary,
                cost: summary.cost.plus(SizeExpr.ONE),
                depth: summary.depth.plus(SizeExpr.ONE),
                resultSize: summary.resultSize.plus(SizeExpr.ONE),
                provenance: { kind: "constructor", name },
                resultKind: "data",
            }
        }
    }

    /** varProd: the variable's denotation from the threaded environment. */
    protected varProd(
        node: DerivationNode,
        _children: readonly DeferredSummary[],
    ): DeferredSummary {
        const name = descendantValue<string>(node, "ident") ?? leafText(node) ?? ""
        return (env) => varSummary(name, env)
    }

    /**
     * lambdaProd: λx:σ. body — the closure (O(1) production; the body's
     * deferred chain rides along for the application sites).
     */
    protected lambdaProd(
        node: DerivationNode,
        children: readonly DeferredSummary[],
    ): DeferredSummary {
        void children
        const binderNode = directChildren(node, "ident")[0]
        const binder = (binderNode?.value as string) ?? leafText(binderNode) ?? "_"
        const bodyNodes = directChildren(node, "exprProd")
        const body = bodyNodes.length === 1 ? this.defer(bodyNodes[0]!) : passthroughSummary
        return (env) => closureSummary(binder, body(env))
    }

    /**
     * opProd: op(tⱼ) — the callee's MEMOIZED summary instantiated at the
     * arguments' sizes (the identity-survival payoff: the tree names the
     * op, the summary comes from Ω once).
     */
    protected opProd(node: DerivationNode, _children: readonly DeferredSummary[]): DeferredSummary {
        const nameNode = directChildren(node, "ident")[0]
        if (nameNode === undefined) {
            // The wrapper form (the checker's appProd recomposition): a
            // single exprProd child flows through — the arg-bearing opProd
            // deeper in the chain carries the op semantics.
            const inner = directChildren(node, "exprProd")[0]
            return inner === undefined ? passthroughSummary : this.defer(inner)
        }
        const name = (nameNode?.value as string) ?? leafText(nameNode) ??
            this.nodeSourceSlice(node) ?? ""
        const argNodes = directChildren(node, "atomProd")
        const args = argNodes.map((a) => this.defer(a))
        return (env) => {
            const op = this.omega.lookup(name)
            if (op === undefined) {
                // The structural residual: the tree names an op Ω does not
                // declare — recorded (the report states it), never a crash.
                this.unresolvedOps.add(name)
                return args.reduce<CostSummary>(
                    (sum, d) => summaryPlus(sum, d(env)),
                    emptySummary(),
                )
            }
            this.resolvedOps.add(name)
            const argSummaries = args.map((d) => d(env))
            const opSummary = this.store.summaryOf(this.omega, op)
            return instantiateOpSummary(op, opSummary, argSummaries)
        }
    }

    /**
     * letProd: let x:σ = t in u — the definition's cost + the body's cost
     * under the binding (the body's thunk applied to the extended env —
     * the binding denotes the definition's result).
     */
    protected letProd(
        node: DerivationNode,
        _children: readonly DeferredSummary[],
    ): DeferredSummary {
        const binderNode = directChildren(node, "ident")[0]
        const binder = (binderNode?.value as string) ?? leafText(binderNode) ?? "_"
        const defNodes = directChildren(node, "exprProd")
        if (defNodes.length < 2) return passthroughSummary
        const def = this.defer(defNodes[0]!)
        const body = this.defer(defNodes[defNodes.length - 1]!)
        return (env) => {
            const defSummary = def(env)
            const binderDenotation: Denotation = {
                type: undefined,
                kind: defSummary.resultKind,
                size: defSummary.resultSize,
                provenance: defSummary.provenance,
            }
            const bodySummary = body(env.extend(binder, binderDenotation))
            return summaryPlus(defSummary, bodySummary)
        }
    }

    /**
     * obsProd: e.o — the observation: the seed's cost + the generator
     * latency (the codata dual). A dotted observation carries the
     * observer's name as a DIRECT ident child; a zero-observation wrapper
     * has only the subject chain.
     */
    protected obsProd(
        node: DerivationNode,
        _children: readonly DeferredSummary[],
    ): DeferredSummary {
        const nameNode = directChildren(node, "ident")[0]
        if (nameNode === undefined) {
            const inner = directChildren(node, "obsProd")[0] ??
                directChildren(node, "appProd")[0] ??
                directChildren(node, "exprProd")[0]
            return inner === undefined ? passthroughSummary : this.defer(inner)
        }
        const name = (nameNode.value as string) ?? leafText(nameNode) ?? ""
        const inner = directChildren(node, "obsProd")[0] ?? firstExprChild(node)
        const subject = inner === undefined ? undefined : this.defer(inner)
        return (env) => {
            const seed = subject === undefined ? emptySummary() : subject(env)
            return obsSummary(seed, name)
        }
    }

    /**
     * spanFoldHandler: the checker's handler record (variant name, binding
     * names, body span) — the fold structure's source when the tree keeps
     * it. The record summarizes as the identity; the fold's assembly
     * consumes the values.
     */
    protected spanFoldHandler(
        node: DerivationNode,
        _children: readonly DeferredSummary[],
    ): DeferredSummary {
        void node
        return passthroughSummary
    }

    /**
     * foldProd: the fold's assembly from the tree's records: the carrier
     * (the typeProd descendant's value), the scrutinee (the first expr
     * child), the handler records (variantName/bindings/bodySpan). Bodies
     * re-read from their spans through the shared engine under the handler
     * environments — the same denotation rule the engine's own fold builds
     * (non-recursive fields raw; recursive fields the fold-recursion
     * denotation). When the tree did not keep the records (a fragmented
     * forest), the node's own source span re-reads through the engine — the
     * fallback that keeps the report the algebra's.
     */
    protected foldProd(
        node: DerivationNode,
        children: readonly DeferredSummary[],
    ): DeferredSummary {
        const carrierNode = collectDescendants(node, "typeProd")[0]
        const carrier = carrierNode?.value
        const scrutineeNode = firstExprChild(node)
        const scrutinee = scrutineeNode === undefined ? undefined : this.defer(scrutineeNode)
        const childFlow = children.length === 1 ? children[0]! : undefined
        return (env) => {
            const carrierName = carrier instanceof DataType
                ? carrier.name
                : carrier instanceof Type
                ? dataTypeNameOfType(carrier)
                : undefined
            const dataType = carrierName === undefined
                ? undefined
                : this.registry.lookup(carrierName)
            const scrutineeSummary = scrutinee === undefined ? emptySummary() : scrutinee(env)
            if (!(dataType instanceof DataType)) {
                return childFlow === undefined ? scrutineeSummary : childFlow(env)
            }
            const records = collectDescendants(node, "spanFoldHandler")
                .map((h) => h.value as SpanFoldRecord | undefined)
                .filter((r): r is SpanFoldRecord => r !== undefined)
            if (records.length === 0) {
                // No records on this tree: re-read the fold's span through
                // the engine (the honest structure source).
                const slice = this.nodeSourceSlice(node)
                return slice === undefined
                    ? scrutineeSummary
                    : this.engine.analyze(slice, env) ?? scrutineeSummary
            }
            const handlers = records.map((r) => ({
                variantName: r.variantName,
                bindings: r.bindings,
                body: this.engine.analyze(
                    this.engineSource().slice(r.bodySpan.start, r.bodySpan.end),
                    this.handlerEnv(dataType, r, env),
                ) ?? emptySummary(),
            }))
            return foldSummaryFrom(dataType, scrutineeSummary, handlers)
        }
    }

    // ── Tree-reading helpers ──────────────────────────────────────────────

    /** The source text the pass reads spans against (the engine's input). */
    private sourceText: string | undefined

    /** The per-node defer memo (the shared-structure guard). */
    private readonly deferMemo = new Map<DerivationNode, DeferredSummary>()

    /** Bind the source text (called by `evaluateReport's wrapper). */
    private withSource<T>(source: string | undefined, f: () => T): T {
        const saved = this.sourceText
        this.sourceText = source
        try {
            return f()
        } finally {
            this.sourceText = saved
        }
    }

    private engineSource(): string {
        return this.sourceText ?? ""
    }

    /** The node's source slice against the bound source text. */
    private nodeSourceSlice(node: DerivationNode): string | undefined {
        if (this.sourceText === undefined) return undefined
        return this.sourceText.slice(node.span.start, node.span.end)
    }

    /**
     * Defer one node's evaluation: dispatch through the pass's own methods
     * (the same contract `evaluate` applies — the pass re-enters its
     * dispatch for fragments the parents need directly). Memoized per node:
     * the checker's left-recursion duplicates subtrees across production
     * chains, and one deferred summary per node keeps the walk linear.
     */
    private defer(node: DerivationNode): DeferredSummary {
        const memoized = this.deferMemo.get(node)
        if (memoized !== undefined) return memoized
        const childResults = node.children.map((c) => this.defer(c))
        const fn = (this as unknown as Record<string, unknown>)[node.label]
        const deferred = typeof fn === "function"
            ? (fn as (n: DerivationNode, c: readonly DeferredSummary[]) => DeferredSummary)
                .call(this, node, childResults)
            : childResults.length === 1
            ? childResults[0]!
            : passthroughSummary
        this.deferMemo.set(node, deferred)
        return deferred
    }

    /**
     * The handler environment for one handler record: non-recursive fields
     * bound to their declared types' denotations (the raw field sizes),
     * Family fields bound to the fold-recursion denotation (the μ-bound's
     * named producer end). The same rule the engine's
     * `foldFieldType` + `extendCtx` pair applies.
     */
    private handlerEnv(dataType: DataType, record: SpanFoldRecord, outer: CostEnv): CostEnv {
        let env = outer
        const variant = dataType.findVariant(record.variantName)
        if (variant === undefined) return env
        record.bindings.forEach((binding, i) => {
            const field = variant.fields[i]
            if (field === undefined) return
            env = field.type instanceof FamilyType
                ? env.extend(binding, foldRecDenotation(dataType.name, binding))
                : env.extend(binding, denotationFor(binding, field.type))
        })
        return env
    }
}

/** The checker's `spanFoldHandler` record shape. */
interface SpanFoldRecord {
    readonly variantName: string
    readonly bindings: string[]
    readonly bodySpan: { start: number; end: number }
}

/** The pass's identity summary (no work, no records). */
function passthroughSummary(_env: CostEnv): CostSummary {
    return emptySummary()
}

/** The variable's summary: its denotation, or an honest free-variable size. */
function varSummary(name: string, env: CostEnv): CostSummary {
    const d = env.lookup(name)
    if (d === undefined) {
        return {
            cost: SizeExpr.ZERO,
            depth: DepthExpr.ZERO,
            resultSize: SizeExpr.variable(name),
            provenance: { kind: "param", name },
            resultKind: "unknown",
            edges: [],
            unresolved: [],
            latencies: [],
        }
    }
    return {
        cost: SizeExpr.ZERO,
        depth: DepthExpr.ZERO,
        resultSize: d.size,
        provenance: d.provenance,
        resultKind: d.kind,
        edges: [],
        unresolved: [],
        latencies: [],
    }
}

/** The observation's summary (the codata dual — the seed's cost + latency). */
function obsSummary(seed: CostSummary, observerName: string): CostSummary {
    const seedLatency = SizeExpr.variable(`latency(${observerName})`)
    return {
        cost: seed.cost.plus(seedLatency),
        depth: seed.depth.plus(seedLatency),
        resultSize: SizeExpr.variable(`obs(${observerName})`),
        provenance: { kind: "unknown" },
        resultKind: "unknown",
        edges: [
            ...seed.edges,
            {
                producer: seed.provenance,
                consumer: { kind: "unknown" },
                position: "observation generator",
                consumerSite: observerName,
                bound: seed.resultSize.isOpaque ? undefined : seed.resultSize,
                isFlagged: seed.resultSize.isOpaque,
            },
        ],
        unresolved: seed.unresolved,
        latencies: [
            ...seed.latencies,
            { observer: observerName, latency: seedLatency },
        ],
    }
}

/**
 * The fold's summary from assembled parts (the tree's structure + the
 * engine's handler analyses) — the same algebra the engine's own fold
 * action computes: the scrutinee edge, the per-handler recursion
 * substitution, the recurrence solve.
 */
function foldSummaryFrom(
    dataType: DataType,
    scrutinee: CostSummary,
    handlers: { variantName: string; bindings: string[]; body: CostSummary }[],
): CostSummary {
    const edges: CostEdge[] = [...scrutinee.edges]
    const unresolved: UnresolvedCost[] = [...scrutinee.unresolved]
    const latencies: LatencyReport[] = [...scrutinee.latencies]
    for (const handler of handlers) {
        edges.push(...handler.body.edges)
        unresolved.push(...handler.body.unresolved)
        latencies.push(...handler.body.latencies)
    }
    edges.push({
        producer: scrutinee.provenance,
        consumer: { kind: "fold", name: dataType.name },
        position: "fold scrutinee",
        consumerSite: `fold [${dataType.name}]`,
        bound: scrutinee.resultSize.isOpaque ? undefined : scrutinee.resultSize,
        isFlagged: scrutinee.resultSize.isOpaque,
    })
    const RECURSION = "#foldRec"
    const perHandler = handlers.map((handler) => {
        const variant = dataType.findVariant(handler.variantName)
        let bodyCost = handler.body.cost
        let bodySize = handler.body.resultSize
        let bodyDepth = handler.body.depth
        if (variant !== undefined) {
            variant.fields.forEach((field: Field, i: number) => {
                const binding = handler.bindings[i]
                if (binding === undefined) return
                if (field.type instanceof FamilyType) {
                    const recResult = SizeExpr.variable(RECURSION)
                    bodyCost = bodyCost.substitute(binding, recResult)
                    bodySize = bodySize.substitute(binding, recResult)
                    bodyDepth = bodyDepth.substitute(binding, recResult)
                }
            })
        }
        return {
            variantName: handler.variantName,
            cost: bodyCost,
            size: bodySize,
            depth: bodyDepth,
        }
    })
    let perNodeWork = SizeExpr.ZERO
    let perNodeDepth = DepthExpr.ZERO
    for (const h of perHandler) {
        perNodeWork = perNodeWork.plus(h.cost)
        perNodeDepth = perNodeDepth.max(h.depth)
    }
    const allVariants = dataType.allVariants()
    const recursiveVariants = allVariants.filter((v) =>
        v.fields.some((f) => f.type instanceof FamilyType)
    )
    let resultSize: SizeExpr
    let recurrence: string | undefined
    const isChain = recursiveVariants.length === 1 &&
        recursiveVariants[0]!.fields.filter((f) => f.type instanceof FamilyType).length === 1
    if (isChain) {
        const recVariant = recursiveVariants[0]!
        const baseVariants = allVariants.filter(
            (v) => !v.fields.some((f) => f.type instanceof FamilyType),
        )
        const baseSize = baseVariants.reduce<SizeExpr>((sum, v) => {
            const h = perHandler.find((ph) => ph.variantName === v.name)
            return sum.plus(h ? h.size : SizeExpr.ZERO)
        }, SizeExpr.ZERO)
        const stepHandler = perHandler.find((ph) => ph.variantName === recVariant.name)
        const stepSize = stepHandler ? stepHandler.size : SizeExpr.ZERO
        // The recurrence's input is the scrutinee's FULL size expression —
        // the invocation count is the input's node count, whatever variables
        // name it. An opaque scrutinee names itself honestly (the shared
        // conservative fallback).
        const inputSize = scrutinee.resultSize.isOpaque
            ? SizeExpr.variable("#scrutinee")
            : scrutinee.resultSize
        const solved = solveChainRecurrence(baseSize, stepSize, RECURSION, inputSize)
        resultSize = solved.closed ?? SizeExpr.opaque("super-affine structural growth")
        recurrence = solved.recurrence
    } else {
        resultSize = SizeExpr.variable(RECURSION)
    }
    const isLiteral = scrutinee.provenance.kind === "constructor"
    const invocations = isLiteral
        ? scrutinee.resultSize
        : scrutinee.resultSize.isOpaque
        ? SizeExpr.variable("#scrutinee")
        : scrutinee.resultSize
    const foldCost = invocations.times(perNodeWork)
    const foldDepth = scrutinee.depth.plus(invocations).max(perNodeDepth.plus(invocations))
    return {
        cost: scrutinee.cost.plus(foldCost),
        depth: foldDepth,
        resultSize,
        recurrence,
        provenance: { kind: "fold", name: dataType.name },
        resultKind: resultSize.isOpaque ? "unknown" : "data",
        edges,
        unresolved,
        latencies,
    }
}

// ── Tree-reading utilities ────────────────────────────────────────────────

/** The node's direct children with the given label. */
function directChildren(node: DerivationNode, label: string): DerivationNode[] {
    return node.children.filter((c) => c.label === label)
}

/**
 * The first expr/obs child of the node (the subject/scrutinee slot).
 */
function firstExprChild(node: DerivationNode): DerivationNode | undefined {
    return directChildren(node, "exprProd")[0] ?? directChildren(node, "obsProd")[0]
}

/** The first descendant with the given label (pre-order), with its value. */
function descendantValue<T>(node: DerivationNode, label: string): T | undefined {
    if (node.label === label) return node.value as T
    for (const child of node.children) {
        const found = descendantValue<T>(child, label)
        if (found !== undefined) return found
    }
    return undefined
}

/** All descendants with the given label, in pre-order. */
function collectDescendants(node: DerivationNode, label: string): DerivationNode[] {
    const found: DerivationNode[] = []
    const walk = (n: DerivationNode) => {
        if (n.label === label) found.push(n)
        for (const c of n.children) walk(c)
    }
    walk(node)
    return found
}

/**
 * The leaf text an ident chain carries: the LONGEST ident descendant's
 * value (the chain's final node holds the full lexeme).
 */
function leafText(node: DerivationNode | undefined): string | undefined {
    if (node === undefined) return undefined
    const idents = collectDescendants(node, "ident")
    if (idents.length === 0) return undefined
    let best = ""
    for (const n of idents) {
        const v = n.value
        if (typeof v === "string" && v.length > best.length) best = v
    }
    return best
}

/** The carrier's name from a type value (`undefined` for non-μ types). */
function dataTypeNameOfType(type: Type): string | undefined {
    return type instanceof DataType ? type.name : undefined
}
