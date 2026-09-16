/**
 * LC Values — the value forms of the Lapis Core Calculus.
 *
 * See _docs/theory/lc.md §2.3 for the formal specification.
 *
 *   v ::= λx:σ. t                           closure
 *       | Cᵢ(v₁, ..., vₙ)                   constructed variant (eager: fields are values)
 *       | match(pₖ)                         matched token (a value of pattern-matched type)
 *       | unfold [T] s {oⱼ → gⱼ}            codata value (lazy: seed stored, generators deferred)
 */

import type { DataType, Type } from "./types.ts"
import type { Span } from "@lapis-lang/lang-forma"

// ── Value ─────────────────────────────────────────────────────────────────────

/** The root of the LC value hierarchy. */
export abstract class Value {
    abstract readonly kind: string
}

// ── SpanClosure ───────────────────────────────────────────────────────────────

/**
 * A closure that captures the body's **input span** (not a pre-evaluated body
 * term). Used by the grammar-based evaluator (`LCEval`): the body is
 * re-evaluated on demand by re-parsing its source substring under the
 * extended environment via `_forward` — the higher-order attribute mechanism.
 *
 * `input` is the source text the span indexes into. For closures captured
 * during the main parse it is the parse input; for closures captured while
 * evaluating an operation definition (E-Op — the definition lives in the
 * `OpRegistry`, not the parse input) it is the definition source. Carrying
 * it on the closure keeps an escaping closure (e.g. an op returning a
 * function) applicable after the definition-evaluation window closes.
 */
export class SpanClosure extends Value {
    readonly kind = "closure"
    constructor(
        readonly param: string,
        readonly paramType: Type,
        readonly bodySpan: Span,
        readonly env: ValueEnv,
        /** The source text that `bodySpan` indexes into. */
        readonly input: string = "",
    ) {
        super()
    }

    /** Alias for `paramType`, for duck-typing compatibility with lang-forma's `inferValueType`. */
    get type(): Type {
        return this.paramType
    }
}

// ── Variant value ─────────────────────────────────────────────────────────────

/**
 * `Cᵢ(v₁, ..., vₙ)` — a constructed variant. Eager: fields are already values.
 */
export class VariantVal extends Value {
    readonly kind = "variantVal"
    constructor(
        readonly variantName: string,
        readonly dataType: DataType,
        readonly fields: Map<string, Value>,
    ) {
        super()
    }
}

// ── Pattern match value ───────────────────────────────────────────────────────

// ── Value environment ─────────────────────────────────────────────────────────

/**
 * The value environment `ρ` — maps names to values.
 * Used during evaluation (the inherited attribute for the evaluator).
 */
export class ValueEnv {
    private readonly bindings: Map<string, Value>

    constructor(entries?: Map<string, Value>) {
        this.bindings = entries ?? new Map()
    }

    lookup(name: string): Value | undefined {
        return this.bindings.get(name)
    }

    extend(name: string, value: Value): ValueEnv {
        const next = new Map(this.bindings)
        next.set(name, value)
        return new ValueEnv(next)
    }

    /** Create a ValueEnv from a raw Map. */
    static from(map: Map<string, Value>): ValueEnv {
        return new ValueEnv(map)
    }

    /** Export to a raw Map. */
    toMap(): Map<string, Value> {
        return new Map(this.bindings)
    }
}

// ── Structural value equality ─────────────────────────────────────────────────

/**
 * Structural equality on data values — the runtime `=` primitive's equality
 * on data (semantics.md §7): two values are equal when they have the same
 * constructor and equal fields, recursively.
 *
 * Scope (first cut): finite data values — `VariantVal` trees. Function
 * values (closures) and codata values have no structural equality:
 * closures are code, codata equality is bisimulation, and both are outside
 * the first cut — comparing a value containing one returns `false` unless
 * it is literally the same reference (identical closures ARE equal, which
 * keeps `idempotent` on a closure-valued argument well-defined at the
 * reference level). Law screening (law_checking.ts) restricts itself to
 * operations whose parameter types are data types, so its comparisons
 * observe only the `VariantVal` part.
 */
export function valueEquals(a: Value, b: Value): boolean {
    if (a === b) return true

    if (a instanceof VariantVal && b instanceof VariantVal) {
        return a.variantName === b.variantName &&
            a.dataType.name === b.dataType.name &&
            fieldsEqual(a.fields, b.fields)
    }
    return false
}

/** Field-wise structural equality on a variant's fields (same key sets). */
function fieldsEqual(a: Map<string, Value>, b: Map<string, Value>): boolean {
    if (a.size !== b.size) return false
    for (const [name, value] of a) {
        const other = b.get(name)
        if (other === undefined || !valueEquals(value, other)) return false
    }
    return true
}
