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
 */
export class SpanClosure extends Value {
    readonly kind = "closure"
    constructor(
        readonly param: string,
        readonly paramType: Type,
        readonly bodySpan: Span,
        readonly env: ValueEnv,
    ) {
        super()
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
