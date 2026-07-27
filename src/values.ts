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

import type { Type, DataType, CodataType, PatternDataType } from "./types.ts";
import type { Term, UnfoldGenerator } from "./terms.ts";

// ── Value ─────────────────────────────────────────────────────────────────────

/** The root of the LC value hierarchy. */
export abstract class Value {
    abstract readonly kind: string;
}

// ── Closure ───────────────────────────────────────────────────────────────────

/**
 * `λx:σ. t` — a closure: the unevaluated body, the parameter name, the
 * parameter type, and the environment captured at abstraction time.
 */
export class Closure extends Value {
    readonly kind = "closure";
    constructor(
        readonly param: string,
        readonly paramType: Type,
        readonly body: Term,
        readonly env: Map<string, Value>,
    ) { super(); }
}

// ── Variant value ─────────────────────────────────────────────────────────────

/**
 * `Cᵢ(v₁, ..., vₙ)` — a constructed variant. Eager: fields are already values.
 */
export class VariantVal extends Value {
    readonly kind = "variantVal";
    constructor(
        readonly variantName: string,
        readonly dataType: DataType,
        readonly fields: Map<string, Value>,
    ) { super(); }
}

// ── Pattern match value ───────────────────────────────────────────────────────

/** `match(pₖ)` — a matched token. A value of a pattern-matched data type. */
export class MatchVal extends Value {
    readonly kind = "matchVal";
    constructor(
        readonly patternIndex: number,
        readonly dataType: PatternDataType,
        readonly token: string,
    ) { super(); }
}

// ── Codata value ──────────────────────────────────────────────────────────────

/**
 * `unfold [T] s {oⱼ → gⱼ}` — a codata value. Lazy: the seed is stored,
 * generators are deferred until observation.
 */
export class CodataVal extends Value {
    readonly kind = "codataVal";
    constructor(
        readonly codataType: CodataType,
        readonly seed: Value,
        readonly generators: UnfoldGenerator[],
        readonly env: Map<string, Value>,
    ) { super(); }
}

// ── Value environment ─────────────────────────────────────────────────────────

/**
 * The value environment `ρ` — maps names to values.
 * Used during evaluation (the inherited attribute for the evaluator).
 */
export class ValueEnv {
    private readonly bindings: Map<string, Value>;

    constructor(entries?: Map<string, Value>) {
        this.bindings = entries ?? new Map();
    }

    lookup(name: string): Value | undefined {
        return this.bindings.get(name);
    }

    extend(name: string, value: Value): ValueEnv {
        const next = new Map(this.bindings);
        next.set(name, value);
        return new ValueEnv(next);
    }

    /** Create a ValueEnv from a raw Map (e.g. from a Closure's captured env). */
    static from(map: Map<string, Value>): ValueEnv {
        return new ValueEnv(map);
    }

    /** Export to a raw Map (e.g. for creating a Closure). */
    toMap(): Map<string, Value> {
        return new Map(this.bindings);
    }
}

// ── IsValue check ─────────────────────────────────────────────────────────────

/** Check if a term is a value (i.e., fully evaluated). */
export function isValue(term: Term): boolean {
    // Values are: closures, variant constructions with value args,
    // pattern matches, and unfolds. But at the term level, we check
    // if the term is already a Value (i.e., evaluation has produced it).
    // This is used by the Progress check.
    return false; // Terms are not values; values are produced by evaluation.
    // The actual isValue check operates on the result of evaluation,
    // not on terms. See eval.ts for the evaluation that produces values.
}

/** Check if a Value is fully evaluated (all values are fully evaluated by construction). */
export function isFullyEvaluated(value: Value): boolean {
    return value instanceof Closure
        || value instanceof VariantVal
        || value instanceof MatchVal
        || value instanceof CodataVal;
}