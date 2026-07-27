/**
 * LC Terms — the abstract syntax of the Lapis Core Calculus.
 *
 * See _docs/theory/lc.md §2.2 for the formal specification.
 *
 *   t, u ::= x                              variable
 *          | λx:σ. t                        lambda
 *          | t u                            application
 *          | Cᵢ(t₁, ..., tₙ)                named variant construction
 *          | match(pₖ)                      pattern-matched construction
 *          | fold [T] t {Cᵢ(xⱼ) → tᵢ}       fold (catamorphism)
 *          | e.oⱼ                           observation
 *          | unfold [T] t {oⱼ → tⱼ}         unfold (anamorphism)
 *          | cofold [T] t {oⱼ(xⱼ) → t}      cofold (codata elimination)
 *          | Λα <: σ. t                     type abstraction
 *          | t [τ]                          type application
 *          | let x:σ = t in u               let-binding
 */

import type { Type, DataType, CodataType, PatternDataType } from "./types.ts";

// ── Term ──────────────────────────────────────────────────────────────────────

/** The root of the LC term hierarchy. */
export abstract class Term {
    abstract readonly kind: string;
}

// ── Variable ──────────────────────────────────────────────────────────────────

/** `x` — a variable reference. */
export class Var extends Term {
    readonly kind = "var";
    constructor(readonly name: string) { super(); }
}

// ── Lambda ────────────────────────────────────────────────────────────────────

/** `λx:σ. t` — lambda abstraction with type annotation. */
export class Lam extends Term {
    readonly kind = "lam";
    constructor(
        readonly param: string,
        readonly paramType: Type,
        readonly body: Term,
    ) { super(); }
}

// ── Application ───────────────────────────────────────────────────────────────

/** `t u` — function application. */
export class App extends Term {
    readonly kind = "app";
    constructor(
        readonly fn: Term,
        readonly arg: Term,
    ) { super(); }
}

// ── Variant construction ──────────────────────────────────────────────────────

/** `Cᵢ(t₁, ..., tₙ)` — named variant construction (data introduction). */
export class VariantCon extends Term {
    readonly kind = "variantCon";
    constructor(
        readonly variantName: string,
        readonly dataType: DataType,
        readonly args: Term[],
    ) { super(); }
}

// ── Pattern-matched construction ──────────────────────────────────────────────

/** `match(pₖ)` — pattern-matched construction (data introduction via lexer). */
export class PatternMatch extends Term {
    readonly kind = "patternMatch";
    constructor(
        readonly patternIndex: number,
        readonly dataType: PatternDataType,
        readonly token: string,
    ) { super(); }
}

// ── Fold handler ──────────────────────────────────────────────────────────────

/** A handler in a fold: `Cᵢ(xⱼ) → tᵢ`. Binds field names to (folded) values. */
export class FoldHandler {
    constructor(
        readonly variantName: string,
        readonly fieldBindings: string[],
        readonly body: Term,
    ) {}
}

/** A handler in a pattern-matched fold: `pᵢ → tᵢ`. Binds the `match` token. */
export class PatternHandler {
    constructor(
        readonly patternIndex: number,
        readonly body: Term,
    ) {}
}

// ── Fold (catamorphism) ───────────────────────────────────────────────────────

/** `fold [T] t {Cᵢ(xⱼ) → tᵢ}` — fold over data (data elimination). */
export class Fold extends Term {
    readonly kind = "fold";
    constructor(
        readonly dataType: DataType,
        readonly scrutinee: Term,
        readonly handlers: FoldHandler[],
        readonly resultType: Type,
    ) { super(); }

    /** Find a handler by variant name. */
    findHandler(variantName: string): FoldHandler | undefined {
        return this.handlers.find((h) => h.variantName === variantName);
    }
}

// ── Pattern-matched fold ──────────────────────────────────────────────────────

/** `fold [T] e {pᵢ → tᵢ}` — fold over pattern-matched data. */
export class PatternFold extends Term {
    readonly kind = "patternFold";
    constructor(
        readonly dataType: PatternDataType,
        readonly scrutinee: Term,
        readonly handlers: PatternHandler[],
        readonly resultType: Type,
    ) { super(); }
}

// ── Observation ───────────────────────────────────────────────────────────────

/** `e.oⱼ` — observation (codata elimination). */
export class Obs extends Term {
    readonly kind = "obs";
    constructor(
        readonly scrutinee: Term,
        readonly observerName: string,
        readonly codataType: CodataType,
    ) { super(); }
}

// ── Unfold generator ──────────────────────────────────────────────────────────

/** A generator in an unfold: `oⱼ → gⱼ`. Produces the value for observer oⱼ. */
export class UnfoldGenerator {
    constructor(
        readonly observerName: string,
        readonly body: Term,
    ) {}
}

// ── Unfold (anamorphism) ──────────────────────────────────────────────────────

/** `unfold [T] s {oⱼ → gⱼ}` — unfold from seed into codata (codata introduction). */
export class Unfold extends Term {
    readonly kind = "unfold";
    constructor(
        readonly codataType: CodataType,
        readonly seed: Term,
        readonly generators: UnfoldGenerator[],
        readonly seedType: Type,
    ) { super(); }

    /** Find a generator by observer name. */
    findGenerator(observerName: string): UnfoldGenerator | undefined {
        return this.generators.find((g) => g.observerName === observerName);
    }
}

// ── Cofold handler ────────────────────────────────────────────────────────────

/** A handler in a cofold: `oⱼ(xⱼ) → t`. Receives all observations simultaneously. */
export class CofoldHandler {
    constructor(
        readonly observerName: string,
        readonly fieldBindings: string[],
        readonly body: Term,
    ) {}
}

// ── Cofold (codata elimination) ───────────────────────────────────────────────

/** `cofold [T] e {oⱼ(xⱼ) → t}` — cofold over codata (behavior fold). */
export class Cofold extends Term {
    readonly kind = "cofold";
    constructor(
        readonly codataType: CodataType,
        readonly scrutinee: Term,
        readonly handler: CofoldHandler,
        readonly resultType: Type,
    ) { super(); }
}

// ── Type abstraction ──────────────────────────────────────────────────────────

/** `Λα <: σ. t` — bounded type abstraction (F<:). */
export class TypeAbs extends Term {
    readonly kind = "typeAbs";
    constructor(
        readonly typeVarName: string,
        readonly bound: Type,
        readonly body: Term,
    ) { super(); }
}

// ── Type application ──────────────────────────────────────────────────────────

/** `t [τ]` — type application. */
export class TypeApp extends Term {
    readonly kind = "typeApp";
    constructor(
        readonly body: Term,
        readonly argType: Type,
    ) { super(); }
}

// ── Let binding ───────────────────────────────────────────────────────────────

/** `let x:σ = t in u` — let-binding. */
export class Let extends Term {
    readonly kind = "let";
    constructor(
        readonly name: string,
        readonly type: Type,
        readonly value: Term,
        readonly body: Term,
    ) { super(); }
}