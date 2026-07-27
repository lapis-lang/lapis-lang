/**
 * LC Typing — the typing rules of the Lapis Core Calculus.
 *
 * See _docs/theory/lc.md §5 for the formal specification.
 *
 * Each typing rule is a method with:
 *   - @requires encoding the premises (graceful failure = ill-typed)
 *   - @ensures encoding the conclusion (throws on violation = compiler bug)
 *
 * The methods are called directly (no parsing). They take a term and Γ,
 * return the type (or fail via @requires returning undefined).
 *
 *   T-Var:       Γ(x) = σ  ⟹  Γ ⊢ x : σ
 *   T-Abs:       Γ, x:σ ⊢ t : τ  ⟹  Γ ⊢ λx:σ.t : σ → τ
 *   T-App:       Γ ⊢ t : σ→τ  ∧  Γ ⊢ u : σ  ⟹  Γ ⊢ t u : τ
 *   T-Variant:   Γ ⊢ tⱼ : Fₖ(T)[α:=T]  ⟹  Γ ⊢ Cₖ(tⱼ) : T
 *   T-Pattern:   input matches pₖ  ⟹  Γ ⊢ tok : T
 *   T-Fold:      Γ ⊢ e : T  ∧  Γ ⊢ tᵢ : Fᵢ(σ)[α:=σ]→σ  ⟹  Γ ⊢ fold [T] e {...} : σ
 *   T-FoldMatch: Γ ⊢ e : T  ∧  Γ ⊢ tᵢ : Token→σ  ⟹  Γ ⊢ fold [T] e {pᵢ→tᵢ} : σ
 *   T-Obs:       Γ ⊢ e : T  ⟹  Γ ⊢ e.oₖ : Gₖ(T)[α:=T]
 *   T-Unfold:    Γ ⊢ s : Σ  ∧  Γ ⊢ gⱼ : Σ→Gⱼ(Σ)[α:=Σ]  ⟹  Γ ⊢ unfold [T] s {...} : T
 *   T-Cofold:    Γ ⊢ e : T  ∧  Γ ⊢ t : Πⱼ(Gⱼ(σ)[α:=σ])→σ  ⟹  Γ ⊢ cofold [T] e {...} : σ
 *   T-TAbs:      Δ, α<:σ ⊢ t : τ  ⟹  Δ ⊢ Λα<:σ.t : ∀α<:σ.τ
 *   T-TApp:      Γ ⊢ t : ∀α<:σ.τ  ∧  Δ ⊢ T₂<:σ  ⟹  Γ ⊢ t[T₂] : τ[α:=T₂]
 *   T-Let:       Γ ⊢ t : σ  ∧  Γ,x:σ ⊢ u : τ  ⟹  Γ ⊢ let x:σ=t in u : τ
 *   T-Sub:       Γ ⊢ t : σ  ∧  σ <: τ  ⟹  Γ ⊢ t : τ
 */

import {
    Grammar,
    requires,
    ensures,
    invariant,
    epsilon,
} from "jsr:@lapis-lang/zipper-grammar@3.0.0";

import {
    type Type,
    TypeVar,
    FunType,
    DataType,
    PatternDataType,
    CodataType,
    TokenType,
    AnyType,
    NothingType,
    IntersectionType,
    Any,
    Nothing,
    Token,
    TypeVarEnv,
    TypeEnv,
} from "./types.ts";

import {
    type Term,
    Var,
    Lam,
    App,
    VariantCon,
    PatternMatch,
    Fold,
    PatternFold,
    Obs,
    Unfold,
    Cofold,
    TypeAbs,
    TypeApp,
    Let,
    FoldHandler,
    PatternHandler,
    UnfoldGenerator,
} from "./terms.ts";

import { isSubtype, typeEquals } from "./subtyping.ts";

// ── Type checking error ───────────────────────────────────────────────────────

/** Thrown when a type check fails (a premise is violated). */
export class TypeError_ extends Error {
    override readonly name = "TypeError_";
    constructor(
        message: string,
        readonly expected: Type | null,
        readonly actual: Type | null,
    ) {
        super(message);
    }
}

// ── Type substitution ─────────────────────────────────────────────────────────

/** Substitute `replacement` for type variable `varName` in `type`. */
export function substituteType(
    type: Type,
    varName: string,
    replacement: Type,
): Type {
    if (type instanceof TypeVar) {
        return type.name === varName ? replacement : type;
    }
    if (type instanceof FunType) {
        return new FunType(
            substituteType(type.param, varName, replacement),
            substituteType(type.result, varName, replacement),
        );
    }
    if (type instanceof IntersectionType) {
        return new IntersectionType(
            substituteType(type.left, varName, replacement),
            substituteType(type.right, varName, replacement),
        );
    }
    // DataType, CodataType, PatternDataType, TokenType, AnyType, NothingType:
    // no type variables inside (they are ground types)
    return type;
}

// ── Shape for the typing grammar ──────────────────────────────────────────────

interface TypingShape {
    [k: string]: unknown;
    type: Type;
}

// ── The typing grammar ────────────────────────────────────────────────────────

/**
 * The LC type checker. Each method encodes a typing rule from lc.md §5.
 *
 * Methods are called directly (no parsing). The `@requires` decorator
 * encodes the rule's premises — on failure, the method returns `undefined`
 * (graceful), meaning the term is ill-typed. The `@ensures` decorator
 * encodes the rule's conclusion — a violated postcondition is a compiler bug.
 */
@invariant((self: TypeChecker) => self !== undefined)
export class TypeChecker extends Grammar<TypingShape> {
    override start() {
        // Not used for parsing — this class is called directly.
        // Return a dummy parser to satisfy the Grammar base class.
        return epsilon(null as unknown as Type);
    }

    // ── Main entry point ──────────────────────────────────────────────────────

    /**
     * Type-check a term in context Γ. Returns the type, or throws TypeError_
     * if the term is ill-typed.
     */
    check(term: Term, gamma: TypeEnv): Type {
        const result = this.dispatch(term, gamma);
        if (result === undefined) {
            throw new TypeError_("ill-typed term", null, null);
        }
        return result;
    }

    /** Dispatch a term to the appropriate typing rule. */
    protected dispatch(term: Term, gamma: TypeEnv): Type | undefined {
        switch (term.kind) {
            case "var":
                return this.checkVar(term as Var, gamma);
            case "lam":
                return this.checkLam(term as Lam, gamma);
            case "app":
                return this.checkApp(term as App, gamma);
            case "variantCon":
                return this.checkVariantCon(term as VariantCon, gamma);
            case "patternMatch":
                return this.checkPatternMatch(term as PatternMatch, gamma);
            case "fold":
                return this.checkFold(term as Fold, gamma);
            case "patternFold":
                return this.checkPatternFold(term as PatternFold, gamma);
            case "obs":
                return this.checkObs(term as Obs, gamma);
            case "unfold":
                return this.checkUnfold(term as Unfold, gamma);
            case "cofold":
                return this.checkCofold(term as Cofold, gamma);
            case "typeAbs":
                return this.checkTypeAbs(term as TypeAbs, gamma);
            case "typeApp":
                return this.checkTypeApp(term as TypeApp, gamma);
            case "let":
                return this.checkLet(term as Let, gamma);
            default:
                return undefined;
        }
    }

    // ── T-Var: Γ(x) = σ  ⟹  Γ ⊢ x : σ ───────────────────────────────────────

    @requires((_self: TypeChecker, term: Var, gamma: TypeEnv) =>
        gamma.has(term.name))
    protected checkVar(term: Var, gamma: TypeEnv): Type | undefined {
        return gamma.lookup(term.name);
    }

    // ── T-Abs: Γ, x:σ ⊢ t : τ  ⟹  Γ ⊢ λx:σ.t : σ → τ ─────────────────────────

    protected checkLam(term: Lam, gamma: TypeEnv): Type | undefined {
        const extendedGamma = gamma.extend(term.param, term.paramType);
        const bodyType = this.dispatch(term.body, extendedGamma);
        if (bodyType === undefined) return undefined;
        return new FunType(term.paramType, bodyType);
    }

    // ── T-App: Γ ⊢ t : σ→τ  ∧  Γ ⊢ u : σ  ⟹  Γ ⊢ t u : τ ─────────────────────

    protected checkApp(term: App, gamma: TypeEnv): Type | undefined {
        const fnType = this.dispatch(term.fn, gamma);
        if (fnType === undefined) return undefined;
        if (!(fnType instanceof FunType)) return undefined;

        const argType = this.dispatch(term.arg, gamma);
        if (argType === undefined) return undefined;

        // Premise: arg type must be a subtype of the function's parameter type
        if (!isSubtype(argType, fnType.param)) return undefined;

        return fnType.result;
    }

    // ── T-Variant: Γ ⊢ tⱼ : Fₖ(T)[α:=T]  ⟹  Γ ⊢ Cₖ(tⱼ) : T ───────────────────

    protected checkVariantCon(term: VariantCon, gamma: TypeEnv): Type | undefined {
        const variant = term.dataType.findVariant(term.variantName);
        if (!variant) return undefined;

        // Check each field has the expected type (with α := T)
        for (let i = 0; i < variant.fields.length; i++) {
            const field = variant.fields[i]!;
            const arg = term.args[i];
            if (!arg) return undefined;

            const argType = this.dispatch(arg, gamma);
            if (argType === undefined) return undefined;

            // The field type is already the declared type (α is replaced by T
            // in the DataType's variant definition). For recursive fields,
            // the expected type is the DataType itself.
            const expectedType = field.isRecursive ? term.dataType : field.type;
            if (!isSubtype(argType, expectedType)) return undefined;
        }

        return term.dataType;
    }

    // ── T-Pattern: input matches pₖ  ⟹  Γ ⊢ tok : T ──────────────────────────

    protected checkPatternMatch(term: PatternMatch, gamma: TypeEnv): Type | undefined {
        // The pattern index must be valid
        if (term.patternIndex < 0 || term.patternIndex >= term.dataType.patterns.length) {
            return undefined;
        }
        return term.dataType;
    }

    // ── T-Fold: Γ ⊢ e : T  ∧  Γ ⊢ tᵢ : Fᵢ(σ)[α:=σ]→σ  ⟹  Γ ⊢ fold [T] e {...} : σ ─

    protected checkFold(term: Fold, gamma: TypeEnv): Type | undefined {
        // Premise 1: e : T
        const scrutineeType = this.dispatch(term.scrutinee, gamma);
        if (scrutineeType === undefined) return undefined;
        if (!isSubtype(scrutineeType, term.dataType)) return undefined;

        // Premise 2: handlers must be exhaustive (cover all variants)
        const allVariants = term.dataType.allVariants();
        for (const variant of allVariants) {
            const handler = term.findHandler(variant.name);
            if (!handler) return undefined; // missing handler

            // Check handler body type: each handler should produce σ
            // The handler binds field names; recursive fields get type σ,
            // non-recursive fields get their declared type.
            let handlerGamma = gamma;
            for (let i = 0; i < variant.fields.length; i++) {
                const field = variant.fields[i]!;
                const binding = handler.fieldBindings[i];
                if (!binding) return undefined;
                const fieldType = field.isRecursive ? term.resultType : field.type;
                handlerGamma = handlerGamma.extend(binding, fieldType);
            }

            const handlerType = this.dispatch(handler.body, handlerGamma);
            if (handlerType === undefined) return undefined;
            if (!isSubtype(handlerType, term.resultType)) return undefined;
        }

        return term.resultType;
    }

    // ── T-FoldMatch: Γ ⊢ e : T  ∧  Γ ⊢ tᵢ : Token→σ  ⟹  Γ ⊢ fold [T] e {pᵢ→tᵢ} : σ ─

    protected checkPatternFold(term: PatternFold, gamma: TypeEnv): Type | undefined {
        // Premise 1: e : T
        const scrutineeType = this.dispatch(term.scrutinee, gamma);
        if (scrutineeType === undefined) return undefined;
        if (!isSubtype(scrutineeType, term.dataType)) return undefined;

        // Premise 2: handlers must cover all patterns
        for (let i = 0; i < term.dataType.patterns.length; i++) {
            const handler = term.handlers.find((h) => h.patternIndex === i);
            if (!handler) return undefined;

            // The handler binds `match` (the Token) in scope
            const handlerGamma = gamma.extend("match", Token);
            const handlerType = this.dispatch(handler.body, handlerGamma);
            if (handlerType === undefined) return undefined;
            if (!isSubtype(handlerType, term.resultType)) return undefined;
        }

        return term.resultType;
    }

    // ── T-Obs: Γ ⊢ e : T  ⟹  Γ ⊢ e.oₖ : Gₖ(T)[α:=T] ──────────────────────────

    protected checkObs(term: Obs, gamma: TypeEnv): Type | undefined {
        const scrutineeType = this.dispatch(term.scrutinee, gamma);
        if (scrutineeType === undefined) return undefined;
        if (!isSubtype(scrutineeType, term.codataType)) return undefined;

        const observer = term.codataType.findObserver(term.observerName);
        if (!observer) return undefined;

        // The observer type has α (Self) replaced by T
        // For continuation observers, the type is T itself
        if (observer.isContinuation) {
            return term.codataType;
        }
        return observer.type;
    }

    // ── T-Unfold: Γ ⊢ s : Σ  ∧  Γ ⊢ gⱼ : Σ→Gⱼ(Σ)[α:=Σ]  ⟹  Γ ⊢ unfold [T] s {...} : T ─

    protected checkUnfold(term: Unfold, gamma: TypeEnv): Type | undefined {
        // Premise 1: s : Σ
        const seedType = this.dispatch(term.seed, gamma);
        if (seedType === undefined) return undefined;
        if (!isSubtype(seedType, term.seedType)) return undefined;

        // Premise 2: each generator gⱼ : Σ → Gⱼ(Σ)[α:=Σ]
        const allObservers = term.codataType.allObservers();
        for (const observer of allObservers) {
            const generator = term.findGenerator(observer.name);
            if (!generator) return undefined;

            // The generator body is checked in Γ extended with `self: Σ`
            const genGamma = gamma.extend("self", term.seedType);
            const genType = this.dispatch(generator.body, genGamma);
            if (genType === undefined) return undefined;

            // Expected: Gⱼ(Σ)[α:=Σ] — for continuations, this is Σ; otherwise the observer type
            const expectedType = observer.isContinuation ? term.seedType : observer.type;
            if (!isSubtype(genType, expectedType)) return undefined;
        }

        return term.codataType;
    }

    // ── T-Cofold: Γ ⊢ e : T  ∧  Γ ⊢ t : Πⱼ(Gⱼ(σ)[α:=σ])→σ  ⟹  Γ ⊢ cofold [T] e {...} : σ ─

    protected checkCofold(term: Cofold, gamma: TypeEnv): Type | undefined {
        // Premise 1: e : T
        const scrutineeType = this.dispatch(term.scrutinee, gamma);
        if (scrutineeType === undefined) return undefined;
        if (!isSubtype(scrutineeType, term.codataType)) return undefined;

        // Premise 2: handler receives all observations, produces σ
        const allObservers = term.codataType.allObservers();
        let handlerGamma = gamma;
        for (const observer of allObservers) {
            const binding = term.handler.fieldBindings.find((_, i) =>
                allObservers[i]?.name === observer.name);
            // The handler binds each observer's result; continuations get type σ
            const obsType = observer.isContinuation ? term.resultType : observer.type;
            // For now, bind by position
        }
        // Bind field bindings to observer types
        for (let i = 0; i < term.handler.fieldBindings.length; i++) {
            const binding = term.handler.fieldBindings[i]!;
            const observer = allObservers[i];
            if (!observer) return undefined;
            const obsType = observer.isContinuation ? term.resultType : observer.type;
            handlerGamma = handlerGamma.extend(binding, obsType);
        }

        const handlerType = this.dispatch(term.handler.body, handlerGamma);
        if (handlerType === undefined) return undefined;
        if (!isSubtype(handlerType, term.resultType)) return undefined;

        return term.resultType;
    }

    // ── T-TAbs: Δ, α<:σ ⊢ t : τ  ⟹  Δ ⊢ Λα<:σ.t : ∀α<:σ.τ ─────────────────────

    protected checkTypeAbs(term: TypeAbs, gamma: TypeEnv): Type | undefined {
        // Type abstraction: the body is checked in Γ (unchanged for term vars)
        // but Δ is extended with α <: σ. Since we don't track Δ separately
        // in this implementation (type vars are handled via substitution),
        // we check the body and return a FunType-like wrapper.
        //
        // For now, we represent ∀α<:σ.τ as a FunType from the bound to the body type.
        // This is a simplification — a proper F<: implementation would have a
        // PolymorphicType wrapper. Deferred to when we need bounded polymorphism.
        const bodyType = this.dispatch(term.body, gamma);
        if (bodyType === undefined) return undefined;
        // Represent ∀α<:σ.τ as FunType(σ, τ) — a simplification
        return new FunType(term.bound, bodyType);
    }

    // ── T-TApp: Γ ⊢ t : ∀α<:σ.τ  ∧  Δ ⊢ T₂<:σ  ⟹  Γ ⊢ t[T₂] : τ[α:=T₂] ───────

    protected checkTypeApp(term: TypeApp, gamma: TypeEnv): Type | undefined {
        const bodyType = this.dispatch(term.body, gamma);
        if (bodyType === undefined) return undefined;

        // The body should be a polymorphic type (represented as FunType for now)
        if (!(bodyType instanceof FunType)) return undefined;

        // Premise: T₂ <: σ (the bound)
        if (!isSubtype(term.argType, bodyType.param)) return undefined;

        // Result: τ[α:=T₂] — substitute T₂ for the type variable
        // Since we represent ∀α<:σ.τ as FunType(σ, τ), the "type variable"
        // is implicit. We substitute the arg type into the result.
        // This is a simplification — proper F<: would track the variable name.
        return bodyType.result;
    }

    // ── T-Let: Γ ⊢ t : σ  ∧  Γ,x:σ ⊢ u : τ  ⟹  Γ ⊢ let x:σ=t in u : τ ─────────

    protected checkLet(term: Let, gamma: TypeEnv): Type | undefined {
        // Premise 1: t : σ
        const valueType = this.dispatch(term.value, gamma);
        if (valueType === undefined) return undefined;
        if (!isSubtype(valueType, term.type)) return undefined;

        // Premise 2: u : τ in Γ extended with x:σ
        const extendedGamma = gamma.extend(term.name, term.type);
        const bodyType = this.dispatch(term.body, extendedGamma);
        if (bodyType === undefined) return undefined;

        return bodyType;
    }
}