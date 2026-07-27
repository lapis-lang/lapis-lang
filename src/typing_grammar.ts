/**
 * LC Type Checker — a grammar subclass that type-checks LC terms during parsing.
 *
 * Following the stlc.ts pattern from zipper-grammar: the typing judgment
 * `Γ ⊢ t : σ` becomes a parameterised production `exprProd(Γ): Parser<Type>`.
 * `chain` threads the extended Γ through sub-productions.
 * `@requires` encodes premises (graceful failure = ill-typed).
 * `@ensures` encodes conclusions (throws on violation = compiler bug).
 * Rejection (empty parse forest) = type error.
 *
 * See _docs/theory/lc.md §5 for the formal specification.
 * See _docs/theory/grammar-as-semantics.md for the architecture.
 */

import {
    rule,
    requires,
    ensures,
    or,
    seq,
    epsilon,
    empty,
    type Parser,
} from "@lapis-lang/zipper-grammar";

import {
    type Type,
    FunType,
    DataType,
    CodataType,
    Any,
    TypeEnv,
} from "./types.ts";

import {
    AbstractLC,
    type LCShape,
} from "./grammar.ts";

import { isSubtype } from "./subtyping.ts";

// ── Shape for type checking ───────────────────────────────────────────────────

interface TypeCheckShape extends LCShape {
    expr: Type;
    atom: Type;
    type: Type;
}

// ── The type-checking grammar ─────────────────────────────────────────────────

/**
 * One-pass type checker. Parses LC text and produces types.
 *
 *   parseWith("\\x:Int. x", TypeEnv.empty()) → Set { FunType(Int, Int) }
 *   parseWith("\\x:Int. x x", TypeEnv.empty()) → Set {} (ill-typed — empty forest)
 *
 * Inference rules encoded as semantic actions:
 *
 *   T-Var:  Γ(x) = σ  ⟹  Γ ⊢ x : σ          (@requires: x must be in Γ)
 *   T-Abs:  Γ, x:σ ⊢ t : τ  ⟹  Γ ⊢ λx:σ.t : σ → τ
 *   T-App:  Γ ⊢ t : σ→τ  ∧  Γ ⊢ u : σ  ⟹  Γ ⊢ t u : τ  (@requires: domain match)
 *   T-Let:  Γ ⊢ t : σ  ∧  Γ, x:σ ⊢ u : τ  ⟹  Γ ⊢ let x:σ=t in u : τ
 */
export class LCTypeCheck extends AbstractLC<TypeCheckShape> {
    /**
     * Parse and type-check input under `gamma`.
     * Returns the set of possible types (usually one; empty = ill-typed).
     */
    parseWith(input: string, gamma: TypeEnv): Set<Type> {
        return this._parseWith(input, this.exprProd(gamma));
    }

    override start(): Parser<Type> {
        return this.exprProd(new TypeEnv());
    }

    // ── Context extension: extend Γ with x:σ ─────────────────────────────────

    protected override extendCtx(ctx: unknown, name: string, type: Type): unknown {
        if (ctx instanceof TypeEnv) {
            return ctx.extend(name, type);
        }
        return ctx;
    }

    // ── T-Abs: Γ, x:σ ⊢ t : τ  ⟹  Γ ⊢ λx:σ.t : σ → τ ─────────────────────────

    protected lam(_param: string, type: Type, body: Type): Type {
        // The body type τ was computed by parsing the body under Γ + x:σ.
        // The result is σ → τ.
        return new FunType(type, body);
    }

    // ── T-App: Γ ⊢ t : σ→τ  ∧  Γ ⊢ u : σ  ⟹  Γ ⊢ t u : τ ─────────────────────

    /**
     * Application typing rule. The premise (fn must be a function type whose
     * domain matches arg's type) is checked via @requires.
     * On failed premise, @requires returns undefined → the calling chain
     * produces empty() → the ill-typed branch is rejected.
     */
    @requires((_self: LCTypeCheck, fn: Type, arg: Type) =>
        fn instanceof FunType && isSubtype(arg, fn.param))
    @ensures((_self: LCTypeCheck, _args: [Type, Type], _old, result: Type) =>
        result !== undefined)
    protected app(fn: Type, _arg: Type): Type {
        // Premise enforced by @requires; body is the conclusion.
        return (fn as FunType).result;
    }

    // ── T-Let: Γ ⊢ t : σ  ∧  Γ, x:σ ⊢ u : τ  ⟹  Γ ⊢ let x:σ=t in u : τ ────────

    protected let_(_name: string, _type: Type, _def: Type, body: Type): Type {
        // The body type τ was computed under Γ + x:σ.
        return body;
    }

    // ── T-Var: Γ(x) = σ  ⟹  Γ ⊢ x : σ ────────────────────────────────────────

    /**
     * Variable typing rule. @requires: name must be bound in ctx.
     * On failure, returns undefined → empty parse forest (ill-typed).
     */
    @requires((_self: LCTypeCheck, name: string, ctx: unknown) =>
        ctx instanceof TypeEnv && ctx.lookup(name) !== undefined)
    protected varRef(name: string, ctx: unknown): Type {
        return (ctx as TypeEnv).lookup(name) as Type;
    }

    protected paren(e: Type): Type {
        return e;
    }

    protected variantCon(_name: string, _args: Type[]): Type {
        // Look up the variant in the registry to find its DataType
        // For now, return Any — a proper implementation would look up
        // the variant name in the registry and return the DataType.
        // This requires a variant-to-type mapping in the registry.
        return Any;
    }

    protected obs(_scrutinee: Type, _observerName: string): Type {
        // Look up the observer in the registry to find its return type
        // For now, return Any — a proper implementation would look up
        // the observer and return Gₖ(T)[α := T].
        return Any;
    }

    protected fold(
        _dataType: DataType,
        _scrutinee: Type,
        _handlers: { variantName: string; bindings: string[]; body: Type }[],
        resultType: Type,
    ): Type {
        // T-Fold: the fold has type σ (the declared result type).
        // Premises (scrutinee : T, handlers exhaustive) are checked
        // during parsing via the foldProd production.
        return resultType;
    }

    protected unfold(
        codataType: CodataType,
        _seed: Type,
        _generators: { observerName: string; body: Type }[],
        _seedType: Type,
    ): Type {
        // T-Unfold: the unfold has type T (the codata type).
        return codataType;
    }

    // ── Override appProd for type checking via chain ──────────────────────────

    /**
     * Override application to type-check via chain:
     * parse fn → get fnType; parse arg → get argType;
     * if fnType is FunType and argType <: fnType.param,
     * return ε(fnType.result), else ∅ (empty — ill-typed).
     */
    @rule
    protected override appProd(ctx: unknown): Parser<Type> {
        return or(
            this.appProd(ctx)
                .map((fnTy) => ({ fnTy }))
                .chain(({ fnTy }) =>
                    seq(this.ws1, this.atomProd(ctx))
                        .map(([, argTy]) => ({ fnTy, argTy }))
                        .chain(({ fnTy, argTy }) => {
                            if (!(fnTy instanceof FunType) || !isSubtype(argTy, fnTy.param)) {
                                return empty() as unknown as Parser<Type>;
                            }
                            return epsilon<Type>(fnTy.result);
                        })
                        .map(([, result]) => result),
                )
                .map(([, result]) => result),
            this.atomProd(ctx) as unknown as Parser<Type>,
        );
    }
}