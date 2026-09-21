/**
 * LC Type Checker — a grammar subclass that type-checks LC terms during parsing.
 *
 * Following the stlc.ts pattern from lang-forma: the typing judgment
 * `Γ ⊢ t : σ` becomes a parameterised production `exprProd(Γ): Parser<Type>`.
 * `bind` threads the extended Γ through sub-productions.
 * `@requires` encodes premises (graceful failure = ill-typed).
 * `@ensures` encodes conclusions (throws on violation = compiler bug).
 * Rejection (empty parse forest) = type error.
 *
 * Typing rules (lc.md §5):
 *
 *   T-Var:      x:σ ∈ Γ  ⟹  Γ ⊢ x : σ
 *   T-Abs:      Γ, x:σ ⊢ t : τ  ⟹  Γ ⊢ λx:σ.t : σ → τ
 *   T-App:      Γ ⊢ t : σ→τ  ∧  Γ ⊢ u : σ  ⟹  Γ ⊢ t u : τ
 *   T-Let:      Γ ⊢ t : σ  ∧  σ <: τ  ∧  Γ, x:τ ⊢ u : τ'  ⟹  Γ ⊢ let x:τ=t in u : τ'
 *   T-Variant:  Γ ⊢ tⱼ : Fₖ(T)[α:=T]  ⟹  Γ ⊢ Cₖ(tⱼ) : T
 *   T-Fold:     Γ ⊢ e : T  ∧  Γ ⊢ tᵢ : Fᵢ(σ)[α:=σ]→σ  ⟹  Γ ⊢ fold [T] e {...} : σ
 *   T-Obs:      Γ ⊢ e : T  ⟹  Γ ⊢ e.oₖ : Gₖ(T)[α:=T]
 *   T-Unfold:   Γ ⊢ s : Σ  ∧  Γ ⊢ gⱼ : Σ→Gⱼ(Σ)[α:=Σ]  ⟹  Γ ⊢ unfold [T] s {...} : T
 *   T-Cofold:   Γ ⊢ e : T  ∧  Γ ⊢ t : Πⱼ(Gⱼ(σ)[α:=σ])→σ  ⟹  Γ ⊢ cofold [T] e {...} : σ
 *   T-TAbs:     Δ, α<:σ ⊢ t : τ  ⟹  Δ ⊢ Λα<:σ.t : ∀α<:σ.τ
 *   T-TApp:     Γ ⊢ t : ∀α<:σ.τ  ∧  Δ ⊢ T₂<:σ  ⟹  Γ ⊢ t[T₂] : τ[α:=T₂]
 *   T-Op:       Ω(op) = σ₁→...→σₙ→τ  ∧  Γ ⊢ tᵢ : σᵢ  ⟹  Γ ⊢ op(t₁,...,tₙ) : τ
 *   T-Sub:      Γ ⊢ t : σ  ∧  σ <: τ  ⟹  Γ ⊢ t : τ  (applied at use sites via isSubtype)
 *
 * T-Fold uses parseToFixpoint for circular attribute flow: σ is refined
 * iteratively until convergence (σ₀ = DataType, σₙ₊₁ = join of handler body types).
 *
 * See _docs/theory/lc.md §5 for the formal specification.
 * See _docs/theory/grammar-as-semantics.md for the architecture.
 */

import {
    assert,
    char,
    empty,
    ensures,
    epsilon,
    or,
    type Parser,
    requires,
    rule,
    sepBy,
    seq,
    type Span,
} from "@lapis-lang/lang-forma"

import {
    Any,
    AnyType,
    CodataType,
    DataType,
    FamilyType,
    FunType,
    IntersectionType,
    mapType,
    Nothing,
    NothingType,
    PatternDataType,
    PolymorphicType,
    TokenType,
    type Type,
    TypeEnv,
    TypeVar,
    TypeVarEnv,
} from "./types.ts"

import { AbstractLC, type LCShape } from "./grammar.ts"

import { type OpSig, OpWellFormedness } from "./ops.ts"

import { isSubtype, join } from "./subtyping.ts"

// ── Shape for type checking ───────────────────────────────────────────────────

interface TypeCheckShape extends LCShape {
    expr: Type
    atom: Type
    type: Type
}

// ── Combined typing context (Γ + Δ) ──────────────────────────────────────────

/**
 * The inherited context for type checking bundles the term-variable context
 * `Γ` (TypeEnv) and the type-variable context `Δ` (TypeVarEnv). The base
 * grammar's `ctx` is `unknown`; the type checker uses this pair so that
 * `typeVarCtx` can extract Δ and `extendCtx`/`extendTypeVarCtx` can extend
 * the correct half.
 */
class TypeCheckCtx {
    constructor(
        readonly gamma: TypeEnv,
        readonly delta: TypeVarEnv = new TypeVarEnv(),
    ) {}

    /** True if `ctx` is a `TypeCheckCtx`. */
    static is(ctx: unknown): ctx is TypeCheckCtx {
        return ctx instanceof TypeCheckCtx
    }
}

// ── Well-formedness check for @ensures ────────────────────────────────────────

/**
 * Substitute `replacement` for type variable `varName` in `type`.
 * Used by T-TApp to compute τ[α := T₂]. The binder scopes over its BODY
 * only: a polymorphic type binding `varName` stops the substitution inside
 * the body (α is shadowed) — but the BOUND is parsed under the outer
 * type-variable context (the binder does not scope over its own bound), so
 * an occurrence of the variable there must still be substituted
 * (`∀A <: A. A` under `A := Any` becomes `∀A <: Any. A`).
 *
 * Routed through `mapType` — the type universe's one structural traversal;
 * only the kinds that can hold the variable are spelled. The polymorphic
 * handler composes the shadowing rule explicitly (bound mapped, body
 * original — identity-reused when nothing moved); the non-shadowing case
 * returns `undefined`, delegating to mapType's structural default: the
 * original binder is reused when no child moved (no allocation), rebuilt
 * only when a child moved.
 */
function substituteTypeVar(type: Type, varName: string, replacement: Type): Type {
    return mapType(type, {
        typeVar: (tv) => (tv.name === varName ? replacement : tv),
        polymorphic: (pt, bound) => {
            if (pt.typeVarName !== varName) return undefined
            // Shadowed body — but the bound still carries the substitution
            // (it is under the OUTER context): rebuild when the mapped bound
            // moved, reuse the original binder when it did not.
            if (bound === pt.bound) return pt
            return new PolymorphicType(pt.typeVarName, bound, pt.body)
        },
    })
}

/**
 * Check that a type is well-formed (a proper Type instance, not undefined or
 * a broken value). Used by @ensures contracts to verify the conclusion of
 * each typing rule produces a valid type.
 *
 * Progress follows from @requires premises + grammar structure, not from
 * this check. This check catches implementation bugs (returning undefined
 * or non-Type values from a typing rule).
 */
function isWellFormedType(t: Type | undefined): boolean {
    return t !== undefined && t !== null &&
        (t instanceof FunType ||
            t instanceof DataType ||
            t instanceof CodataType ||
            t instanceof AnyType ||
            t instanceof NothingType ||
            t instanceof TypeVar ||
            t instanceof TokenType ||
            t instanceof IntersectionType ||
            t instanceof PatternDataType ||
            t instanceof PolymorphicType ||
            t instanceof FamilyType)
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
 *   T-Let:  Γ ⊢ t : σ  ∧  σ <: τ  ∧  Γ, x:τ ⊢ u : τ'  ⟹  Γ ⊢ let x:τ=t in u : τ'
 */
export class LCTypeCheck extends AbstractLC<TypeCheckShape> {
    /** The source text, stored for `parseToFixpoint` re-parsing of fold handler bodies. */
    private _input: string = ""

    /**
     * Parse and type-check input under `gamma`.
     * Returns the set of possible types (usually one; empty = ill-typed).
     */
    parseWith(input: string, gamma: TypeEnv): Set<Type> {
        this._input = input
        return this._parseWith(input, this.exprProd(new TypeCheckCtx(gamma)))
    }

    override start(): Parser<Type> {
        return this.exprProd(new TypeCheckCtx(new TypeEnv()))
    }

    // ── Context extension: extend Γ with x:σ ─────────────────────────────────

    protected override extendCtx(ctx: unknown, name: string, type: Type): unknown {
        if (TypeCheckCtx.is(ctx)) {
            return new TypeCheckCtx(ctx.gamma.extend(name, type), ctx.delta)
        }
        return ctx
    }

    /** Extract Δ (type-variable context) from the inherited context. */
    protected override typeVarCtx(ctx: unknown): TypeVarEnv {
        return TypeCheckCtx.is(ctx) ? ctx.delta : new TypeVarEnv()
    }

    /** Extend the inherited context with an updated Δ. */
    protected override extendTypeVarCtx(ctx: unknown, delta: TypeVarEnv): unknown {
        if (TypeCheckCtx.is(ctx)) {
            return new TypeCheckCtx(ctx.gamma, delta)
        }
        return ctx
    }

    // NOTE: foldFieldType is NOT overridden here. The foldProd override below
    // uses spanFoldHandler (which binds Family fields to the carrier and
    // other fields to field.type) and parseToFixpoint for circular attribute
    // flow. The base foldProd (which calls foldFieldType) is never reached
    // because foldProd is overridden.

    // ── T-Abs: Γ, x:σ ⊢ t : τ  ⟹  Γ ⊢ λx:σ.t : σ → τ ─────────────────────────

    /**
     * @ensures Progress: a lambda is always a value (closure), so it trivially
     * satisfies Progress — no step needed.
     */
    @ensures(
        (_self: LCTypeCheck, _args: [string, Type, Type], _old, result: Type) =>
            result instanceof FunType,
        { rule: "T-Abs", role: "conclusion", formula: "result : σ → τ" },
    )
    protected lam(_param: string, type: Type, body: Type): Type {
        // The body type τ was computed by parsing the body under Γ + x:σ.
        // The result is σ → τ.
        return new FunType(type, body)
    }

    // ── T-App: Γ ⊢ t : σ→τ  ∧  Γ ⊢ u : σ  ⟹  Γ ⊢ t u : τ ─────────────────────

    /**
     * Application typing rule. The premise (fn must be a function type whose
     * domain matches arg's type) is enforced by the `appProd` override: it
     * checks the premise inline and returns `empty()` on failure, so the
     * ill-typed branch is rejected. The `@requires` decorator is declarative
     * metadata for the rule model; this action is bypassed on the production
     * path (the override computes the conclusion directly).
     */
    @requires(
        (_self: LCTypeCheck, fn: Type, arg: Type) =>
            fn instanceof FunType && isSubtype(arg, fn.param),
        { rule: "T-App", role: "premise", formula: "fn : σ → τ  ∧  arg <: σ" },
    )
    @ensures(
        (_self: LCTypeCheck, _args: [Type, Type], _old, result: Type) => isWellFormedType(result),
        { rule: "T-App", role: "conclusion", formula: "result : τ" },
    )
    protected app(fn: Type, _arg: Type): Type {
        // Premise enforced by @requires; body is the conclusion.
        return (fn as FunType).result
    }

    // ── T-Let: Γ ⊢ t : σ  ∧  σ <: τ  ∧  Γ, x:τ ⊢ u : τ'  ⟹  Γ ⊢ let x:τ=t in u : τ' ───

    /**
     * Let-binding typing rule. Premise 1 (def type <: declared type) is
     * enforced in the `letProd` override: if the definition's type is not a
     * subtype of the declared annotation, the override returns `empty<Type>()`
     * (empty parse forest — ill-typed). This method is only reached after
     * the premise check passes.
     *
     * This is the subsumption site for let-bindings: `let x:τ = (e : σ)`
     * where `σ <: τ` is accepted (the body sees `x : τ`, the widened type).
     * Subsumption is implicit — no standalone T-Sub production is needed;
     * each consumer site checks `isSubtype` in its own premise.
     *
     * @ensures Progress: let can always step (E-Let) if the value is not yet a
     * value, or is a value after evaluation. The result type is the body type.
     */
    @requires(
        (_self: LCTypeCheck, _name: string, type: Type, def: Type, _body: Type) =>
            isSubtype(def, type),
        { rule: "T-Let", role: "premise", formula: "def : σ  ∧  σ <: τ" },
    )
    @ensures(
        (_self: LCTypeCheck, _args: [string, Type, Type, Type], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Let", role: "conclusion", formula: "result : τ'" },
    )
    protected let_(_name: string, _type: Type, _def: Type, body: Type): Type {
        // Premise 1 is enforced in the `letProd` override (returns empty on
        // failure). The body type τ was computed under Γ + x:τ (the declared
        // type, widened via subsumption from the def's actual type σ).
        return body
    }

    // ── T-Var: Γ(x) = σ  ⟹  Γ ⊢ x : σ ────────────────────────────────────────

    /**
     * Variable typing rule. The premise (name must be bound in Γ) is
     * declarative metadata for the rule model: `varRef` is called from
     * `varProd`, and the production-path check lives in the `varProd`
     * override below, which rejects the branch (`empty<Type>()`) before the
     * contracted action is ever reached.
     *
     * @ensures Progress: a variable in a closed term is always substituted
     * before evaluation, so it can always step (or is already a value).
     */
    @requires(
        (_self: LCTypeCheck, name: string, ctx: unknown) =>
            TypeCheckCtx.is(ctx) && ctx.gamma.lookup(name) !== undefined,
        { rule: "T-Var", role: "premise", formula: "x : σ ∈ Γ" },
    )
    @ensures(
        (_self: LCTypeCheck, _args: [string, unknown], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Var", role: "conclusion", formula: "result : σ" },
    )
    protected varRef(name: string, ctx: unknown): Type {
        return (ctx as TypeCheckCtx).gamma.lookup(name) as Type
    }

    /**
     * Override the variable production to enforce T-Var's premise in the
     * production path: `x : σ ∈ Γ`. A name not bound in Γ fails the premise —
     * the branch is rejected (`empty<Type>()`, empty parse forest — ill-typed).
     * On success the conclusion is computed directly from Γ and committed via
     * `epsilon`, the same shape as the `appProd`/`typeAppProd` overrides: the
     * contracted `varRef` action is only called on the verified path, so a
     * failed `@requires` can never leak `undefined` into the parse forest (and
     * the `@ensures` safety net still runs, because the action is reached).
     */
    // Ident  — T-Var via bind (type-checks Γ(x) ≠ undefined)
    @rule
    protected override varProd(ctx: unknown): Parser<Type> {
        return this.ident.bind((name) => {
            if (!TypeCheckCtx.is(ctx) || ctx.gamma.lookup(name) === undefined) {
                return empty<Type>()
            }
            return epsilon<Type>(this.varRef(name, ctx))
        })
    }

    protected paren(e: Type): Type {
        return e
    }

    /**
     * Γ membership for the token gate: a name bound in Γ is a term variable
     * (`patternTokenProd` falls through to `varProd`), so a PascalCase
     * variable always types by its Γ binding — the registry's pattern-type
     * entry never shadows it.
     */
    protected override nameBound(name: string, ctx: unknown): boolean {
        return TypeCheckCtx.is(ctx) && ctx.gamma.lookup(name) !== undefined
    }

    /**
     * @ensures Progress: a variant construction with value args is a value;
     * with non-value args, it can step (E-VariantArg). Either way, Progress holds.
     */
    @ensures(
        (_self: LCTypeCheck, _args: [string, Type[]], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Variant", role: "conclusion", formula: "result : T" },
    )
    protected variantCon(name: string, args: Type[]): Type {
        // T-Variant: Γ ⊢ tⱼ : Fₖ(T)[α:=T] ⟹ Γ ⊢ Cₖ(tⱼ) : T
        // Look up the variant in the registry to find its DataType.
        const dataType = this.registry.lookupVariant(name)
        if (!dataType) return Any // unknown variant → ill-typed (Any won't match)
        const variant = dataType.findVariant(name)
        if (!variant) return Any
        // Arity must match exactly — extra args are as ill-typed as missing ones.
        if (args.length !== variant.fields.length) return Any

        // Check each arg type is a subtype of the expected field type.
        // A Family-typed field (the μ-bound) expects the DataType itself.
        // (A Nothing arg satisfies the premise via S-Bot; it is tracked and
        // propagated after the loop so a genuine premise violation on a
        // later arg is not silently subsumed by Nothing.)
        let hasNothingArg = false
        for (let i = 0; i < variant.fields.length; i++) {
            const field = variant.fields[i]!
            const argType = args[i]
            if (argType === undefined) return Any
            if (argType instanceof NothingType) hasNothingArg = true
            const expected = field.type instanceof FamilyType ? dataType : field.type
            if (!isSubtype(argType, expected)) return Any
        }

        // Nothing propagation: an eagerly-evaluated arg of type Nothing makes
        // the construction uninhabited (principle of explosion).
        if (hasNothingArg) return Nothing

        return dataType
    }

    /**
     * Override the variant-construction production to enforce T-Variant's
     * premises in the production path: the variant is declared in the
     * registry, the arity matches, and every field argument type is a subtype
     * of the declared field type. Any failed premise rejects the branch
     * (`empty<Type>()` — empty parse forest, ill-typed) before the contracted
     * `variantCon` action is reached, closing the `let x:Any =
     * UnknownVariant() in x` absorption hole: the permissive-`Any` sentinel
     * inside `variantCon` was sound only where `Any` is not a legal type, but
     * under an `Any` annotation the sentinel *is* the declared type and the
     * ill-typed def was accepted via S-Refl.
     */
    // Ident(args)  — T-Variant via bind (type-checks registry + field premises)
    @rule
    protected override variantProd(ctx: unknown): Parser<Type> {
        return seq(
            this.variantName,
            this.ws,
            char("("),
            this.ws,
            sepBy(this.atomProd(ctx), seq(this.ws, char(","), this.ws)),
            this.ws,
            char(")"),
        )
            .bind(([name, , , , args]) => {
                const argTypes = (args as Type[]) ?? []
                if (!this.variantPremisesHold(name as string, argTypes)) {
                    return empty<Type>()
                }
                return epsilon<Type>(this.variantCon(name as string, argTypes))
            })
    }

    /**
     * Check the T-Variant premises on already-parsed argument types. Returns
     * `true` iff the variant is declared, the arity matches, and every
     * argument is a subtype of its declared field type (recursive fields
     * against the DataType itself).
     */
    private variantPremisesHold(name: string, args: Type[]): boolean {
        const dataType = this.registry.lookupVariant(name)
        if (!dataType) return false // unknown variant
        const variant = dataType.findVariant(name)
        if (!variant) return false
        // Arity must match exactly — extra args are as ill-typed as missing ones.
        if (args.length !== variant.fields.length) return false
        for (let i = 0; i < variant.fields.length; i++) {
            const field = variant.fields[i]!
            const argType = args[i]
            if (argType === undefined) return false
            const expected = field.type instanceof FamilyType ? dataType : field.type
            if (!isSubtype(argType, expected)) return false
        }
        return true
    }

    /**
     * @ensures Progress: an observation on a codata value can step (E-Obs);
     * on a non-value, it can step (E-ObsArg). Progress holds.
     */
    @ensures(
        (_self: LCTypeCheck, _args: [Type, string], _old, result: Type) => isWellFormedType(result),
        { rule: "T-Obs", role: "conclusion", formula: "result : Gₖ(T)[α:=T]" },
    )
    protected obs(scrutinee: Type, observerName: string): Type {
        // T-Obs: Γ ⊢ e : T ⟹ Γ ⊢ e.oₖ : Gₖ(T)[α:=T]
        // Look up the observer in the registry to find its CodataType.
        // Premises (observer declared, scrutinee <: codata type) are enforced
        // in the `obsProd` override below — this action is only reached on the
        // verified path, so it computes the conclusion directly.
        const codataType = this.registry.lookupObserver(observerName)
        if (!codataType) return Any // unknown observer → ill-typed
        const observer = codataType.findObserver(observerName)
        if (!observer) return Any

        // Nothing propagation: observing an uninhabited scrutinee yields an
        // uninhabited result (principle of explosion). Checked after the
        // premises so a genuine type error is never masked.
        if (scrutinee instanceof NothingType) return Nothing

        // Result: Gₖ(T)[α:=T]. For continuation observers, the type is T itself.
        if (observer.isContinuation) {
            return codataType
        }
        return observer.type
    }

    // e.o  — T-Obs via bind (type-checks observer + scrutinee premises per observation)
    @rule
    protected override obsProd(ctx: unknown): Parser<Type> {
        return this.appProd(ctx)
            .bind((scrutineeType) =>
                seq(this.ws, char("."), this.ws, this.ident)
                    .map(([, , , obsName]) => obsName)
                    .many()
                    .bind((obsNames) => {
                        // Each observation in the chain e.o₁.o₂ is checked
                        // individually: the scrutinee of the next observation
                        // is the previous observation's result type.
                        let current: Type = scrutineeType
                        for (const obsName of obsNames) {
                            if (!this.obsPremiseHolds(current, obsName)) {
                                return empty<Type>()
                            }
                            current = this.obs(current, obsName)
                        }
                        return epsilon<Type>(current)
                    })
            )
    }

    /**
     * Check the T-Obs premises for one observation: the observer is declared
     * in the registry and the scrutinee type is a subtype of the observer's
     * codata type.
     */
    private obsPremiseHolds(scrutinee: Type, observerName: string): boolean {
        const codataType = this.registry.lookupObserver(observerName)
        if (!codataType) return false // unknown observer
        if (!codataType.findObserver(observerName)) return false
        return isSubtype(scrutinee, codataType)
    }

    /**
     * @ensures Progress: a fold on a variant value can step (E-Fold);
     * on a non-value, it can step (E-FoldArg). Progress holds.
     * @ensures Preservation: the result type σ is the join of all handler body types.
     */
    @ensures(
        (_self: LCTypeCheck, _args: [DataType, Type, unknown[], Type], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Fold", role: "conclusion", formula: "result : σ (join of handler body types)" },
    )
    protected fold(
        dataType: DataType,
        scrutinee: Type,
        handlers: { variantName: string; bindings: string[]; body: Type }[],
        _resultType: Type,
    ): Type {
        // T-Fold: Γ ⊢ e : T ∧ Γ ⊢ tᵢ : Fᵢ(σ)[α:=σ]→σ ⟹ Γ ⊢ fold [T] e {...} : σ
        //
        // Premise 1: scrutinee : T (scrutinee type must be a subtype of dataType)
        if (!isSubtype(scrutinee, dataType)) return Any // ill-typed

        // Premise 2: handlers must be exhaustive (cover all variants)
        const allVariants = dataType.allVariants()
        for (const variant of allVariants) {
            const handler = handlers.find((h) => h.variantName === variant.name)
            if (!handler) return Any // missing handler → ill-typed
        }

        // Premise 3: all handler body types must agree (infer σ)
        // σ is the join (least upper bound) of all handler body types.
        // This uses the lattice operation from TAPL §16.4 — the join finds
        // the smallest type that all handler bodies are subtypes of.
        if (handlers.length === 0) return Any

        // Nothing propagation: an eagerly-evaluated scrutinee of type Nothing
        // makes the fold uninhabited (principle of explosion). Checked after
        // the premises so a genuine type error is never masked.
        if (scrutinee instanceof NothingType) return Nothing

        let sigma = handlers[0]!.body
        for (let i = 1; i < handlers.length; i++) {
            sigma = join(sigma, handlers[i]!.body)
        }

        return sigma
    }

    // ── Fold with parseToFixpoint for circular attribute flow ─────────────────
    //
    // Override foldProd to capture handler body spans and use parseToFixpoint
    // to iteratively refine σ (the fold result type). This replaces the
    // Any-placeholder workaround: recursive fields are bound to the current
    // σ estimate, and σ is refined until convergence.

    // fold [T] e {Cᵢ(xⱼ) → tᵢ}  — T-Fold with parseToFixpoint
    @rule
    protected override foldProd(ctx: unknown): Parser<Type> {
        return seq(
            this.kw("fold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("]"),
            this.ws,
        ).bind(([, , , , ty]) => {
            // Premise: the annotation must be a DataType. A wrong-kind
            // annotation (e.g. `fold [Stream] ...`) rejects the branch
            // (`empty<Type>()`) like any other failed premise — an `assert`
            // here would throw out of the parse instead of rejecting it.
            if (!(ty instanceof DataType)) {
                return empty<Type>()
            }
            const dataType = ty
            return this.exprProd(ctx)
                .bind((scrutineeType) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.spanFoldHandlers(dataType, ctx as TypeCheckCtx)
                                .bind((spanHandlers) =>
                                    seq(this.ws, char("}"))
                                        .map(() =>
                                            this.evalFoldFixpoint(
                                                dataType,
                                                scrutineeType,
                                                spanHandlers,
                                            )
                                        )
                                        // T-Fold premises are checked inside
                                        // evalFoldFixpoint; a failure is
                                        // `undefined` — reject the branch.
                                        .bind((result) =>
                                            result === undefined
                                                ? empty<Type>()
                                                : epsilon<Type>(result)
                                        )
                                )
                        )
                )
        })
    }

    /** Parse fold handlers, capturing body spans for fixpoint iteration. */
    // Cᵢ(xⱼ) → tᵢ, ...  — fold handlers (span-captured for fixpoint)
    @rule
    protected spanFoldHandlers(
        dataType: DataType,
        ctx: TypeCheckCtx,
    ): Parser<{ variantName: string; bindings: string[]; bodySpan: Span; ctx: TypeCheckCtx }[]> {
        return sepBy(
            this.spanFoldHandler(dataType, ctx),
            seq(this.ws, char(","), this.ws),
        )
    }

    // Cᵢ(xⱼ) → tᵢ  — single fold handler (span-captured)
    @rule
    protected spanFoldHandler(
        dataType: DataType,
        ctx: TypeCheckCtx,
    ): Parser<{ variantName: string; bindings: string[]; bodySpan: Span; ctx: TypeCheckCtx }> {
        return seq(
            this.variantName,
            this.ws,
            char("("),
            this.ws,
            sepBy(this.ident, this.ws1),
            this.ws,
            char(")"),
            this.ws,
            this.arrow,
            this.ws,
        ).bind(([vName, , , , bindings]) => {
            const variant = dataType.findVariant(vName)
            if (!variant) {
                return empty<
                    { variantName: string; bindings: string[]; bodySpan: Span; ctx: TypeCheckCtx }
                >()
            }
            const bindingList = (bindings as string[] | undefined) ?? []
            // Build the handler context: non-recursive fields at their declared
            // types, Family fields at σ (initially the carrier — the fixpoint
            // rebinds Family fields to the current σ each iteration).
            let handlerCtx = ctx
            for (let i = 0; i < bindingList.length; i++) {
                const field = variant.fields[i]
                if (field) {
                    handlerCtx = new TypeCheckCtx(
                        handlerCtx.gamma.extend(
                            bindingList[i]!,
                            field.type instanceof FamilyType ? dataType : field.type,
                        ),
                        handlerCtx.delta,
                    )
                }
            }
            // Parse the body to capture the span (the type is discarded — it was
            // computed under the placeholder σ = Any)
            return this.exprProd(handlerCtx)
                .map((_body, span) => ({
                    variantName: vName,
                    bindings: bindingList,
                    bodySpan: { start: span.start, end: span.end },
                    ctx: handlerCtx,
                }))
        })
    }

    /**
     * Use parseToFixpoint to iteratively refine σ:
     * 1. Start with σ₀ = DataType (recursive fields' declared type)
     * 2. Re-parse each handler body under σₙ (recursive fields bound to σₙ)
     * 3. Compute σₙ₊₁ = join of all body types
     * 4. Repeat until σₙ₊₁ = σₙ
     *
     * State is passed as parameters (not instance fields) to support nested folds.
     */
    private evalFoldFixpoint(
        dataType: DataType,
        scrutineeType: Type,
        spanHandlers: {
            variantName: string
            bindings: string[]
            bodySpan: Span
            ctx: TypeCheckCtx
        }[],
    ): Type | undefined {
        // Premise 1: scrutinee : T
        if (!isSubtype(scrutineeType, dataType)) return undefined

        // Premise 2: handlers must be exhaustive
        const allVariants = dataType.allVariants()
        for (const variant of allVariants) {
            const handler = spanHandlers.find((h) => h.variantName === variant.name)
            if (!handler) return undefined
        }

        if (spanHandlers.length === 0) return undefined

        // Nothing propagation: an eagerly-evaluated scrutinee of type Nothing
        // makes the fold uninhabited (principle of explosion). Checked after
        // the premises so a genuine type error is never masked.
        if (scrutineeType instanceof NothingType) return Nothing

        // Use parseToFixpoint to refine σ
        // Start at the DataType itself (not Any) because recursive fields
        // have declared type = DataType. This gives a better initial estimate.
        //
        // A handler body that fails to re-parse under the refined σ is a
        // genuine ill-typedness: the recursion was valid under the previous
        // estimate but not under the refined one. A failed body poisons the
        // iteration (the failure flag below), and the fold is rejected after
        // the fixpoint converges — a failure must never be laundered into an
        // `Any` body type that silently satisfies the join.
        let reparseFailed = false
        const sigma = this.parseToFixpoint(
            dataType as Type, // σ₀ = DataType (recursive fields' declared type)
            (currentSigma: Type) => {
                // Re-parse each handler body under currentSigma
                // (recursive fields rebound to currentSigma)
                const bodyTypes: Type[] = []
                for (const handler of spanHandlers) {
                    // Rebuild context with recursive fields bound to currentSigma
                    const variant = dataType.findVariant(handler.variantName)
                    if (!variant) {
                        bodyTypes.push(Any)
                        continue
                    }
                    let handlerCtx = handler.ctx
                    for (let i = 0; i < handler.bindings.length; i++) {
                        const field = variant.fields[i]
                        if (field && field.type instanceof FamilyType) {
                            // Rebind Family fields to currentSigma
                            handlerCtx = new TypeCheckCtx(
                                handlerCtx.gamma.extend(handler.bindings[i]!, currentSigma),
                                handlerCtx.delta,
                            )
                        }
                    }
                    // Re-parse the handler body under the refined context
                    const results = [...this._forward(
                        this._input,
                        handler.bodySpan,
                        this.exprProd(handlerCtx),
                    )]
                    if (results.length === 0) {
                        reparseFailed = true
                        // Keep the join well-defined for the remaining
                        // iterations (Any is absorbent, so the sequence
                        // still converges monotonically); the flag discards
                        // the converged σ below.
                        bodyTypes.push(Any)
                    } else {
                        bodyTypes.push(results[0]!)
                    }
                }
                return bodyTypes
            },
            (a: Type, b: Type) => join(a, b), // lattice join
            (a: Type, b: Type) => a.equals(b), // fixpoint detection
        )
        if (reparseFailed) return undefined

        return sigma
    }

    /**
     * @ensures Progress: an unfold is always a value (codata value).
     * @ensures Preservation: the result type is the codata type T.
     */
    @ensures(
        (_self: LCTypeCheck, _args: [CodataType, Type, unknown[], Type], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Unfold", role: "conclusion", formula: "result : T" },
    )
    protected unfold(
        codataType: CodataType,
        seed: Type,
        generators: { observerName: string; body: Type }[],
        _seedType: Type,
    ): Type {
        // T-Unfold: Γ ⊢ s : Σ ∧ Γ ⊢ gⱼ : Σ→Gⱼ(Σ)[α:=Σ] ⟹ Γ ⊢ unfold [T] s {...} : T
        //
        // Premise 1: seed type is already computed (passed as seed).
        //   The seed type Σ is whatever the seed expression typed as.
        //   We don't enforce a specific seed type here — the generators
        //   are checked in the extended context with self: Σ.
        //
        // Premise 2 (generator exhaustiveness) is enforced in the
        // `unfoldProd` override below — this action is only reached on the
        // verified path, so it computes the conclusion directly.
        const allObservers = codataType.allObservers()
        for (const observer of allObservers) {
            const generator = generators.find((g) => g.observerName === observer.name)
            if (!generator) return Any // missing generator → ill-typed
        }

        // Nothing propagation: an eagerly-evaluated seed of type Nothing makes
        // the unfold uninhabited (principle of explosion). Checked after the
        // premises so a genuine type error is never masked.
        if (seed instanceof NothingType) return Nothing

        // The result type is T (the codata type from the annotation).
        return codataType
    }

    // unfold [T] s { o → t, ... }  — T-Unfold via bind (type-checks exhaustiveness
    // and each generator body against its observer's result type)
    @rule
    protected override unfoldProd(ctx: unknown): Parser<Type> {
        return seq(
            this.kw("unfold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("]"),
            this.ws,
        ).bind(([, , , , ty]) => {
            // Premise: the annotation must be a CodataType. A wrong-kind
            // annotation (e.g. `unfold [Nat] ...`) rejects the branch
            // (`empty<Type>()`) like any other failed premise — an `assert`
            // here would throw out of the parse instead of rejecting it.
            if (!(ty instanceof CodataType)) {
                return empty<Type>()
            }
            const codataType = ty
            return this.exprProd(ctx)
                .bind((seed) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            // The generator contexts are the base-shaped
                            // ones; the premise (body <: Gⱼ) is checked below
                            // via generatorBodiesHold.
                            this.typedUnfoldGenerators(codataType, ctx)
                                .bind((generators) => {
                                    if (!this.generatorsAreExhaustive(codataType, generators)) {
                                        return empty<Type>()
                                    }
                                    if (!this.generatorBodiesHold(codataType, generators)) {
                                        return empty<Type>()
                                    }
                                    return seq(this.ws, char("}"))
                                        .map(() => this.unfold(codataType, seed, generators, Any))
                                })
                        )
                )
        })
    }

    /**
     * Check T-Unfold's exhaustiveness premise: every observer of the codata
     * type must have a generator.
     */
    private generatorsAreExhaustive(
        codataType: CodataType,
        generators: { observerName: string; body: Type }[],
    ): boolean {
        return codataType.allObservers().every((observer) =>
            generators.some((g) => g.observerName === observer.name)
        )
    }

    /**
     * Check T-Unfold's generator premise on already-parsed bodies:
     * `Γ, self:T ⊢ gⱼ : Gⱼ(Σ)[α:=Σ]` — each generator body type must be a
     * subtype of its observer's result type. For a continuation observer the
     * result type is the codata type itself (the generator produces the next
     * codata value); for a plain observer it is the observer's declared type.
     */
    private generatorBodiesHold(
        codataType: CodataType,
        generators: { observerName: string; body: Type }[],
    ): boolean {
        return codataType.allObservers().every((observer) => {
            const generator = generators.find((g) => g.observerName === observer.name)
            if (!generator) return false // exhaustiveness handles this too
            return isSubtype(generator.body, observer.type)
        })
    }

    /**
     * Checker-local generator productions — mirror the base `unfoldGenerators`
     * pair (same signatures, so `unfoldProd` can call them from inside its
     * bind). They exist so the generator premise is enforceable: the result
     * premise (`body <: Gⱼ`) is enforced in `unfoldProd` via
     * `generatorBodiesHold`.
     *
     * `self` binds to the codata type being constructed — the corecursive
     * reading: a generator body's `self` refers to the codata value being
     * produced, so `tail -> self` (the canonical producer) types as the
     * codata type and satisfies the continuation-observer premise, while a
     * body producing a wrong-typed value (`tail -> Zero()`) fails the premise.
     */
    // o → t, ...  — T-Unfold generators (premise-checked in unfoldProd)
    @rule
    protected typedUnfoldGenerators(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<{ observerName: string; body: Type }[]> {
        return sepBy(
            this.typedUnfoldGenerator(codataType, ctx),
            seq(this.ws, char(","), this.ws),
        )
    }

    // o → t  — single T-Unfold generator (self: the codata type under construction)
    @rule
    protected typedUnfoldGenerator(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<{ observerName: string; body: Type }> {
        return seq(
            this.ident,
            this.ws,
            this.arrow,
            this.ws,
        ).bind(([obsName]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty<{ observerName: string; body: Type }>()
            }
            // self:T — the codata value this unfold constructs (corecursion).
            const extendedCtx = this.extendCtx(ctx, "self", codataType)
            return this.exprProd(extendedCtx)
                .map((body) => ({ observerName: obsName, body }))
        })
    }

    // ── T-TAbs: Δ, α <: σ ⊢ t : τ ⟹ Δ ⊢ Λα<:σ.t : ∀α<:σ.τ ────────────────────

    /**
     * Type abstraction. The body type τ is computed under the (unchanged) Γ.
     * The result is ∀α<:σ.τ, represented as FunType(bound, body) for now.
     */
    @ensures(
        (_self: LCTypeCheck, _args: [string, Type, Type], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-TAbs", role: "conclusion", formula: "result : ∀α<:σ.τ" },
    )
    protected typeAbs(tyVar: string, bound: Type, body: Type): Type {
        // ∀α<:σ.τ — a bounded polymorphic type.
        return new PolymorphicType(tyVar, bound, body)
    }

    // ── T-Cofold: Γ ⊢ e : T ∧ Γ ⊢ t : Πⱼ(Gⱼ(σ)[α:=σ])→σ ⟹ Γ ⊢ cofold [T] e {...} : σ ─

    /**
     * Cofold (codata elimination). The handler receives all observations
     * and produces σ. For now, we return the handler body type as σ.
     */
    @ensures(
        (_self: LCTypeCheck, _args: [CodataType, Type, unknown, Type], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Cofold", role: "conclusion", formula: "result : σ" },
    )
    protected cofold(
        _codataType: CodataType,
        scrutinee: Type,
        handler: { observerName: string; bindings: string[]; body: Type },
        _resultType: Type,
    ): Type {
        // Premise (scrutinee <: codata type) is enforced in the `cofoldProd`
        // override below — this action is only reached on the verified path,
        // so it computes the conclusion directly.

        // Nothing propagation: an eagerly-evaluated scrutinee of type Nothing
        // makes the cofold uninhabited (principle of explosion). Checked after
        // the premises so a genuine type error is never masked.
        if (scrutinee instanceof NothingType) return Nothing

        // The handler body type is σ.
        return handler.body
    }

    // cofold [T] e { o(x) → t }  — T-Cofold via bind (type-checks scrutinee premise)
    @rule
    protected override cofoldProd(ctx: unknown): Parser<Type> {
        return seq(
            this.kw("cofold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("]"),
            this.ws,
        ).bind(([, , , , ty]) => {
            // Premise: the annotation must be a CodataType. A wrong-kind
            // annotation (e.g. `cofold [Nat] ...`) rejects the branch
            // (`empty<Type>()`) like any other failed premise — an `assert`
            // here would throw out of the parse instead of rejecting it.
            if (!(ty instanceof CodataType)) {
                return empty<Type>()
            }
            const codataType = ty
            return this.exprProd(ctx)
                .bind((scrutinee) => {
                    if (!isSubtype(scrutinee, codataType)) {
                        return empty<Type>()
                    }
                    return seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.cofoldHandler(codataType, ctx)
                                .bind((handler) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.cofold(codataType, scrutinee, handler, Any))
                                )
                        )
                })
        })
    }

    // ── T-TApp: Γ ⊢ t : ∀α<:σ.τ ∧ Δ ⊢ T₂<:σ ⟹ Γ ⊢ t[T₂] : τ[α:=T₂] ───────────

    /**
     * Type application. The premises (body is a polymorphic type; argument
     * type is a subtype of the bound) are enforced in the `typeAppProd`
     * override — `@requires` is declarative metadata for the rule model,
     * not a runtime check. The result is the body type with α := T₂
     * (type substitution).
     *
     * The `@requires` premise is therefore purely declarative: this method
     * is only reached after the `typeAppProd` override has checked the
     * premises, so the cast below is safe. The decorator is kept because it
     * feeds the rule model (`Grammar.rules`, asserted in
     * `test/metadata.test.ts`).
     */
    @requires(
        (_self: LCTypeCheck, body: Type, argType: Type) =>
            body instanceof PolymorphicType && isSubtype(argType, body.bound),
        { rule: "T-TApp", role: "premise", formula: "body : ∀α<:σ.τ  ∧  T₂ <: σ" },
    )
    @ensures(
        (_self: LCTypeCheck, _args: [Type, Type], _old, result: Type) => isWellFormedType(result),
        { rule: "T-TApp", role: "conclusion", formula: "result : τ[α:=T₂]" },
    )
    protected typeApp(body: Type, argType: Type): Type {
        // Substitute T₂ for α in τ. For now, this is type erasure —
        // the body type is already computed, so we return the body
        // with the type variable substituted.
        const poly = body as PolymorphicType
        return substituteTypeVar(poly.body, poly.typeVarName, argType)
    }

    // ── T-Op: Ω(op) = σ₁→...→σₙ→τ  ∧  Γ ⊢ tᵢ : σᵢ  ⟹  Γ ⊢ op(t₁,...,tₙ) : τ ────

    /**
     * The signature/definition well-formedness checker for `OpRegistry.declare`
     * (lc.md §2.4): an operation's definition must type as
     * `paramTypes → resultType` before it enters Ω.
     *
     * Injected by the caller because the registry cannot check this itself
     * (`ops.ts` importing this module would be a cycle through `grammar.ts`).
     * This is what makes T-Op's trust in `resultType` sound: E-Op executes the
     * raw `definition`, so an unvalidated mismatch would type-check as one
     * type and evaluate as another — a Preservation violation through Ω.
     * Every entry the grammar reads is a `CheckedOpSig`; this check is the
     * only producer of those.
     */
    readonly opWellFormedness: OpWellFormedness = {
        checkDefinition: (op: OpSig): string | undefined => {
            // The definition must be a curried function over the declared
            // parameters, returning the declared result type: peel one
            // FunType layer per parameter, then check the body against
            // resultType (up to subsumption — T-Sub at the result).
            const defType = this.typeCheckSource(op.definition)
            if (defType === undefined) {
                return `definition does not type-check: "${op.definition}"`
            }
            let def = defType
            for (const _ of op.paramTypes) {
                if (!(def instanceof FunType)) {
                    return "definition is not a function of the declared arity"
                }
                def = def.result
            }
            if (!isSubtype(def, op.resultType)) {
                return `definition returns ${def}, which is not <: ${op.resultType}`
            }
            return undefined
        },
    }

    /**
     * Type-check a standalone LC source fragment (used by
     * `opWellFormedness` to check an operation's definition). Returns the
     * type, or `undefined` when the source does not type-check.
     */
    private typeCheckSource(source: string): Type | undefined {
        const results = [...this.parseWith(source, new TypeEnv())]
        if (results.length !== 1) {
            return undefined
        }
        return results[0]
    }

    /**
     * Named operation application (lc.md §5.8 T-Op). The premises — the
     * operation is declared in Ω, the arity matches, and each argument type is
     * a subtype of the declared parameter type — are enforced in the
     * `opProd` override (the production path); `@requires` is declarative
     * metadata for the rule model, like the other premise-enforcing
     * overrides (`letProd`, `typeAppProd`).
     *
     * Nothing propagation: an eagerly-evaluated argument of type Nothing makes
     * the application uninhabited (principle of explosion). Checked after the
     * premises so a genuine type error is never masked.
     */
    @requires(
        (_self: LCTypeCheck, opName: string, args: Type[]) =>
            _self.opRegistry.lookup(opName) !== undefined &&
            _self.opRegistry.lookup(opName)!.paramTypes.length === args.length,
        { rule: "T-Op", role: "premise", formula: "Ω(op) = σ₁→...→σₙ→τ  ∧  arity matches" },
    )
    @ensures(
        (_self: LCTypeCheck, _args: [string, Type[]], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Op", role: "conclusion", formula: "result : τ" },
    )
    protected opApp(opName: string, args: Type[]): Type {
        const opSig = this.opRegistry.lookup(opName)
        if (!opSig) return Any // unknown op → ill-typed (unreachable via opProd's gate)

        // Premise: arity must match exactly.
        if (args.length !== opSig.paramTypes.length) return Any

        // Premise: each argument type must be a subtype of the declared
        // parameter type. A Nothing argument is tracked and propagated after
        // the loop so a genuine premise violation on a later arg is not
        // silently subsumed by Nothing (the variantCon pattern).
        let hasNothingArg = false
        for (let i = 0; i < args.length; i++) {
            const argType = args[i]
            if (argType === undefined) return Any
            if (argType instanceof NothingType) hasNothingArg = true
            if (!isSubtype(argType, opSig.paramTypes[i]!)) return Any
        }

        // Nothing propagation (principle of explosion).
        if (hasNothingArg) return Nothing

        return opSig.resultType
    }

    // ── Override opProd to enforce T-Op premises in the production path ───────

    /**
     * Override `opProd` to enforce the T-Op premises in the production path:
     * parse the arguments, check arity and argument types against the
     * signature, and only then commit `opApp`'s conclusion. A failed premise
     * returns `empty<Type>()` (ill-typed — empty parse forest), the same
     * rejection semantics as the `letProd` and `typeAppProd` overrides.
     *
     * The base `opApp` action remains the rule-model conclusion (its
     * `@requires`/`@ensures` contracts feed `collectRules`); the premises are
     * enforced here because `@requires` is declarative metadata, not a
     * runtime check.
     */
    // op(t₁, ..., tₙ)  — T-Op via bind (type-checks signature premises)
    @rule
    protected override opProd(ctx: unknown): Parser<Type> {
        return seq(
            this.opIdent,
            char("("),
            this.ws,
        ).bind(([opName]) => {
            const opSig = this.opRegistry.lookup(opName)
            if (!opSig) {
                return empty<Type>()
            }
            return sepBy(this.atomProd(ctx), seq(this.ws, char(","), this.ws))
                .bind((args) =>
                    seq(this.ws, char(")"))
                        .map(() => this.checkOpPremises(opSig, args))
                )
                .bind((result) => result === undefined ? empty<Type>() : epsilon<Type>(result))
        })
    }

    /**
     * Check the T-Op premises on already-parsed argument types. Returns the
     * conclusion type, or `undefined` when a premise fails (the production
     * turns that into an empty parse forest — ill-typed).
     */
    private checkOpPremises(opSig: OpSig, args: Type[]): Type | undefined {
        // Premise: arity must match exactly.
        if (args.length !== opSig.paramTypes.length) return undefined

        let hasNothingArg = false
        for (let i = 0; i < args.length; i++) {
            const argType = args[i]
            if (argType === undefined) return undefined
            if (argType instanceof NothingType) hasNothingArg = true
            if (!isSubtype(argType, opSig.paramTypes[i]!)) return undefined
        }

        // Nothing propagation (principle of explosion) — checked after the
        // premises so a genuine type error is never masked.
        if (hasNothingArg) return Nothing

        return this.opApp(opSig.name, args)
    }

    // ── Override appProd for type checking via bind ──────────────────────────

    /**
     * Override application to type-check via bind:
     * parse fn → get fnType; parse arg → get argType;
     * if fnType is FunType and argType <: fnType.param,
     * return ε(fnType.result), else ∅ (empty — ill-typed).
     */
    // t u  — T-App via bind (type-checks domain match)
    @rule
    protected override appProd(ctx: unknown): Parser<Type> {
        return or(
            this.appProd(ctx)
                .map((fnTy) => ({ fnTy }))
                .bind(({ fnTy }) =>
                    seq(this.ws1, this.typeAppProd(ctx))
                        .map(([, argTy]) => ({ fnTy, argTy }))
                        .bind(({ fnTy, argTy }) => {
                            if (!(fnTy instanceof FunType) || !isSubtype(argTy, fnTy.param)) {
                                return empty<Type>()
                            }
                            return epsilon<Type>(fnTy.result)
                        })
                ),
            this.typeAppProd(ctx),
        )
    }

    // ── Override typeAppProd to enforce the T-TApp premises ───────────────────

    /**
     * Override type application to enforce the T-TApp premises in the
     * production path: parse atom → get bodyType; parse [τ] → get argType;
     * if bodyType is a PolymorphicType and argType <: bodyType.bound,
     * return ε(τ[α:=argType]), else ∅ (empty — ill-typed).
     *
     * The base production folds over `many()` without checking, so a failed
     * premise fell through to `typeApp`, which cast the body and read `.body`
     * off a non-polymorphic type — putting `undefined` in the parse forest.
     * The `@requires` premise is declarative metadata (for the rule model),
     * not a runtime check, so the premise is enforced here instead.
     *
     * The bind formulation is left-recursive (`typeAppProd` calls itself
     * via `this`), which the lang-forma engine resolves — the same shape as the
     * `appProd` override above. Each application in `t[τ₁][τ₂]` is checked
     * individually.
     */
    // t [τ]  — T-TApp via bind (type-checks polymorphic body + bound)
    @rule
    protected override typeAppProd(ctx: unknown): Parser<Type> {
        return or(
            this.typeAppProd(ctx)
                .map((bodyTy) => ({ bodyTy }))
                .bind(({ bodyTy }) =>
                    seq(
                        this.ws,
                        char("["),
                        this.ws,
                        this.typeProd(this.typeVarCtx(ctx)),
                        this.ws,
                        char("]"),
                    )
                        .map(([, , , argTy]) => ({ bodyTy, argTy }))
                        .bind(({ bodyTy, argTy }) => {
                            if (
                                !(bodyTy instanceof PolymorphicType) ||
                                !isSubtype(argTy, bodyTy.bound)
                            ) {
                                return empty<Type>()
                            }
                            return epsilon<Type>(this.typeApp(bodyTy, argTy))
                        })
                ),
            this.atomProd(ctx),
        )
    }

    // ── Override letProd to enforce T-Let premise 1 ───────────────────────────

    /**
     * Override `letProd` to enforce T-Let premise 1 (def type <: declared
     * type) in the production path. The base production parses the def, then
     * the body under the extended context, and calls `let_`. But `@requires`
     * is declarative metadata only (not a runtime check), so the premise
     * must be enforced here.
     *
     * After parsing the def and getting its type σ, we check `isSubtype(σ, τ)`
     * where τ is the declared type. If the check fails, we return
     * `empty<Type>()` (ill-typed — empty parse forest). If it passes, the
     * body is parsed under Γ + x:τ (the declared type, widened via
     * subsumption), and `let_` returns the body type.
     *
     * This is the subsumption site for let-bindings: `let x:τ = (e : σ)`
     * where `σ <: τ` is accepted. Subsumption is implicit — no standalone
     * T-Sub production; each consumer site checks `isSubtype` in its own
     * premise.
     */
    // let x:τ = t in u  — T-Let via bind (type-checks def <: declared)
    @rule
    protected override letProd(ctx: unknown): Parser<Type> {
        return seq(
            this.kw("let"),
            this.ws1,
            this.ident,
            this.ws,
            char(":"),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("="),
            this.ws,
        ).bind(([, , name, , , , ty]) => {
            return this.exprProd(ctx)
                .map((def) => ({ name, ty, def }))
                .bind(({ name, ty, def }) => {
                    // T-Let premise 1: def type σ must be <: declared type τ
                    if (!isSubtype(def, ty)) return empty<Type>()
                    return seq(this.ws1, this.kw("in"), this.ws1)
                        .bind(() =>
                            this.exprProd(this.extendCtx(ctx, name, ty))
                                .map((body) => this.let_(name, ty, def, body))
                        )
                })
        })
    }

    /**
     * A matched token types as the pattern-matched type it inhabits
     * (lc.md §5.1 T-Token: the sole inhabitant of a `PatternDataType`).
     *
     * The premise `p ∈ registry ∧ p is a PatternDataType` is enforced by the
     * base `patternTokenProd`'s gate — the branch is only taken when the
     * lookup yields a `PatternDataType`, so a violation here is a caller
     * bug, not an input error: it fails LOUDLY (`assert`) rather than
     * degrading to `Any`. A silent `Any` would type an unregistered token,
     * and under an `Any` annotation the wrong type satisfies S-Refl — the
     * same absorption shape the variantProd override closes for T-Variant.
     */
    protected matchedToken(dataTypeName: string, _text: string): Type {
        const resolved = this.registry.lookup(dataTypeName)
        assert(
            resolved instanceof PatternDataType,
            `matchedToken premise violated: "${dataTypeName}" does not resolve to a registered PatternDataType — the token gate (patternTokenProd) must be consulted before this action`,
        )
        return resolved
    }
}
