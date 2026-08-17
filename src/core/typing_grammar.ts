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
 * Typing rules (lc.md §5):
 *
 *   T-Var:      x:σ ∈ Γ  ⟹  Γ ⊢ x : σ
 *   T-Abs:      Γ, x:σ ⊢ t : τ  ⟹  Γ ⊢ λx:σ.t : σ → τ
 *   T-App:      Γ ⊢ t : σ→τ  ∧  Γ ⊢ u : σ  ⟹  Γ ⊢ t u : τ
 *   T-Let:      Γ ⊢ t : σ  ∧  Γ, x:σ ⊢ u : τ  ⟹  Γ ⊢ let x:σ=t in u : τ
 *   T-Variant:  Γ ⊢ tⱼ : Fₖ(T)[α:=T]  ⟹  Γ ⊢ Cₖ(tⱼ) : T
 *   T-Fold:     Γ ⊢ e : T  ∧  Γ ⊢ tᵢ : Fᵢ(σ)[α:=σ]→σ  ⟹  Γ ⊢ fold [T] e {...} : σ
 *   T-Obs:      Γ ⊢ e : T  ⟹  Γ ⊢ e.oₖ : Gₖ(T)[α:=T]
 *   T-Unfold:   Γ ⊢ s : Σ  ∧  Γ ⊢ gⱼ : Σ→Gⱼ(Σ)[α:=Σ]  ⟹  Γ ⊢ unfold [T] s {...} : T
 *   T-Cofold:   Γ ⊢ e : T  ∧  Γ ⊢ t : Πⱼ(Gⱼ(σ)[α:=σ])→σ  ⟹  Γ ⊢ cofold [T] e {...} : σ
 *   T-TAbs:     Δ, α<:σ ⊢ t : τ  ⟹  Δ ⊢ Λα<:σ.t : ∀α<:σ.τ
 *   T-TApp:     Γ ⊢ t : ∀α<:σ.τ  ∧  Δ ⊢ T₂<:σ  ⟹  Γ ⊢ t[T₂] : τ[α:=T₂]
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
    FunType,
    IntersectionType,
    NothingType,
    PatternDataType,
    PolymorphicType,
    TokenType,
    type Type,
    TypeEnv,
    TypeVar,
} from "./types.ts"

import { AbstractLC, type LCShape } from "./grammar.ts"

import { isSubtype, join } from "./subtyping.ts"

// ── Shape for type checking ───────────────────────────────────────────────────

interface TypeCheckShape extends LCShape {
    expr: Type
    atom: Type
    type: Type
}

// ── Well-formedness check for @ensures ────────────────────────────────────────

/**
 * Substitute `replacement` for type variable `varName` in `type`.
 * Used by T-TApp to compute τ[α := T₂].
 */
function substituteTypeVar(type: Type, varName: string, replacement: Type): Type {
    if (type instanceof TypeVar) {
        return type.name === varName ? replacement : type
    }
    if (type instanceof FunType) {
        return new FunType(
            substituteTypeVar(type.param, varName, replacement),
            substituteTypeVar(type.result, varName, replacement),
        )
    }
    if (type instanceof PolymorphicType) {
        // Shadowing: if the polymorphic type binds the same variable name,
        // don't substitute inside its body (α is shadowed).
        if (type.typeVarName === varName) return type
        return new PolymorphicType(
            type.typeVarName,
            substituteTypeVar(type.bound, varName, replacement),
            substituteTypeVar(type.body, varName, replacement),
        )
    }
    if (type instanceof IntersectionType) {
        return new IntersectionType(
            substituteTypeVar(type.left, varName, replacement),
            substituteTypeVar(type.right, varName, replacement),
        )
    }
    // DataType, CodataType, PatternDataType, TokenType, AnyType, NothingType:
    // no type variables inside (they are ground types)
    return type
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
            t instanceof PolymorphicType)
}

// ── Inference rule generation ─────────────────────────────────────────────────

/** A formal inference rule generated from contract metadata. */
export interface InferenceRule {
    /** Rule name (e.g., "T-App"). */
    name: string
    /** Premise formulas (from @requires metadata). */
    premises: string[]
    /** Conclusion formula (from @ensures metadata). */
    conclusion: string
    /** The grammar production method that implements this rule. */
    production: string
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
    /** The source text, stored for `parseToFixpoint` re-parsing of fold handler bodies. */
    private _input: string = ""

    /**
     * Generate inference rules from contract metadata.
     * Walks `Grammar.metadata` (via `Symbol.metadata`) and collects all
     * `@requires`/`@ensures` with `rule` metadata into structured rules.
     */
    toInference(): InferenceRule[] {
        const meta = LCTypeCheck.metadata
        const rules = new Map<string, InferenceRule>()

        for (const [method, report] of Object.entries(meta.methods)) {
            for (const req of report.requires) {
                const ruleName = req.meta?.rule as string | undefined
                if (!ruleName) continue
                const entry = rules.get(ruleName) ??
                    { name: ruleName, premises: [], conclusion: "", production: method }
                if (req.meta?.formula) entry.premises.push(req.meta.formula as string)
                rules.set(ruleName, entry)
            }
            for (const ens of report.ensures) {
                const ruleName = ens.meta?.rule as string | undefined
                if (!ruleName) continue
                const entry = rules.get(ruleName) ??
                    { name: ruleName, premises: [], conclusion: "", production: method }
                if (ens.meta?.formula) entry.conclusion = ens.meta.formula as string
                rules.set(ruleName, entry)
            }
        }

        return [...rules.values()]
    }

    /**
     * Parse and type-check input under `gamma`.
     * Returns the set of possible types (usually one; empty = ill-typed).
     */
    parseWith(input: string, gamma: TypeEnv): Set<Type> {
        this._input = input
        return this._parseWith(input, this.exprProd(gamma))
    }

    override start(): Parser<Type> {
        return this.exprProd(new TypeEnv())
    }

    // ── Context extension: extend Γ with x:σ ─────────────────────────────────

    protected override extendCtx(ctx: unknown, name: string, type: Type): unknown {
        if (ctx instanceof TypeEnv) {
            return ctx.extend(name, type)
        }
        return ctx
    }

    // NOTE: foldFieldType is NOT overridden here. The foldProd override below
    // uses spanFoldHandler (which binds fields to field.type directly) and
    // parseToFixpoint for circular attribute flow. The base foldProd (which
    // calls foldFieldType) is never reached because foldProd is overridden.

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
     * domain matches arg's type) is checked via @requires.
     * On failed premise, @requires returns undefined → the calling chain
     * produces empty() → the ill-typed branch is rejected.
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

    // ── T-Let: Γ ⊢ t : σ  ∧  Γ, x:σ ⊢ u : τ  ⟹  Γ ⊢ let x:σ=t in u : τ ────────

    /**
     * @ensures Progress: let can always step (E-Let) if the value is not yet a
     * value, or is a value after evaluation. The result type is the body type.
     */
    @ensures(
        (_self: LCTypeCheck, _args: [string, Type, Type, Type], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Let", role: "conclusion", formula: "result : τ" },
    )
    protected let_(_name: string, _type: Type, _def: Type, body: Type): Type {
        // The body type τ was computed under Γ + x:σ.
        return body
    }

    // ── T-Var: Γ(x) = σ  ⟹  Γ ⊢ x : σ ────────────────────────────────────────

    /**
     * Variable typing rule. @requires: name must be bound in ctx.
     * On failure, returns undefined → empty parse forest (ill-typed).
     *
     * @ensures Progress: a variable in a closed term is always substituted
     * before evaluation, so it can always step (or is already a value).
     */
    @requires(
        (_self: LCTypeCheck, name: string, ctx: unknown) =>
            ctx instanceof TypeEnv && ctx.lookup(name) !== undefined,
        { rule: "T-Var", role: "premise", formula: "x : σ ∈ Γ" },
    )
    @ensures(
        (_self: LCTypeCheck, _args: [string, unknown], _old, result: Type) =>
            isWellFormedType(result),
        { rule: "T-Var", role: "conclusion", formula: "result : σ" },
    )
    protected varRef(name: string, ctx: unknown): Type {
        return (ctx as TypeEnv).lookup(name) as Type
    }

    protected paren(e: Type): Type {
        return e
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

        // Check each arg type is a subtype of the expected field type.
        // For recursive fields, the expected type is the DataType itself.
        for (let i = 0; i < variant.fields.length; i++) {
            const field = variant.fields[i]!
            const argType = args[i]
            if (argType === undefined) return Any
            const expected = field.isRecursive ? dataType : field.type
            if (!isSubtype(argType, expected)) return Any
        }
        return dataType
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
        const codataType = this.registry.lookupObserver(observerName)
        if (!codataType) return Any // unknown observer → ill-typed
        const observer = codataType.findObserver(observerName)
        if (!observer) return Any

        // Premise: scrutinee must be a subtype of the codata type.
        if (!isSubtype(scrutinee, codataType)) return Any

        // Result: Gₖ(T)[α:=T]. For continuation observers, the type is T itself.
        if (observer.isContinuation) {
            return codataType
        }
        return observer.type
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
            this.typeProd,
            this.ws,
            char("]"),
            this.ws,
        ).chain(([, , , , ty]) => {
            assert(ty instanceof DataType, "fold type must be a DataType")
            const dataType = ty as DataType
            return this.exprProd(ctx)
                .chain((scrutineeType) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.spanFoldHandlers(dataType, ctx as TypeEnv)
                                .chain((spanHandlers) =>
                                    seq(this.ws, char("}"))
                                        .map(() =>
                                            this.evalFoldFixpoint(
                                                dataType,
                                                scrutineeType,
                                                spanHandlers,
                                            )
                                        )
                                )
                                .map(([, result]) => result)
                        )
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        }).map(([, result]) => result)
    }

    /** Parse fold handlers, capturing body spans for fixpoint iteration. */
    // Cᵢ(xⱼ) → tᵢ, ...  — fold handlers (span-captured for fixpoint)
    @rule
    protected spanFoldHandlers(
        dataType: DataType,
        ctx: TypeEnv,
    ): Parser<{ variantName: string; bindings: string[]; bodySpan: Span; ctx: TypeEnv }[]> {
        return sepBy(
            this.spanFoldHandler(dataType, ctx),
            seq(this.ws, char(","), this.ws),
        )
    }

    // Cᵢ(xⱼ) → tᵢ  — single fold handler (span-captured)
    @rule
    protected spanFoldHandler(
        dataType: DataType,
        ctx: TypeEnv,
    ): Parser<{ variantName: string; bindings: string[]; bodySpan: Span; ctx: TypeEnv }> {
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
        ).chain(([vName, , , , bindings]) => {
            const variant = dataType.findVariant(vName)
            if (!variant) {
                return empty() as unknown as Parser<
                    { variantName: string; bindings: string[]; bodySpan: Span; ctx: TypeEnv }
                >
            }
            const bindingList = (bindings as string[] | undefined) ?? []
            // Build the handler context with non-recursive fields at their declared types
            // and recursive fields at σ (initially Any — will be refined by parseToFixpoint)
            let handlerCtx = ctx
            for (let i = 0; i < bindingList.length; i++) {
                const field = variant.fields[i]
                if (field) {
                    handlerCtx = handlerCtx.extend(bindingList[i]!, field.type)
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
        }).map(([, result]) => result)
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
        spanHandlers: { variantName: string; bindings: string[]; bodySpan: Span; ctx: TypeEnv }[],
    ): Type {
        // Premise 1: scrutinee : T
        if (!isSubtype(scrutineeType, dataType)) return Any

        // Premise 2: handlers must be exhaustive
        const allVariants = dataType.allVariants()
        for (const variant of allVariants) {
            const handler = spanHandlers.find((h) => h.variantName === variant.name)
            if (!handler) return Any
        }

        if (spanHandlers.length === 0) return Any

        // Use parseToFixpoint to refine σ
        // Start at the DataType itself (not Any) because recursive fields
        // have declared type = DataType. This gives a better initial estimate.
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
                        if (field && field.isRecursive) {
                            // Rebind recursive field to currentSigma
                            handlerCtx = handlerCtx.extend(handler.bindings[i]!, currentSigma)
                        }
                    }
                    // Re-parse the handler body under the refined context
                    const results = [...this._forward(
                        this._input,
                        handler.bodySpan,
                        this.exprProd(handlerCtx),
                    )]
                    if (results.length === 0) {
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
        _seed: Type,
        generators: { observerName: string; body: Type }[],
        _seedType: Type,
    ): Type {
        // T-Unfold: Γ ⊢ s : Σ ∧ Γ ⊢ gⱼ : Σ→Gⱼ(Σ)[α:=Σ] ⟹ Γ ⊢ unfold [T] s {...} : T
        //
        // Premise 1: seed type is already computed (passed as _seed).
        //   The seed type Σ is whatever the seed expression typed as.
        //   We don't enforce a specific seed type here — the generators
        //   are checked in the extended context with self: Σ.
        //
        // Premise 2: generators must be exhaustive (cover all observers)
        const allObservers = codataType.allObservers()
        for (const observer of allObservers) {
            const generator = generators.find((g) => g.observerName === observer.name)
            if (!generator) return Any // missing generator → ill-typed
        }

        // The result type is T (the codata type from the annotation).
        return codataType
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
        _scrutinee: Type,
        _handler: { observerName: string; bindings: string[]; body: Type },
        _resultType: Type,
    ): Type {
        // Premise: scrutinee must be a subtype of the codata type.
        // The handler body type is σ.
        // For now, return the handler body type.
        return _handler.body
    }

    // ── T-TApp: Γ ⊢ t : ∀α<:σ.τ ∧ Δ ⊢ T₂<:σ ⟹ Γ ⊢ t[T₂] : τ[α:=T₂] ───────────

    /**
     * Type application. The body must have a polymorphic type (`PolymorphicType`).
     * The argument type must be a subtype of the bound. The result is the
     * body type with α := T₂ (type substitution).
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

    // ── Override appProd for type checking via chain ──────────────────────────

    /**
     * Override application to type-check via chain:
     * parse fn → get fnType; parse arg → get argType;
     * if fnType is FunType and argType <: fnType.param,
     * return ε(fnType.result), else ∅ (empty — ill-typed).
     */
    // t u  — T-App via chain (type-checks domain match)
    @rule
    protected override appProd(ctx: unknown): Parser<Type> {
        return or(
            this.appProd(ctx)
                .map((fnTy) => ({ fnTy }))
                .chain(({ fnTy }) =>
                    seq(this.ws1, this.typeAppProd(ctx))
                        .map(([, argTy]) => ({ fnTy, argTy }))
                        .chain(({ fnTy, argTy }) => {
                            if (!(fnTy instanceof FunType) || !isSubtype(argTy, fnTy.param)) {
                                return empty() as unknown as Parser<Type>
                            }
                            return epsilon<Type>(fnTy.result)
                        })
                        .map(([, result]) => result)
                )
                .map(([, result]) => result),
            this.typeAppProd(ctx) as unknown as Parser<Type>,
        )
    }
}
