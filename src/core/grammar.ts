/**
 * LC Grammar — the concrete syntax of the Lapis Core Calculus.
 *
 * This is NOT the Lapis surface syntax. It is a minimal notation for LC terms,
 * suitable as an executable spec, test input, and potential IR.
 *
 * Concrete syntax:
 *
 *   Types:    σ ::= Ident                    type name (Stack, Stream, Int, ...)
 *             | σ → σ                        function type
 *             | ( σ )                        parenthesized
 *
 *   Terms:    t ::= \x:σ. t                  lambda
 *             | ^α <: σ. t                   type abstraction (Λα <: σ. t)
 *             | let x:σ = t in t             let-binding
 *             | fold [σ] t {handlers}        fold (catamorphism)
 *             | fold [σ] t {patternHandlers} pattern-matched fold (T/E-FoldMatch)
 *             | unfold [σ] t {generators}    unfold (anamorphism)
 *             | cofold [σ] t {handler}       cofold (codata elimination)
 *             | t t                          application (left-assoc)
 *             | t . Ident                    observation (postfix)
 *             | t [σ]                        type application (postfix)
 *             | Ident                        variable
 *             | Ident (args)                 variant construction
 *             | ident (args)                 named operation application
 *             | match("p")                   pattern-matched construction
 *             | ( t )                        parenthesized
 *
 *   Handlers: C(x₁ x₂ ...) → t              fold handler (variant + bindings)
 *
 *   Pattern handler: match("pᵢ") → t         pattern-matched fold handler
 *                                            (no binding position — the body
 *                                            references `match : Token`)
 *
 *   Generators: o → t                        unfold generator (observer + body)
 *
 *   Cofold handler: o(x₁ x₂ ...) → t         cofold handler (observer + bindings)
 *
 * Productions:
 *
 *   exprProd      = lambdaProd | typeAbsProd | letProd | patternFoldProd
 *                 | foldProd | unfoldProd | cofoldProd | obsProd
 *   obsProd       = appProd ( "." ident | "[" type "]" )*
 *   appProd       = typeAppProd ( ws1 typeAppProd )*
 *   typeAppProd   = atomProd ( "[" type "]" )*
 *   atomProd      = "(" expr ")" | variantName "(" args ")" | opProd | patternToken
 *                 | patternMatchProd | ident
 *   opProd        = ident "(" args ")"   (registry-gated; tight paren — no ws)
 *   patternMatchProd = "match" "(" patternString ")"  (registry-gated; tight paren)
 *   patternString = '"' patternChar* '"'    (the quoted pattern source)
 *   typeProd      = atomType ( "→" typeProd )?
 *   atomType      = "(" type ")" | typeName
 *
 * An abstract grammar declares the shared structure (productions), and concrete
 * subclasses implement semantic actions (type checker, evaluator).
 *
 * See _docs/theory/lc.md for the formal specification.
 */

import {
    assert,
    char,
    empty,
    epsilon,
    Grammar,
    invariant,
    literal,
    or,
    type Parser,
    pred,
    rule,
    sepBy,
    seq,
} from "@lapis-lang/lang-forma"

import {
    Any,
    CodataType,
    DataType,
    Field,
    FunType,
    Nothing,
    PatternDataType,
    Token,
    type Type,
    TypeVar,
    TypeVarEnv,
} from "./types.ts"

import { OpRegistry } from "./ops.ts"

import { parsePattern, patternToString } from "./pattern_lang.ts"

/**
 * The reserved words of the LC concrete syntax — never lexed as an `ident`.
 *
 * The list is minimal by design: every entry must be load-bearing.
 *
 * `in` is the one genuinely load-bearing reservation. It is the only
 * keyword in a mid-expression position — the `let` terminator, exactly
 * where a variable could appear as an application argument. With `in`
 * lexed as an `ident`, `let x:Any = f in y in z` has two parses that type
 * at different types (def = `(f in) y`, body = `z` vs. def = `f`, body =
 * `(y in) z`) — a type-splitting ambiguity. Rejecting `in` from `ident`
 * kills the second reading.
 *
 * The keyword formers (`let`, `fold`, `unfold`, `cofold`) are NOT reserved
 * — their keyword positions are all prefix positions with mandatory
 * whitespace-delimited continuations (`fold [T] e {...}`, `let x:σ =
 * ...`), which a variable occurrence can never match. A variable named
 * `fold` parses exactly once: as a variable (`fold a b` is application)
 * or not at all. The same positional-disjointness argument that lets
 * `opIdent` accept keywords applies to `ident`.
 *
 * `opIdent` (operation names) is fully keyword-permissive for the same
 * reason.
 */
export const LC_RESERVED_WORDS: readonly string[] = [
    "in",
] as const

// ── Pattern anchoring (the T-Pattern lexer premise) ─────────────────────────────

// The anchoring walk lives on the abstract grammar as a METHOD
// (`isResolvableAndAnchored`, below — it needs the registry to propagate
// the anchoring through type references transitively).

// ── Shape ─────────────────────────────────────────────────────────────────────

/**
 * The shape maps production names to their parse-tree types.
 * Subclasses specialize these (e.g., AST builder: expr=Term, type checker: expr=Type).
 */
export interface LCShape {
    [k: string]: unknown
    expr: unknown
    atom: unknown
    type: Type
}

// ── Type registry ─────────────────────────────────────────────────────────────

/**
 * A registry of named types, used to resolve type names during parsing.
 * The grammar needs to know what `Stack`, `Stream`, etc. refer to.
 *
 * Also provides reverse lookups: variant name → DataType, observer name →
 * CodataType, pattern source → PatternDataType. These let `variantCon`, `obs`,
 * and `matchedPattern` semantic actions resolve the containing type from just
 * the constructor/observer/pattern name.
 *
 * **Registration is final.** `register` REJECTS a type whose name is already
 * registered (`TypeRegistryError`) — the same duplicate-redeclaration policy
 * `OpRegistry.declare` applies (its check 2), and for the same reason: the
 * reverse indexes (variant, observer, pattern) are built incrementally, with
 * the pattern index deliberately keeping a source's FIRST declaration (the
 * lexer's declaration-order tie-break). A same-named re-registration would
 * overwrite the `types` entry while leaving the reverse indexes pointing at
 * the PRIOR instance — a stale mapping the lookups cannot surface (the
 * indexes key by variant/observer/pattern names, not by type name, so
 * "remove the old entries for this type name" has no sound implementation
 * without a full index rebuild, and a silent first-pick is the ambiguity the
 * tie-break exists to name). Every call site constructs a fresh registry per
 * harness (fixtures, per-test setups, the shared-store memo keys by registry
 * identity) — replacement is not a supported operation, so it is an error,
 * not a hazard.
 *
 * Cross-type NAME collisions (two distinct types declaring the same VARIANT
 * or OBSERVER name) are NOT rejected here — the last registration wins that
 * reverse-lookup key, and the certificate machinery treats the collision as
 * a loud failure when it matters (the certified-prefix construction
 * validates the constructed value's carrier against the declaring type). The
 * pattern index keeps first-declaration-wins, the one key whose tie-break
 * the lexer's own resolution documents.
 */
export class TypeRegistryError extends Error {
    constructor(message: string) {
        super(message)
        this.name = "TypeRegistryError"
    }
}

export class TypeRegistry {
    private readonly types = new Map<string, DataType | CodataType | PatternDataType>()
    private readonly variantIndex = new Map<string, DataType>()
    private readonly observerIndex = new Map<string, CodataType>()
    private readonly patternIndex = new Map<string, PatternDataType>()

    /**
     * Register a type. A type whose NAME is already registered is rejected —
     * registration is final (see the class doc).
     *
     * @throws TypeRegistryError when the name is already registered.
     */
    register(type: DataType | CodataType | PatternDataType): void {
        if (this.types.has(type.name)) {
            throw new TypeRegistryError(
                `"${type.name}" is already registered — registration is final; ` +
                    "construct a fresh TypeRegistry for a revised type set",
            )
        }
        this.types.set(type.name, type)
        // Index variants for reverse lookup
        if (type instanceof DataType) {
            for (const variant of type.allVariants()) {
                this.variantIndex.set(variant.name, type)
            }
        }
        // Index observers for reverse lookup
        if (type instanceof CodataType) {
            for (const observer of type.allObservers()) {
                this.observerIndex.set(observer.name, type)
            }
        }
        // Index patterns for reverse lookup: the pattern's canonical source
        // (patternToString — the round-trip normalization) maps to its type.
        // A source already indexed is LEFT at its first declaration — matching
        // the lexer's declaration-order tie-break; a later type declaring the
        // identical pattern is shadowed (two types declaring the same pattern
        // is an ambiguity the surface declaration machinery must reject; at
        // the core layer the first declaration wins, deterministically).
        if (type instanceof PatternDataType) {
            for (const pattern of type.patterns) {
                const source = patternToString(pattern)
                if (!this.patternIndex.has(source)) {
                    this.patternIndex.set(source, type)
                }
            }
        }
    }

    lookup(name: string): DataType | CodataType | PatternDataType | undefined {
        return this.types.get(name)
    }

    /** Reverse lookup: find the DataType that declares a variant by name. */
    lookupVariant(variantName: string): DataType | undefined {
        return this.variantIndex.get(variantName)
    }

    /** Reverse lookup: find the CodataType that declares an observer by name. */
    lookupObserver(observerName: string): CodataType | undefined {
        return this.observerIndex.get(observerName)
    }

    /**
     * Reverse lookup: find the PatternDataType that declares a pattern by its
     * canonical source. The key is `patternToString`'s rendering (the
     * round-trip normalization), so a caller's source string must be in the
     * same canonical form — the `match("…")` form's payload parses through
     * `parsePattern` and compares canonically, so two spellings of one AST
     * (`[0123456789]` and `[0-9]`) agree.
     *
     * Returns the FIRST type that declared the pattern (registration order —
     * the lexer's declaration-order tie-break, `surface-syntax.md` §1.3).
     */
    lookupPatternSource(patternSource: string): PatternDataType | undefined {
        return this.patternIndex.get(patternSource)
    }
}

// ── Abstract LC grammar ───────────────────────────────────────────────────────

/**
 * Abstract LC grammar. Defines the shared productions for parsing LC terms.
 *
 * Subclasses implement abstract semantic-action methods to choose the
 * representation (AST, Type, Value) — the Bracha pattern from stlc.ts.
 *
 * The `registry` provides named types (Stack, Stream, etc.) that the grammar
 * resolves during parsing.
 */
// deno-lint-ignore no-explicit-any
@invariant((self: AbstractLC<any>) => self.start() !== undefined)
export abstract class AbstractLC<S extends LCShape> extends Grammar<S> {
    /** The type registry, set before parsing. */
    protected registry: TypeRegistry = new TypeRegistry()

    /** The operation registry (Ω), set before parsing. */
    protected opRegistry: OpRegistry = new OpRegistry()

    /** Set the type registry before parsing. */
    setRegistry(registry: TypeRegistry): this {
        this.registry = registry
        return this
    }

    /** Set the operation registry (Ω) before parsing. */
    setOpRegistry(opRegistry: OpRegistry): this {
        this.opRegistry = opRegistry
        return this
    }

    // ── Abstract semantic actions ─────────────────────────────────────────────

    protected abstract lam(param: string, type: Type, body: S["expr"]): S["expr"]
    protected abstract app(fn: S["atom"], arg: S["atom"]): S["expr"]
    protected abstract let_(name: string, type: Type, def: S["expr"], body: S["expr"]): S["expr"]
    protected abstract varRef(name: string, ctx: unknown): S["atom"]
    protected abstract paren(e: S["expr"]): S["atom"]
    protected abstract variantCon(name: string, args: S["atom"][]): S["atom"]
    protected abstract obs(scrutinee: S["atom"], observerName: string): S["expr"]
    protected abstract fold(
        dataType: DataType,
        scrutinee: S["expr"],
        handlers: { variantName: string; bindings: string[]; body: S["expr"] }[],
        resultType: Type,
    ): S["expr"]
    protected abstract unfold(
        codataType: CodataType,
        seed: S["expr"],
        generators: { observerName: string; body: S["expr"] }[],
        seedType: Type,
    ): S["expr"]
    protected abstract typeAbs(tyVar: string, bound: Type, body: S["expr"]): S["expr"]
    protected abstract typeApp(body: S["expr"], argType: Type): S["expr"]
    protected abstract cofold(
        codataType: CodataType,
        scrutinee: S["expr"],
        handler: { observerName: string; bindings: string[]; body: S["expr"] },
        resultType: Type,
    ): S["expr"]
    protected abstract opApp(opName: string, args: S["atom"][]): S["atom"]

    /**
     * A pattern-matched fold: `fold [T] e { match("pᵢ") → tᵢ }` — the
     * elimination form over a pattern-matched data type (T/E-FoldMatch, lc.md
     * §5.2b + §3.1). The action receives the carrier (the registered
     * `PatternDataType` the annotation resolves to), the scrutinee, the
     * handlers — each carrying the pattern's CANONICAL source (the same
     * `patternToString` identity the introduction form carries, so dispatch
     * and exhaustiveness key on canonical form everywhere) — and the result
     * type slot (the checker's σ; `Any` at the base grammar, as `fold()`
     * receives). There is NO binding position: the handler body references
     * `match`, the fixed binding (`match : Token`, lc.md §5.2b's `tᵢ : Token
     * → σ`) — the base production extends the context with it before parsing
     * the body, exactly as `foldHandler` extends with field types.
     */
    protected abstract patternFold(
        dataType: PatternDataType,
        scrutinee: S["expr"],
        handlers: { patternSource: string; body: S["expr"] }[],
        resultType: Type,
    ): S["expr"]

    /**
     * A matched token: `Ident` resolving to a registered `PatternDataType`.
     * The action receives both the type name and the raw matched text (they
     * coincide in this grammar-based lexer — the token's source IS its
     * content; a richer lexer would pass the lexed span's text here).
     */
    protected abstract matchedToken(dataTypeName: string, text: string): S["atom"]

    /**
     * A pattern-matched construction: `match("p")` — the explicit introduction
     * form for a pattern-matched data type (T-Pattern, lc.md §5.1). The action
     * receives the type the declared pattern belongs to, the pattern's
     * CANONICAL source (`patternToString` — the declared pattern's identity,
     * so two spellings of one AST yield identical tokens), and the raw
     * spelling the term carried (diagnostics). The premises (the pattern is
     * declared on a registered `PatternDataType`, anchored, and its type
     * references resolve) are enforced by `patternMatchProd`'s gate before
     * this action is reached.
     */
    protected abstract matchedPattern(
        dataTypeName: string,
        patternSource: string,
        rawSource: string,
    ): S["atom"]

    // ── Context extension hook (for type checker / evaluator subclasses) ──────

    protected extendCtx(ctx: unknown, _name: string, _type: Type): unknown {
        return ctx // no-op for AST builder
    }

    /**
     * Extend the context for a pattern-fold handler's fixed `match` binding
     * (lc.md §5.2b's `tᵢ : Token → σ`). The binding carries the handler's
     * CANONICAL pattern source alongside the Token type, so a subclass can
     * bind the TOKEN's identity (its per-pattern size variable
     * `token(T:<p>)`), not just the kind. The base returns the plain
     * `extendCtx(ctx, "match", Token)` extension (the checker's shape — the
     * binding's Γ type is Token); the cost engine overrides this to give the
     * binding its pattern-specific size identity (the same variable
     * `matchedPattern`'s cost summary produces — a body that references
     * `match` keeps the token's size/dispatch identity).
     */
    protected patternFoldBinding(
        ctx: unknown,
        _dataTypeName: string,
        _canonicalSource: string,
    ): unknown {
        return this.extendCtx(ctx, "match", Token)
    }

    /**
     * Whether `name` is bound as a TERM VARIABLE in the inherited context
     * (Γ for the type checker, ρ for the evaluator). The base grammar has no
     * term context, so this returns `false`.
     *
     * Consumed by `patternTokenProd`: the token branch is ordered BEFORE the
     * variable branch, so a registered pattern-type name would shadow a
     * bound variable of the same name — the gate consults this hook to fall
     * through to `varProd` whenever the name is a live term variable, which
     * keeps T-Var/E-Var reachable for PascalCase names.
     */
    protected nameBound(_name: string, _ctx: unknown): boolean {
        return false
    }

    /**
     * Extract the type-variable context (Δ) from the inherited context.
     * The base grammar has no Δ, so this returns an empty TypeVarEnv.
     * Subclasses that track Δ (e.g. the type checker) override this to
     * return the Δ portion of their context.
     */
    protected typeVarCtx(_ctx: unknown): TypeVarEnv {
        return new TypeVarEnv()
    }

    /**
     * Extend the inherited context with an updated type-variable context (Δ).
     * The base grammar has no Δ, so this is a no-op (returns ctx unchanged).
     * Subclasses that track Δ override this to thread the extended Δ through
     * the context.
     */
    protected extendTypeVarCtx(ctx: unknown, _delta: TypeVarEnv): unknown {
        return ctx
    }

    /**
     * Hook for the type of a fold handler's field binding.
     * - AST builder: returns `field.type` (the declared type; a Family field
     *   stays Family — the carrier is the consumer's knowledge).
     * - Type checker: the fixpoint subclass overrides the fold production
     *   entirely (Family fields rebind to σ); this hook is never reached.
     * - Cost engine: returns the fold-recursion marker for Family fields.
     */
    protected foldFieldType(field: Field, _dataType: DataType): Type {
        return field.type
    }

    // ── Type productions ──────────────────────────────────────────────────────

    // σ → τ
    //
    // `delta` (Δ) is the type-variable context, threaded through type
    // productions so `atomType` can resolve bound type variables before the
    // registry. The default empty Δ is used at top level; `typeAbsProd`
    // extends Δ when entering a type-abstraction body.
    @rule
    typeProd(delta: TypeVarEnv = new TypeVarEnv()): Parser<Type> {
        return or(
            seq(this.atomType(delta), this.ws, this.arrow, this.ws, this.typeProd(delta))
                .map(([dom, , , , cod]) => new FunType(dom, cod)),
            this.atomType(delta),
        )
    }

    // → | ->
    protected get arrow(): Parser<string> {
        return or(literal("→"), literal("->"))
    }

    // ( σ )  |  Ident
    //
    // Resolution order: bound type variable (Δ) → built-in → registry → TypeVar.
    // Checking Δ first resolves a bound type variable to a `TypeVar` carrying
    // its declared bound, before consulting built-ins or the registry.
    @rule
    protected atomType(delta: TypeVarEnv = new TypeVarEnv()): Parser<Type> {
        return or(
            seq(char("("), this.ws, this.typeProd(delta), this.ws, char(")"))
                .map(([, , t]) => t),
            this.typeName.map((name) => {
                // Bound type variable — resolve via Δ, carrying the declared bound
                const tyVarBound = delta.lookup(name)
                if (tyVarBound) return new TypeVar(name, tyVarBound)
                // Built-in types
                if (name === "Any") return Any
                if (name === "Nothing") return Nothing
                if (name === "Token") return Token
                // Resolve type name from registry
                const resolved = this.registry.lookup(name)
                if (resolved) return resolved
                // Unknown type name — return as a TypeVar (for type variables)
                return new TypeVar(name, Any)
            }),
        )
    }

    // Ident
    @rule
    protected get typeName(): Parser<string> {
        return seq(this.typeIdentFirst, this.typeIdentRest)
            .map(([h, t]) => h + t)
    }

    protected get typeIdentFirst(): Parser<string> {
        return pred((c) => c >= "A" && c <= "Z", "<Type-letter>")
    }

    // identRest
    @rule
    protected get typeIdentRest(): Parser<string> {
        return or(
            seq(this.typeIdentChar, this.typeIdentRest).map(([c, cs]) => c + cs),
            epsilon(""),
        )
    }

    protected get typeIdentChar(): Parser<string> {
        return pred(
            (c) =>
                (c >= "A" && c <= "Z") || (c >= "a" && c <= "z") || (c >= "0" && c <= "9") ||
                c === "_",
            "<type-char>",
        )
    }

    // ── Term productions ──────────────────────────────────────────────────────

    @rule
    exprProd(ctx: unknown): Parser<S["expr"]> {
        return or(
            this.lambdaProd(ctx),
            this.typeAbsProd(ctx),
            this.letProd(ctx),
            this.patternFoldProd(ctx),
            this.foldProd(ctx),
            this.unfoldProd(ctx),
            this.cofoldProd(ctx),
            this.obsProd(ctx),
        )
    }

    // λx:σ. t  (or \x:σ. t)
    @rule
    protected lambdaProd(ctx: unknown): Parser<S["expr"]> {
        return seq(
            this.lambdaHead,
            this.ident,
            this.ws,
            char(":"),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("."),
            this.ws,
        ).bind(([, param, , , , ty]) => {
            assert(typeof param === "string", "lambda param must be a string")
            assert(ty !== undefined, "lambda type must be defined")
            return this.exprProd(this.extendCtx(ctx, param, ty))
                .map((body) => this.lam(param, ty, body))
        })
    }

    protected get lambdaHead(): Parser<string> {
        return or(char("λ"), char("\\"))
    }

    // Λα <: σ. t  (type abstraction — ^ or Λ)
    //
    // The type-variable binder uses `typeName` (uppercase-first), matching the
    // type-position grammar (`atomType` resolves via `typeName`). This lets a
    // bound type variable be referenced in a type annotation: `^A <: Any. \x:A. x`.
    // The bound type variable is added to Δ (type-variable context) so that
    // references inside the body resolve to a `TypeVar` carrying the declared
    // bound. The bound σ is parsed under the *outer* Δ (the variable is not in
    // scope in its own bound).
    //
    // The binder is validated: it must not be a built-in type name (`Any`,
    // `Nothing`, `Token`) or a registered type name. Binding such a name would
    // shadow a real type inside the body, which is misleading even with
    // lexical scoping. The term is rejected (empty parse forest) instead.
    @rule
    protected typeAbsProd(ctx: unknown): Parser<S["expr"]> {
        const delta = this.typeVarCtx(ctx)
        return seq(
            or(char("^"), literal("Λ")),
            this.typeName,
            this.ws,
            this.kw("<:"),
            this.ws,
            this.typeProd(delta),
            this.ws,
            char("."),
            this.ws,
        ).bind(([, tyVar, , , , bound]) => {
            assert(typeof tyVar === "string", "type var must be a string")
            assert(bound !== undefined, "type bound must be defined")
            if (this.isReservedTypeName(tyVar)) {
                return empty<S["expr"]>()
            }
            const bodyDelta = delta.extend(tyVar, bound)
            return this.exprProd(this.extendTypeVarCtx(ctx, bodyDelta))
                .map((body) => this.typeAbs(tyVar, bound, body))
        })
    }

    /**
     * Check whether `name` is a reserved type name — a built-in (`Any`,
     * `Nothing`, `Token`) or a registered type. Binding such a name as a type
     * variable would shadow a real type, which is misleading even with
     * lexical scoping.
     */
    protected isReservedTypeName(name: string): boolean {
        return name === "Any" || name === "Nothing" || name === "Token" ||
            this.registry.lookup(name) !== undefined
    }

    // cofold [T] e { o₁(x₁) → t, ... }
    @rule
    protected cofoldProd(ctx: unknown): Parser<S["expr"]> {
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
            assert(ty instanceof CodataType, "cofold type must be a CodataType")
            const codataType = ty as CodataType
            return this.exprProd(ctx)
                .bind((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.cofoldHandler(codataType, ctx)
                                .bind((handler) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.cofold(codataType, scrutinee, handler, Any))
                                )
                        )
                )
        })
    }

    // oⱼ(xⱼ) → t  (cofold handler)
    @rule
    protected cofoldHandler(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<{ observerName: string; bindings: string[]; body: S["expr"] }> {
        return seq(
            this.ident,
            this.ws,
            char("("),
            this.ws,
            sepBy(this.ident, this.ws1),
            this.ws,
            char(")"),
            this.ws,
            this.arrow,
            this.ws,
        ).bind(([obsName, , , , bindings]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty<
                    { observerName: string; bindings: string[]; body: S["expr"] }
                >()
            }
            const bindingList = (bindings as string[] | undefined) ?? []
            let extendedCtx = ctx
            for (let i = 0; i < bindingList.length; i++) {
                extendedCtx = this.extendCtx(extendedCtx, bindingList[i]!, Any)
            }
            return this.exprProd(extendedCtx)
                .map((body) => ({ observerName: obsName, bindings: bindingList, body }))
        })
    }

    // let x:σ = t in t
    @rule
    protected letProd(ctx: unknown): Parser<S["expr"]> {
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
                .bind(({ name, ty, def }) =>
                    seq(this.ws1, this.kw("in"), this.ws1)
                        .bind(() =>
                            this.exprProd(this.extendCtx(ctx, name, ty))
                                .map((body) => this.let_(name, ty, def, body))
                        )
                )
        })
    }

    // fold [T] e { match("pᵢ") → tᵢ, ... }  — the pattern-matched fold
    // (T/E-FoldMatch, lc.md §5.2b + §3.1)
    //
    // Ordered BEFORE `foldProd`: the two productions are lexically IDENTICAL
    // up to the annotation's type gate (both `fold [T] e { … }`), so the
    // ordering — not lexical shape — decides which branch owns a source. This
    // branch owns pattern-typed carriers (a `PatternDataType` annotation) and
    // REJECTS every other kind (`empty`); `foldProd`, now reached only with a
    // non-pattern annotation, keeps its own gate as a caller-bug guard. The
    // base grammar never throws on a user program — a wrong-kind annotation is
    // a failed parse, not a crash.
    @rule
    protected patternFoldProd(ctx: unknown): Parser<S["expr"]> {
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
            // The annotation must be a PatternDataType — the wrong-kind branch
            // rejects (the caller falls through to `foldProd`'s reading; a
            // failed premise is `empty`, never a throw out of the parse).
            if (!(ty instanceof PatternDataType)) {
                return empty<S["expr"]>()
            }
            const patternType = ty
            return this.exprProd(ctx)
                .bind((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.patternFoldHandlers(patternType, ctx)
                                .bind((handlers) =>
                                    seq(this.ws, char("}"))
                                        .map(() =>
                                            this.patternFold(
                                                patternType,
                                                scrutinee,
                                                handlers,
                                                Any,
                                            )
                                        )
                                )
                        )
                )
        })
    }

    // Pattern-fold handlers: match("pᵢ") → tᵢ, ...
    @rule
    protected patternFoldHandlers(
        dataType: PatternDataType,
        ctx: unknown,
    ): Parser<{ patternSource: string; body: S["expr"] }[]> {
        return sepBy(
            this.patternFoldHandler(dataType, ctx),
            seq(this.ws, char(","), this.ws),
        )
    }

    // match("pᵢ") → tᵢ  (pattern-fold handler)
    //
    // The handler head is the CONSTRUCTOR (T-Pattern's premise: `input
    // matches pₖ ∈ {pᵢ}`) spelled exactly as the introduction form — the same
    // `match` + tight paren + quoted pattern shape, and the SAME gate walk
    // (`patternTypeName`: parses, anchored, declared on a registered pattern
    // type, references resolve). One additional premise: the pattern is
    // declared on THIS fold's carrier — a pattern owned by a different
    // registered type would be unmatchable (the scrutinee's `isSubtype` to the
    // carrier can never reach it) and would corrupt the exhaustiveness
    // accounting, so the branch rejects it. The handler carries the CANONICAL
    // source (the gate's resolution), not the raw spelling — dispatch,
    // exhaustiveness, and the evaluator's handler lookup all key canonical
    // form.
    //
    // The body parses under `match : Token` (lc.md §5.2b: `tᵢ : Token → σ`) —
    // the fixed binding, extended through the context hook exactly as a fold
    // handler's field bindings are. A user binder named `match` in an outer
    // scope is shadowed for the body, the usual lexical rule.
    @rule
    protected patternFoldHandler(
        dataType: PatternDataType,
        ctx: unknown,
    ): Parser<{ patternSource: string; body: S["expr"] }> {
        return seq(
            this.kw("match"),
            char("("), // tight paren — the pattern form's discipline
            this.ws,
            this.patternString,
            this.ws,
            char(")"),
            this.ws,
            this.arrow,
            this.ws,
        ).bind(([, , , patternSource]) => {
            const resolved = this.patternTypeName(patternSource as string)
            if (resolved === undefined || resolved.typeName !== dataType.name) {
                return empty<{ patternSource: string; body: S["expr"] }>()
            }
            // The body parses under `match : Token` — through the binding
            // hook, which carries the CANONICAL source (a subclass may bind
            // the token's identity, not just the type).
            return this.exprProd(this.patternFoldBinding(ctx, dataType.name, resolved.source))
                .map((body) => ({ patternSource: resolved.source, body }))
        })
    }

    // fold [T] e { C(x₁ x₂) → t, ... }
    @rule
    protected foldProd(ctx: unknown): Parser<S["expr"]> {
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
            // The annotation must be a DataType. `patternFoldProd` is ordered
            // BEFORE this branch, so a pattern-typed annotation is consumed
            // there; a wrong-kind annotation (e.g. `fold [Stream] ...` —
            // codata) REJECTS the branch like any other failed premise — an
            // `assert` here would throw out of the parse instead of rejecting
            // it (the caller-bug guard lives on the checker's/evaluator's
            // action overrides, where the premise is formally owned).
            if (!(ty instanceof DataType)) {
                return empty<S["expr"]>()
            }
            const dataType = ty
            return this.exprProd(ctx)
                .bind((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.foldHandlers(dataType, ctx)
                                .bind((handlers) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.fold(dataType, scrutinee, handlers, Any))
                                )
                        )
                )
        })
    }

    // Fold handlers: C(x₁ x₂) → t, ...
    @rule
    protected foldHandlers(
        dataType: DataType,
        ctx: unknown,
    ): Parser<{ variantName: string; bindings: string[]; body: S["expr"] }[]> {
        return sepBy(
            this.foldHandler(dataType, ctx),
            seq(this.ws, char(","), this.ws),
        )
    }

    // C(x₁ x₂) → t  (fold handler)
    @rule
    protected foldHandler(
        dataType: DataType,
        ctx: unknown,
    ): Parser<{ variantName: string; bindings: string[]; body: S["expr"] }> {
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
                    { variantName: string; bindings: string[]; body: S["expr"] }
                >()
            }
            const bindingList = (bindings as string[] | undefined) ?? []
            // Extend context with bindings
            let extendedCtx = ctx
            for (let i = 0; i < bindingList.length; i++) {
                const field = variant.fields[i]
                if (field) {
                    extendedCtx = this.extendCtx(
                        extendedCtx,
                        bindingList[i]!,
                        this.foldFieldType(field, dataType),
                    )
                }
            }
            return this.exprProd(extendedCtx)
                .map((body) => ({ variantName: vName, bindings: bindingList, body }))
        })
    }

    // unfold [T] s { o → t, ... }
    @rule
    protected unfoldProd(ctx: unknown): Parser<S["expr"]> {
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
            assert(ty instanceof CodataType, "unfold type must be a CodataType")
            const codataType = ty as CodataType
            return this.exprProd(ctx)
                .bind((seed) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.unfoldGenerators(codataType, ctx)
                                .bind((generators) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.unfold(codataType, seed, generators, Any))
                                )
                        )
                )
        })
    }

    // o → t, ...  (unfold generators)
    @rule
    protected unfoldGenerators(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<{ observerName: string; body: S["expr"] }[]> {
        return sepBy(
            this.unfoldGenerator(codataType, ctx),
            seq(this.ws, char(","), this.ws),
        )
    }

    // o → t  (unfold generator)
    @rule
    protected unfoldGenerator(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<{ observerName: string; body: S["expr"] }> {
        return seq(
            this.ident,
            this.ws,
            this.arrow,
            this.ws,
        ).bind(([obsName]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty<{ observerName: string; body: S["expr"] }>()
            }
            // Extend context with self: seed type
            const extendedCtx = this.extendCtx(ctx, "self", Any)
            return this.exprProd(extendedCtx)
                .map((body) => ({ observerName: obsName, body }))
        })
    }

    // e.o (observation — postfix dot, zero or more)
    @rule
    protected obsProd(ctx: unknown): Parser<S["expr"]> {
        return seq(
            this.appProd(ctx),
            seq(this.ws, char("."), this.ws, this.ident)
                .map(([, , , obsName]) => obsName)
                .many(),
        ).map(([scrut, obsNames]) =>
            obsNames.reduce(
                (s, obsName) => this.obs(s as unknown as S["atom"], obsName),
                scrut,
            )
        )
    }

    // Application (left-associative, zero or more) + type application t[τ]
    @rule
    protected appProd(ctx: unknown): Parser<S["expr"]> {
        return seq(
            this.typeAppProd(ctx),
            seq(this.ws1, this.typeAppProd(ctx))
                .map(([, arg]) => arg)
                .many(),
        ).map(([first, args]) =>
            args.reduce(
                (fn, arg) => this.app(fn as unknown as S["atom"], arg),
                first,
            )
        )
    }

    // Type application: atom [τ]* (postfix, binds tighter than application)
    @rule
    protected typeAppProd(ctx: unknown): Parser<S["expr"]> {
        return seq(
            this.atomProd(ctx),
            seq(
                this.ws,
                char("["),
                this.ws,
                this.typeProd(this.typeVarCtx(ctx)),
                this.ws,
                char("]"),
            )
                .map(([, , , ty]) => ty)
                .many(),
        ).map(([atom, types]) =>
            types.reduce(
                (s, ty) => this.typeApp(s, ty),
                atom,
            )
        )
    }

    // ( expr )  |  Ident(args)  |  ident(args)  |  Ident  |  patternToken
    @rule
    protected atomProd(ctx: unknown): Parser<S["atom"]> {
        return or(
            // ( expr )
            seq(char("("), this.ws, this.exprProd(ctx), this.ws, char(")"))
                .map(([, , e]) => this.paren(e)),
            // Named operation application: ident(args) — registry-gated, tight paren
            this.opProd(ctx),
            // Variant construction: Ident(args)
            this.variantProd(ctx),
            // Matched token: Ident — gated on the registry (a PatternDataType
            // name) and on the term context (a bound name is a variable)
            this.patternTokenProd(ctx),
            // Pattern-matched construction: match("p") — gated on the registry
            // (a registered type declares the pattern) and the anchoredness
            // premise
            this.patternMatchProd(ctx),
            // Variable
            this.varProd(ctx),
        )
    }

    // Ident — matched token (registry-gated, variable-binding-aware)
    //
    // A bare PascalCase atom whose name resolves to a registered
    // `PatternDataType` is a matched token: the sole inhabitant of a
    // pattern-matched type (T-Token, lc.md §2.3 — the bare atom is the token
    // introduction the abstract notation writes as `match(pₖ)`). Gated on the registry —
    // like `opProd`'s Ω gate — and on the term context via `nameBound`: a
    // name bound as a term variable (Γ/ρ) is a VARIABLE reference, not a
    // token — the branch falls through to `varProd` so T-Var/E-Var stays
    // reachable for PascalCase names (a bound `NatPat` variable must type as
    // its Γ type, not as the pattern type the registry happens to hold).
    // An unresolved name also falls through, keeping the grammar's ambiguity
    // surface unchanged.
    //
    // Ordered AFTER `variantProd`: `Ident(args)` is tried first, so a
    // pattern-typed name used as a constructor attempt fails here rather
    // than being mis-lexed as a token.
    @rule
    protected patternTokenProd(ctx: unknown): Parser<S["atom"]> {
        return this.variantName.bind((name) => {
            if (this.nameBound(name, ctx)) {
                return empty<S["atom"]>()
            }
            const resolved = this.registry.lookup(name)
            if (!(resolved instanceof PatternDataType)) {
                return empty<S["atom"]>()
            }
            return epsilon(name).map(() => this.matchedToken(name, name))
        })
    }

    // match("p") — pattern-matched construction (T-Pattern, lc.md §5.1)
    //
    // The explicit introduction form for a pattern-matched data type: the
    // constructor is the PATTERN ITSELF (lc.md §5.1 — `input matches pₖ ∈
    // {pᵢ}`), carried as a quoted pattern source. The bare `Ident` token atom
    // (`patternTokenProd`) is the lexer's registry-gated reading (any name the
    // registry holds); this form additionally PROVES its pattern is one of the
    // type's declared constructor patterns.
    //
    // `match` is camelCase + a tight paren — the op-application shape — but Ω
    // can never hold the name (`BUILTIN_CALL_FORMS` reserves it, `ops.ts`), so
    // the branch is unambiguous: the op gate declines and this branch owns the
    // form. The tight paren keeps it positionally disjoint from variable
    // application (`match ("…")` is a variable applied, not the pattern form),
    // and a λ-bound `match` variable remains an ordinary variable reference.
    //
    // The branch is ordered AFTER `patternTokenProd` — the two are lexically
    // disjoint (camelCase-then-`(` vs PascalCase-then-anything), so the order
    // is for documentation, not correctness.
    @rule
    protected patternMatchProd(_ctx: unknown): Parser<S["atom"]> {
        return seq(
            this.kw("match"),
            char("("), // tight paren — no whitespace (the op form's discipline)
            this.ws,
            this.patternString,
            this.ws,
            char(")"),
        ).bind(([, , , patternSource]) => {
            const source = patternSource as string
            const resolved = this.patternTypeName(source)
            if (resolved === undefined) {
                return empty<S["atom"]>()
            }
            // The CANONICAL source rides along: the token's text (its size,
            // its equality, its cost variable) is the DECLARED pattern's
            // identity — two spellings of one AST (`[0123456789]` and
            // `[0-9]`) introduce EQUAL tokens, whichever spelling the term
            // carried. The raw spelling stays available for diagnostics.
            return epsilon(this.matchedPattern(resolved.typeName, resolved.source, source))
        })
    }

    /**
     * Resolve a pattern source to the registered `PatternDataType` that
     * declares it — the owner's name AND the pattern's canonical source. The
     * source parses through `parsePattern` (the SAME parse the declaration
     * machinery uses) and compares canonically — `patternToString`
     * normalization — against the registry's pattern index.
     *
     * Premises checked here (the T-Pattern gate, lc.md §5.1):
     * 1. the source parses as a pattern (a malformed source is a REJECTION —
     *    empty parse forest, the term is ill-typed — never a thrown error out
     *    of the parse),
     * 2. the parsed pattern is DECLARED on a registered `PatternDataType`
     *    (canonical comparison — `patternToString` normalization — so two
     *    spellings of one AST agree),
     * 3. the pattern is ANCHORED (surface-syntax.md §1.3: it must start with a
     *    specific literal or class — a leading `.`/`*`/`+`/`?`-driven shape
     *    would match from any position; the explicit form names its pattern,
     *    so the lexer-side premise is checkable at parse time),
     * 4. every TYPE REFERENCE in the pattern resolves to a registered
     *    pattern type (recursively — a `<Missing>` reference produces a
     *    token whose language the registry cannot enumerate, and a reference
     *    chain that is itself anchored only passes when each target's own
     *    declared patterns are anchored — the declaration machinery's
     *    obligation, enforced at the gate because the registry's own
     *    registration accepts parsed ASTs as given).
     *
     * `undefined` — any failed premise; the caller rejects the branch.
     */
    protected patternTypeName(
        patternSource: string,
    ): { typeName: string; source: string } | undefined {
        let ast: ReturnType<typeof parsePattern>
        try {
            ast = parsePattern(patternSource)
        } catch {
            // A malformed pattern is a REJECTION (empty parse forest — the
            // term is ill-typed), never a thrown error out of the parse.
            return undefined
        }
        // The combined gate walk: every type reference resolves AND the
        // anchoring propagates through references transitively (a reference
        // is anchored iff its target's declared patterns are). Cycle-safe
        // via the seen set.
        if (!this.isResolvableAndAnchored(ast, new Set())) {
            return undefined
        }
        const canonical = patternToString(ast)
        const resolved = this.registry.lookupPatternSource(canonical)
        if (!resolved) {
            return undefined
        }
        return { typeName: resolved.name, source: canonical }
    }

    /**
     * The gate's combined walk: RESOLVABILITY (every type reference names a
     * registered pattern type — the registry can enumerate the pattern's
     * language) and TRANSITIVE ANCHORING (the pattern's first atom is a
     * literal or class, through the postfix wrappers AND through type
     * references — a reference's language is its target's, so a reference to
     * a type declaring an unanchored pattern is unanchored itself). The two
     * premises share one walk because they share the same structure and the
     * same cycle guard (surface-syntax.md §1.3 — both are lexer-side
     * obligations the declaration machinery may have skipped: the registry
     * accepts parsed ASTs as given, so the term gate owns them).
     */
    private isResolvableAndAnchored(
        ast: ReturnType<typeof parsePattern>,
        seen: Set<string>,
    ): boolean {
        switch (ast.kind) {
            case "char":
            case "class":
                return true
            case "any":
                // A leading `.` matches any character from any position —
                // the shape the spec rejects (surface-syntax.md §1.3).
                return false
            case "concat": {
                // The first part decides where the match must start. The
                // parser never produces an empty concat (a concat node
                // requires at least one parsed atom — an exhausted source
                // throws in `parseAtom` first), but the arm treats empty as
                // unanchored (a pattern matching NOTHING anchors nothing)
                // rather than trusting the cross-module invariant blindly.
                const first = ast.parts[0]
                return first === undefined ? false : this.isResolvableAndAnchored(first, seen)
            }
            case "star":
            case "plus":
            case "opt":
                // A postfix wrapper is transparent for anchoring: the
                // pattern starts at its inner's first atom (`[0-9]+` anchors
                // at the class; `".*"` anchors at the quote).
                return this.isResolvableAndAnchored(ast.inner, seen)
            case "typeref": {
                if (seen.has(ast.name)) return true
                seen.add(ast.name)
                const resolved = this.registry.lookup(ast.name)
                if (!(resolved instanceof PatternDataType)) {
                    // An unresolvable reference: no registered type owns the
                    // name — the language is unknowable (the constructor
                    // would be accepted with a language the registry cannot
                    // enumerate).
                    return false
                }
                // The reference's language is the target's: anchored iff the
                // target's declared patterns all are (the transitive
                // obligation — a chain ending in `.` is unanchored).
                return resolved.patterns.every((p) => this.isResolvableAndAnchored(p, seen))
            }
        }
    }

    // The quoted pattern string: "…" with `\` escapes.
    //
    // The payload is a PATTERN (the constructor) — the one deliberate string
    // literal in the LC concrete syntax. A `"` inside the payload is escaped
    // (`\"`) and a `\\` as `\\\\`: the DELIMITER's escapes, undone here so
    // the pattern language reads its own raw source (a pattern's own `\`
    // escapes — `\+`, `\.` — are payload characters, carried through
    // unescaped, because only `"` and `\\` are special to the string form).
    @rule
    protected get patternString(): Parser<string> {
        return seq(char('"'), this.patternChars, char('"'))
            .map(([, chars]) => chars)
    }

    // The payload: patternChar* (zero or more pieces, collected into an
    // array and joined ONCE). A pattern is never empty (parsePattern rejects
    // the empty pattern), so a zero-length payload still parses here and is
    // rejected by the declared-pattern check — the gate, not the lexeme,
    // owns that premise.
    //
    // `many`, not right-recursion: the identRest-style `seq(char, rest)` +
    // `.or(epsilon(""))` shape builds the string by one concatenation PER
    // character (O(n²) in the payload length) and one recursion frame PER
    // character — a long pattern payload would pay quadratic string work
    // and stack depth linear in the payload. `.many()` (the combinator
    // `obsProd`'s observation chains already use) collects the pieces into
    // an array first; the single `join` keeps the lexeme linear and flat.
    @rule
    protected get patternChars(): Parser<string> {
        return this.patternChar.many().map((chars) => chars.join(""))
    }

    // One payload piece: an escaped delimiter char (`\"` or `\\` → the raw
    // char), or a plain character (not a delimiter, not a backslash).
    @rule
    protected get patternChar(): Parser<string> {
        return or(
            seq(char("\\"), pred((c) => c === '"' || c === "\\", "<escaped-delim>"))
                .map(([, c]) => c),
            pred((c) => c !== '"' && c !== "\\", "<pattern-char>"),
        )
    }

    // Ident(args)  — variant construction
    //
    // Factored out of atomProd so subclasses can enforce premises on the
    // production path (T-Variant's field checks). The default action is the
    // semantic action itself; subclasses override to reject failed premises.
    @rule
    protected variantProd(ctx: unknown): Parser<S["atom"]> {
        return seq(
            this.variantName,
            this.ws,
            char("("),
            this.ws,
            sepBy(this.atomProd(ctx), seq(this.ws, char(","), this.ws)),
            this.ws,
            char(")"),
        )
            .map(([name, , , , args]) =>
                this.variantCon(name as string, (args as S["atom"][]) ?? [])
            )
    }

    // Ident  — variable reference
    //
    // Factored out of atomProd so subclasses can enforce the T-Var premise
    // (`x : σ ∈ Γ`) on the production path — the contracted `varRef` action
    // returns `undefined` on a failed `@requires`, which would surface in the
    // parse forest instead of rejecting the branch.
    @rule
    protected varProd(ctx: unknown): Parser<S["atom"]> {
        return this.ident.map((name) => this.varRef(name, ctx))
    }

    // ── Named operation application (lc.md §2.2) ─────────────────────────────

    /**
     * `op(t₁, ..., tₙ)` — named operation application.
     *
     * Gated on the operation registry (Ω): the production only matches when
     * the name matches a declared operation. Disambiguation from the keyword
     * forms is positional, not lexical: every keyword position is
     * whitespace-delimited (`fold [T] e {...}`, `let x:σ = ...`, `... in u`),
     * while the op form requires the tight paren (`fold(a, b)`). The two are
     * disjoint by construction, so the op lexeme (`opIdent`) accepts keywords
     * — an operation may be named `fold` and still be appliable.
     *
     * Disambiguation from variables is the registry gate: `add(a, b)` parses
     * as an op application because `add ∈ Ω`; `unknownOp(a, b)` fails the gate
     * and falls through to variable application, which requires whitespace
     * (`f x`, never `f(a)`), so it fails too. The tight paren is the shadowing
     * escape hatch — a let-bound `add` remains applicable with spacing.
     *
     * Arguments are atoms (like variant construction), evaluated leftmost by
     * the one-pass grammar (E-OpArg).
     */
    @rule
    protected opProd(ctx: unknown): Parser<S["atom"]> {
        return seq(
            this.opIdent,
            char("("),
            this.ws,
        ).bind(([opName]) => {
            if (this.opRegistry.lookup(opName) === undefined) {
                return empty<S["atom"]>()
            }
            return sepBy(this.atomProd(ctx), seq(this.ws, char(","), this.ws))
                .bind((args) =>
                    seq(this.ws, char(")"))
                        .map(() => this.opApp(opName, args))
                )
        })
    }

    // ── Lexemes ───────────────────────────────────────────────────────────────

    // PascalCase
    @rule
    protected get variantName(): Parser<string> {
        // PascalCase identifier — no keyword check needed: every reserved word
        // is lowercase (ident-first is [a-z_]), so a PascalCase lexeme can
        // never equal one.
        return seq(this.pascalFirst, this.identRest)
            .map(([h, t]) => h + t)
    }

    protected get pascalFirst(): Parser<string> {
        return pred((c) => c >= "A" && c <= "Z", "<Pascal-letter>")
    }

    // lowercase
    @rule
    protected get ident(): Parser<string> {
        return seq(this.identFirst, this.identRest)
            .map(([h, t]) => h + t)
            .bind((name) => {
                if (LC_RESERVED_WORDS.includes(name)) {
                    return empty<string>()
                }
                return epsilon(name)
            })
    }

    /**
     * The operation-name lexeme: like `ident`, but keyword-permissive. The
     * op form's tight paren (`fold(a, b)`) is positionally disjoint from every
     * keyword position (all whitespace-delimited: `fold [T] e {...}`, `let
     * x:σ = ...`, `... in u`), so an operation may be named `fold` — the
     * registry gate resolves which reading applies, not the lexeme.
     */
    @rule
    protected get opIdent(): Parser<string> {
        return seq(this.identFirst, this.identRest)
            .map(([h, t]) => h + t)
    }

    protected get identFirst(): Parser<string> {
        return pred((c) => (c >= "a" && c <= "z") || c === "_", "<ident-head>")
    }

    // identRest
    @rule
    protected get identRest(): Parser<string> {
        return or(
            seq(this.identChar, this.identRest).map(([c, cs]) => c + cs),
            epsilon(""),
        )
    }

    protected get identChar(): Parser<string> {
        return pred(
            (c) =>
                (c >= "a" && c <= "z") || (c >= "A" && c <= "Z") || (c >= "0" && c <= "9") ||
                c === "_",
            "<ident-char>",
        )
    }

    protected kw(word: string): Parser<string> {
        return literal(word)
    }

    // ── Whitespace ────────────────────────────────────────────────────────────

    // ws
    @rule
    protected override get ws(): Parser<string> {
        return or(
            seq(this.wsChar, this.ws).map(([c, cs]) => c + cs),
            epsilon(""),
        )
    }

    // ws1
    @rule
    protected get ws1(): Parser<string> {
        return seq(this.wsChar, this.ws).map(([c, cs]) => c + cs)
    }

    protected get wsChar(): Parser<string> {
        return pred(
            (c) => c === " " || c === "\t" || c === "\n" || c === "\r",
            "<ws>",
        )
    }
}
