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
 *             | unfold [σ] t {generators}    unfold (anamorphism)
 *             | cofold [σ] t {handler}       cofold (codata elimination)
 *             | t t                          application (left-assoc)
 *             | t . Ident                    observation (postfix)
 *             | t [σ]                        type application (postfix)
 *             | Ident                        variable
 *             | Ident (args)                 variant construction
 *             | ( t )                        parenthesized
 *
 *   Handlers: C(x₁ x₂ ...) → t              fold handler (variant + bindings)
 *
 *   Generators: o → t                        unfold generator (observer + body)
 *
 *   Cofold handler: o(x₁ x₂ ...) → t         cofold handler (observer + bindings)
 *
 * Productions:
 *
 *   exprProd      = lambdaProd | typeAbsProd | letProd | foldProd | unfoldProd
 *                 | cofoldProd | obsProd
 *   obsProd       = appProd ( "." ident | "[" type "]" )*
 *   appProd       = typeAppProd ( ws1 typeAppProd )*
 *   typeAppProd   = atomProd ( "[" type "]" )*
 *   atomProd      = "(" expr ")" | variantName "(" args ")" | ident
 *   typeProd      = atomType ( "→" typeProd )?
 *   atomType      = "(" type ")" | typeName
 *
 * An abstract grammar declares the shared structure (productions), and concrete
 * subclasses implement semantic actions (AST builder, type checker, evaluator).
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
} from "@lapis-lang/zipper-grammar"

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
} from "./types.ts"

import {
    App,
    Cofold,
    CofoldHandler,
    Fold,
    FoldHandler,
    Lam,
    Let,
    Obs,
    type Term,
    TypeAbs,
    TypeApp,
    Unfold,
    UnfoldGenerator,
    Var,
    VariantCon,
} from "./terms.ts"

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
 * CodataType. These let `variantCon` and `obs` semantic actions resolve the
 * containing type from just the constructor/observer name.
 */
export class TypeRegistry {
    private readonly types = new Map<string, DataType | CodataType | PatternDataType>()
    private readonly variantIndex = new Map<string, DataType>()
    private readonly observerIndex = new Map<string, CodataType>()

    register(type: DataType | CodataType | PatternDataType): void {
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

    /** Set the type registry before parsing. */
    setRegistry(registry: TypeRegistry): this {
        this.registry = registry
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

    // ── Context extension hook (for type checker / evaluator subclasses) ──────

    protected extendCtx(ctx: unknown, _name: string, _type: Type): unknown {
        return ctx // no-op for AST builder
    }

    /**
     * Hook for the type of a fold handler's field binding.
     * - AST builder: returns `field.type` (the declared type).
     * - Type checker: for recursive fields, returns `Any` (the result type σ
     *   is unknown during one-pass parsing; the fold semantic action checks
     *   handler body types agree).
     */
    protected foldFieldType(field: Field, _dataType: DataType): Type {
        return field.type
    }

    // ── Type productions ──────────────────────────────────────────────────────

    // σ → τ
    @rule
    get typeProd(): Parser<Type> {
        return or(
            seq(this.atomType, this.ws, this.arrow, this.ws, this.typeProd)
                .map(([dom, , , , cod]) => new FunType(dom, cod)),
            this.atomType,
        )
    }

    // → | ->
    protected get arrow(): Parser<string> {
        return or(literal("→"), literal("->"))
    }

    // ( σ )  |  Ident
    @rule
    protected get atomType(): Parser<Type> {
        return or(
            seq(char("("), this.ws, this.typeProd, this.ws, char(")"))
                .map(([, , t]) => t),
            this.typeName.map((name) => {
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
            this.typeProd,
            this.ws,
            char("."),
            this.ws,
        ).chain(([, param, , , , ty]) => {
            assert(typeof param === "string", "lambda param must be a string")
            assert(ty !== undefined, "lambda type must be defined")
            return this.exprProd(this.extendCtx(ctx, param, ty))
                .map((body) => this.lam(param, ty, body))
        }).map(([, result]) => result)
    }

    protected get lambdaHead(): Parser<string> {
        return or(char("λ"), char("\\"))
    }

    // Λα <: σ. t  (type abstraction — ^ or Λ)
    @rule
    protected typeAbsProd(ctx: unknown): Parser<S["expr"]> {
        return seq(
            or(char("^"), literal("Λ")),
            this.ident,
            this.ws,
            this.kw("<:"),
            this.ws,
            this.typeProd,
            this.ws,
            char("."),
            this.ws,
        ).chain(([, tyVar, , , , bound]) => {
            assert(typeof tyVar === "string", "type var must be a string")
            assert(bound !== undefined, "type bound must be defined")
            return this.exprProd(ctx)
                .map((body) => this.typeAbs(tyVar, bound, body))
        }).map(([, result]) => result)
    }

    // cofold [T] e { o₁(x₁) → t, ... }
    @rule
    protected cofoldProd(ctx: unknown): Parser<S["expr"]> {
        return seq(
            this.kw("cofold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd,
            this.ws,
            char("]"),
            this.ws,
        ).chain(([, , , , ty]) => {
            assert(ty instanceof CodataType, "cofold type must be a CodataType")
            const codataType = ty as CodataType
            return this.exprProd(ctx)
                .chain((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.cofoldHandler(codataType, ctx)
                                .chain((handler) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.cofold(codataType, scrutinee, handler, Any))
                                )
                                .map(([, result]) => result)
                        )
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        }).map(([, result]) => result)
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
        ).chain(([obsName, , , , bindings]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty() as unknown as Parser<
                    { observerName: string; bindings: string[]; body: S["expr"] }
                >
            }
            const bindingList = (bindings as string[] | undefined) ?? []
            let extendedCtx = ctx
            for (let i = 0; i < bindingList.length; i++) {
                extendedCtx = this.extendCtx(extendedCtx, bindingList[i]!, Any)
            }
            return this.exprProd(extendedCtx)
                .map((body) => ({ observerName: obsName, bindings: bindingList, body }))
        }).map(([, result]) => result)
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
            this.typeProd,
            this.ws,
            char("="),
            this.ws,
        ).chain(([, , name, , , , ty]) => {
            return this.exprProd(ctx)
                .map((def) => ({ name, ty, def }))
                .chain(({ name, ty, def }) =>
                    seq(this.ws1, this.kw("in"), this.ws1)
                        .chain(() =>
                            this.exprProd(this.extendCtx(ctx, name, ty))
                                .map((body) => this.let_(name, ty, def, body))
                        )
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        }).map(([, result]) => result)
    }

    // fold [T] e { C(x₁ x₂) → t, ... }
    @rule
    protected foldProd(ctx: unknown): Parser<S["expr"]> {
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
                .chain((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.foldHandlers(dataType, ctx)
                                .chain((handlers) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.fold(dataType, scrutinee, handlers, Any))
                                )
                                .map(([, result]) => result)
                        )
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        }).map(([, result]) => result)
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
        ).chain(([vName, , , , bindings]) => {
            const variant = dataType.findVariant(vName)
            if (!variant) {
                return empty() as unknown as Parser<
                    { variantName: string; bindings: string[]; body: S["expr"] }
                >
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
        }).map(([, result]) => result)
    }

    // unfold [T] s { o → t, ... }
    @rule
    protected unfoldProd(ctx: unknown): Parser<S["expr"]> {
        return seq(
            this.kw("unfold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd,
            this.ws,
            char("]"),
            this.ws,
        ).chain(([, , , , ty]) => {
            assert(ty instanceof CodataType, "unfold type must be a CodataType")
            const codataType = ty as CodataType
            return this.exprProd(ctx)
                .chain((seed) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.unfoldGenerators(codataType, ctx)
                                .chain((generators) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.unfold(codataType, seed, generators, Any))
                                )
                                .map(([, result]) => result)
                        )
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        }).map(([, result]) => result)
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
        ).chain(([obsName]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty() as unknown as Parser<{ observerName: string; body: S["expr"] }>
            }
            // Extend context with self: seed type
            const extendedCtx = this.extendCtx(ctx, "self", Any)
            return this.exprProd(extendedCtx)
                .map((body) => ({ observerName: obsName, body }))
        }).map(([, result]) => result)
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
            seq(this.ws, char("["), this.ws, this.typeProd, this.ws, char("]"))
                .map(([, , , ty]) => ty)
                .many(),
        ).map(([atom, types]) =>
            types.reduce(
                (s, ty) => this.typeApp(s, ty),
                atom,
            )
        )
    }

    // ( expr )  |  Ident(args)  |  Ident
    @rule
    protected atomProd(ctx: unknown): Parser<S["atom"]> {
        return or(
            // ( expr )
            seq(char("("), this.ws, this.exprProd(ctx), this.ws, char(")"))
                .map(([, , e]) => this.paren(e)),
            // Variant construction: Ident(args)
            seq(
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
                ),
            // Variable
            this.ident.map((name) => this.varRef(name, ctx)),
        )
    }

    // ── Lexemes ───────────────────────────────────────────────────────────────

    // PascalCase
    @rule
    protected get variantName(): Parser<string> {
        // PascalCase identifier
        return seq(this.pascalFirst, this.identRest)
            .map(([h, t]) => h + t)
            .chain((name) => {
                // Reject if it's a keyword
                if (["fold", "unfold", "cofold", "let", "in"].includes(name)) {
                    return empty() as unknown as Parser<string>
                }
                return epsilon(name)
            })
            .map(([, r]) => r)
    }

    protected get pascalFirst(): Parser<string> {
        return pred((c) => c >= "A" && c <= "Z", "<Pascal-letter>")
    }

    // lowercase
    @rule
    protected get ident(): Parser<string> {
        return seq(this.identFirst, this.identRest)
            .map(([h, t]) => h + t)
            .chain((name) => {
                if (["let", "in", "fold", "unfold", "cofold"].includes(name)) {
                    return empty() as unknown as Parser<string>
                }
                return epsilon(name)
            })
            .map(([, r]) => r)
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

// ── Concrete: AST builder ─────────────────────────────────────────────────────

/**
 * AST builder — parses LC text into Term objects.
 * No context (ctx is null). Pure syntax.
 */
export class LCAST extends AbstractLC<{ expr: Term; atom: Term; type: Type }> {
    override start(): Parser<Term> {
        return this.exprProd(null)
    }

    protected lam(param: string, type: Type, body: Term): Term {
        return new Lam(param, type, body)
    }

    protected app(fn: Term, arg: Term): Term {
        return new App(fn, arg)
    }

    protected let_(name: string, type: Type, def: Term, body: Term): Term {
        return new Let(name, type, def, body)
    }

    protected varRef(name: string, _ctx: unknown): Term {
        return new Var(name)
    }

    protected paren(e: Term): Term {
        return e
    }

    protected variantCon(name: string, args: Term[]): Term {
        const dataType = this.registry.lookupVariant(name)
        if (!dataType) {
            throw new Error(`unknown variant: ${name} — not registered in TypeRegistry`)
        }
        return new VariantCon(name, dataType, args)
    }

    protected obs(scrutinee: Term, observerName: string): Term {
        const codataType = this.registry.lookupObserver(observerName)
        if (!codataType) {
            throw new Error(`unknown observer: ${observerName} — not registered in TypeRegistry`)
        }
        return new Obs(scrutinee, observerName, codataType)
    }

    protected fold(
        dataType: DataType,
        scrutinee: Term,
        handlers: { variantName: string; bindings: string[]; body: Term }[],
        resultType: Type,
    ): Term {
        return new Fold(
            dataType,
            scrutinee,
            handlers.map((h) => new FoldHandler(h.variantName, h.bindings, h.body)),
            resultType,
        )
    }

    protected unfold(
        codataType: CodataType,
        seed: Term,
        generators: { observerName: string; body: Term }[],
        seedType: Type,
    ): Term {
        return new Unfold(
            codataType,
            seed,
            generators.map((g) => new UnfoldGenerator(g.observerName, g.body)),
            seedType,
        )
    }

    protected typeAbs(tyVar: string, bound: Type, body: Term): Term {
        return new TypeAbs(tyVar, bound, body)
    }

    protected typeApp(body: Term, argType: Type): Term {
        return new TypeApp(body, argType)
    }

    protected cofold(
        codataType: CodataType,
        scrutinee: Term,
        handler: { observerName: string; bindings: string[]; body: Term },
        resultType: Type,
    ): Term {
        return new Cofold(
            codataType,
            scrutinee,
            new CofoldHandler(handler.observerName, handler.bindings, handler.body),
            resultType,
        )
    }
}
