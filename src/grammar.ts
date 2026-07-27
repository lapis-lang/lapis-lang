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
 *             | let x:σ = t in t             let-binding
 *             | t t                          application (left-assoc)
 *             | t . Ident                    observation
 *             | fold [σ] t {handlers}        fold (catamorphism)
 *             | unfold [σ] t {generators}    unfold (anamorphism)
 *             | Ident                        variable
 *             | Ident (args)                 variant construction
 *             | ( t )                        parenthesized
 *
 *   Handlers: C(x₁ x₂ ...) → t              fold handler (variant + bindings)
 *
 *   Generators: o → t                        unfold generator (observer + body)
 *
 * The grammar follows the Bracha executable-grammar pattern from zipper-grammar:
 * an abstract grammar declares the shared structure (productions), and concrete
 * subclasses implement semantic actions (AST builder, type checker, evaluator).
 *
 * See _docs/theory/lc.md for the formal specification.
 * See zipper-grammar examples/stlc.ts for the headline example of this pattern.
 */

import {
    Grammar,
    rule,
    invariant,
    assert,
    char,
    pred,
    literal,
    or,
    seq,
    epsilon,
    empty,
    keyword,
    sepBy,
    type Parser,
} from "jsr:@lapis-lang/zipper-grammar@3.0.0";

import {
    type Type,
    TypeVar,
    FunType,
    DataType,
    PatternDataType,
    CodataType,
    Any,
} from "./types.ts";

import {
    type Term,
    Var,
    Lam,
    App,
    Let,
    Fold,
    FoldHandler,
    Unfold,
    UnfoldGenerator,
} from "./terms.ts";

// ── Shape ─────────────────────────────────────────────────────────────────────

/**
 * The shape maps production names to their parse-tree types.
 * Subclasses specialize these (e.g., AST builder: expr=Term, type checker: expr=Type).
 */
export interface LCShape {
    [k: string]: unknown;
    expr: unknown;
    atom: unknown;
    type: Type;
}

// ── Type registry ─────────────────────────────────────────────────────────────

/**
 * A registry of named types, used to resolve type names during parsing.
 * The grammar needs to know what `Stack`, `Stream`, etc. refer to.
 */
export class TypeRegistry {
    private readonly types = new Map<string, DataType | CodataType | PatternDataType>();

    register(type: DataType | CodataType | PatternDataType): void {
        this.types.set(type.name, type);
    }

    lookup(name: string): DataType | CodataType | PatternDataType | undefined {
        return this.types.get(name);
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
    protected registry: TypeRegistry = new TypeRegistry();

    /** Set the type registry before parsing. */
    setRegistry(registry: TypeRegistry): this {
        this.registry = registry;
        return this;
    }

    // ── Abstract semantic actions ─────────────────────────────────────────────

    protected abstract lam(param: string, type: Type, body: S["expr"]): S["expr"];
    protected abstract app(fn: S["atom"], arg: S["atom"]): S["expr"];
    protected abstract let_(name: string, type: Type, def: S["expr"], body: S["expr"]): S["expr"];
    protected abstract varRef(name: string): S["atom"];
    protected abstract paren(e: S["expr"]): S["atom"];
    protected abstract variantCon(name: string, args: S["atom"][]): S["atom"];
    protected abstract obs(scrutinee: S["atom"], observerName: string): S["expr"];
    protected abstract fold(
        dataType: DataType,
        scrutinee: S["expr"],
        handlers: { variantName: string; bindings: string[]; body: S["expr"] }[],
        resultType: Type,
    ): S["expr"];
    protected abstract unfold(
        codataType: CodataType,
        seed: S["expr"],
        generators: { observerName: string; body: S["expr"] }[],
        seedType: Type,
    ): S["expr"];

    // ── Context extension hook (for type checker / evaluator subclasses) ──────

    protected extendCtx(ctx: unknown, _name: string, _type: Type): unknown {
        return ctx; // no-op for AST builder
    }

    // ── Type productions ──────────────────────────────────────────────────────

    @rule
    get typeProd(): Parser<Type> {
        return or(
            seq(this.atomType, this.ws, this.arrow, this.ws, this.typeProd)
                .map(([dom, , , , cod]) => new FunType(dom, cod)),
            this.atomType,
        );
    }

    protected get arrow(): Parser<string> {
        return or(literal("→"), literal("->"));
    }

    @rule
    protected get atomType(): Parser<Type> {
        return or(
            seq(char("("), this.ws, this.typeProd, this.ws, char(")"))
                .map(([, , t]) => t),
            this.typeName.map((name) => {
                // Resolve type name from registry
                const resolved = this.registry.lookup(name);
                if (resolved) return resolved;
                // Unknown type name — return as a TypeVar (for type variables)
                return new TypeVar(name, Any);
            }),
        );
    }

    @rule
    protected get typeName(): Parser<string> {
        return seq(this.typeIdentFirst, this.typeIdentRest)
            .map(([h, t]) => h + t);
    }

    protected get typeIdentFirst(): Parser<string> {
        return pred((c) => c >= "A" && c <= "Z", "<Type-letter>");
    }

    @rule
    protected get typeIdentRest(): Parser<string> {
        return or(
            seq(this.typeIdentChar, this.typeIdentRest).map(([c, cs]) => c + cs),
            epsilon(""),
        );
    }

    protected get typeIdentChar(): Parser<string> {
        return pred(
            (c) => (c >= "A" && c <= "Z") || (c >= "a" && c <= "z") || (c >= "0" && c <= "9") || c === "_",
            "<type-char>",
        );
    }

    // ── Term productions ──────────────────────────────────────────────────────

    @rule
    exprProd(ctx: unknown): Parser<S["expr"]> {
        return or(
            this.lambdaProd(ctx),
            this.letProd(ctx),
            this.foldProd(ctx),
            this.unfoldProd(ctx),
            this.obsProd(ctx),
            this.appProd(ctx),
        );
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
        ).chain(([, param, , , , ty, , ,]) => {
            assert(typeof param === "string", "lambda param must be a string");
            assert(ty !== undefined, "lambda type must be defined");
            return this.exprProd(this.extendCtx(ctx, param, ty))
                .map((body) => this.lam(param, ty, body));
        }).map(([, result]) => result);
    }

    protected get lambdaHead(): Parser<string> {
        return or(char("λ"), char("\\"));
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
        ).chain(([, , name, , , , ty, , ,]) => {
            return this.exprProd(ctx)
                .map((def) => ({ name, ty, def }))
                .chain(({ name, ty, def }) =>
                    seq(this.ws1, this.kw("in"), this.ws1)
                        .chain(() =>
                            this.exprProd(this.extendCtx(ctx, name, ty))
                                .map((body) => this.let_(name, ty, def, body)),
                        )
                        .map(([, result]) => result),
                )
                .map(([, result]) => result);
        }).map(([, result]) => result);
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
        ).chain(([, , , , ty, , ,]) => {
            assert(ty instanceof DataType, "fold type must be a DataType");
            const dataType = ty as DataType;
            return this.exprProd(ctx)
                .chain((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.foldHandlers(dataType, ctx)
                                .chain((handlers) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.fold(dataType, scrutinee, handlers, Any)),
                                ),
                        )
                        .map(([, result]) => result),
                )
                .map(([, result]) => result);
        }).map(([, result]) => result);
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
        );
    }

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
            sepBy(this.ident, seq(this.ws, char(","), this.ws)).opt(),
            this.ws,
            char(")"),
            this.ws,
            this.arrow,
            this.ws,
        ).chain(([, vName, , , bindings, , , , ,]) => {
            const variant = dataType.findVariant(vName);
            if (!variant) return empty() as unknown as Parser<{ variantName: string; bindings: string[]; body: S["expr"] }>;
            const bindingList = (bindings as string[] | undefined) ?? [];
            // Extend context with bindings
            let extendedCtx = ctx;
            for (let i = 0; i < bindingList.length; i++) {
                const field = variant.fields[i];
                if (field) {
                    extendedCtx = this.extendCtx(extendedCtx, bindingList[i]!, field.type);
                }
            }
            return this.exprProd(extendedCtx)
                .map((body) => ({ variantName: vName, bindings: bindingList, body }));
        }).map(([, result]) => result);
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
        ).chain(([, , , , ty, , ,]) => {
            assert(ty instanceof CodataType, "unfold type must be a CodataType");
            const codataType = ty as CodataType;
            return this.exprProd(ctx)
                .chain((seed) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.unfoldGenerators(codataType, ctx)
                                .chain((generators) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.unfold(codataType, seed, generators, Any)),
                                ),
                        )
                        .map(([, result]) => result),
                )
                .map(([, result]) => result);
        }).map(([, result]) => result);
    }

    @rule
    protected unfoldGenerators(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<{ observerName: string; body: S["expr"] }[]> {
        return sepBy(
            this.unfoldGenerator(codataType, ctx),
            seq(this.ws, char(","), this.ws),
        );
    }

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
        ).chain(([, obsName, ,]) => {
            const observer = codataType.findObserver(obsName);
            if (!observer) return empty() as unknown as Parser<{ observerName: string; body: S["expr"] }>;
            // Extend context with self: seed type
            const extendedCtx = this.extendCtx(ctx, "self", Any);
            return this.exprProd(extendedCtx)
                .map((body) => ({ observerName: obsName, body }));
        }).map(([, result]) => result);
    }

    // e.o (observation — postfix dot)
    @rule
    protected obsProd(ctx: unknown): Parser<S["expr"]> {
        return or(
            seq(this.obsProd(ctx), this.ws, char("."), this.ws, this.ident)
                .map(([scrut, , , , obs]) => this.obs(scrut as unknown as S["atom"], obs)),
            this.appProd(ctx),
        );
    }

    // Application (left-associative)
    @rule
    protected appProd(ctx: unknown): Parser<S["expr"]> {
        return or(
            seq(this.appProd(ctx), this.ws1, this.atomProd(ctx))
                .map(([fn, , arg]) => this.app(fn as unknown as S["atom"], arg)),
            this.atomProd(ctx) as unknown as Parser<S["expr"]>,
        );
    }

    @rule
    protected atomProd(ctx: unknown): Parser<S["atom"]> {
        return or(
            // ( expr )
            seq(char("("), this.ws, this.exprProd(ctx), this.ws, char(")"))
                .map(([, , e]) => this.paren(e)),
            // Variant construction: Ident(args)
            seq(this.variantName, this.ws, char("("), this.ws, sepBy(this.atomProd(ctx), seq(this.ws, char(","), this.ws)).opt(), this.ws, char(")"))
                .map(([name, , , , args, ,]) => this.variantCon(name as string, (args as S["atom"][] | undefined) ?? [])),
            // Variable
            this.ident.map((name) => this.varRef(name)),
        );
    }

    // ── Lexemes ───────────────────────────────────────────────────────────────

    @rule
    protected get variantName(): Parser<string> {
        // PascalCase identifier
        return seq(this.pascalFirst, this.identRest)
            .map(([h, t]) => h + t)
            .chain((name) => {
                // Reject if it's a keyword
                if (["fold", "unfold", "let", "in"].includes(name)) {
                    return empty() as unknown as Parser<string>;
                }
                return epsilon(name);
            })
            .map(([, r]) => r);
    }

    protected get pascalFirst(): Parser<string> {
        return pred((c) => c >= "A" && c <= "Z", "<Pascal-letter>");
    }

    @rule
    protected get ident(): Parser<string> {
        return seq(this.identFirst, this.identRest)
            .map(([h, t]) => h + t)
            .chain((name) => {
                if (["let", "in", "fold", "unfold"].includes(name)) {
                    return empty() as unknown as Parser<string>;
                }
                return epsilon(name);
            })
            .map(([, r]) => r);
    }

    protected get identFirst(): Parser<string> {
        return pred((c) => (c >= "a" && c <= "z") || c === "_", "<ident-head>");
    }

    @rule
    protected get identRest(): Parser<string> {
        return or(
            seq(this.identChar, this.identRest).map(([c, cs]) => c + cs),
            epsilon(""),
        );
    }

    protected get identChar(): Parser<string> {
        return pred(
            (c) => (c >= "a" && c <= "z") || (c >= "A" && c <= "Z") || (c >= "0" && c <= "9") || c === "_",
            "<ident-char>",
        );
    }

    protected kw(word: string): Parser<string> {
        return keyword(word, ["let", "in", "fold", "unfold"]);
    }

    // ── Whitespace ────────────────────────────────────────────────────────────

    protected override get ws(): Parser<string> {
        return or(
            seq(this.wsChar, this.ws).map(([c, cs]) => c + cs),
            epsilon(""),
        );
    }

    protected get ws1(): Parser<string> {
        return seq(this.wsChar, this.ws).map(([c, cs]) => c + cs);
    }

    protected get wsChar(): Parser<string> {
        return pred(
            (c) => c === " " || c === "\t" || c === "\n" || c === "\r",
            "<ws>",
        );
    }
}

// ── Concrete: AST builder ─────────────────────────────────────────────────────

/**
 * AST builder — parses LC text into Term objects.
 * No context (ctx is null). Pure syntax.
 */
export class LCAST extends AbstractLC<{ expr: Term; atom: Term; type: Type }> {
    override start(): Parser<Term> {
        return this.exprProd(null);
    }

    protected lam(param: string, type: Type, body: Term): Term {
        return new Lam(param, type, body);
    }

    protected app(fn: Term, arg: Term): Term {
        return new App(fn, arg);
    }

    protected let_(name: string, type: Type, def: Term, body: Term): Term {
        return new Let(name, type, def, body);
    }

    protected varRef(name: string): Term {
        return new Var(name);
    }

    protected paren(e: Term): Term {
        return e;
    }

    protected variantCon(name: string, _args: Term[]): Term {
        // Look up the type from registry to find the DataType
        // For now, we need the DataType — but we don't know which type this variant belongs to.
        // This is a limitation: variant construction needs to know the type.
        // For testing, we'll handle this by looking up the variant in the registry.
        // A proper implementation would have a variant-to-type mapping.
        throw new Error(`variantCon not yet implemented for ${name} — needs type registry lookup`);
    }

    protected obs(_scrutinee: Term, _observerName: string): Term {
        // Need the CodataType — similar issue as variantCon
        throw new Error("obs not yet implemented — needs type registry lookup");
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
        );
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
        );
    }
}