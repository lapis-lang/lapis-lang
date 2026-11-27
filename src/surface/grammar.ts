/**
 * The Lapis surface grammar — an executable grammar producing the surface AST.
 *
 * Implemented: one `data` declaration with named variants and an in-body
 * `fold`. Not implemented (no production): `behavior`, `protocol`, `relation`,
 * `query`, `io`, `unfold`/`merge`/`scan`/`satisfies:` body items, pattern
 * members, variant inheritance.
 *
 * ## Concrete syntax
 *
 * ```
 * program        ::= declaration*
 * declaration    ::= dataDecl
 *
 * dataDecl       ::= "data" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ dataBody
 * dataBody       ::= ␣(4) dataBodyItem+
 * dataBodyItem   ::= variantDecl | foldDecl          (* mapDecl is parsed, not elaborated *)
 *
 * variantDecl    ::= pascalIdent ( ␣ ident ":" ␣ typeExpr )*   (* fields, in declaration order *)
 * fieldDecl      ::= ident ":" ␣ typeExpr
 *
 * foldDecl       ::= "fold" ident specRecord? ⏎ foldBody
 * foldBody       ::= ␣(8) foldItem+
 * foldItem       ::= contractClause | caseArm
 * contractClause ::= clauseKind ":" ␣ ident* ( "|" ␣ )? ⏎ ␣(12) expr
 * clauseKind     ::= "demands" | "ensures" | "invariant" | "rescue"
 * caseArm        ::= armHead "->" armBody
 * armHead        ::= pascalIdent ( ␣ binding )* | "_" ( ␣ binding )*
 * binding        ::= ident | "_"
 * armBody        ::= expr | ⏎ ␣(12) expr
 *
 * mapDecl        ::= "map" ident specRecord? ⏎ mapBody
 * mapBody        ::= ␣(8) fieldTransform+
 * fieldTransform ::= ident ␣ binding "->" ␣ expr
 *
 * specRecord     ::= "<" ( specEntry ( "," ␣ specEntry )* )? ">"
 * specEntry      ::= "in"  ":" ␣ typeExpr
 *                  | "out" ":" ␣ typeExpr
 *                  | "para" | "histo" | "aux"            (* bare flags *)
 *                  | "aux" ":" ␣ "#" ident
 *                  | ident ":" ␣ expr                    (* e.g. properties; unvalidated *)
 *
 * typeExpr       ::= atomType
 * atomType       ::= "(" typeExpr ")"
 *                  | pascalIdent                          (* a declared type *)
 *                  | "Family" | "Self" | "Any" | "Nothing"
 *
 * expr           ::= keywordExpr
 * keywordExpr    ::= binaryExpr ( ␣ keywordPart )+
 *                  | binaryExpr
 * keywordPart    ::= ident ":" ␣ expr
 * binaryExpr     ::= binaryExpr ␣ binaryOp ␣ unaryExpr
 *                  | unaryExpr
 * binaryOp       ::= symbolicOp | ident
 * unaryExpr      ::= unaryExpr ␣ ident                   (* unary send *)
 *                  | primary
 * primary        ::= literal
 *                  | "(" expr ")"
 *                  | reference
 *                  | "nil" | "true" | "false"
 *                  | construction | variantRef
 *                  | ident                              (* operation reference *)
 *
 * construction   ::= pascalIdent ( ␣ ident ":" ␣ expr )+
 * variantRef     ::= pascalIdent
 * reference      ::= "self" | "Family" | "Self"
 *                  | "old" ident | "prev" ident | "aux" ident
 *
 * literal        ::= patternLiteral | stringLiteral | charLiteral
 * stringLiteral  ::= '"' .* '"'                          (* no escapes beyond \" *)
 * charLiteral    ::= "'" . "'"
 *
 * ident          ::= alphaLower alnum*                  (* excludes keywords *)
 * pascalIdent    ::= alphaUpper alnum*                  (* excludes Family, Self *)
 * symbolicOp     ::= ( "+" | "-" | "*" | "/" | "<" | ">" | "=" | "!" | "?" | "&"
 *                    | "|" | "," | "." )+
 * comment        ::= opener ( comment | notCloser )* closer   (* nests; metasyntax *)
 *                                                      (* opener "*" "/", closer "/" "*" *)
 * hws            ::= " "*        hws1 ::= " "+       (* spaces only — never tabs *)
 * ```
 *
 * ## Layout (§7)
 *
 * L1: a block's contents sit at exactly the introducing line's column + 4.
 * L2: a newline separates body lines; blank lines and comments are eaten
 * between them.
 *
 *            0  declaration          8  fold item / arm
 *            4  declaration body    12  multi-line arm body
 *
 * The column is a `@rule` *parameter* (`item(column)`), not a pre-pass: the
 * engine memoizes one slot per column, which is its documented answer for
 * context-sensitive grammars. `layout.ts` supplies the newline-excluding
 * `hws`/`hws1`, since the engine's `ws` family matches newlines too.
 *
 * ## Three structural decisions
 *
 * 1. **No application production.** There is no `expr expr` and no `value:`
 *    suffix. Application is a *core* rule: a send to a function-typed receiver
 *    applies it. The surface can never produce such a receiver — `atomType`
 *    has no function-type form — so the rule is reached by elaboration only.
 * 2. **Rejection is the production path's job.** A failed `@requires` yields
 *    `undefined` in the forest, which is not a rejection. Premises are checked
 *    inline; a failed branch yields `empty()`.
 * 3. **Greedy keyword collection.** When `key: arg` pairs follow an expression
 *    they all belong to one send — never nested. So a construction absorbs the
 *    pairs after it, and a nested construction must be parenthesized.
 */

import {
    char,
    empty,
    epsilon,
    Grammar,
    literal,
    or,
    type Parser,
    rule,
    seq,
} from "@lapis-lang/lang-forma"

import type {
    ArmHead,
    AtomType,
    CaseArm,
    ContractClause,
    DataBodyItem,
    DataDecl,
    Declaration,
    Expr,
    FieldDecl,
    FieldTransform,
    FoldDecl,
    KeyArg,
    MapDecl,
    Primary,
    SpecEntry,
    SpecRecord,
    SurfaceProgram,
    VariantDecl,
} from "./ast.ts"
import {
    charLiteral,
    ident,
    keyword,
    pascalIdent,
    patternLiteral,
    stringLiteral,
    SURFACE_KEYWORDS,
    symbolicOp,
} from "./lexemes.ts"

import {
    ARM_BODY_COLUMN,
    ARM_COLUMN,
    DECL_BODY_COLUMN,
    hws,
    hws1,
    lineEnd,
    spaces,
    trivia,
} from "./layout.ts"

import { BUILTIN_TYPE_NAMES } from "./resolve.ts"

/** The shape: every production's parse-tree type. */
export interface SurfaceShape {
    [k: string]: unknown
    program: SurfaceProgram
    declaration: Declaration
    expr: Expr
    primary: Primary
    atomType: AtomType
    specRecord: SpecRecord
}

/**
 * The abstract surface grammar: productions plus abstract semantic actions.
 *
 * A concrete subclass chooses the representation and the actions. Only one is
 * needed today — `SurfaceParse`, which builds the AST — but keeping the actions
 * abstract means a trace or diagnostic interpretation needs no new productions.
 */
export abstract class AbstractSurface<S extends SurfaceShape> extends Grammar<S> {
    // ── Abstract semantic actions ────────────────────────────────────────────

    /** Assemble a program from its declarations (§4). */
    protected abstract program(declarations: Declaration[]): S["program"]

    /** Assemble a `data` declaration (§4.1). */
    protected abstract dataDecl(
        name: string,
        parent: string | undefined,
        items: DataBodyItem[],
    ): S["declaration"]

    /** Assemble a variant declaration (§4.1). */
    protected abstract variantDecl(name: string, fields: FieldDecl[]): VariantDecl

    /** Assemble a `fold` declaration (§5.1). */
    protected abstract foldDecl(
        name: string,
        spec: SpecRecord | undefined,
        contractClauses: ContractClause[],
        arms: CaseArm[],
    ): FoldDecl

    /** Assemble a `map` declaration (§5.3). */
    protected abstract mapDecl(
        name: string,
        spec: SpecRecord | undefined,
        transforms: FieldTransform[],
    ): MapDecl

    /** Assemble a message chain from a receiver and its messages (§3.3). */
    protected abstract call(
        receiver: Primary,
        parts: KeyArg[],
        messages: string[],
    ): Expr

    /** Assemble a binary call (§3.1). */
    protected abstract binOp(op: string, lhs: Expr, rhs: Expr): Expr

    /** Assemble a unary call (§3.1). */
    protected abstract unaryOp(op: string, operand: Primary): Expr

    // ── Shared productions ───────────────────────────────────────────────────

    /**
     * A name where the grammar also admits a keyword.
     *
     * `ident` excludes keywords, but some positions legitimately spell one as a
     * name: a clause's bindings are `self`/`old`, a spec's keys include `in`/`aux`.
     */
    @rule
    protected nameOrKeyword(): Parser<string> {
        return or(
            ident,
            or(...SURFACE_KEYWORDS.map((word) => keyword(word))),
        )
    }

    /**
     * A name an arm head may bind.
     *
     * An arm head's bindings are the variant's field names, so a keyword is
     * admissible only where a variant could have declared one (it cannot — a
     * field is an `ident`). The machinery-supplied names are therefore excluded
     * here: `in`, `self`, `old`, `prev`, and `aux` are read from a body, never
     * declared in a head, which is what keeps a field from colliding with one.
     */
    private armBindingName(): Parser<string> {
        return or(
            ident,
            or(...this.bindableKeywords().map((word) => keyword(word))),
        )
    }

    /** The keywords a field may be named with — i.e. none of the machinery's. */
    private bindableKeywords(): readonly string[] {
        return SURFACE_KEYWORDS.filter((word) =>
            word !== "in" && word !== "self" && word !== "old" && word !== "prev" &&
            word !== "aux"
        )
    }

    // ── Program and declarations (§4) ────────────────────────────────────────

    /** `program ::= declaration*` — declarations only, no expression statements. */
    @rule
    protected programProd(): Parser<S["program"]> {
        return seq(
            trivia,
            this.declarationProd(),
            seq(trivia, this.declarationProd()).map(([, d]) => d as Declaration).many(),
            trivia,
        ).map(([, first, rest]) =>
            this.program([first, ...(rest as Declaration[])] as Declaration[])
        )
    }

    /** `declaration ::= dataDecl` — the other five forms have no production yet. */
    @rule
    protected declarationProd(): Parser<S["declaration"]> {
        return this.dataDeclProd()
    }

    /**
     * A declaration's name position.
     *
     * Admits `Family`/`Self`, which `pascalIdent` excludes: a declaration that
     * *takes* a reserved name must parse, so resolution can report it with a
     * remedy. A parse failure would give the author no reason.
     */
    @rule
    protected declarationName(): Parser<string> {
        return or(pascalIdent, keyword("Family"), keyword("Self"))
    }

    /** `dataDecl ::= "data" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ dataBody`, body at 4. */
    @rule
    protected dataDeclProd(): Parser<S["declaration"]> {
        return seq(
            keyword("data"),
            hws1,
            this.declarationName(),
            this.parentClause(),
            lineEnd,
            this.body(DECL_BODY_COLUMN, (c) => this.dataBodyItem(c)),
        ).map(([, , name, parent, , items]) =>
            this.dataDecl(name as string, parent as string | undefined, items as DataBodyItem[])
        )
    }

    /** The optional `<: Parent` clause (§4.1). */
    private parentClause(): Parser<string | undefined> {
        return seq(hws, literal("<:"), hws1, pascalIdent)
            .map(([, , , parent]) => parent as string)
            .opt()
            .map((p) => p ?? undefined)
    }

    /**
     * A block: items at exactly `column`, interleaved with trivia.
     *
     * Each item consumes its own line end, so a dedent ends the block rather
     * than being absorbed. The column is a parameter, so a misplaced item fails
     * the branch instead of being silently accepted.
     */
    @rule
    protected body<T>(column: number, item: (column: number) => Parser<T>): Parser<T[]> {
        return seq(
            trivia,
            item(column),
            seq(trivia, item(column)).map(([, i]) => i).many(),
        ).map(([, first, rest]) => [first, ...(rest as T[])])
    }

    /** `dataBodyItem ::= variantDecl | foldDecl` — `mapDecl` parses but is not elaborated. */
    @rule
    protected dataBodyItem(column: number): Parser<DataBodyItem> {
        return or<DataBodyItem>(
            this.mapDeclProd(column),
            this.foldDeclProd(column),
            this.variantDeclProd(column),
        )
    }

    /**
     * `variantDecl ::= pascalIdent ( ␣ ident ":" ␣ typeExpr )*` (§4.1).
     *
     * Fields are positional in declaration order; the surface spells them by
     * name.
     */
    @rule
    protected variantDeclProd(column: number): Parser<VariantDecl> {
        return seq(
            spaces(column),
            pascalIdent,
            this.fieldDecls(),
            lineEnd,
        ).map(([, name, fields]) => this.variantDecl(name as string, fields as FieldDecl[]))
    }

    /** The zero-or-more `name: Type` fields of a variant declaration. */
    private fieldDecls(): Parser<FieldDecl[]> {
        return seq(hws1, ident, hws, char(":"), hws, this.atomTypeProd())
            .map(([, name, , , , type]) => ({ name: name as string, type }))
            .many()
    }

    // ── Fold declarations (§5.1) ─────────────────────────────────────────────

    /**
     * ```
     * foldDecl ::= "fold" ident specRecord? ⏎ foldBody
     * foldBody ::= ␣(8) foldItem+
     * ```
     */
    @rule
    protected foldDeclProd(column: number): Parser<FoldDecl> {
        return seq(
            spaces(column),
            keyword("fold"),
            hws1,
            ident,
            hws,
            this.specRecordProd().opt(),
            lineEnd,
            this.body(ARM_COLUMN, (c) => this.foldItemProd(c)),
        ).map(([, , , name, , spec, , items]) => {
            const foldItems = items as FoldItem[]
            return this.foldDecl(
                name as string,
                spec as SpecRecord | undefined,
                foldItems.filter((i): i is ContractClause & { itemKind: "clause" } =>
                    i.itemKind === "clause"
                ),
                foldItems.filter((i): i is CaseArm & { itemKind: "arm" } => i.itemKind === "arm"),
            )
        })
    }

    /** `foldItem ::= contractClause | caseArm` (§5.1). */
    @rule
    protected foldItemProd(column: number): Parser<FoldItem> {
        return or<FoldItem>(
            this.contractClauseProd(column),
            this.caseArmProd(column),
        )
    }

    /**
     * A map is **field-keyed**, not variant-keyed: each transform names a field
     * and binds its own parameter, so only the named fields change. Recursion
     * through `Family` descends automatically — that is what makes it a map
     * rather than a fold that happens to rebuild, and what makes it fusible.
     */
    @rule
    protected mapDeclProd(column: number): Parser<MapDecl> {
        return seq(
            spaces(column),
            keyword("map"),
            hws1,
            ident,
            hws,
            this.specRecordProd().opt(),
            lineEnd,
            this.body(ARM_COLUMN, (c) => this.fieldTransformProd(c)),
        ).map(([, , , name, , spec, , transforms]) =>
            this.mapDecl(
                name as string,
                spec as SpecRecord | undefined,
                transforms as FieldTransform[],
            )
        )
    }

    /** `fieldTransform ::= ident ␣ binding "->" ␣ expr` — the field's value binds to `param`. */
    @rule
    protected fieldTransformProd(column: number): Parser<FieldTransform> {
        return seq(
            spaces(column),
            ident,
            hws1,
            this.bindingName(),
            hws,
            literal("->"),
            this.armBody(),
            lineEnd,
        ).map(([, field, , param, , , body]) => ({
            field: field as string,
            param: param as string,
            body: body as Expr,
        }))
    }

    /**
     * Two body forms: inline after `|` on the head's line, or indented to 12 on
     * the next. Any `ident*` head is accepted — the bindable-name set per clause
     * kind is a resolution rule, not a parse rule.
     */
    @rule
    protected contractClauseProd(column: number): Parser<ContractClause & { itemKind: "clause" }> {
        return seq(
            spaces(column),
            or(
                keyword("demands").map(() => "demands" as const),
                keyword("ensures").map(() => "ensures" as const),
                keyword("invariant").map(() => "invariant" as const),
                keyword("rescue").map(() => "rescue" as const),
            ),
            hws,
            char(":"),
            hws,
            this.identRun(),
            this.clauseBody(),
        ).map(([, kind, , , , bindings, body]) => ({
            itemKind: "clause" as const,
            kind: kind as ContractClause["kind"],
            bindings: bindings as string[],
            body: body as Expr,
        }))
    }

    /** A clause's body: inline after `|`, or indented on the next line (§7). */
    private clauseBody(): Parser<Expr> {
        return or<Expr>(
            // Inline: `| expr` then the line end.
            seq(hws, char("|"), hws1, this.exprProd(), lineEnd)
                .map((parts) => parts[3] as Expr),
            // Indented: an optional `|`, the line end, then column 12.
            seq(hws, char("|").opt(), lineEnd, spaces(ARM_BODY_COLUMN), this.exprProd())
                .map((parts) => parts[4] as Expr),
        )
    }

    /**
     * A clause's parameter list. Keywords are admitted — the machinery supplies
     * `self`, `old`, `result`, `err`, `args`, `retry`, all of which are keywords.
     *
     * The separator is `hws1`, not `hws`: an empty-matching separator inside a
     * repetition makes the segmentation ambiguous (n names, hundreds of
     * derivations, one list).
     */
    private identRun(): Parser<string[]> {
        return seq(
            this.bindingName(),
            seq(hws1, this.bindingName()).map(([, n]) => n as string).many(),
        )
            .map(([first, rest]) => [first as string, ...(rest as string[])])
    }

    /**
     * A binding name that is not followed by `:` — a clause head ends where its
     * `|` separator begins, and `|` is a symbolic-operator character (§2.3), so
     * without this guard it reads as one more binding.
     */
    private bindingName(): Parser<string> {
        return this.nameOrKeyword().bind((name) =>
            seq(hws, or(char(":"), char("|"))).opt().bind((stop) =>
                stop === undefined ? epsilon(name) : empty<string>()
            )
        )
    }

    /** `caseArm ::= armHead "->" armBody` */
    @rule
    protected caseArmProd(column: number): Parser<CaseArm & { itemKind: "arm" }> {
        return seq(
            spaces(column),
            this.armHeadProd(),
            hws,
            literal("->"),
            this.armBody(),
            lineEnd,
        ).map(([, head, , , body]) => ({
            itemKind: "arm" as const,
            head: head as ArmHead,
            body: body as Expr,
        }))
    }

    /** A variant name with its bindings, or the wildcard `_`. */
    @rule
    protected armHeadProd(): Parser<ArmHead> {
        return or(
            seq(pascalIdent, this.bindings()).map(([variant, bindings]) => ({
                variant: variant as string,
                bindings: bindings as string[],
            })),
            seq(char("_"), this.bindings()).map(([, bindings]) => ({
                bindings: bindings as string[],
            })),
        )
    }

    /** The bindings an arm head carries, each preceded by horizontal space. */
    private bindings(): Parser<string[]> {
        return or(
            seq(hws1, this.armBindingName()).map(([, name]) => name as string),
            seq(hws1, char("_")).map(() => "_"),
        ).many().map((names: string[]) => names)
    }

    /**
     * An arm body: inline, or indented to 12 on the next line. The indented form
     * is tried first (longer match) so a continued body is not misread as inline.
     */
    private armBody(): Parser<Expr> {
        return or(
            seq(hws, lineEnd, spaces(ARM_BODY_COLUMN), this.exprProd())
                .map(([, , , e]) => e as Expr),
            seq(hws1, this.exprProd()).map(([, e]) => e as Expr),
        )
    }
    // ── Spec records (§3.7) ──────────────────────────────────────────────────

    /**
     * ```
     * specRecord ::= "<" ( specEntry ( "," ␣ specEntry )* )? ">"
     * specEntry  ::= ident ":" ␣ expr | ident
     * ```
     */
    @rule
    protected specRecordProd(): Parser<SpecRecord> {
        return seq(
            char("<"),
            hws,
            this.specEntryProd(),
            seq(hws, char(","), hws, this.specEntryProd())
                .map(([, , , e]) => e as SpecEntry)
                .many(),
            hws,
            char(">"),
        ).map(([, , first, rest]) => ({
            entries: [first as SpecEntry, ...(rest as SpecEntry[])],
        })).or(
            seq(char("<"), hws, char(">")).map(() => ({ entries: [] })),
        )
    }

    /**
     * The value's shape follows the key, so the key selects the production. A
     * key-blind alternation would let `in: 5` parse as a type entry, and would
     * give `Any` two derivations (declared name and variant reference), doubling
     * every forest that declares a spec.
     */
    @rule
    protected specEntryProd(): Parser<SpecEntry> {
        return this.nameOrKeyword().bind((key) =>
            seq(hws, char(":"), hws, this.specValue(key))
                .map(([, , , entry]) => ({ ...(entry as object), key } as SpecEntry))
                .or(epsilon({ key, kind: "flag" as const } as SpecEntry))
        )
    }

    /**
     * `in`/`out` take a type and nothing else — a non-type value is a parse
     * failure, not a silently accepted expression. `aux` takes a `#name`;
     * `properties` takes an expression; `para`/`histo` are bare flags. An
     * unrecognized key falls back to an expression so the resolver can report it.
     */
    private specValue(key: string): Parser<Omit<SpecEntry, "key">> {
        switch (key) {
            case "in":
            case "out":
                return this.atomTypeProd().map((type) => ({ kind: "type" as const, type }))
            case "aux":
                return seq(char("#"), ident).map(([, name]) => ({
                    kind: "aux" as const,
                    name: name as string,
                }))
            default:
                return this.exprProd().map((value) => ({ kind: "expr" as const, value }))
        }
    }

    // ── Types (§3.8) ─────────────────────────────────────────────────────────

    /**
     * The entire type grammar: a type is a name, never a shape. There is no
     * function-type production, so nothing here builds a type a later pass must
     * reject. The parenthesised branch re-enters this production, so `((Any))`
     * parses and the inner value is an `AtomType` by construction, not by cast.
     *
     * `Any`/`Nothing` are matched before `pascalIdent` because they are not
     * keywords: otherwise they would also match as declared names, yielding a
     * second, structurally identical parse.
     */
    @rule
    protected atomTypeProd(): Parser<S["atomType"]> {
        return or(
            seq(char("("), hws, this.atomTypeProd(), hws, char(")")).map(
                ([, , inner]) => inner,
            ),
            or(
                keyword("Family").map(() => atom("Family")),
                keyword("Self").map(() => atom("Self")),
                keyword("Any").map(() => atom("Any")),
                keyword("Nothing").map(() => atom("Nothing")),
            ),
            pascalIdent.bind((name) =>
                BUILTIN_TYPE_NAMES.includes(name) ? empty<AtomType>() : epsilon(atom(name))
            ),
        )
    }

    // ── Expressions (§3) ─────────────────────────────────────────────────────

    /** `expr ::= keywordExpr` (§3.2). */
    @rule
    protected exprProd(): Parser<S["expr"]> {
        return this.keywordExprProd()
    }

    /** Three strictly ordered levels; binary is one flat left-associative level. */
    @rule
    protected keywordExprProd(): Parser<Expr> {
        return this.binaryExprProd().bind((receiver) =>
            this.keywordParts(receiver as S["expr"]).map((parts) => {
                const keyArgs = parts as KeyArg[]
                return keyArgs.length === 0 ? receiver : this.call(asPrimary(receiver), keyArgs, [])
            })
        )
    }

    /**
     * All `key: arg` pairs form one call, never nested sends. So a part's value is
     * a `binaryExpr`, not an `expr` — at `expr` level `a: b c: d` would nest as
     * `a: (b c: d)`, the reading the greedy rule forbids. And a construction
     * receiver takes no parts: its own production has this same shape.
     */
    private keywordParts(receiver: S["expr"]): Parser<KeyArg[]> {
        if (takesNoKeywordParts(receiver)) return epsilon([])
        return seq(hws1, ident, hws, char(":"), hws, this.binaryExprProd())
            .map(([, key, , , , value]) => ({ key: key as string, value: value as Expr }))
            .many()
    }

    /**
     * `binaryExpr ::= binaryExpr ␣ binaryOp ␣ unaryExpr | unaryExpr`.
     *
     * Left-associative by construction: the tail is `(op rhs)*`, folded left.
     */
    @rule
    protected binaryExprProd(): Parser<Expr> {
        return seq(this.unaryExprProd(), this.binaryTail())
            .map(([first, rest]) => {
                let acc = first as Expr
                for (const [op, rhs] of rest as [string, Expr][]) {
                    acc = this.binOp(op, acc, rhs)
                }
                return acc
            })
    }

    /** The `(op unaryExpr)*` tail of a binary expression. */
    private binaryTail(): Parser<[string, Expr][]> {
        return seq(hws1, this.binaryOpProd(), hws1, this.unaryExprProd())
            .map(([, op, , rhs]) => [op as string, rhs as Expr] as [string, Expr])
            .many()
    }

    /**
     * `binaryOp ::= symbolicOp | ident` (§3.2).
     *
     * The symbolic form is tried first: a declared operator is a symbolic name,
     * and `ident` excludes keywords, so the two are lexically disjoint in the
     * position that matters.
     */
    @rule
    protected binaryOpProd(): Parser<string> {
        return or(symbolicOp, ident)
    }

    /**
     * `unaryExpr ::= unaryExpr ␣ ident | primary`.
     *
     * The postfix unary send of §3.1 level 3. A `primary` that is not a paren
     * yields itself.
     */
    @rule
    protected unaryExprProd(): Parser<Expr> {
        return seq(this.primaryProd(), this.unaryMessages())
            .map(([first, messages]) => {
                const msgs = messages as string[]
                return msgs.length === 0 ? first : this.call(first as Primary, [], msgs)
            })
    }

    /**
     * A unary message stops before a `key:` pair: `x rest: Empty` is a keyword
     * call whose receiver is `x`, not a send of `Empty` to `rest:`. Without the
     * guard both readings parse and mean different things.
     */
    private unaryMessages(): Parser<string[]> {
        return seq(hws1, this.nameOrKeyword(), seq(hws, char(":")).opt())
            .bind(([, name, colon]) =>
                colon === undefined ? epsilon(name as string) : empty<string>()
            )
            .many()
    }

    /**
     * Ordered by specificity. A parenthesized expression re-opens the message
     * chain; a PascalCase name is a constructor position, so it is tried before
     * `ident` (which admits lowercase names only).
     */
    @rule
    protected primaryProd(): Parser<S["primary"]> {
        return or(
            this.parenOrRecord(),
            this.constructionOrVariantRef(),
            this.referenceProd(),
            this.literalProd(),
            ident.map((name) => opRef(name)),
        )
    }

    /** `( expr )` — parentheses re-open the message chain. */
    private parenOrRecord(): Parser<Primary> {
        return seq(char("("), hws, this.exprProd(), hws, char(")"))
            .map(([, , inner]) => ({ kind: "paren", inner: inner as Expr }) as Primary)
    }

    /**
     * `Type Variant field: v …` (qualified construction or qualified reference),
     * `Variant field: v …` (bare construction), or `Variant` (bare reference).
     *
     * One production: the qualified form is `pascalIdent ␣ pascalIdent …`, and
     * bare/qualified is a resolution concern, not a syntactic one.
     */
    private constructionOrVariantRef(): Parser<Primary> {
        return seq(pascalIdent, this.qualifierOrFields())
            .map(([first, tail]) => {
                const rest = tail as
                    | { kind: "qualified"; variant: string; fields: KeyArg[] }
                    | { kind: "bare"; fields: KeyArg[] }
                if (rest.kind === "qualified") {
                    return rest.fields.length === 0
                        ? ({
                            kind: "variantRef",
                            qualifier: first as string,
                            name: rest.variant,
                        }) as Primary
                        : ({
                            kind: "construction",
                            qualifier: first as string,
                            variant: rest.variant,
                            fields: rest.fields,
                        }) as Primary
                }
                return rest.fields.length === 0
                    ? ({ kind: "variantRef", name: first as string }) as Primary
                    : ({
                        kind: "construction",
                        variant: first as string,
                        fields: rest.fields,
                    }) as Primary
            })
    }

    /** What follows a leading PascalCase name: a qualifier + variant, or fields. */
    private qualifierOrFields(): Parser<
        | { kind: "qualified"; variant: string; fields: KeyArg[] }
        | { kind: "bare"; fields: KeyArg[] }
    > {
        return or<
            | { kind: "qualified"; variant: string; fields: KeyArg[] }
            | { kind: "bare"; fields: KeyArg[] }
        >(
            seq(hws1, pascalIdent, this.namedFields()).map(([, variant, fields]) => ({
                kind: "qualified" as const,
                variant: variant as string,
                fields: fields as KeyArg[],
            })),
            this.namedFields().map((fields) => ({
                kind: "bare" as const,
                fields: fields as KeyArg[],
            })),
        )
    }

    /**
     * A field's value cannot be an unparenthesized construction. `key: arg` pairs
     * are collected greedily, so in `Push value: Empty rest: Empty` every pair
     * belongs to `Push`; letting the value absorb `rest:` would give the input a
     * second reading meaning something else. A nested construction is therefore
     * parenthesized, and the gate rejects the absorbing reading outright.
     */
    private namedFields(): Parser<KeyArg[]> {
        return seq(hws1, ident, hws, char(":"), hws, this.binaryExprProd())
            .bind(([, key, , , , value]) =>
                containsUnparenthesizedConstruction(value)
                    ? empty<KeyArg>()
                    : epsilon({ key: key as string, value: value as Expr })
            )
            .many()
    }

    /** `self` | `in` | `Family` | `Self` | `old x` | `prev x` | `aux x` */
    private referenceProd(): Parser<Primary> {
        return or(
            keyword("self").map(() => ({ kind: "ref", name: "self" }) as Primary),
            // The fold's extra argument, read like `self`: machinery-supplied, so
            // it is never declared in an arm head (see `bindings`).
            keyword("in").map(() => ({ kind: "ref", name: "in" }) as Primary),
            keyword("Family").map(() => ({ kind: "ref", name: "Family" }) as Primary),
            keyword("Self").map(() => ({ kind: "ref", name: "Self" }) as Primary),
            seq(keyword("old"), hws1, ident).map(([, , n]) =>
                ({ kind: "ref", name: `old ${n}` }) as Primary
            ),
            seq(keyword("prev"), hws1, ident).map(([, , n]) =>
                ({ kind: "ref", name: `prev ${n}` }) as Primary
            ),
            seq(keyword("aux"), hws1, ident).map(([, , n]) =>
                ({ kind: "ref", name: `aux ${n}` }) as Primary
            ),
        )
    }

    /**
     * A pattern literal is tried last: it is a permissive numeric form and must
     * not shadow a symbolic operator.
     */
    private literalProd(): Parser<Primary> {
        return or(
            stringLiteral.map((text) => ({ kind: "lit", text }) as Primary),
            charLiteral.map((text) => ({ kind: "lit", text }) as Primary),
            // A pattern literal is tried last: it is a permissive numeric form
            // and must not shadow a symbolic operator.
            seq(patternLiteral, seq(hws1, ident).many()).bind(([text, trailing]) =>
                (trailing as string[][]).length === 0
                    ? epsilon(({ kind: "lit", text }) as Primary)
                    : empty<Primary>()
            ),
        )
    }
}

/** A `fold` body item: a contract clause or a case arm (§5.1). */
type FoldItem =
    | (ContractClause & { itemKind: "clause" })
    | (CaseArm & { itemKind: "arm" })

/** `AtomType` construction — one spelling for the four built-ins and names. */
function atom(name: string): AtomType {
    return { kind: "atom", name }
}

/** An operation reference — a `camelCase` name in `primary` position (§3.6.1). */
function opRef(name: string): Primary {
    return { kind: "opRef", name }
}

/** Whether an expression is a variant construction (§3.4). */
function isConstruction(expr: unknown): boolean {
    return typeof expr === "object" && expr !== null &&
        (expr as { kind?: string }).kind === "construction"
}

/**
 * Whether a receiver cannot take keyword parts.
 *
 * Two shapes, both from §3.3's greedy collection — the `key: value` pairs after
 * a construction belong to that construction, so nothing enclosing it may claim
 * them:
 *
 * - A **variant reference or construction** is the construction production's own
 *   material (§3.4), so a PascalCase-led receiver followed by pairs _is_ a
 *   construction. Only a `camelCase` receiver — an operation or a binding —
 *   sends keyword messages.
 * - An expression that **contains** a construction holds one too: in
 *   `Push value: 1 + 2 rest: Empty`, the `rest:` pair belongs to `Push`, not to
 *   the `+` it appears to follow.
 */
function takesNoKeywordParts(expr: unknown): boolean {
    if (isConstruction(expr) || kindOf(expr) === "variantRef") return true
    return typeof expr === "object" && expr !== null &&
        containsUnparenthesizedConstruction(expr as Expr)
}

/** An AST node's discriminant, for the guards above. */
function kindOf(expr: unknown): string | undefined {
    return typeof expr === "object" && expr !== null ? (expr as { kind?: string }).kind : undefined
}

/**
 * Whether an expression contains a construction that is not parenthesized.
 *
 * A construction absorbs the `key: value` pairs that follow it (§3.3, §3.4), so
 * one appearing as a *field value* would swallow the enclosing construction's
 * remaining fields. The corpus writes such a nesting in parentheses —
 * `Cons head: 1 rest: (Cons head: 2 rest: Nil)` — and a value reached through a
 * `Paren` is already closed, so the walk stops there.
 */
function containsUnparenthesizedConstruction(expr: Expr): boolean {
    switch (expr.kind) {
        case "construction":
            return true
        case "call":
            return containsUnparenthesizedConstruction(expr.receiver) ||
                expr.parts.some((p) => containsUnparenthesizedConstruction(p.value))
        case "binop":
            return containsUnparenthesizedConstruction(expr.lhs) ||
                containsUnparenthesizedConstruction(expr.rhs)
        case "unary":
            return containsUnparenthesizedConstruction(expr.operand)
        case "paren":
            return false
        default:
            return false
    }
}

/**
 * Reinterpret a parsed primitive as a message receiver.
 *
 * §3.2's `keywordExpr` heads a chain with a `binaryExpr`; when that expression is
 * not itself a call, the chain's receiver is its `primary`. A `BinOp`/`UnaryOp`
 * receiver means the chain applies to a computed value, which the surface
 * spells by parenthesizing — so the conversion is total for well-formed input.
 */
function asPrimary(expr: Expr): Primary {
    return expr.kind === "paren" ? expr : (expr as Primary)
}

/**
 * The AST-building surface grammar.
 *
 * `parse` yields the forest of programs; `parseOne` is the convenience form for
 * the single-parse case the pipeline uses.
 */
export class SurfaceParse extends AbstractSurface<SurfaceShape> {
    /**
     * Parse a program, returning it, or `undefined` when the input is not a
     * well-formed program.
     *
     * A well-formed input has exactly one parse — the grammar is unambiguous by
     * construction (declarations are keyword-led, the message chain is greedy,
     * and each precedence level is a single production).
     */
    parseProgram(source: string): SurfaceProgram | undefined {
        return [...this.parse(source)][0] as SurfaceProgram | undefined
    }

    override start(): Parser<SurfaceProgram> {
        return this.programProd()
    }

    // ── Semantic actions ─────────────────────────────────────────────────────

    protected program(declarations: Declaration[]): SurfaceProgram {
        return { declarations }
    }

    protected dataDecl(
        name: string,
        parent: string | undefined,
        items: DataBodyItem[],
    ): DataDecl {
        return parent === undefined
            ? { kind: "data", name, items }
            : { kind: "data", name, parent, items }
    }

    protected variantDecl(name: string, fields: FieldDecl[]): VariantDecl {
        return { kind: "variantDecl", name, fields }
    }

    protected foldDecl(
        name: string,
        spec: SpecRecord | undefined,
        contractClauses: ContractClause[],
        arms: CaseArm[],
    ): FoldDecl {
        return spec === undefined
            ? { kind: "foldDecl", name, contractClauses, arms }
            : { kind: "foldDecl", name, spec, contractClauses, arms }
    }

    protected mapDecl(
        name: string,
        spec: SpecRecord | undefined,
        transforms: FieldTransform[],
    ): MapDecl {
        return spec === undefined
            ? { kind: "mapDecl", name, transforms }
            : { kind: "mapDecl", name, spec, transforms }
    }

    protected call(receiver: Primary, parts: KeyArg[], messages: string[]): Expr {
        return { kind: "call", receiver, parts, messages }
    }

    protected binOp(op: string, lhs: Expr, rhs: Expr): Expr {
        return { kind: "binop", op, lhs, rhs }
    }

    protected unaryOp(op: string, operand: Primary): Expr {
        return { kind: "unary", op, operand }
    }
}
