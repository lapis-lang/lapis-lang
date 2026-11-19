/**
 * The Lapis surface grammar — an executable grammar producing the surface AST.
 *
 * Scope is one `data` declaration with its `fold`: enough for a *complete*
 * program, because the surface has no top-level expression form (a program is
 * `declaration*`, overview §12.6). Patterns, captures, inheritance, `unfold` in
 * data, and the other five declaration kinds are later production sets that
 * plug into this same shape.
 *
 * Two structural notes that differ from the core grammar:
 *
 * 1. **Layout is significant** (`surface-grammar.md` §7). Block-introducing
 *    productions take the child column as a parameter (`@rule item(column)`),
 *    so the engine memoizes one slot per column — the documented answer for
 *    context-sensitive grammars. `src/surface/layout.ts` supplies the
 *    newline-excluding primitives the engine's `ws` family cannot provide.
 * 2. **There is no application production** (§3.2). Application is *derived*: a
 *    keyword send eliminates its receiver and applies the arguments, and a
 *    receiver of function type applies through `value:` (§3.3).
 *
 * Rejection is the production path's job, not a contract's: a failed `@requires`
 * yields `undefined` in the forest, which is not a rejection. Premises are
 * therefore checked inline and a failed branch yields `empty()`.
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
    specialValue,
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
     * A name in a position where the grammar admits a keyword.
     *
     * `ident` excludes keywords (§2.2), but several productions legitimately
     * spell a keyword as a *name*: a contract clause's bindings are `self`,
     * `old`, and the result (§5.1), a spec record's keys include `aux` and `in`
     * (§3.7), and a binding may legitimately be named after any of them. In
     * each case the keyword *is* the name, so the position admits it.
     */
    @rule
    protected nameOrKeyword(): Parser<string> {
        return or(
            ident,
            or(...SURFACE_KEYWORDS.map((word) => keyword(word))),
        )
    }

    // ── Program and declarations (§4) ────────────────────────────────────────

    /**
     * `program ::= declaration*` (§4).
     *
     * A program is declarations only — no expression statements, no binding
     * form (overview §12.6, §12.21).
     */
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

    /** `dataDecl | behaviorDecl | …` — this PBI implements `data` (§4.1). */
    @rule
    protected declarationProd(): Parser<S["declaration"]> {
        return this.dataDeclProd()
    }

    /**
     * ```
     * dataDecl ::= "data" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ dataBody
     * dataBody ::= ␣(4) dataBodyItem+
     * ```
     */
    /**
     * A declaration's name position.
     *
     * This admits `Family` and `Self`, which `pascalIdent` excludes as keywords:
     * a declaration that *takes* a reserved name must parse, so resolution can
     * report it with a remedy (#101). Failing to parse would give the author no
     * indication of why the name is rejected.
     */
    @rule
    protected declarationName(): Parser<string> {
        return or(pascalIdent, keyword("Family"), keyword("Self"))
    }

    /**
     * `dataDecl ::= "data" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ dataBody`
     * `dataBody ::= ␣(4) dataBodyItem+`
     */
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
     * A block: one or more items at exactly `column`, interleaved with trivia
     * (§7 L1/L2).
     *
     * Each item consumes its own line terminator, so a line that dedents past
     * `column` ends the block rather than being absorbed into it. The column is
     * the production's parameter, so an item at any other column fails the
     * branch instead of being silently accepted.
     */
    @rule
    protected body<T>(column: number, item: (column: number) => Parser<T>): Parser<T[]> {
        return seq(
            trivia,
            item(column),
            seq(trivia, item(column)).map(([, i]) => i).many(),
        ).map(([, first, rest]) => [first, ...(rest as T[])])
    }

    /** `variantDecl | foldDecl | …` — this PBI implements the first two (§4.1). */
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
     * ```
     * mapDecl         ::= "map" ident specRecord? ⏎ mapBody
     * mapBody         ::= ␣(8) fieldTransform+
     * fieldTransform  ::= ident ␣ binding "->" ␣ expr
     * ```
     *
     * A map's body is **field-keyed**, not variant-keyed (§5.3): each transform
     * names a *field* and binds its own parameter, so the structure is preserved and
     * only the named fields change. Recursion through `Family`/`Self` fields is
     * automatic — that is what makes a map a map rather than a fold that happens to
     * rebuild, and only a map is eligible for pipeline fusion.
     *
     * The production reuses a fold arm's shape, keyed on a field name instead of a
     * variant name, so a transform needs no lambda form: `head x -> (x + 1)` binds
     * the field's current value to `x`.
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

    /** `fieldTransform ::= ident ␣ binding "->" ␣ expr` (§5.3). */
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
     * ```
     * contractClause ::= clauseKind ":" ␣ ident* ( "|" ␣ )? ⏎ ␣(12) expr
     * clauseKind ::= "demands" | "ensures" | "invariant" | "rescue"
     * ```
     *
     * Two body forms, matching §7's "inline vs. indented bodies" rule: the body
     * follows the `|` separator on the head's own line (`ensures: self old result
     * | result`), or it is indented to `ARM_BODY_COLUMN` on the next. §5.1's
     * examples use the first; the production above reads as the second.
     *
     * The bindable-name set per clause kind and the head arity are #110's scope;
     * this production accepts any `ident*`.
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
     * One or more binding names separated by whitespace — a clause's parameter
     * list.
     *
     * Keywords are admitted: a clause's bindings are supplied by the machinery
     * and are literally `self`, `old`, `result`, `err`, `args`, `retry`
     * (`surface-grammar.md` §5.1), every one of which is a keyword in §2.5.
     *
     * The separator is `hws1`, not `hws`: a separator that may match the empty
     * string and sits inside a repetition makes the *segmentation* ambiguous —
     * three names separated by optional whitespace have hundreds of derivations,
     * all yielding the same list. Requiring a non-empty gap between names makes
     * the reading unique.
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

    /**
     * ```
     * caseArm ::= armHead "->" armBody
     * armHead ::= pascalIdent ( ␣ binding )* | "_" ( ␣ binding )*
     * binding  ::= ident | "_"
     * armBody  ::= expr | ⏎ ␣(12) expr
     * ```
     */
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
            seq(hws1, this.nameOrKeyword()).map(([, name]) => name as string),
            seq(hws1, char("_")).map(() => "_"),
        ).many().map((names: string[]) => names)
    }

    /**
     * An arm body: an expression on the arm's own line, or one indented to
     * `ARM_BODY_COLUMN` on the next (`surface-grammar.md` §7's "inline vs.
     * indented bodies").
     *
     * The indented form is tried first — §7's "longer match" rule — so an arm
     * whose body continues on the next line is not misread as an inline body.
     * There is no separator: the production is `armHead "->" armBody`, and §5.2's
     * `guard | payload` form belongs to `unfold` arms alone.
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
     * One spec entry (§3.7).
     *
     * The value's shape **follows the key** (§3.7's table), so the key selects the
     * production rather than the value being tried against every shape. A
     * key-blind alternation would have two consequences, and both are defects: a
     * type-shaped key could silently accept a value that is not a type (`in: 5`,
     * `in: (Any -> Any)` both parse as expressions), and a value that is both a
     * type and an expression would parse twice (`Any` is a declared name _and_ a
     * variant reference), doubling every forest that declares a spec.
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
     * A spec entry's value, chosen by its key (§3.7's table).
     *
     * `in`/`out` carry a type (and nothing else — a non-type value is a parse
     * failure rather than a silently accepted expression), `aux` carries a `#name`
     * reference, and `properties` carries an expression. An unrecognized key falls
     * back to an expression so it reaches the resolver with a name to report;
     * `para` and `histo` are bare flags and so never take a value at all.
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
     * `atomType ::= "(" typeExpr ")" | pascalIdent | "Family" | "Self" | "Any" |
     * "Nothing"` (§3.8), where `typeExpr` *is* `atomType`.
     *
     * This is the entire type grammar: there is no function-type production, so
     * nothing here can build a type that some later pass has to reject. Because
     * the parenthesised branch re-enters this same production, `((Any))` parses
     * exactly as the spec's recursion says it should, and the inner value is an
     * `AtomType` by construction rather than by cast.
     *
     * The built-in names are matched *before* `pascalIdent`, and `pascalIdent`
     * then rejects them: `Any` and `Nothing` are not keywords (§2.5 reserves
     * only `Family` and `Self`), so the PascalCase production would otherwise
     * match them as declared names and yield a second, structurally identical
     * parse — an ambiguity with no semantic difference, but one that doubles
     * every forest containing a bound.
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

    /**
     * ```
     * keywordExpr ::= binaryExpr ( ␣ keywordPart )+
     *               | binaryExpr
     * binaryExpr  ::= binaryExpr ␣ binaryOp ␣ unaryExpr | unaryExpr
     * unaryExpr   ::= unaryExpr ␣ ident | primary
     * ```
     *
     * The three levels are strictly ordered (§3.1) and binary is a *single*
     * flat, left-associative level — there is no precedence ladder.
     */
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
     * The greedy keyword parts (§3.3): all `key: arg` pairs form one call.
     *
     * Two restrictions, both from §3.3's *greedy collection* rule — "when
     * keyword suffixes are present, _all_ `key: arg` pairs are collected into a
     * single `KeywordCall` — they are not nested sends":
     *
     * - A part's **value is a `binaryExpr`**, not a full `expr`. Parsing it at the
     *   `expr` level would let `a: b c: d` nest as `a: (b c: d)`, which is exactly
     *   the reading the greedy rule forbids.
     * - A receiver that is a **variant reference or construction takes no parts**:
     *   §3.4's `construction ::= pascalIdent ( ␣ ident ":" ␣ expr )+` has this same
     *   shape, so a PascalCase receiver followed by `key: value` pairs _is_ a
     *   construction. Only a `camelCase` receiver (an operation or binding) sends.
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
     * The postfix unary messages of §3.1 level 3, one or more `␣ ident` sends.
     *
     * A message stops before a `key:` pair: `nil rest: Empty` is a *keyword call*
     * whose receiver is `nil` (§3.3's greedy collection), not the unary send
     * `nil rest:` applied to `Empty`. Without the guard both readings parse and
     * mean different things.
     */
    private unaryMessages(): Parser<string[]> {
        return seq(hws1, this.nameOrKeyword(), seq(hws, char(":")).opt())
            .bind(([, name, colon]) =>
                colon === undefined ? epsilon(name as string) : empty<string>()
            )
            .many()
    }

    /**
     * `primary ::= literal | "(" expr ")" | arrayLiteral | recordLiteral |
     *              specRecord | reference | "nil" "true" "false" |
     *              variantRef | ident`
     *
     * The construction and variant-reference forms are §3.4's; array, record
     * and spec-record primaries arrive with #97.
     */
    @rule
    protected primaryProd(): Parser<S["primary"]> {
        return or(
            // A parenthesized expression re-opens the message chain (§3.3) or
            // is a record literal (§3.6). Parenthesized first: the record form
            // needs the `key:` head, which an expression cannot produce.
            this.parenOrRecord(),
            // Construction and variant reference — PascalCase-led (§3.4).
            this.constructionOrVariantRef(),
            // References (§3.5).
            this.referenceProd(),
            // Literals (§2.4).
            this.literalProd(),
            // A bare operation reference or binding (§3.6.1). `nil`/`true`/`false`
            // are excluded: they are values, not references (§2.5), and letting
            // `ident` match them would give every such literal two parses.
            ident.bind((name) => isSpecialValue(name) ? empty<Primary>() : epsilon(opRef(name))),
        )
    }

    /** `( expr )` — a parenthesized expression (§3.2). */
    private parenOrRecord(): Parser<Primary> {
        return seq(char("("), hws, this.exprProd(), hws, char(")"))
            .map(([, , inner]) => ({ kind: "paren", inner: inner as Expr }) as Primary)
    }

    /**
     * `Type Variant field: v …` (qualified construction or qualified reference),
     * `Variant field: v …` (bare construction), or `Variant` (bare reference).
     *
     * One production: the qualified form is `pascalIdent ␣ pascalIdent …`, and
     * bare/qualified is a resolution concern, not a syntactic one (#84).
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
     * The named fields of a construction: `( ␣ ident ":" ␣ expr )+` (§3.4).
     */
    /**
     * The named fields of a construction: `( ␣ ident ":" ␣ expr )+` (§3.4).
     *
     * A field's value cannot itself be an unparenthesized construction. §3.3's
     * greedy collection decides it: "when keyword suffixes are present, _all_
     * `key: arg` pairs are collected into a single `KeywordCall` — they are not
     * nested sends." A construction has that same shape (§3.4), so in
     * `Push value: Empty rest: Empty` every pair belongs to `Push`. Allowing the
     * value to absorb `rest:` would give the input a second reading, and the two
     * readings mean different things.
     *
     * A nested construction is therefore written in parentheses — which is how
     * the corpus always writes it: `Cons head: 1 rest: (Cons head: 2 rest: Nil)`.
     * The gate below rejects the absorbing reading outright rather than letting
     * it through as an ambiguous branch.
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

    /** §3.5's references: `self`, `Family`, `Self`, `old x`, `prev x`, `aux x`. */
    private referenceProd(): Parser<Primary> {
        return or(
            keyword("self").map(() => ({ kind: "ref", name: "self" }) as Primary),
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
     * The literal spellings of §2.4: a quoted string or char, a pattern-matched
     * text, or one of §2.5's special values.
     */
    private literalProd(): Parser<Primary> {
        return or(
            stringLiteral.map((text) => ({ kind: "lit", text }) as Primary),
            charLiteral.map((text) => ({ kind: "lit", text }) as Primary),
            specialValue.map((text) => ({ kind: "lit", text }) as Primary),
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

/** §2.5's special values: they are values, not operation references. */
function isSpecialValue(name: string): boolean {
    return name === "nil" || name === "true" || name === "false"
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
