/**
 * Lapis language grammar — executable grammar built on jsr:@lapis-lang/zipper-grammar.
 *
 * Architecture:
 *  - `LapisShape`    — per-production type map (shape interface).
 *  - `LapisGrammar`  — abstract class; declares all productions as @rule
 *                      getters/methods. No AST construction here.
 *  - `LapisParser`   — concrete subclass; implements factory methods to build
 *                      class-based AST nodes (src/ast.ts).
 *
 * Indentation strategy (P4P-inspired, no pre-pass):
 *  Fixed 4-space indent unit. Every block-introducing production is a
 *  parameterised @rule method accepting `col: number` (the child column).
 *  `spaces(n)` matches exactly n space characters via recursion, cached per n.
 */

import { Grammar, rule } from 'jsr:@lapis-lang/zipper-grammar';
import type { GrammarShape, Parser, Span } from 'jsr:@lapis-lang/zipper-grammar';
import {
    type Node,
    type TopLevelDecl,
    type DataBodyItem,
    type BehaviorBodyItem,
    AuxRef,
    ArrayLit,
    BinarySend,
    Block,
    CaseArm,
    CoSelfRef,
    ContractClause,
    type ContractKind,
    DataDecl,
    BehaviorDecl,
    FoldDecl,
    FamilyRef,
    Field,
    Ident,
    IntLit,
    IoDecl,
    KeywordSend,
    MapDecl,
    MergeDecl,
    Module,
    OldRef,
    PrefixSend,
    ProtocolDecl,
    PrevRef,
    QueryDecl,
    Record,
    RecordEntry,
    RelationDecl,
    Satisfies,
    SelfRef,
    Spec,
    SpecEntry,
    StringLit,
    SymbolLit,
    UnarySend,
    UnfoldDecl,
    Variant,
    VariantRef,
} from './ast.ts';

// ── Shape ─────────────────────────────────────────────────────────────────────

export interface LapisShape extends GrammarShape {
    // Lexical
    digit: string;
    alpha: string;
    alnum: string;
    ident: string;
    pascalIdent: string;
    intLit: IntLit;
    strLit: StringLit;
    symbolLit: SymbolLit;
    comment: null;
    ws: null;
    newline: string;
    // Keywords (return their literal text)
    kwData: string;
    kwBehavior: string;
    kwProtocol: string;
    kwRelation: string;
    kwQuery: string;
    kwIo: string;
    kwFold: string;
    kwUnfold: string;
    kwMap: string;
    kwMerge: string;
    kwSatisfies: string;
    kwNot: string;
    kwSelf: string;
    kwFamily: string;
    kwSelf2: string;  // capital Self
    kwOld: string;
    kwPrev: string;
    kwAux: string;
    // Expressions
    expr: Node;
    orExpr: Node;
    andExpr: Node;
    cmpExpr: Node;
    addExpr: Node;
    mulExpr: Node;
    consExpr: Node;
    unaryExpr: Node;
    messageChain: Node;
    primary: Node;
    // Composites
    blockLit: Block;
    recordLit: Record;
    arrayLit: ArrayLit;
    specRecord: Spec;
    // Declarations (top-level)
    module: Module;
    topDecl: TopLevelDecl;
    // Sub-declarations
    variantDecl: Variant;
    foldDecl: FoldDecl;
    unfoldDecl: UnfoldDecl;
    mapDecl: MapDecl;
    mergeDecl: MergeDecl;
    satisfiesClause: Satisfies;
    caseArm: CaseArm;
    fieldDecl: Field;
    contractClause: ContractClause;
}

// ── Indent unit ───────────────────────────────────────────────────────────────

const INDENT = 4;

// ── Abstract grammar ──────────────────────────────────────────────────────────

export abstract class LapisGrammar<S extends LapisShape> extends Grammar<S> {

    override start(): Parser<S['module']> { return this.module; }

    // ── Whitespace / structural ──────────────────────────────────────────────

    @rule get newline(): Parser<S['newline']> {
        return this.or(
            this.literal('\r\n') as Parser<string>,
            this.literal('\n') as Parser<string>,
        ) as unknown as Parser<S['newline']>;
    }

    /** Match exactly `n` space characters. Cached per n via @rule on method. */
    @rule spaces(n: number): Parser<string> {
        if (n === 0) return this.epsilon('');
        return this.seq(this.char(' '), this.spaces(n - 1)).map(() => '');
    }

    /** Inline whitespace (spaces/tabs) — zero or more, no newlines */
    @rule get ws(): Parser<S['ws']> {
        return this.pred(c => c === ' ' || c === '\t', '<ws>').many()
            .map(() => null) as unknown as Parser<S['ws']>;
    }

    /** `"..."` comment — consumed and discarded */
    @rule get comment(): Parser<S['comment']> {
        return this.seq(
            this.char('"'),
            this.pred(c => c !== '"', '<non-quote>').many(),
            this.char('"'),
        ).map(() => null) as unknown as Parser<S['comment']>;
    }

    // ── Lexical ───────────────────────────────────────────────────────────────

    @rule get digit(): Parser<S['digit']> {
        return this.pred(c => c >= '0' && c <= '9', '<digit>') as unknown as Parser<S['digit']>;
    }

    @rule get alpha(): Parser<S['alpha']> {
        return this.pred(
            c => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c === '_',
            '<alpha>',
        ) as unknown as Parser<S['alpha']>;
    }

    @rule get alnum(): Parser<S['alnum']> {
        return this.pred(
            c => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                 (c >= '0' && c <= '9') || c === '_',
            '<alnum>',
        ) as unknown as Parser<S['alnum']>;
    }

    /** camelCase (or underscore-starting) identifier, not a keyword */
    @rule get ident(): Parser<S['ident']> {
        const head = this.pred(
            c => (c >= 'a' && c <= 'z') || c === '_',
            '<ident-head>',
        );
        return this.seq(head, this.alnum.many())
            .map(([h, t], span) => this.mkIdent(h + (t as string[]).join(''), span)) as unknown as Parser<S['ident']>;
    }

    /** PascalCase identifier */
    @rule get pascalIdent(): Parser<S['pascalIdent']> {
        const head = this.pred(c => c >= 'A' && c <= 'Z', '<pascal-head>');
        return this.seq(head, this.alnum.many())
            .map(([h, t], span) => this.mkPascalIdent(h + (t as string[]).join(''), span)) as unknown as Parser<S['pascalIdent']>;
    }

    @rule get intLit(): Parser<S['intLit']> {
        return this.seq(this.digit, this.digit.many())
            .map(([h, t], span) => this.mkIntLit(Number(h + (t as string[]).join('')), span)) as unknown as Parser<S['intLit']>;
    }

    /** Single-quoted string `'...'` (no escape sequences in v0) */
    @rule get strLit(): Parser<S['strLit']> {
        return this.seq(
            this.char("'"),
            this.pred(c => c !== "'" && c !== '\n', '<strchar>').many(),
            this.char("'"),
        ).map(([, chars], span) =>
            this.mkStrLit((chars as string[]).join(''), span),
        ) as unknown as Parser<S['strLit']>;
    }

    /** `#name` symbol literal */
    @rule get symbolLit(): Parser<S['symbolLit']> {
        const head = this.pred(
            c => (c >= 'a' && c <= 'z') || c === '_',
            '<sym-head>',
        );
        return this.seq(
            this.char('#'),
            head,
            this.alnum.many(),
        ).map(([, h, t], span) =>
            this.mkSymbolLit(h + (t as string[]).join(''), span),
        ) as unknown as Parser<S['symbolLit']>;
    }

    // ── Keywords ──────────────────────────────────────────────────────────────
    // Each keyword is followed by a word-boundary check (next char is not alnum/_)
    // to prevent e.g. "dataFoo" from matching "data".

    private kw(word: string): Parser<string> {
        return this.seq(
            this.literal(word),
            // lookahead: peek character after word must not be alnum or _
            this.pred(c => !((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                             (c >= '0' && c <= '9') || c === '_'), '<word-boundary>').opt(),
        ).map(([w]) => w);
    }

    @rule get kwData():      Parser<S['kwData']>      { return this.kw('data')      as unknown as Parser<S['kwData']>;      }
    @rule get kwBehavior():  Parser<S['kwBehavior']>  { return this.kw('behavior')  as unknown as Parser<S['kwBehavior']>;  }
    @rule get kwProtocol():  Parser<S['kwProtocol']>  { return this.kw('protocol')  as unknown as Parser<S['kwProtocol']>;  }
    @rule get kwRelation():  Parser<S['kwRelation']>  { return this.kw('relation')  as unknown as Parser<S['kwRelation']>;  }
    @rule get kwQuery():     Parser<S['kwQuery']>     { return this.kw('query')     as unknown as Parser<S['kwQuery']>;     }
    @rule get kwIo():        Parser<S['kwIo']>        { return this.kw('io')        as unknown as Parser<S['kwIo']>;        }
    @rule get kwFold():      Parser<S['kwFold']>      { return this.kw('fold')      as unknown as Parser<S['kwFold']>;      }
    @rule get kwUnfold():    Parser<S['kwUnfold']>    { return this.kw('unfold')    as unknown as Parser<S['kwUnfold']>;    }
    @rule get kwMap():       Parser<S['kwMap']>       { return this.kw('map')       as unknown as Parser<S['kwMap']>;       }
    @rule get kwMerge():     Parser<S['kwMerge']>     { return this.kw('merge')     as unknown as Parser<S['kwMerge']>;     }
    @rule get kwSatisfies(): Parser<S['kwSatisfies']> { return this.kw('satisfies') as unknown as Parser<S['kwSatisfies']>; }
    @rule get kwNot():       Parser<S['kwNot']>       { return this.kw('not')       as unknown as Parser<S['kwNot']>;       }
    @rule get kwSelf():      Parser<S['kwSelf']>      { return this.kw('self')      as unknown as Parser<S['kwSelf']>;      }
    @rule get kwFamily():    Parser<S['kwFamily']>    { return this.kw('Family')    as unknown as Parser<S['kwFamily']>;    }
    @rule get kwSelf2():     Parser<S['kwSelf2']>     { return this.kw('Self')      as unknown as Parser<S['kwSelf2']>;     }
    @rule get kwOld():       Parser<S['kwOld']>       { return this.kw('old')       as unknown as Parser<S['kwOld']>;       }
    @rule get kwPrev():      Parser<S['kwPrev']>      { return this.kw('prev')      as unknown as Parser<S['kwPrev']>;      }
    @rule get kwAux():       Parser<S['kwAux']>       { return this.kw('aux')       as unknown as Parser<S['kwAux']>;       }

    // ── Expressions ───────────────────────────────────────────────────────────

    @rule get expr(): Parser<S['expr']>     { return this.orExpr  as unknown as Parser<S['expr']>; }
    @rule get orExpr(): Parser<S['orExpr']> {
        return this.or(
            this.seq(this.orExpr, this.ws, this.char('|'), this.ws, this.andExpr)
                .map(([l, , , , r], span) => this.mkBinaryOp(l as Node, '|', r as Node, span)) as Parser<S['andExpr']>,
            this.andExpr,
        ) as unknown as Parser<S['orExpr']>;
    }

    @rule get andExpr(): Parser<S['andExpr']> {
        return this.or(
            this.seq(this.andExpr, this.ws, this.char('&'), this.ws, this.cmpExpr)
                .map(([l, , , , r], span) => this.mkBinaryOp(l as Node, '&', r as Node, span)) as Parser<S['cmpExpr']>,
            this.cmpExpr,
        ) as unknown as Parser<S['andExpr']>;
    }

    @rule get cmpExpr(): Parser<S['cmpExpr']> {
        const op = this.or(
            this.literal('<=') as Parser<string>,
            this.literal('>=') as Parser<string>,
            this.literal('<>') as Parser<string>,
            this.char('=') as Parser<string>,
            this.char('<') as Parser<string>,
            this.char('>') as Parser<string>,
        );
        return this.or(
            this.seq(this.addExpr, this.ws, op, this.ws, this.addExpr)
                .map(([l, , o, , r], span) => this.mkBinaryOp(l as Node, o as string, r as Node, span)) as Parser<S['addExpr']>,
            this.addExpr,
        ) as unknown as Parser<S['cmpExpr']>;
    }

    @rule get addExpr(): Parser<S['addExpr']> {
        const op = this.or(this.char('+') as Parser<string>, this.char('-') as Parser<string>);
        return this.or(
            this.seq(this.addExpr, this.ws, op, this.ws, this.mulExpr)
                .map(([l, , o, , r], span) => this.mkBinaryOp(l as Node, o as string, r as Node, span)) as Parser<S['mulExpr']>,
            this.mulExpr,
        ) as unknown as Parser<S['addExpr']>;
    }

    @rule get mulExpr(): Parser<S['mulExpr']> {
        const op = this.or(this.char('*') as Parser<string>, this.char('/') as Parser<string>);
        return this.or(
            this.seq(this.mulExpr, this.ws, op, this.ws, this.consExpr)
                .map(([l, , o, , r], span) => this.mkBinaryOp(l as Node, o as string, r as Node, span)) as Parser<S['consExpr']>,
            this.consExpr,
        ) as unknown as Parser<S['mulExpr']>;
    }

    /** `,` used as concatenation/cons operator (design doc: `{value} , rest`) */
    @rule get consExpr(): Parser<S['consExpr']> {
        return this.or(
            this.seq(this.consExpr, this.ws, this.char(','), this.ws, this.unaryExpr)
                .map(([l, , , , r], span) => this.mkBinaryOp(l as Node, ',', r as Node, span)) as Parser<S['unaryExpr']>,
            this.unaryExpr,
        ) as unknown as Parser<S['consExpr']>;
    }

    @rule get unaryExpr(): Parser<S['unaryExpr']> {
        return this.or(
            this.seq(this.char('-'), this.ws, this.messageChain)
                .map(([, , e], span) => this.mkPrefixOp('-', e as Node, span)) as Parser<S['messageChain']>,
            this.seq(this.kwNot, this.char(' '), this.messageChain)
                .map(([, , e], span) => this.mkPrefixOp('not', e as Node, span)) as Parser<S['messageChain']>,
            this.messageChain,
        ) as unknown as Parser<S['unaryExpr']>;
    }

    /**
     * Smalltalk message chain: primary followed by zero or more sends.
     * Unary sends bind tighter; keyword sends are collected greedily.
     *
     *   messageChain = primary (unarySuffix* keywordSuffix?)?
     *   unarySuffix  = ' ' ident
     *   keywordSuffix = (' ' ident ':' ' ' expr)+
     */
    @rule get messageChain(): Parser<S['messageChain']> {
        return this.or(
            // primary + at least one keyword send
            this.seq(
                this.primary,
                // optional unary chain before keyword
                this.seq(this.char(' '), this.ident as Parser<S['ident']>)
                    .map(([, name]) => name as string).many(),
                // one or more keyword:arg pairs
                this.seq(
                    this.char(' '),
                    this.ident as Parser<S['ident']>,
                    this.char(':'),
                    this.char(' '),
                    this.primary,
                ).map(([, k, , , v]) => [k as string, v as Node] as [string, Node]).many().then(
                    // require at least one
                    this.epsilon(null)
                ),
            ).map(([recv, unaryNames, kwPairs], span) => {
                let node: Node = recv as Node;
                for (const name of unaryNames as string[])
                    node = this.mkUnarySend(node, name, span);
                const [pairs] = kwPairs as [Array<[string, Node]>, null];
                if (pairs.length > 0) {
                    const sels = pairs.map(p => p[0]);
                    const args = pairs.map(p => p[1]);
                    node = this.mkKeywordSend(node, sels, args, span);
                }
                return node;
            }) as Parser<S['primary']>,
            // primary + unary chain only
            this.seq(
                this.primary,
                this.seq(this.char(' '), this.ident as Parser<S['ident']>)
                    .map(([, name]) => name as string).many(),
            ).map(([recv, names], span) => {
                let node: Node = recv as Node;
                for (const name of names as string[])
                    node = this.mkUnarySend(node, name, span);
                return node;
            }) as Parser<S['primary']>,
            this.primary,
        ) as unknown as Parser<S['messageChain']>;
    }

    @rule get primary(): Parser<S['primary']> {
        return this.or<Node>(
            this.intLit as unknown as Parser<Node>,
            this.strLit as unknown as Parser<Node>,
            this.symbolLit as unknown as Parser<Node>,
            // Special references
            this.seq(this.kwOld, this.char(' '), this.ident)
                .map(([, , name], span) => this.mkOldRef(name as string, span)),
            this.seq(this.kwPrev, this.char(' '), this.ident)
                .map(([, , name], span) => this.mkPrevRef(name as string, span)),
            this.seq(this.kwAux, this.char(' '), this.ident)
                .map(([, , name], span) => this.mkAuxRef(name as string, span)),
            this.kwSelf.map((_, span) => this.mkSelfRef(span)),
            this.kwFamily.map((_, span) => this.mkFamilyRef(span)),
            this.kwSelf2.map((_, span) => this.mkCoSelfRef(span)),
            this.kwMerge.map((_, span) => this.mkIdentFromKw('merge', span)),
            // Nil / true / false
            this.literal('nil').map((_, span) => this.mkIdentNode('nil', span)),
            this.literal('true').map((_, span) => this.mkIdentNode('true', span)),
            this.literal('false').map((_, span) => this.mkIdentNode('false', span)),
            // Block literal [params | body]
            this.blockLit as unknown as Parser<Node>,
            // Array literal { items }
            this.arrayLit as unknown as Parser<Node>,
            // Record / parenthesised expr
            this.seq(this.char('('), this.expr, this.char(')'))
                .map(([, e]) => e as Node),
            // PascalIdent (variant reference) then optional message chain
            (this.pascalIdent as unknown as Parser<Node>),
            // camelCase identifier
            (this.ident as unknown as Parser<Node>),
        ) as unknown as Parser<S['primary']>;
    }

    // ── Block literal `[params | body]` ──────────────────────────────────────

    @rule get blockLit(): Parser<S['blockLit']> {
        // Form 1: [param1 param2 ... | expr]
        const withParams = this.seq(
            this.char('['),
            this.ident as Parser<S['ident']>,
            this.seq(this.char(' '), this.ident as Parser<S['ident']>)
                .map(([, name]) => name as string).many(),
            this.literal(' | '),
            this.expr,
            this.char(']'),
        ).map(([, first, rest, , body], span) => {
            const params = [first as string, ...(rest as string[])].map(
                name => this.mkIdentNode(name, span)
            );
            return this.mkBlock(params, body as Node, span);
        });
        // Form 2: [expr]  — block with no params
        const noParams = this.seq(
            this.char('['),
            this.expr,
            this.char(']'),
        ).map(([, body], span) => this.mkBlock([], body as Node, span));
        return this.or(withParams, noParams) as unknown as Parser<S['blockLit']>;
    }

    // ── Array literal `{ expr, expr, ... }` ──────────────────────────────────

    @rule get arrayLit(): Parser<S['arrayLit']> {
        const itemSep = this.seq(this.ws, this.char(','), this.ws);
        const items = this.seq(
            this.expr,
            itemSep.then(this.expr).map(([, e]) => e as Node).many(),
        ).map(([first, rest]) => [first as Node, ...(rest as Node[])]);
        return this.seq(
            this.char('{'),
            this.ws,
            this.or(
                items as Parser<Node[]>,
                this.epsilon([]) as unknown as Parser<Node[]>,
            ),
            this.ws,
            this.char('}'),
        ).map(([, , elems], span) => this.mkArrayLit(elems as Node[], span)) as unknown as Parser<S['arrayLit']>;
    }

    // ── Record `(key: val, ...)` ──────────────────────────────────────────────

    @rule get recordLit(): Parser<S['recordLit']> {
        const entry = this.seq(
            this.ident as Parser<S['ident']>,
            this.literal(': '),
            this.expr,
        ).map(([k, , v], span) => this.mkRecordEntry(k as string, v as Node, span));
        const sep = this.seq(this.ws, this.char(','), this.ws);
        const entries = this.seq(
            entry,
            sep.then(entry).map(([, e]) => e).many(),
        ).map(([first, rest]) => [first, ...(rest as RecordEntry[])]);
        return this.seq(
            this.char('('),
            this.ws,
            this.or(
                entries as Parser<RecordEntry[]>,
                this.epsilon([]) as unknown as Parser<RecordEntry[]>,
            ),
            this.ws,
            this.char(')'),
        ).map(([, , es], span) => this.mkRecord(es as RecordEntry[], span)) as unknown as Parser<S['recordLit']>;
    }

    // ── Spec record `<key: val, key, ...>` ───────────────────────────────────

    @rule get specRecord(): Parser<S['specRecord']> {
        // An entry is either `key: value` or a bare flag like `para`, `histo`
        const flagEntry = this.ident.map(
            (name, span) => this.mkSpecEntry(name as string, null, span)
        );
        const kvEntry = this.seq(
            this.ident as Parser<S['ident']>,
            this.char(':'),
            this.ws,
            this.expr,
        ).map(([k, , , v], span) => this.mkSpecEntry(k as string, v as Node, span));
        const entry = this.or(kvEntry as Parser<SpecEntry>, flagEntry as unknown as Parser<SpecEntry>);
        const sep = this.seq(this.ws, this.char(','), this.ws);
        const entries = this.seq(
            entry,
            sep.then(entry).map(([, e]) => e).many(),
        ).map(([first, rest]) => [first, ...(rest as SpecEntry[])]);
        return this.seq(
            this.char('<'),
            this.ws,
            this.or(entries as Parser<SpecEntry[]>, this.epsilon([]) as unknown as Parser<SpecEntry[]>),
            this.ws,
            this.char('>'),
        ).map(([, , es], span) => this.mkSpec(es as SpecEntry[], span)) as unknown as Parser<S['specRecord']>;
    }

    // ── Field declaration `fieldName: TypeName` ───────────────────────────────

    @rule get fieldDecl(): Parser<S['fieldDecl']> {
        return this.or(
            this.seq(this.ident as Parser<S['ident']>, this.literal(': '), this.pascalIdent)
                .map(([name, , type_], span) => this.mkField(name as string, type_ as string, span)),
            this.ident.map((name, span) => this.mkField(name as string, null, span)),
        ) as unknown as Parser<S['fieldDecl']>;
    }

    // ── Contract clause ───────────────────────────────────────────────────────

    @rule get contractClause(): Parser<S['contractClause']> {
        const clause = (kw: ContractKind) =>
            this.seq(
                this.literal(kw + ':'),
                this.ws,
                this.blockLit as unknown as Parser<Block>,
            ).map(([, , blk], span) => this.mkContractClause(kw, blk, span));
        return this.or(
            clause('invariant') as Parser<ContractClause>,
            clause('demands') as Parser<ContractClause>,
            clause('ensures') as Parser<ContractClause>,
            clause('rescue') as Parser<ContractClause>,
        ) as unknown as Parser<S['contractClause']>;
    }

    // ── Pattern case arm ──────────────────────────────────────────────────────

    /**
     * `PatternName binding1 binding2 ... -> bodyExpr`
     *
     * Bindings are camelCase names (fields) or `_` (wildcard).
     * The body can be on the same line or indented on the next.
     * `col` is the column at which this arm must start (already spaces-consumed
     * by the caller).
     */
    @rule caseArm(col: number): Parser<S['caseArm']> {
        const binding = this.or(
            this.char('_') as Parser<string>,
            this.ident as unknown as Parser<string>,
        );
        const bindingList = this.seq(
            binding,
            this.seq(this.char(' '), binding).map(([, b]) => b as string).many(),
        ).map(([first, rest]) => [first as string, ...(rest as string[])]);
        const arrow = this.literal(' -> ');
        // body on same line
        const inlineBody = this.seq(
            this.pascalIdent as Parser<string>,
            this.seq(this.char(' '), bindingList as Parser<string[]>).map(([, bl]) => bl).opt(),
            arrow,
            this.expr,
        ).map(([variant, bindings, , body], span) =>
            this.mkCaseArm(variant as string, bindings as string[] ?? [], body as Node, span)
        );
        // body on next line (indented)
        const blockBody = this.seq(
            this.pascalIdent as Parser<string>,
            this.seq(this.char(' '), bindingList as Parser<string[]>).map(([, bl]) => bl).opt(),
            this.literal(' ->'),
            this.newline,
            this.spaces(col + INDENT),
            this.expr,
        ).map(([variant, bindings, , , , body], span) =>
            this.mkCaseArm(variant as string, bindings as string[] ?? [], body as Node, span)
        );
        return this.or(blockBody, inlineBody) as unknown as Parser<S['caseArm']>;
    }

    // ── fold declaration ──────────────────────────────────────────────────────

    @rule foldDecl(col: number): Parser<S['foldDecl']> {
        const childCol = col + INDENT;
        // Contract clauses appear before case arms in body, one per line
        const contractLine = this.seq(this.spaces(childCol), this.contractClause)
            .map(([, c]) => c as ContractClause);
        const armLine = this.seq(this.spaces(childCol), this.caseArm(childCol))
            .map(([, a]) => a as CaseArm);
        const bodyLine: Parser<ContractClause | CaseArm> = this.or(
            contractLine as Parser<ContractClause | CaseArm>,
            armLine as Parser<ContractClause | CaseArm>,
        );
        return this.seq(
            this.kwFold,
            this.char(' '),
            this.ident as Parser<S['ident']>,
            this.specRecord.opt(),
            this.newline,
            bodyLine,
            this.seq(this.newline, bodyLine).map(([, l]) => l as ContractClause | CaseArm).many(),
        ).map(([, , name, spec, , first, rest], span) => {
            const all = [first, ...(rest as Array<ContractClause | CaseArm>)];
            const contracts = all.filter((x): x is ContractClause => x instanceof ContractClause);
            const arms = all.filter((x): x is CaseArm => x instanceof CaseArm);
            return this.mkFoldDecl(name as string, spec as Spec | null, contracts, arms, span);
        }) as unknown as Parser<S['foldDecl']>;
    }

    // ── unfold declaration ────────────────────────────────────────────────────

    @rule unfoldDecl(col: number): Parser<S['unfoldDecl']> {
        const childCol = col + INDENT;
        const armLine = this.seq(this.spaces(childCol), this.caseArm(childCol))
            .map(([, a]) => a as CaseArm);
        return this.seq(
            this.kwUnfold,
            this.char(' '),
            this.pascalIdent as Parser<string>,
            this.specRecord.opt(),
            this.newline,
            armLine,
            this.seq(this.newline, armLine).map(([, a]) => a as CaseArm).many(),
        ).map(([, , name, spec, , first, rest], span) =>
            this.mkUnfoldDecl(
                name as string,
                spec as Spec | null,
                [first as CaseArm, ...(rest as CaseArm[])],
                span,
            )
        ) as unknown as Parser<S['unfoldDecl']>;
    }

    // ── map declaration ───────────────────────────────────────────────────────

    @rule mapDecl(col: number): Parser<S['mapDecl']> {
        void col;  // map body is a single-line block literal
        return this.seq(
            this.kwMap,
            this.char(' '),
            this.ident as Parser<S['ident']>,
            this.specRecord.opt(),
            this.char(' '),
            this.blockLit as unknown as Parser<Block>,
        ).map(([, , name, spec, , blk], span) =>
            this.mkMapDecl(name as string, spec as Spec | null, blk as Block, span)
        ) as unknown as Parser<S['mapDecl']>;
    }

    // ── merge declaration ─────────────────────────────────────────────────────

    @rule mergeDecl(col: number): Parser<S['mergeDecl']> {
        void col;
        const refList = this.seq(
            this.symbolLit as unknown as Parser<SymbolLit>,
            this.seq(this.literal(', '), this.symbolLit as unknown as Parser<SymbolLit>)
                .map(([, s]) => s).many(),
        ).map(([first, rest]) =>
            ([first, ...(rest as SymbolLit[])]).map(s => s.name)
        );
        return this.seq(
            this.kwMerge,
            this.char(' '),
            this.ident as Parser<S['ident']>,
            this.char(' '),
            this.char('<'),
            refList as Parser<string[]>,
            this.char('>'),
        ).map(([, , name, , , refs], span) =>
            this.mkMergeDecl(name as string, refs as string[], span)
        ) as unknown as Parser<S['mergeDecl']>;
    }

    // ── satisfies clause ──────────────────────────────────────────────────────

    @rule get satisfiesClause(): Parser<S['satisfiesClause']> {
        return this.seq(
            this.kwSatisfies,
            this.literal(': '),
            this.pascalIdent as Parser<string>,
        ).map(([, , name], span) => this.mkSatisfies(name as string, span)) as unknown as Parser<S['satisfiesClause']>;
    }

    // ── Variant declaration ───────────────────────────────────────────────────

    /**
     * `VariantName field1: Type1 field2: Type2 ...`
     * with optional invariant clauses on same line or indented below.
     * `col` is the column at which this line starts (spaces already consumed).
     */
    @rule variantDecl(col: number): Parser<S['variantDecl']> {
        void col;
        const fieldPair = this.seq(
            this.ident as Parser<S['ident']>,
            this.literal(': '),
            this.pascalIdent as Parser<string>,
        ).map(([name, , type_], span) => this.mkField(name as string, type_ as string, span));
        const fields = this.seq(
            fieldPair,
            this.seq(this.char(' '), fieldPair).map(([, f]) => f as Field).many(),
        ).map(([first, rest]) => [first as Field, ...(rest as Field[])]);

        return this.seq(
            this.pascalIdent as Parser<string>,
            this.seq(this.char(' '), fields as Parser<Field[]>).map(([, fs]) => fs).opt(),
        ).map(([name, fieldList], span) =>
            this.mkVariant(name as string, fieldList as Field[] ?? [], [], span)
        ) as unknown as Parser<S['variantDecl']>;
    }

    // ── data declaration ──────────────────────────────────────────────────────

    @rule dataDecl(col: number): Parser<S['topDecl']> {
        const childCol = col + INDENT;
        const bodyForm: Parser<DataBodyItem> = this.or(
            this.foldDecl(childCol) as unknown as Parser<DataBodyItem>,
            this.unfoldDecl(childCol) as unknown as Parser<DataBodyItem>,
            this.mapDecl(childCol) as unknown as Parser<DataBodyItem>,
            this.mergeDecl(childCol) as unknown as Parser<DataBodyItem>,
            this.satisfiesClause as unknown as Parser<DataBodyItem>,
            this.variantDecl(childCol) as unknown as Parser<DataBodyItem>,
        );
        const bodyLine = this.seq(this.spaces(childCol), bodyForm)
            .map(([, item]) => item as DataBodyItem);
        const parent = this.seq(this.literal(' <: '), this.pascalIdent as Parser<string>)
            .map(([, name]) => name as string);
        return this.seq(
            this.kwData,
            this.char(' '),
            this.pascalIdent as Parser<string>,
            parent.opt(),
            this.newline,
            bodyLine,
            this.seq(this.newline, bodyLine).map(([, l]) => l as DataBodyItem).many(),
        ).map(([, , name, par, , first, rest], span) =>
            this.mkDataDecl(
                name as string,
                par as string | null,
                [first as DataBodyItem, ...(rest as DataBodyItem[])],
                span,
            )
        ) as unknown as Parser<S['topDecl']>;
    }

    // ── behavior declaration ──────────────────────────────────────────────────

    @rule behaviorDecl(col: number): Parser<S['topDecl']> {
        const childCol = col + INDENT;
        // Observer signatures: `name: <out: Type>`
        const observerSig = this.seq(
            this.ident as Parser<S['ident']>,
            this.literal(': '),
            this.specRecord,
        ).map(([name, , spec], span) => this.mkField(name as string, null, span));

        const bodyForm: Parser<BehaviorBodyItem | Field> = this.or(
            this.foldDecl(childCol) as unknown as Parser<BehaviorBodyItem>,
            this.unfoldDecl(childCol) as unknown as Parser<BehaviorBodyItem>,
            this.mapDecl(childCol) as unknown as Parser<BehaviorBodyItem>,
            this.mergeDecl(childCol) as unknown as Parser<BehaviorBodyItem>,
            observerSig as unknown as Parser<BehaviorBodyItem>,
        );
        const bodyLine = this.seq(this.spaces(childCol), bodyForm as Parser<BehaviorBodyItem | Field>)
            .map(([, item]) => item as BehaviorBodyItem | Field);
        const parent = this.seq(this.literal(' <: '), this.pascalIdent as Parser<string>)
            .map(([, name]) => name as string);
        return this.seq(
            this.kwBehavior,
            this.char(' '),
            this.pascalIdent as Parser<string>,
            parent.opt(),
            this.newline,
            bodyLine,
            this.seq(this.newline, bodyLine).map(([, l]) => l as BehaviorBodyItem | Field).many(),
        ).map(([, , name, par, , first, rest], span) => {
            const all = [first, ...(rest as Array<BehaviorBodyItem | Field>)] as Array<BehaviorBodyItem | Field>;
            const observers = all.filter((x): x is Field => x instanceof Field);
            const body = all.filter((x): x is BehaviorBodyItem => !(x instanceof Field));
            return this.mkBehaviorDecl(name as string, par as string | null, observers, body, span);
        }) as unknown as Parser<S['topDecl']>;
    }

    // ── protocol declaration ──────────────────────────────────────────────────

    @rule protocolDecl(col: number): Parser<S['topDecl']> {
        const childCol = col + INDENT;
        const bodyLine = this.seq(this.spaces(childCol), this.foldDecl(childCol))
            .map(([, f]) => f as FoldDecl);
        const parent = this.seq(this.literal(' <: '), this.pascalIdent as Parser<string>)
            .map(([, name]) => name as string);
        return this.seq(
            this.kwProtocol,
            this.char(' '),
            this.pascalIdent as Parser<string>,
            parent.opt(),
            this.newline,
            bodyLine,
            this.seq(this.newline, bodyLine).map(([, l]) => l as FoldDecl).many(),
        ).map(([, , name, par, , first, rest], span) =>
            this.mkProtocolDecl(
                name as string,
                par as string | null,
                [first as FoldDecl, ...(rest as FoldDecl[])],
                span,
            )
        ) as unknown as Parser<S['topDecl']>;
    }

    // ── relation declaration ──────────────────────────────────────────────────

    @rule relationDecl(col: number): Parser<S['topDecl']> {
        const childCol = col + INDENT;
        const bodyForm: Parser<Variant | FoldDecl> = this.or(
            this.foldDecl(childCol) as unknown as Parser<FoldDecl>,
            this.variantDecl(childCol) as unknown as Parser<FoldDecl>,
        );
        const bodyLine = this.seq(this.spaces(childCol), bodyForm)
            .map(([, item]) => item as Variant | FoldDecl);
        return this.seq(
            this.kwRelation,
            this.char(' '),
            this.pascalIdent as Parser<string>,
            this.newline,
            bodyLine,
            this.seq(this.newline, bodyLine).map(([, l]) => l as Variant | FoldDecl).many(),
        ).map(([, , name, , first, rest], span) => {
            const all = [first, ...(rest as Array<Variant | FoldDecl>)];
            const variants = all.filter((x): x is Variant => x instanceof Variant);
            const folds = all.filter((x): x is FoldDecl => x instanceof FoldDecl);
            return this.mkRelationDecl(name as string, variants, folds, span);
        }) as unknown as Parser<S['topDecl']>;
    }

    // ── query declaration ─────────────────────────────────────────────────────

    @rule queryDecl(col: number): Parser<S['topDecl']> {
        const childCol = col + INDENT;
        const observerSig = this.seq(
            this.ident as Parser<string>,
            this.literal(': '),
            this.specRecord,
        ).map(([name, , spec], span) => this.mkField(name as string, null, span));
        const bodyForm: Parser<Field | UnfoldDecl> = this.or(
            this.unfoldDecl(childCol) as unknown as Parser<UnfoldDecl>,
            observerSig as unknown as Parser<UnfoldDecl>,
        );
        const bodyLine = this.seq(this.spaces(childCol), bodyForm)
            .map(([, item]) => item as Field | UnfoldDecl);
        return this.seq(
            this.kwQuery,
            this.char(' '),
            this.pascalIdent as Parser<string>,
            this.newline,
            bodyLine,
            this.seq(this.newline, bodyLine).map(([, l]) => l as Field | UnfoldDecl).many(),
        ).map(([, , name, , first, rest], span) => {
            const all = [first, ...(rest as Array<Field | UnfoldDecl>)];
            const observers = all.filter((x): x is Field => x instanceof Field);
            const unfolds = all.filter((x): x is UnfoldDecl => x instanceof UnfoldDecl);
            return this.mkQueryDecl(name as string, observers, unfolds, span);
        }) as unknown as Parser<S['topDecl']>;
    }

    // ── io declaration ────────────────────────────────────────────────────────

    @rule ioDecl(col: number): Parser<S['topDecl']> {
        const childCol = col + INDENT;
        const stateField = this.seq(
            this.ident as Parser<string>,
            this.literal(': '),
            this.pascalIdent as Parser<string>,
        ).map(([name, , type_], span) => this.mkField(name as string, type_ as string, span));
        const ioArm = this.seq(
            this.pascalIdent as Parser<string>,
            this.char(' '),
            this.ident as Parser<string>,
            this.literal(' -> '),
            this.recordLit,
        ).map(([variant, , binding, , record], span) =>
            this.mkCaseArm(variant as string, [binding as string], record as Node, span)
        );
        const bodyForm: Parser<Field | CaseArm> = this.or(
            stateField as unknown as Parser<Field>,
            ioArm as unknown as Parser<Field>,
        );
        const bodyLine = this.seq(this.spaces(childCol), bodyForm)
            .map(([, item]) => item as Field | CaseArm);
        return this.seq(
            this.kwIo,
            this.char(' '),
            this.pascalIdent as Parser<string>,
            this.newline,
            bodyLine,
            this.seq(this.newline, bodyLine).map(([, l]) => l as Field | CaseArm).many(),
        ).map(([, , name, , first, rest], span) => {
            const all = [first, ...(rest as Array<Field | CaseArm>)];
            const stateFields = all.filter((x): x is Field => x instanceof Field);
            const arms = all.filter((x): x is CaseArm => x instanceof CaseArm);
            return this.mkIoDecl(name as string, stateFields, arms, span);
        }) as unknown as Parser<S['topDecl']>;
    }

    // ── top-level declarations ────────────────────────────────────────────────

    @rule topDecl(col: number): Parser<S['topDecl']> {
        return this.or(
            this.dataDecl(col),
            this.behaviorDecl(col),
            this.protocolDecl(col),
            this.relationDecl(col),
            this.queryDecl(col),
            this.ioDecl(col),
        );
    }

    // ── module ────────────────────────────────────────────────────────────────

    @rule get module(): Parser<S['module']> {
        const declAt0 = this.topDecl(0);
        return this.seq(
            declAt0,
            this.seq(this.newline, declAt0).map(([, d]) => d as TopLevelDecl).many(),
        ).map(([first, rest], span) =>
            this.mkModule(
                [first as TopLevelDecl, ...(rest as TopLevelDecl[])],
                span,
            )
        ) as unknown as Parser<S['module']>;
    }

    // ── Abstract factory methods (implemented by LapisParser) ─────────────────

    protected abstract mkIdent(name: string, span: Span): string;
    protected abstract mkPascalIdent(name: string, span: Span): string;
    protected abstract mkIdentNode(name: string, span: Span): Ident;
    protected abstract mkIdentFromKw(name: string, span: Span): Ident;
    protected abstract mkIntLit(value: number, span: Span): IntLit;
    protected abstract mkStrLit(value: string, span: Span): StringLit;
    protected abstract mkSymbolLit(name: string, span: Span): SymbolLit;
    protected abstract mkSelfRef(span: Span): SelfRef;
    protected abstract mkFamilyRef(span: Span): FamilyRef;
    protected abstract mkCoSelfRef(span: Span): CoSelfRef;
    protected abstract mkOldRef(fieldName: string, span: Span): OldRef;
    protected abstract mkPrevRef(fieldName: string, span: Span): PrevRef;
    protected abstract mkAuxRef(foldName: string, span: Span): AuxRef;
    protected abstract mkBinaryOp(l: Node, op: string, r: Node, span: Span): BinarySend;
    protected abstract mkPrefixOp(op: string, operand: Node, span: Span): PrefixSend;
    protected abstract mkUnarySend(receiver: Node, selector: string, span: Span): UnarySend;
    protected abstract mkKeywordSend(receiver: Node, sels: string[], args: Node[], span: Span): KeywordSend;
    protected abstract mkBlock(params: Ident[], body: Node, span: Span): Block;
    protected abstract mkArrayLit(items: Node[], span: Span): ArrayLit;
    protected abstract mkRecord(entries: RecordEntry[], span: Span): Record;
    protected abstract mkRecordEntry(key: string, value: Node, span: Span): RecordEntry;
    protected abstract mkSpec(entries: SpecEntry[], span: Span): Spec;
    protected abstract mkSpecEntry(key: string, value: Node | null, span: Span): SpecEntry;
    protected abstract mkField(name: string, typeName: string | null, span: Span): Field;
    protected abstract mkContractClause(kind: ContractKind, block: Block, span: Span): ContractClause;
    protected abstract mkVariant(name: string, fields: Field[], invariants: ContractClause[], span: Span): Variant;
    protected abstract mkCaseArm(pattern: string, bindings: string[], body: Node, span: Span): CaseArm;
    protected abstract mkSatisfies(protocolName: string, span: Span): Satisfies;
    protected abstract mkFoldDecl(name: string, spec: Spec | null, contracts: ContractClause[], arms: CaseArm[], span: Span): FoldDecl;
    protected abstract mkUnfoldDecl(name: string, spec: Spec | null, arms: CaseArm[], span: Span): UnfoldDecl;
    protected abstract mkMapDecl(name: string, spec: Spec | null, transform: Block, span: Span): MapDecl;
    protected abstract mkMergeDecl(name: string, foldNames: string[], span: Span): MergeDecl;
    protected abstract mkDataDecl(name: string, parent: string | null, body: DataBodyItem[], span: Span): DataDecl;
    protected abstract mkBehaviorDecl(name: string, parent: string | null, observers: Field[], body: BehaviorBodyItem[], span: Span): BehaviorDecl;
    protected abstract mkProtocolDecl(name: string, parent: string | null, methods: FoldDecl[], span: Span): ProtocolDecl;
    protected abstract mkRelationDecl(name: string, variants: Variant[], folds: FoldDecl[], span: Span): RelationDecl;
    protected abstract mkQueryDecl(name: string, observers: Field[], unfolds: UnfoldDecl[], span: Span): QueryDecl;
    protected abstract mkIoDecl(name: string, stateFields: Field[], arms: CaseArm[], span: Span): IoDecl;
    protected abstract mkModule(declarations: TopLevelDecl[], span: Span): Module;
}

// ── Concrete parser (builds AST nodes) ───────────────────────────────────────

export class LapisParser extends LapisGrammar<LapisShape> {

    protected mkIdent(name: string, _span: Span): string           { return name; }
    protected mkPascalIdent(name: string, _span: Span): string     { return name; }
    protected mkIdentNode(name: string, span: Span): Ident         { return new Ident(name, span); }
    protected mkIdentFromKw(name: string, span: Span): Ident       { return new Ident(name, span); }
    protected mkIntLit(value: number, span: Span): IntLit          { return new IntLit(value, span); }
    protected mkStrLit(value: string, span: Span): StringLit       { return new StringLit(value, span); }
    protected mkSymbolLit(name: string, span: Span): SymbolLit     { return new SymbolLit(name, span); }
    protected mkSelfRef(span: Span): SelfRef                       { return new SelfRef(span); }
    protected mkFamilyRef(span: Span): FamilyRef                   { return new FamilyRef(span); }
    protected mkCoSelfRef(span: Span): CoSelfRef                   { return new CoSelfRef(span); }
    protected mkOldRef(fieldName: string, span: Span): OldRef      { return new OldRef(fieldName, span); }
    protected mkPrevRef(fieldName: string, span: Span): PrevRef    { return new PrevRef(fieldName, span); }
    protected mkAuxRef(foldName: string, span: Span): AuxRef       { return new AuxRef(foldName, span); }

    protected mkBinaryOp(l: Node, op: string, r: Node, span: Span): BinarySend {
        return new BinarySend(l, op, r, span);
    }
    protected mkPrefixOp(op: string, operand: Node, span: Span): PrefixSend {
        return new PrefixSend(op, operand, span);
    }
    protected mkUnarySend(receiver: Node, selector: string, span: Span): UnarySend {
        return new UnarySend(receiver, selector, span);
    }
    protected mkKeywordSend(receiver: Node, sels: string[], args: Node[], span: Span): KeywordSend {
        return new KeywordSend(receiver, sels, args, span);
    }
    protected mkBlock(params: Ident[], body: Node, span: Span): Block {
        return new Block(params, body, span);
    }
    protected mkArrayLit(items: Node[], span: Span): ArrayLit      { return new ArrayLit(items, span); }
    protected mkRecord(entries: RecordEntry[], span: Span): Record  { return new Record(entries, span); }
    protected mkRecordEntry(key: string, value: Node, span: Span): RecordEntry {
        return new RecordEntry(key, value, span);
    }
    protected mkSpec(entries: SpecEntry[], span: Span): Spec        { return new Spec(entries, span); }
    protected mkSpecEntry(key: string, value: Node | null, span: Span): SpecEntry {
        return new SpecEntry(key, value, span);
    }
    protected mkField(name: string, typeName: string | null, span: Span): Field {
        return new Field(name, typeName, span);
    }
    protected mkContractClause(kind: ContractKind, block: Block, span: Span): ContractClause {
        return new ContractClause(kind, block, span);
    }
    protected mkVariant(name: string, fields: Field[], invariants: ContractClause[], span: Span): Variant {
        return new Variant(name, fields, invariants, span);
    }
    protected mkCaseArm(pattern: string, bindings: string[], body: Node, span: Span): CaseArm {
        return new CaseArm(pattern, bindings, body, span);
    }
    protected mkSatisfies(protocolName: string, span: Span): Satisfies {
        return new Satisfies(protocolName, span);
    }
    protected mkFoldDecl(name: string, spec: Spec | null, contracts: ContractClause[], arms: CaseArm[], span: Span): FoldDecl {
        return new FoldDecl(name, spec, contracts, arms, span);
    }
    protected mkUnfoldDecl(name: string, spec: Spec | null, arms: CaseArm[], span: Span): UnfoldDecl {
        return new UnfoldDecl(name, spec, arms, span);
    }
    protected mkMapDecl(name: string, spec: Spec | null, transform: Block, span: Span): MapDecl {
        return new MapDecl(name, spec, transform, span);
    }
    protected mkMergeDecl(name: string, foldNames: string[], span: Span): MergeDecl {
        return new MergeDecl(name, foldNames, span);
    }
    protected mkDataDecl(name: string, parent: string | null, body: DataBodyItem[], span: Span): DataDecl {
        return new DataDecl(name, parent, body, span);
    }
    protected mkBehaviorDecl(name: string, parent: string | null, observers: Field[], body: BehaviorBodyItem[], span: Span): BehaviorDecl {
        return new BehaviorDecl(name, parent, observers, body, span);
    }
    protected mkProtocolDecl(name: string, parent: string | null, methods: FoldDecl[], span: Span): ProtocolDecl {
        return new ProtocolDecl(name, parent, methods, span);
    }
    protected mkRelationDecl(name: string, variants: Variant[], folds: FoldDecl[], span: Span): RelationDecl {
        return new RelationDecl(name, variants, folds, span);
    }
    protected mkQueryDecl(name: string, observers: Field[], unfolds: UnfoldDecl[], span: Span): QueryDecl {
        return new QueryDecl(name, observers, unfolds, span);
    }
    protected mkIoDecl(name: string, stateFields: Field[], arms: CaseArm[], span: Span): IoDecl {
        return new IoDecl(name, stateFields, arms, span);
    }
    protected mkModule(declarations: TopLevelDecl[], span: Span): Module {
        // source is set by the public parse() override; placeholder here
        return new Module(declarations, '', span);
    }

    /**
     * Parse a Lapis source string.
     * Returns the `Module` AST root.
     * Throws if parsing rejects (empty forest) or the grammar is ambiguous (forest size > 1).
     */
    parseSource(source: string): Module {
        const forest = this.parse(source);
        if (forest.size === 0) throw new Error('Parse error: input rejected by the grammar');
        if (forest.size > 1)  throw new Error(`Ambiguous parse: ${forest.size} parse trees produced`);
        const mod = [...forest][0] as Module;
        // Attach the source string for position lookups
        return new Module(mod.declarations, source, mod.span);
    }
}
