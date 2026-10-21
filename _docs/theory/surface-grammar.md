# Lapis Surface Grammar (EBNF)

> **Status:** Draft v0.1. This document is the **single consolidated grammar** for the Lapis surface
> language — every production, in one place, in EBNF. It is the surface counterpart of
> [`lc.md`](./lc.md) §2, which gives the core calculus's grammar in TAPL style.
>
> [`surface-syntax.md`](./surface-syntax.md) remains the _narrative_ specification: lexical
> structure, the pattern language, precedence rationale, railroad diagrams, the indentation
> strategy, and the worked examples. This document is the _normative_ production set — where the two
> disagree, **this document wins** for the shape of the syntax.
>
> **Status of the surface grammar in the implementation:** the core calculus is implemented
> (`src/core/grammar.ts`); the surface declaration productions are **not** (the implemented keywords
> are `<:`, `cofold`, `fold`, `in`, `let`, `match`, `unfold` — no `data`, `behavior`, `protocol`,
> `relation`, `query`, or `io`). This document is the target that Stage 1 of
> [`language-design.md`](./language-design.md) is written against. See §10 for the per-production
> implementation status.

---

## 1. Notation

| Notation         | Meaning                                               |
| ---------------- | ----------------------------------------------------- |
| `X ::= Y`        | `X` is defined as `Y`                                 |
| `X?`, `X*`, `X+` | optional / zero-or-more / one-or-more                 |
| `X \| Y`         | alternation                                           |
| `"lit"`          | a literal token                                       |
| `{ X }`          | zero or more occurrences of `X`                       |
| `[ X ]`          | a bracketed group (not a token)                       |
| `⟨ X ⟩`          | a non-terminal written inline (for readability)       |
| `␣`              | one space (or the layout's required indentation — §8) |
| `⏎`              | a newline (the statement separator — §8)              |
| `ε`              | the empty sequence                                    |

**Terminals** are written as quoted strings; **non-terminals** as `camelCase` or `PascalCase`
identifiers. Keywords (`data`, `fold`, …) are terminals.

**Layout.** Two layout rules apply to every production and are _not_ written inline:

- **L1 — Indentation.** A block's contents must be indented exactly one unit (4 spaces) more than
  the line that introduces it. Continuation lines within a body line are indented further.
- **L2 — Newline.** A newline separates body lines. Blank lines and comments are consumed between
  them.

Both are formalized in §8.

---

## 2. Lexical Structure

### 2.1 Character classes

```
digit       ::= "0" … "9"
alpha       ::= "a" … "z" | "A" … "Z" | "_"
alnum       ::= alpha | digit
alphaLower  ::= "a" … "z" | "_"
alphaUpper  ::= "A" … "Z"
```

### 2.2 Identifiers

```
ident        ::= alphaLower alnum*          (* camelCase: field, operation, spec key, variable *)
pascalIdent  ::= alphaUpper alnum*          (* PascalCase: type, variant, unfold constructor *)
```

Keywords are reserved and cannot be used as identifiers: every keyword in §2.5 is excluded from both
classes, and a keyword must be followed by a non-`alnum` character (`dataFoo` is an identifier,
`data` is a keyword).

### 2.3 Symbolic operation names

An operation name may be symbolic. Symbolic names are **contiguous non-whitespace sequences** of
operator characters, recognized by longest match among _declared_ operators.

```
symbolicOp ::= ( "+" | "-" | "*" | "/" | "<" | ">" | "=" | "!" | "?" | "&" | "|" | "," | "." )+
```

Grouping characters are permitted inside a symbolic name (`<+>`, `<>`). A symbolic name is never a
pattern: the two live in different lexical contexts (expression level vs. pattern level).

> **Open (spec §2.1).** The exact operator-character set is not pinned. The set above is the
> candidate; the _rule_ — contiguous non-whitespace, longest match among declared operators — is
> pinned.

### 2.4 Literals

Literals are not lexical tokens: they are **pattern-matched data** (spec §1.3), and the lexer is
driven by the `data` declarations in scope. A literal token is whatever text a declared pattern
matched.

```
literal ::= <text matched by a declared pattern>
```

The built-ins' _value spellings_ are:

```
stringLiteral  ::= '"' ( char | escape )* '"'
charLiteral    ::= "'" ( char | escape ) "'"
```

where `escape ::= "\\" ( '"' | "'" | "\\" )` — the delimiter escapes, pinned in spec §1.4. The
fuller escape vocabulary (`\n`, `\t`) is **open** (spec §9.1).

### 2.5 Keywords

```
keyword ::= "data" | "behavior" | "protocol" | "relation" | "query" | "io"
          | "fold" | "unfold" | "map" | "merge" | "scan" | "satisfies"
          | "not" | "self" | "old" | "prev" | "aux"
          | "Family" | "Self"
```

Plus the special values `nil`, `true`, `false` (spec §1.6), which are **not** keywords — they are
ordinary values (`nil` is the null reference; `true`/`false` are the `Bool` variants).

> **Open (overview §12.16).** `Family` is reserved in _type position_ — it is the language-defined
> μ-bound reference, and a user declaration may not take the name. The enforcement is not yet in the
> core's lexer (`LC_RESERVED_WORDS` gates only the lowercase `ident` lexeme).

### 2.6 Comments

```
comment ::= "/*" ( comment | anyCharExceptSlashStar )* "*/"
```

Nesting is permitted; there are no escapes, so prose may not contain an unbalanced `*/`. Comments
are **metasyntax** — consumed at statement boundaries before any token phase, and present in no
production below.

---

## 3. Expressions

### 3.1 Precedence

Three operation-application forms, three precedence levels, strictly ordered:

| Level       | Non-terminal  | Message type                       | Associativity      |
| ----------- | ------------- | ---------------------------------- | ------------------ |
| 1 (lowest)  | `keywordExpr` | Keyword calls                      | Left               |
| 2           | `binaryExpr`  | Binary calls (all symbolic ops)    | **Left (uniform)** |
| 3 (highest) | `unaryExpr`   | Unary calls                        | Left               |
| —           | `primary`     | literals, refs, composites, parens | —                  |

**Uniform binary precedence:** _all_ binary operators have the same precedence and are
left-associative. `1 + 2 * 3` parses as `(1 + 2) * 3`. There is no precedence ladder.

### 3.2 The expression grammar

```
expr           ::= keywordExpr

keywordExpr    ::= binaryExpr ( ␣ keywordPart )+
                | binaryExpr

keywordPart    ::= ident ":" ␣ expr

binaryExpr     ::= binaryExpr ␣ binaryOp ␣ unaryExpr
                | unaryExpr

binaryOp       ::= symbolicOp
                | ident                     (* named operation: add, mul, lessThan *)

unaryExpr      ::= unaryExpr ␣ ident        (* unary send *)
                | primary

primary        ::= literal
                | "(" expr ")"              (* parenthesized *)
                | blockLiteral
                | arrayLiteral
                | recordLiteral
                | specRecord
                | reference
                | "nil" | "true" | "false"
                | variantRef
                | ident
```

### 3.3 The message-chain rule

A keyword send is `receiver key1: arg1 key2: arg2 …`. The selector is the concatenation of the
keyword parts.

```
messageChain   ::= primary ( ␣ ident )* ( ␣ ident ":" ␣ expr )?
```

**Greedy collection:** when keyword suffixes are present, _all_ `key: arg` pairs are collected into
a single `KeywordCall` — they are not nested sends. This is the Smalltalk rule and it is what makes
`a between:and: lo hi` a two-argument call rather than a call whose argument is a call.

> **Open (overview §12.2).** The payload of a generator arm (`| head: n rest: n - 1`) has this
> _same_ shape as a keyword send, and §2.3's greedy collection would swallow it. The generator-arm
> body must therefore be a **restricted production** that keeps `head:`/`rest:` as labels rather
> than a send. See §5.2.

### 3.4 Variant references and construction

A `pascalIdent` in expression position is a **variant reference** — a zero-field variant, read as a
value:

```
variantRef     ::= pascalIdent
```

A variant with fields is _constructed_, and the construction is a keyword message with the variant
name as the receiver's role:

```
construction  ::= pascalIdent ( ␣ ident ":" ␣ expr )+
```

> **Open (overview §12.7).** Whether a construction may be _qualified_ by its type
> (`Point3 Cartesian2 x: 1 y: 2`) is unpinned. Both spellings are legal; the qualifier names the
> _type_ whose constructor is meant, and is required only to disambiguate a colliding variant name
> or to select the constructing type for an inherited variant.

### 3.5 References

```
reference      ::= "self"
                | "Family"
                | "Self"
                | "old" ident
                | "prev" ident
                | "aux" ident
```

These are parsed in the `primary` production, _before_ ordinary identifiers — so `old`, `prev`,
`aux`, `self`, `Family`, and `Self` are reserved as keyword-like references.

### 3.6 Composite expressions

```
blockLiteral   ::= "[" ident* ( "|" ␣ expr )? "]"
arrayLiteral   ::= "{" ( expr ( "," ␣ expr )* )? "}"
recordLiteral  ::= "(" ( ident ":" ␣ expr ( "," ␣ ident ":" ␣ expr )* )? ")"
specRecord     ::= "<" ( specEntry ( "," ␣ specEntry )* )? ">"
```

**Block literal** — a first-class block (lambda). Two forms: `[expr]` (no parameters) and
`[x y | expr]` (one or more parameters).

**Array literal** — `{1, 2, 3}`. Elaborates to nested cons.

**Record literal** — `(x: 3, y: 4)`. The named-argument form. (A record may also carry _bare flags_
— `(commutative, associative)` — but only inside a spec's `properties` value; see §3.7.)

### 3.7 Spec records

A spec record appears after a fold/unfold/map name, and also as an observer's _type_ in a `behavior`
declaration.

```
specEntry      ::= ident ":" ␣ expr
                | ident                       (* bare flag *)

specRecord     ::= "<" ( specEntry ( "," ␣ specEntry )* )? ">"
```

**Recognized keys** (spec §3.4):

| Key          | Value shape                | Meaning                                |
| ------------ | -------------------------- | -------------------------------------- |
| `in`         | `typeExpr`                 | Input parameter with type              |
| `out`        | `typeExpr`                 | Output/return type                     |
| `para`       | (flag)                     | Paramorphism — `old field` available   |
| `histo`      | (flag)                     | Histomorphism — `prev field` available |
| `aux`        | `"#" ident` \| `"(" … ")"` | Zygomorphism — auxiliary fold result   |
| `typeParam`  | `typeExpr`                 | Type parameter for map                 |
| `properties` | `recordLiteral`-shaped     | Algebraic property annotations         |

> **Decided (overview §12.19).** `in:` carries **only the type** — `in: Nat`, never `in: v Nat`. A
> fold takes at most one input, so there is nothing for a name to disambiguate; the name would also
> be unspellable under the spec-record's own production (`specEntry ::= ident ":" ␣
> expr` —
> `v Nat` is not an `expr`). The input is bound at the _arm_ (§5.1), not in the spec.

### 3.8 Types

Types appear in field declarations, spec entries, and type parameters.

```
typeExpr       ::= typeExpr "->" typeExpr      (* function type *)
                | atomType

atomType       ::= "(" typeExpr ")"
                | pascalIdent                  (* a declared type *)
                | "Family" | "Self"
                | "Any" | "Nothing"
```

> **Open (overview §12.4, §12.13).** `Family` and `Self` are the recursive self-references; whether
> they are _reserved_ type names or shadowable by user declarations is decided in favour of reserved
> (overview §12.16) but the enforcement is not yet in the core's lexer.

---

## 4. Declaration Forms

There are six declaration forms. All are top-level; a program's top level is declarations and
expression statements (spec §8, overview §12.21).

```
program        ::= declaration*

declaration   ::= dataDecl
                | behaviorDecl
                | protocolDecl
                | relationDecl
                | queryDecl
                | ioDecl
```

### 4.1 `data` — algebraic data type (μ-type)

```
dataDecl       ::= "data" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ dataBody

dataBody       ::= ␣(4) dataBodyItem+

dataBodyItem   ::= variantDecl
                | foldDecl
                | unfoldDecl
                | mapDecl
                | mergeDecl
                | scanDecl
                | satisfiesClause

variantDecl    ::= pascalIdent ( ␣ ident ":" ␣ typeExpr )*     (* fields, in declaration order *)
```

A variant's fields are **positional in declaration order**; the surface spelling
(`Point2D x: 1 y: 2`) is the named-argument form, and elaboration resolves names to positions
(elaboration §2.7).

> **Open (overview §12.4).** A variant may be re-declared in a child type to **narrow** a field type
> (covariant re-specification): every re-specified field's type must be a subtype of the parent's,
> and no new fields may be introduced. Unmentioned fields are inherited.

### 4.2 `behavior` — final coalgebra (ν-type)

```
behaviorDecl   ::= "behavior" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ behaviorBody

behaviorBody   ::= ␣(4) behaviorBodyItem+

behaviorBodyItem ::= observerDecl
                 | foldDecl
                 | unfoldDecl
                 | mapDecl
                 | mergeDecl
                 | scanDecl
                 | satisfiesClause

observerDecl   ::= ident ":" ␣ specRecord
```

A `behavior` is defined by its **observations**; an `unfold` inside it is a _generator_ — one arm
per observer, each producing the next seed.

### 4.3 `protocol` — qualified type

```
protocolDecl   ::= "protocol" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ protocolBody

protocolBody   ::= ␣(4) protocolItem+

protocolItem   ::= foldDecl
                | unfoldDecl
                | mapDecl
                | mergeDecl
                | scanDecl
```

### 4.4 `relation` — span-structured data

```
relationDecl   ::= "relation" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ relationBody

relationBody   ::= ␣(4) relationItem+

relationItem   ::= variantDecl
                | foldDecl
                | unfoldDecl
                | mapDecl
                | mergeDecl
                | scanDecl
```

A `relation` is sugar over `data` with two distinguished folds (`origin`, `destination`) and an
auto-generated join invariant (elaboration §3.4).

### 4.5 `query` — cospan-structured behavior

```
queryDecl      ::= "query" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ queryBody

queryBody      ::= ␣(4) queryItem+

queryItem      ::= observerDecl
                | foldDecl
                | unfoldDecl
                | mapDecl
                | mergeDecl
                | scanDecl
```

### 4.6 `io` — Mealy machine

```
ioDecl         ::= "io" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ ioBody

ioBody         ::= ␣(4) ioItem+

ioItem         ::= stateFieldDecl
                | ioStep

stateFieldDecl ::= ident ":" ␣ typeExpr
ioStep         ::= pascalIdent ( ␣ ident )* "->" ␣ expr
```

An `io` step's body produces a record `(state: …, output: …)` — a `recordLiteral` (elaboration
§3.6).

### 4.7 `satisfies:` — conformance clause

```
satisfiesClause ::= "satisfies" ":" ␣ pascalIdent
```

---

## 5. Operation Declarations

These appear as body items inside a declaration (§4), and each is indented one further unit relative
to its declaration.

### 5.1 `fold` — catamorphism

```
foldDecl       ::= "fold" ident specRecord? ⏎ foldBody

foldBody       ::= ␣(8) foldItem+

foldItem       ::= contractClause
                | caseArm

contractClause ::= ( "demands" | "ensures" | "invariant" | "rescue" ) ":" ␣ blockLiteral

caseArm        ::= armHead "->" armBody

armHead        ::= pascalIdent ( ␣ binding )*
                | "_" ( ␣ binding )*            (* wildcard arm — open variant sets *)

binding        ::= ident | "_"

armBody        ::= expr                        (* inline *)
                | ⏎ ␣(12) expr               (* indented *)
```

**Arm head** — a variant name followed by the bindings for its fields. Bindings beyond the variant's
field count bind the fold's **input** (the `in:` parameter), which is optional per arm.

**Wildcard arm** — `_` catches whatever the other arms don't, keeping the fold total over an open
variant set. Inherited wildcards are overridable.

> **Decided (overview §12.19).** The input is bound _at the arm_, like a field:
> `Cons head rest v
> -> …` binds `v` to the `in:` value. This is the only binding mechanism — the
> record's fields are not bound directly by name, and there is no fixed seed binding in arm scope.

### 5.2 `unfold` — anamorphism

```
unfoldDecl     ::= "unfold" pascalIdent specRecord? ⏎ unfoldBody

unfoldBody     ::= ␣(8) unfoldArm+

unfoldArm      ::= armHead "->" ␣ guard "|" ␣ payload
                | armHead "->" ␣ guard

guard          ::= expr

payload        ::= ident ( ␣ ident ":" ␣ expr )+    (* target-typed field list *)
```

**The arm is `guard | payload`.** The guard decides whether the arm applies; when it holds, the arm
produces the variant named in the arm head, with the fields the payload supplies. Otherwise it
declines and the next arm is tried — the first arm whose guard holds wins (the prototype's shape: a
handler returns either a fields object or `null`, and the first non-null one decides).

**The payload is a target-typed construction.** The variant is not repeated, because the arm head
already names it (C#'s target-typed `new` is the same move — the target comes from context, so the
name is omitted). The payload spells only the fields, as a keyword message — `head: n rest: n - 1` —
the Smalltalk shape; the field names are _labels_ there, not bindings, so `n` is still the seed.

**The payload is required exactly when the arm's variant has fields.** The base arm carries none,
because a fieldless variant has nothing to say:

```lapis
unfold Range <in: Nat>
    Nil n -> n = 0
    Cons n -> n > 0 | head: n rest: n - 1
```

> **Open (overview §12.2).** Two sub-questions remain: (a) the payload's keyword-message shape
> collides with §3.3's greedy keyword-send collection — the arm body needs its own restricted
> production keeping `head:`/`rest:` as labels rather than a send; (b) `|` is listed among the
> symbolic operator names (§2.1), so the spec must either reserve it as a separator or pick another
> (`=>` is the candidate). The _reading_ — guard, separator, target-typed payload — is decided.

**Recursive fields carry the next seed, not a value.** In a recursive field, the payload's value is
the seed for the recursive unfolding: `rest: n - 1` says "the rest is whatever unfolding the seed
`n - 1` produces", not "the rest is the number `n - 1`" (the prototype draws the same line).

### 5.3 `map` — field transformation

```
mapDecl        ::= "map" ident specRecord? ␣ blockLiteral
```

A single-line declaration: the transform is a block literal. The block's parameters are the
transformed field's inputs.

### 5.4 `merge` — deforestation

```
mergeDecl      ::= "merge" ident "<" mergeRef ( "," ␣ mergeRef )* ">"

mergeRef       ::= "#" ident
```

### 5.5 `scan` — scan lemma

```
scanDecl       ::= "scan" ident "<" "#" ident ">"
```

> **Open (overview §12.20).** `scan`'s surface spelling is unpinned; the form above is the
> candidate, matching `merge`'s `#name` reference form.

---

## 6. Module Declarations

> **Open (overview §12.20).** The module system's _surface grammar_ is entirely unpinned — the spec
> has no module production at all, and the module mechanism is Stage 7 of the implementation plan.
> The candidate shape, from the overview's §5.3 and Bracha's ban on imports (modules are
> dependency→export functions):

```
moduleDecl     ::= "module" pascalIdent ( "(" ␣ moduleParam ( "," ␣ moduleParam )* ")" )? ⏎ moduleBody

moduleParam    ::= pascalIdent ":" ␣ typeExpr

moduleBody     ::= ␣(4) moduleExport+

moduleExport   ::= pascalIdent ":" ␣ moduleEntry
                | pascalIdent ":" ␣ "data" ␣ variantList

variantList    ::= variantDecl ( ⏎ ␣(4) variantDecl )*

moduleEntry    ::= dataDecl
                | behaviorDecl
                | relationDecl
                | queryDecl

moduleInstantiation ::= pascalIdent ( ":" ␣ expr )*
```

---

## 7. Top-Level Expressions

```
topExpr        ::= expr
```

> **Open (overview §12.6).** Whether a _definition_ form (`name = expr`) exists is unpinned; the
> grammar has no such production, and `=` is an equality _operator_ (a fold name) in predicates. The
> examples in the docs lean on it; the grammar above does not provide it.

---

## 8. Layout

Layout is a grammar-level concern in Lapis, not a post-pass. Two rules:

### L1 — Indentation

A block's contents are indented exactly one **indent unit** (4 spaces) more than the line that
introduces the block. Continuation lines are indented further.

```
indentUnit    ::= "    " (4 spaces)
```

The declaration/body/case-arm/body nesting is:

| Context                         | Column | Example            |
| ------------------------------- | ------ | ------------------ |
| Top-level declaration           | 0      | `data Color`       |
| Body of a declaration           | 4      | `Red Green Blue`   |
| Case arms / contracts in a fold | 8      | `Red -> "#FF0000"` |
| Multi-line case arm body        | 12     | `expr`             |

The implementation uses **P4P-style column-parameterised productions** (spec §6.2): no pre-pass, no
token rewriting. Every block-introducing production takes the child column as a parameter, and
`spaces(n)` matches exactly `n` spaces.

### L2 — Newline

A newline separates body lines. Blank lines and comments are consumed between them. Both `\r\n` and
`\n` are accepted.

### Inline vs. indented bodies

A case arm's body may be inline (same line, after `->`) or indented (next line, deeper). The parser
tries the indented form first (longer match), then falls back to inline.

---

## 9. Abstract Syntax

The AST node types, matching spec §2.1 and the implementation's shapes:

| Production      | AST node                                                                     |
| --------------- | ---------------------------------------------------------------------------- |
| `expr`          | `Expr` — a discriminated union of the forms below                            |
| `keywordExpr`   | `KeywordCall(receiver, parts: {key, value}[])`                               |
| `binaryExpr`    | `BinaryCall(receiver, op, arg)`                                              |
| `unaryExpr`     | `UnaryCall(receiver, selector)`                                              |
| `primary`       | `primary` — one of the composite/reference/literal forms below               |
| `blockLiteral`  | `Block(params: Ident[], body: Node)`                                         |
| `arrayLiteral`  | `ArrayLit(items: Node[])`                                                    |
| `recordLiteral` | `Record(entries: RecordEntry[])` where `RecordEntry(key, value)`             |
| `specRecord`    | `Spec(entries: SpecEntry[])` where `SpecEntry(key, value: Node \| null)`     |
| `variantRef`    | `VariantRef(name)`                                                           |
| `construction`  | `VariantConstruct(name, args: {field, value}[])`                             |
| `reference`     | `SelfRef` \| `FamilyRef` \| `CoSelfRef` \| `OldRef` \| `PrevRef` \| `AuxRef` |
| `dataDecl`      | `DataDecl(name, parent, body: DataBodyItem[])`                               |
| `behaviorDecl`  | `BehaviorDecl(name, parent, observers: Field[], body: BehaviorBodyItem[])`   |
| `protocolDecl`  | `ProtocolDecl(name, parent, methods: FoldDecl[])`                            |
| `relationDecl`  | `RelationDecl(name, variants: Variant[], folds: FoldDecl[])`                 |
| `queryDecl`     | `QueryDecl(name, observers: Field[], unfolds: UnfoldDecl[])`                 |
| `ioDecl`        | `IoDecl(name, stateFields: Field[], arms: CaseArm[])`                        |
| `foldDecl`      | `FoldDecl(name, spec, contractClauses, arms: CaseArm[])`                     |
| `unfoldDecl`    | `UnfoldDecl(name, spec, arms: CaseArm[])`                                    |
| `mapDecl`       | `MapDecl(name, spec, transform: Block)`                                      |
| `mergeDecl`     | `MergeDecl(name, foldNames: string[])`                                       |
| `caseArm`       | `CaseArm(head, bindings, body)`                                              |
| `unfoldArm`     | `UnfoldArm(head, bindings, guard, payload)`                                  |

---

## 10. Implementation Status

Per-production, against the core in `src/core/`. The core grammar is the abstract base `AbstractLC`
(`grammar.ts`); the semantic passes are its subclasses `LCTypeCheck` (`typing_grammar.ts`) and
`LCEval` (`eval_grammar.ts`).

| Production group              | Status                                                                                                                                                                                                                   |
| ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Core terms (`lc.md` §2.2)     | **Implemented** — `lambdaProd`, `foldProd`, `unfoldProd`, `cofoldProd`, `letProd`, `variantProd`, `patternTokenProd`, `patternMatchProd`, `obsProd`, `appProd`, `opProd`, `typeAbsProd`, `typeAppProd`                   |
| Types (`lc.md` §2.1)          | **Implemented** — `typeProd`, `atomType`                                                                                                                                                                                 |
| Surface expressions (§3)      | **Partial** — the core's expression productions cover the LC core's term forms, not the surface's message chain                                                                                                          |
| Surface declarations (§4, §5) | **Not implemented** — no `data`, `behavior`, `protocol`, `relation`, `query`, or `io` production; the registered types in the test fixtures are built through the `DataTypeBuilder` API, never parsed from a declaration |
| Modules (§6)                  | **Not implemented** — Stage 7                                                                                                                                                                                            |

The implemented keyword set is exactly `<:`, `cofold`, `fold`, `in`, `let`, `match`, `unfold` — the
core's own vocabulary. Every surface declaration keyword above is still a production to write.

The surface declaration productions are the target of Stage 1 in
[`language-design.md`](./language-design.md) ("surface `data`/`fold` → core μ/fold").

---

## 11. Open Questions

The questions this grammar does _not_ settle, with their owning finding in
[`overview.md`](../overview.md) §12:

| #  | Question                                                                                                                         | Finding |
| -- | -------------------------------------------------------------------------------------------------------------------------------- | ------- |
| 1  | The generator-arm payload's collision with the greedy keyword-send collection — the arm body needs its own restricted production | §12.2   |
| 2  | `\|` as the generator separator — reserve it, or pick `=>`?                                                                      | §12.2   |
| 3  | Variant qualification at construction, and the bare default for an _inherited_ variant                                           | §12.7   |
| 4  | Whether a top-level _definition_ form (`name = expr`) exists                                                                     | §12.6   |
| 5  | `scan`'s surface spelling                                                                                                        | §12.20  |
| 6  | The module system's surface grammar                                                                                              | §12.20  |
| 7  | The symbolic operator character set                                                                                              | §2.1    |
| 8  | `Family`'s reservation in type position (decided, but unenforced in the core)                                                    | §12.16  |
| 9  | The string-escape vocabulary (`\n`, `\t`)                                                                                        | §1.4    |
| 10 | Pattern captures: capture-vs-type-reference disambiguation, delimited regions, `\|` in patterns, and slice gating                | §12.8   |
| 11 | The user-declared pattern member's surface syntax (the mixed-carrier form)                                                       | §12.4   |

---

## 12. See Also

- [`surface-syntax.md`](./surface-syntax.md) — the narrative specification: lexical structure, the
  pattern language, precedence rationale, railroad diagrams, indentation strategy, worked examples.
- [`lc.md`](./lc.md) — the core calculus: grammar, typing rules, evaluation rules, soundness.
- [`elaboration.md`](./elaboration.md) — the surface→core mapping this grammar's productions feed.
- [`grammar-as-semantics.md`](./grammar-as-semantics.md) — the implementation architecture: grammar
  subclassing as compiler pipeline.
- [`language-design.md`](./language-design.md) — the staged implementation plan this grammar is
  written against.
- [`../overview.md`](../overview.md) — the 10,000ft view: the language in one document, with the
  sanity-check findings this grammar defers to.
