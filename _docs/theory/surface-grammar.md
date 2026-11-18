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
> [`language-design.md`](./language-design.md) is written against. See §9 for the per-production
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
| `␣`              | one space (or the layout's required indentation — §7) |
| `⏎`              | a newline (the statement separator — §7)              |
| `ε`              | the empty sequence                                    |

**Terminals** are written as quoted strings; **non-terminals** as `camelCase` or `PascalCase`
identifiers. Keywords (`data`, `fold`, …) are terminals.

**Layout.** Two layout rules apply to every production and are _not_ written inline:

- **L1 — Indentation.** A block's contents must be indented exactly one unit (4 spaces) more than
  the line that introduces it. Continuation lines within a body line are indented further.
- **L2 — Newline.** A newline separates body lines. Blank lines and comments are consumed between
  them.

Both are formalized in §7.

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
                | arrayLiteral
                | recordLiteral
                | specRecord
                | reference
                | "nil" | "true" | "false"
                | variantRef
                | ident
```

**There is no application production.** The grammar has no `expr expr` form and no `value:` suffix
of its own: application is _derived_ through the message chain, not spelled. A keyword send
eliminates its receiver and applies the arguments to the result — `fold` for data, observation for
codata, and `value:` for a function type (§3.3). A function value is a value of type `σ → τ`, so
applying one is the ordinary keyword send.

### 3.3 The message-chain rule

A keyword send is `receiver key1: arg1 key2: arg2 …`. The selector is the concatenation of the
keyword parts.

```
messageChain   ::= primary ( ␣ ident )* ( ␣ ident ":" ␣ expr )?
```

**Greedy collection:** when keyword suffixes are present, _all_ `key: arg` pairs are collected into
a single `KeywordCall` — they are not nested sends. This is the Smalltalk rule: a two-part spelling
is one call with two arguments, never a call whose argument is a call.

**A selector has at most one keyword part, because an operation has at most one `in:`** (§3.7). The
receiver supplies one argument and `in:` supplies at most one more, so no surface-declared operation
can have arity 3+. A two-part selector therefore parses but cannot resolve to any declaration — it
is an arity error at elaboration, not a different grouping. The greedy rule still decides the parse;
it just has no satisfiable case.

**A keyword send eliminates its receiver, then applies the arguments** (`elaboration.md` §2.5). The
elimination form is fixed by the receiver's kind: data eliminates by `fold`, codata by observation,
and a function type eliminates by **application**. So `transform value: head` — where `transform` is
a function-typed _parameter_ — is a send whose selector is the function type's fixed application
keyword, `value:`. Application needs no production of its own; this is the only rule it has (§3.2).

**Parentheses re-open the chain.** A parenthesized expression is a `primary`, so
`(f value: x)
value: y` is two sends, not one two-part selector. A function type is
single-parameter, so a multi-argument function value is curried and spelled by nesting.

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
arrayLiteral   ::= "{" ( expr ( "," ␣ expr )* )? "}"
recordLiteral  ::= "(" ( ident ":" ␣ expr ( "," ␣ ident ":" ␣ expr )* )? ")"
specRecord     ::= "<" ( specEntry ( "," ␣ specEntry )* )? ">"
```

**List literal** — `{1, 2, 3}`. Elaborates to nested cons.

**Record literal** — `(x: 3, y: 4)`. The named-argument form. (A record may also carry _bare flags_
— `(commutative, associative)` — but only inside a spec's `properties` value; see §3.7.)

### 3.6.1 Function values

There is no block literal — `[params | expr]` is **not** a production. A function value has type
`σ → τ` and is a value like any other:

```lapis
double                    /* an operation reference — the function value itself */
Int double                /* qualified: the `double` declared by `Int`, when names collide */
xs map: double            /* a function-typed argument */
transform value: head     /* applying one — the send rule, §3.3 */
```

**An operation reference is the only way to name a function value.** An unbound camelCase `ident` in
`primary` position resolves through ρ (an arm binding) and then through `Ω` (§7.4): since no surface
form binds a name at top level or inside a body (overview §12.6), an operation is the only thing
such a name can denote. The reference therefore carries the operation's declared type, its law set,
and its cost summary — which an anonymous lambda could not.

**Qualification is disambiguation.** `Type op` is a unary send whose selector is resolved against
the declaring type's operations, exactly the rule variant construction uses (§3.4): bare when unique
in scope, qualified only to resolve a collision. One rule, both constructor kinds and operations.

**Under-application is an error, not a silent function value.** `xs append` (a typo for
`xs append: 3`) fails on arity — it never becomes a function value. Uniform access (§3.3's
getter/method split) stays intact.

> **Open (overview §12.27, [#109](https://github.com/lapis-lang/lapis-lang/issues/109)).** **Partial
> application** — supplying some of an operation's arguments and holding the rest — has no
> production yet, and is deliberately kept out of expression position: `f a` is never application
> anywhere in the surface grammar. The pinned spelling, when it lands, is the _section_ form
> `(op arg …)` — juxtaposition allowed only inside parentheses, exactly as uniform binary precedence
> confines grouping to parentheses (§3.1). Until then an operation is referenced whole or not at
> all.

> **Open (overview §12.2).** The generator-arm payload (`| head: n rest: n - 1`) has the same shape
> as a keyword send, and §3.3's greedy collection would swallow it. The generator-arm body must
> therefore be a **restricted production** that keeps `head:`/`rest:` as labels rather than a send.
> See §5.2.

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
| `properties` | `recordLiteral`-shaped     | Algebraic property annotations         |

> **Decided (overview §12.29).** There is **no `typeParam` key**. A map's transform takes its
> argument type from the arm that binds it, so a separate declaration-time type parameter would be a
> second spelling for something the arm already carries.

> **Decided (overview §12.19).** `in:` carries **only the type** — `in: Int`, never `in: v Int`. A
> fold takes at most one input, so there is nothing for a name to disambiguate; the name would also
> be unspellable under the spec record's own production (`specEntry ::= ident ":" ␣ expr` — `v Int`
> is not an `expr`, since a unary send's message must be a camelCase `ident` and `Int` is
> PascalCase). **The arm binds the input**, and the same `armHead` binding list carries it: a fold
> arm's bindings beyond the variant's field count bind the input (`Cons head rest v -> …`, optional
> per arm); an unfold arm's bindings bind the **seed** (`Empty arr -> …`, `Push arr -> …` — the arm
> produces a variant rather than destructuring one, so there are no fields to bind). An unfold that
> declares no `in:` has no seed, so its arms carry no bindings at all (§5.2).

**A protocol member's default body binds `other` (§4.3).** A default body has no arm head and no
binding list, so the arm rule above does not reach it: a protocol cannot know its conformers'
variant names, so it cannot destructure anything. Its scope is exactly three things —

- `self`, the receiver, in scope in every body;
- `other`, the member's `in:` value, bound **exactly when the member declares `in:`**; and
- the recursive references `Family` and `Self` (§3.5).

So a getter member (no `in:`) binds no `other`, and a default body that mentions it is an
unbound-name error. There is no other binding mechanism in a default body — no local, no arm
binding, no field name.

### 3.8 Types

Types appear in field declarations, spec entries, and operation result positions.

```
typeExpr       ::= typeExpr "->" typeExpr      (* function type *)
                | atomType

atomType       ::= "(" typeExpr ")"
                | pascalIdent                  (* a declared type *)
                | "Family" | "Self"
                | "Any" | "Nothing"
```

> **Decided (overview §12.29).** **There are no type variables and no type parameters anywhere in
> the surface language — now or in the future.** `atomType` admits no lowercase production, so a
> name like `σ` or `τ` is not a type; every declaration form (`data`, `behavior`, `protocol`,
> `relation`, `query`, `io`) takes a bare `pascalIdent` and no parameter list; and there is no
> type-application form (§4.1). This is not an omission to be filled in later — it is the language's
> type discipline.
>
> Subtyping is the sole abstraction mechanism. Where a generic type would be introduced, one of
> three existing forms is used instead: a **subtype** with narrowed fields (`IntList <: List`, every
> field covariance-checked), the **declaring type itself** (`Self` in an operation spec, which is
> what lets `Num add <in: Self, out: Self>` return its operand type), or the lattice's top **`Any`**
> where the element type genuinely varies and no relation between the element and the container is
> needed. `Any` is what the corpus previously misspelled `Object` — see §12.18's leak class.
>
> Consequences for the rest of this document: no type-abstraction or type-application surface form
> exists (the core's `Λα <: σ. t` and `t[τ]` are core-only, reached by elaboration and never
> written); an operation reference's type is its declared `FunType` chain, never an instantiation.

> **Open (overview §12.4, §12.13).** `Family` and `Self` are the recursive self-references; whether
> they are _reserved_ type names or shadowable by user declarations is decided in favour of reserved
> (overview §12.16) but the enforcement is not yet in the core's lexer.

---

## 4. Declaration Forms

There are six declaration forms. All are top-level; a program's top level is **declarations only** —
there are no expression statements and no binding/definition form (overview §12.6, §12.21).

Named values are _declared_, never bound: a zero-field variant introduces a value (`variantRef`,
§3.4), and an operation declaration introduces a named computation with a declared type and an entry
in `Ω` (so it can carry laws and a cost summary). A `camelCase` name in expression position resolves
to the enclosing declaration's bindings and the declared operations in scope; it is never introduced
by assignment.

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

> **Decided (overview §12.29).** A declaration's head is a bare `pascalIdent` — **never a parameter
> list**. The same holds for §4.2–§4.6: `behavior`, `protocol`, `relation`, `query`, and `io` all
> take `pascalIdent` and nothing else. There is no `data List<a>`, and adding one would require a
> type-application production that `atomType` (§3.8) deliberately does not have. Element types vary
> by **subtyping** (`NatList <: List`, covariance-checked per field) or by `Any`.

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
protocolDecl    ::= "protocol" pascalIdent ( "<:" ␣ pascalIdent )? ⏎ protocolBody

protocolBody    ::= ␣(4) protocolItem+

protocolItem    ::= foldSignature
                 | unfoldSignature
                 | mapSignature
                 | mergeDecl
                 | scanDecl

foldSignature   ::= "fold" ident ␣ specRecord ( ⏎ memberBody )?
mapSignature    ::= "map" ident ␣ specRecord ( ⏎ memberBody )?
unfoldSignature ::= "unfold" pascalIdent ( ␣ specRecord )?

memberBody      ::= ␣(8) ( contractClause ⏎ )* ␣(8) expr
```

**A protocol member is a signature with an optional default.** The `fold`/`unfold`/`map` keyword is
required, because the member's kind is load-bearing: fold and map members admit a default body,
unfold members do not, and `merge`/`scan` are themselves kind-named. A `fold`/`map` member must
state its type with a spec record, and a `merge`/`scan` member with the `#name` form — without one a
conforming type has nothing to satisfy. An **unfold** member needs neither: an unfold's result type
is the declaration site (§5.2), which here is the conforming type itself, so `unfold Identity`
states all there is to state. Its seed, when it has one, is `<in: …>` and is the conformer's to
choose; a seedless unfold requires a constant constructor, which is the shape a protocol needs for
an identity element.

| Item     | Type stated by | Default body | Why                                                        |
| -------- | -------------- | ------------ | ---------------------------------------------------------- |
| `fold`   | `specRecord`   | allowed      | A default composes the type's own operations over `self`   |
| `map`    | `specRecord`   | allowed      | Same; a map is an operation like any other                 |
| `unfold` | — (site)       | **rejected** | Its result type is the declaring type; the seed is `<in:>` |
| `merge`  | `<#name, …>`   | **rejected** | It names a fusion of existing folds, not a computation     |
| `scan`   | `<#name>`      | **rejected** | Same — a fusion directive, not a computation               |

**A default body is an expression, not a `foldBody`.** `foldBody` (§5.1) and `mapBody` (§5.3) both
begin with `caseArm`s, which dispatch on the _declaring_ type's variants — and a protocol cannot see
its conformers' variants. So a default body has no arms and only composes operations:
`(self equals: other) not`. It may be preceded by contract clauses, which the default honours
exactly as a declared operation does; see [`elaboration.md`](./elaboration.md) §3.3.

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

contractClause ::= clauseKind ":" ␣ ident* ( "|" ␣ )? ⏎ ␣(12) expr

clauseKind     ::= "demands" | "ensures" | "invariant" | "rescue"

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

**Contract clauses carry a body, not a block.** A clause names its bindings after the `:` — the same
`ident* ( "|" expr )` head a block literal used — and then takes an indented expression (`␣(12)`,
the column of a multi-line arm body, §7):

```
demands: self | self size > 0
ensures: self old result | result size = old size - 1
rescue:  self err args retry | retry value: 0
```

The clause's body is _always_ forced by the fold machinery — before the body, after the body, at
construction, on failure — and is never held as a value, so it needs no literal and no function
value. What it does need is the binding head, which is a **clause parameter list**, not an anonymous
function: the names are supplied by the machinery (`self`, `old`, the result, the error/args/retry
of `rescue`), exactly as a fold arm's bindings are supplied by its variant. This is the same
relationship an arm head has to its fields — a declared binding position, not a lambda.

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
unfold Range <in: Int>
    Nil n -> n = 0
    Cons n -> n > 0 | head: n rest: n - 1
```

**An unfold may have no seed.** When the spec record omits `in:`, the unfold takes no input and its
arms carry no bindings — the arm head is the variant it produces and the guard alone decides:

```lapis
unfold Identity
    Zero -> true
```

That is a constant constructor: one arm, always applicable, producing a fieldless variant. No spec
record appears because an unfold's result type is the declaration site, never a parameter — so there
is no `out:` to write, and with no seed there is no `in:` either. A seedless unfold is therefore how
a protocol requires a constructor each conformer must supply — the identity element of a monoid is
the worked case — without a `fold`'s arms and without a default body (§4.3).

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
mapDecl        ::= "map" ident specRecord? ⏎ mapBody

mapBody        ::= ␣(8) foldItem+
```

A map is declared in the **same body form as a fold** — one arm per variant, indented at the fold
body's column — because that is what it elaborates to: a fold (data) or an unfold (codata) whose arm
bodies transform each field. There is no separate single-line transform form; a transform is not a
literal, it is the operation's own body.

```lapis
map double <in: Int, out: Family>
    Nil x -> Family Nil
    Cons head tail x -> Family Cons head: (head * x) tail: (tail double: x)
```

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

## 7. Layout

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

> **Decided (overview §12.6).** An arm body is a single expression. There is no arm-level binding
> form — no `let … in`, no `name ::= expr` header, no initialised-slot block. An intermediate needed
> by one arm is a declared operation (a sibling `fold`, possibly companion via `<aux: …>`), which
> carries a declared type, a law set, and a cost summary that an anonymous local could not. See §9's
> `quadratic` example for the worked case.

---

## 8. Abstract Syntax

The AST node types, matching spec §2.1 and the implementation's shapes:

| Production       | AST node                                                                      |
| ---------------- | ----------------------------------------------------------------------------- |
| `expr`           | `Expr` — a discriminated union of the forms below                             |
| `keywordExpr`    | `KeywordCall(receiver, parts: {key, value}[])`                                |
| `binaryExpr`     | `BinaryCall(receiver, op, arg)`                                               |
| `unaryExpr`      | `UnaryCall(receiver, selector)`                                               |
| `primary`        | `primary` — one of the composite/reference/literal forms below                |
| `arrayLiteral`   | `ArrayLit(items: Node[])`                                                     |
| `recordLiteral`  | `Record(entries: RecordEntry[])` where `RecordEntry(key, value)`              |
| `specRecord`     | `Spec(entries: SpecEntry[])` where `SpecEntry(key, value: Node \| null)`      |
| `variantRef`     | `VariantRef(name)`                                                            |
| `construction`   | `VariantConstruct(name, args: {field, value}[])`                              |
| `reference`      | `SelfRef` \| `FamilyRef` \| `CoSelfRef` \| `OldRef` \| `PrevRef` \| `AuxRef`  |
| `dataDecl`       | `DataDecl(name, parent, body: DataBodyItem[])`                                |
| `behaviorDecl`   | `BehaviorDecl(name, parent, observers: Field[], body: BehaviorBodyItem[])`    |
| `protocolDecl`   | `ProtocolDecl(name, parent, members: ProtocolMember[])`                       |
| `relationDecl`   | `RelationDecl(name, variants: Variant[], folds: FoldDecl[])`                  |
| `queryDecl`      | `QueryDecl(name, observers: Field[], unfolds: UnfoldDecl[])`                  |
| `ioDecl`         | `IoDecl(name, stateFields: Field[], arms: CaseArm[])`                         |
| `foldDecl`       | `FoldDecl(name, spec, contractClauses, arms: CaseArm[])`                      |
| `protocolMember` | `FoldDecl \| UnfoldDecl \| MapDecl \| MergeDecl \| ScanDecl`, `arms` optional |
| `unfoldDecl`     | `UnfoldDecl(name, spec, arms: CaseArm[])`                                     |
| `mapDecl`        | `MapDecl(name, spec, arms: CaseArm[])`                                        |
| `mergeDecl`      | `MergeDecl(name, foldNames: string[])`                                        |
| `caseArm`        | `CaseArm(head, bindings, body)`                                               |
| `unfoldArm`      | `UnfoldArm(head, bindings, guard, payload)`                                   |

### 8.1 Why a case arm has no bound intermediate

An arm body's bindings are exactly the arm head's: the variant's fields, plus the fold's `in:`
argument as a trailing binding (§5.1). Nothing else can be introduced — there is no `let … in`, no
`name ::= expr` header, and no initialised-slot block.

The motivating case is the quadratic formula, whose two roots share the discriminant and the `2a`
denominator. The discriminant is spelled as a **declared sibling operation** and fused into `roots`
via `<aux: …>` (§5.1), rather than bound in the arm. The full worked file — with the result type,
the `sqrt` domain as a `demands:` contract, and the `Int`-pattern trap on `-b` — is
[`examples/quadratic.lapis`](../../examples/quadratic.lapis); the shape is:

```lapis
data Quadratic
    Coeffs a: Float b: Float c: Float

    fold discriminant <out: Float>
        Coeffs a b c -> (b * b) - (4 * a * c)

    fold roots <aux: #discriminant, out: QuadraticRoots>
        demands: self | self hasRealRoots
        Coeffs a b c -> Roots
            plus: ((- b + ((aux discriminant) sqrt)) / (2 * a))
            minus: ((- b - ((aux discriminant) sqrt)) / (2 * a))
```

Two details in that snippet are load-bearing rather than stylistic. `- b` is written with a space:
contiguity is position-meaningful, so a contiguous `-3` is one `Int` token (the `-?[0-9]+` pattern)
while `- expr` in prefix position is `negate` applied to `expr`. The space is what picks the second
reading. And the `demands:` clause is how `sqrt`'s partiality is handled — the principal square root
is undefined over the reals for a negative radicand, so `roots` is callable only on a value with a
non-negative discriminant, which makes the precondition checkable instead of a silent domain error.

**This example is a target, not runnable code.** `Float` and `sqrt` are deferred by the prelude
([`prelude.md`](./prelude.md) §5.3) because `sqrt`'s domain restriction needs `demands:` and
contract elaboration is not in the surface implementation's first cut; `Float`'s language
(`-?[0-9]*\.[0-9]+`) is disjoint from `Int`'s, so adding it later costs no collision. The `Int`
arithmetic it also depends on has its own blocker
([#119](https://github.com/lapis-lang/lapis-lang/issues/119)).

This is strictly better than a local would be, on four counts that an anonymous binder cannot match:

- **Type.** `discriminant` is declared `out: Float`; a local would carry only the type of its
  expression, and the surface has no binder that could introduce one in the first place (there is no
  `let`, and no block literal — §3.6.1).
- **Reuse.** It is callable elsewhere (`q discriminant`) instead of being scoped to one body.
- **Laws and cost.** As an operation it holds a place in `Ω`, so it can carry `properties:` and a
  memoized cost summary (`cost.ts`); a local has neither.
- **Identity under substitution.** `E-Op` keeps the named form through elaboration so operation
  identity survives inlining (`lc.md` §3) — the property the optimizer's law-aware passes need.

The corpus bears this out: across every worked example in `_docs/`, no arm body computes an
intermediate it needs twice, except the two-root case above, which `<aux: …>` already serves.

---

## 9. Implementation Status

Per-production, against the core in `src/core/`. The core grammar is the abstract base `AbstractLC`
(`grammar.ts`); the semantic passes are its subclasses `LCTypeCheck` (`typing_grammar.ts`) and
`LCEval` (`eval_grammar.ts`).

| Production group              | Status                                                                                                                                                                                                                                                                                                      |
| ----------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Core terms (`lc.md` §2.2)     | **Implemented** — `lambdaProd`, `foldProd`, `unfoldProd`, `cofoldProd`, `letProd`, `variantProd`, `patternTokenProd`, `patternMatchProd`, `obsProd`, `appProd`, `opProd`, `typeAbsProd`, `typeAppProd`                                                                                                      |
| Types (`lc.md` §2.1)          | **Implemented** — `typeProd`, `atomType`                                                                                                                                                                                                                                                                    |
| Surface expressions (§3)      | **Partial** — the core's expression productions cover the LC core's term forms, not the surface's message chain. `appProd` is the **core's** juxtaposition, which the surface grammar does not expose: the surface has no application production at all, and applies through the keyword send (§3.2, §3.3). |
| Surface declarations (§4, §5) | **Not implemented** — no `data`, `behavior`, `protocol`, `relation`, `query`, or `io` production; the registered types in the test fixtures are built through the `DataTypeBuilder` API, never parsed from a declaration                                                                                    |
| Modules (§6)                  | **Not implemented** — Stage 7                                                                                                                                                                                                                                                                               |

The implemented keyword set is exactly `<:`, `cofold`, `fold`, `in`, `let`, `match`, `unfold` — the
core's own vocabulary. `in` and `let` are the core's `let x:σ = t in u` terminator and former; they
are **not** surface keywords, and the surface grammar has no `let` production (§4, §7). Every
surface declaration keyword above is still a production to write.

The surface declaration productions are the target of Stage 1 in
[`language-design.md`](./language-design.md) ("surface `data`/`fold` → core μ/fold").

---

## 10. Open Questions

The questions this grammar does _not_ settle, with their owning finding in
[`overview.md`](../overview.md) §12:

| #                                                         | Question                                                                                                                           | Finding |
| --------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------- | ------- |
| 1                                                         | The generator-arm payload's collision with the greedy keyword-send collection — the arm body needs its own restricted production   | §12.2   |
| 2                                                         | `\|` as the generator separator — reserve it, or pick `=>`?                                                                        | §12.2   |
| 3                                                         | Variant qualification at construction, and the bare default for an _inherited_ variant                                             | §12.7   |
| 4                                                         | `scan`'s surface spelling                                                                                                          | §12.20  |
| 5                                                         | The module system's surface grammar                                                                                                | §12.20  |
| 6                                                         | The symbolic operator character set (whether `:` is an operator character)                                                         | §2.1    |
| 7                                                         | `Family`'s reservation in type position (decided, but unenforced in the core)                                                      | §12.16  |
| 8                                                         | The string-escape vocabulary (`\n`, `\t`)                                                                                          | §1.4    |
| 9                                                         | Pattern captures: capture-vs-type-reference disambiguation, delimited regions, `\|` in patterns, and slice gating                  | §12.8   |
| 10                                                        | The user-declared pattern member's surface syntax (the mixed-carrier form)                                                         | §12.4   |
| 11                                                        | The `aux` reference's read spelling (`aux d` vs. `aux #d`)                                                                         | §12.26  |
| 12                                                        | Partial application (sections): supplying some of an operation's arguments — spelling, elaboration, and effect on the cost algebra | §12.27  |
| 13                                                        | The law argument's spelling: `identity:` wants a value, `#name` is a reference, and a protocol's identity is an operation          | §12.32  |
| 14                                                        | Operation aliasing (`.as(...)`): no surface spelling, and a protocol is where two naming conventions must coexist                  | §12.33  |
| **Closed (recorded here so the numbering stays stable):** |                                                                                                                                    |         |

- **The conditional's branch arity** — there is no conditional. `ifTrue:ifFalse:` is retired: no
  declaration, no sugar. `Bool` appears in result position only, and branching is structural
  dispatch (fold arms on variants, `guard | payload` arms on unfold seeds). A decision over a value
  with no discriminating variants belongs in an unfold over a declared seed type — `take` is the
  worked case (`syntax-design.md` §"Behavior"). See also `elaboration.md` §10.
- **Surface application** (`expr expr` vs. a `value:` send) — there is **no application
  production**. A keyword send eliminates its receiver and applies the arguments; a receiver of
  function type `σ → τ` applies through the `value:` selector, exactly as μ-types eliminate by
  `fold` and ν-types by observation (§3.2, §3.3, §3.6.1).
- **The top-level definition form** (`name = expr`) — there is none; see §4 and overview §12.6.
- **Arm-level bindings** — there is no `let`/definition/initialised-slot form in any body; see §7.
- **The block literal** (`[params | expr]`) — retired; see §3.6.1.
- **Type variables and type parameters** — there are none, by design and permanently; see §3.8 and
  §4.1, and overview §12.29.
- **Protocol members** — the kind keyword is required and so is the member's type (a spec record, or
  the `#name` form for `merge`/`scan`); `fold` and `map` members admit a default body,
  `unfold`/`merge`/`scan` do not; a default body binds `self` and (when `in:` is declared) `other`,
  and is an expression rather than an arm list. See §4.3, §3.7, and overview §12.30. `between:and:`
  is retired: a selector has at most one keyword part.

---

## 11. See Also

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
