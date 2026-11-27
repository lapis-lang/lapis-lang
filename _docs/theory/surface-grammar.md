# Lapis Surface Grammar

> **Status:** Draft v0.1. This document covers what a production set cannot state about itself:
> lexical structure, layout, the per-production implementation status, and the open questions. The
> **productions themselves** are the `@rule` methods of
> [`src/surface/grammar.ts`](../../src/surface/grammar.ts), whose header carries the same grammar in
> EBNF. That file is normative on _shape_; this document is normative on _tokens_ and _layout_, and
> is the index from a production to its status.
>
> [`surface-syntax.md`](./surface-syntax.md) remains the _narrative_ specification: the pattern
> language, precedence rationale, railroad diagrams, and the worked examples. Where this document
> and the code disagree on the shape of the syntax, **the code wins** — a claim here that no `@rule`
> admits is a defect in this document.
>
> **Status of the surface grammar in the implementation:** the core calculus is implemented
> (`src/core/grammar.ts`) and the surface pipeline is under `src/surface/` — parse to an AST,
> resolve names, then elaborate to the core's concrete syntax. Implemented today: layout (§4),
> `data` with named variants, an in-body `fold`, and the expression forms an arm body needs. The
> other five declaration kinds (`behavior`, `protocol`, `relation`, `query`, `io`), variant
> inheritance, pattern members, and `merge`/`scan`/`map` are not. See §5 for the per-production
> status and for why the surface is a two-phase pipeline while the core is a one-pass executable
> grammar.

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
| `␣`              | one space (or the layout's required indentation — §4) |
| `⏎`              | a newline (the statement separator — §4)              |
| `ε`              | the empty sequence                                    |

**Terminals** are written as quoted strings; **non-terminals** as `camelCase` or `PascalCase`
identifiers. Keywords (`data`, `fold`, …) are terminals.

**Layout.** Two layout rules apply to every production and are _not_ written inline:

- **L1 — Indentation.** A block's contents must be indented exactly one unit (4 spaces) more than
  the line that introduces it. Continuation lines within a body line are indented further.
- **L2 — Newline.** A newline separates body lines. Blank lines and comments are consumed between
  them.

Both are formalized in §4.

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
fuller escape vocabulary (`\n`, `\t`) is **open** (`surface-syntax.md` §9.1).

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

A comment's content is **free text**: it may contain tabs, and any other character except an
unbalanced `*/`. The whitespace rules below apply to code only.

### 2.7 Whitespace

```
hws        ::= " "*
hws1       ::= " "+
```

**Whitespace is spaces, never tabs.** A tab is not a whitespace character in any code position, so a
file that mixes the two is rejected rather than silently re-indented. The rule follows from L1 (§4):
the indent unit is exactly four spaces, so a tab would make a line's column depend on the reader's
tab width — and a mix of the two makes the nesting a matter of editor configuration rather than of
the source.

This is enforced at the lexical level, which is what makes it total: `hws` and `hws1` admit the
space character only, so a tab between tokens, after a line's code, or on an otherwise blank line is
a rejected character rather than a tolerated separator. Comments (§2.6) are the sole exception,
because their content is prose.

---

## 2.8 Constructor position

A **constructor** is a `pascalIdent` in expression position — a `variantRef` or a `construction` —
and nothing else. A `camelCase` name is a binding or an operation reference; a literal is whatever
text a declared pattern matched. Type names are checked where they are written (an annotation), but
a constructor names its variant _inside a body_, so it needs its own resolution rule (implemented by
`src/surface/resolve.ts`).

### Field names bind; order does not

A construction spells its fields as **named arguments**, and a name binds by name:

> A construction denotes its variant **iff** it names every declared field exactly once and nothing
> else. The order the pairs are written in carries no meaning — `P2 x: … y: …` and `P2 y: … x: …`
> are the same construction.

This is the point of named arguments: the caller says which slot each value fills, and a variant's
field names are unique within it, so there is no ambiguity for the order to resolve. Rejecting a
reorder would refuse valid code — the two spellings denote one value.

The core's construction is positional, `Cᵢ(t₁, …, tₙ)`, so **elaboration emits the arguments in
declaration order**, resolving each name to its slot (`elaboration.md` §2.7). That mapping is what
elaboration is for: the surface is order-insensitive, the core is positional.

An undeclared field, a duplicated field, and an omitted field are all rejected — each leaves a slot
unbound or a value with no slot.

### Bare and qualified

A construction may name the type whose constructor is meant — `Point Point2D x: 1 y: 2` — and bare
is the default:

- A **bare** name resolves iff it is unique in scope. Two types with no ancestry relation declaring
  the same variant make it ambiguous, and the qualified form is required.
- A **qualified** name requires the qualifier to be a declared type that declares the variant. A
  qualifier naming no declaration, or a type whose variants lack the name, is an error.
- A **parent and child** that both declare a variant are **not** ambiguous. A child re-declaring an
  inherited variant is narrowing it (comb inheritance, `surface-syntax.md` §4.1), so the two
  declarations are one constructor. Only declarers with no ancestry relation collide.

A bare _inherited_ variant's constructing type — what `Cartesian2 x: 1 y: 2` denotes when
`Point3 <: Point2`, and therefore which member sets the value belongs to — is a different question,
and is not decided here (overview §12.7, [#86](https://github.com/lapis-lang/lapis-lang/issues/86)).

### Diagnostics

| Reason                  | When                                                                  |
| ----------------------- | --------------------------------------------------------------------- |
| `unknown-constructor`   | A bare name no type in scope declares                                 |
| `ambiguous-constructor` | A bare name declared by types unrelated by ancestry (names every one) |
| `bad-qualifier`         | The qualifier is not a declared type, or lacks the named variant      |
| `selector-mismatch`     | A field is omitted, duplicated, or undeclared                         |

The walk covers every expression position a constructor can occupy — a construction's field values,
a call's receiver and its keyword-part values, a `binop`'s operands, a `unary`'s operand, and any
depth of parentheses — plus a fold's arm bodies and contract-clause bodies, and a `map`'s transform
bodies.

**No scope is needed.** An arm head's binding is a `nameOrKeyword` (`ident` or a keyword, never a
`pascalIdent`), so it cannot shadow a constructor, and no other form introduces a name in an
expression. Constructor resolution is therefore a property of the name alone, plus the program's
declarations.

---

## 3. Module Declarations

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

## 4. Layout

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

The implementation uses **P4P-style column-parameterised productions** (see
`src/surface/layout.ts`): no pre-pass, no token rewriting. Every block-introducing production takes
the child column as a parameter, and `spaces(n)` matches exactly `n` spaces.

Because the column is measured in spaces, **a tab is not whitespace in code position** (§2.7): a
file that mixes the two has no well-defined column, so the mix is rejected rather than resolved by
an assumed tab width.

### L2 — Newline

A newline separates body lines. Blank lines and comments are consumed between them. Both `\r\n` and
`\n` are accepted.

### Inline vs. indented bodies

A case arm's body may be inline (same line, after `->`) or indented (next line, deeper). The parser
tries the indented form first (longer match), then falls back to inline.

> **Decided (overview §12.6).** An arm body is a single expression. There is no arm-level binding
> form — no `let … in`, no `name ::= expr` header, no initialised-slot block. An intermediate needed
> by one arm is a declared operation (a sibling `fold`, possibly companion via `<aux: …>`), which
> carries a declared type, a law set, and a cost summary that an anonymous local could not. See
> `examples/quadratic.lapis` for the worked case.

---

### 4.1 Why a case arm has no bound intermediate

An arm body's bindings are exactly the arm head's: the variant's fields, then — when the fold
declares an `in:` — one further name for that parameter (see the `armHead` production). Nothing else
can be introduced — there is no `let … in`, no `name ::= expr` header, and no initialised-slot
block.

**A fold arm's head is a pattern: each binding carries the name of the field it binds.** The `i`th
binding _is_ the `i`th field _and is spelled with that field's name_, because a case arm is a
pattern-matching form and a pattern reads as a destructuring of the declared variant:

```lapis
data P
    M a: Any b: Any

    fold first <out: Any>
        M a b -> a            /* a is field `a`, b is field `b` */
```

`M a b -> a` is the only spelling that denotes this arm. `M x y -> x` is **not** an alternative
spelling — it would bind names the declaration does not have, and is rejected. This is the same rule
§2.8 gives for construction, read in the other direction: a construction's keyword sequence must
equal the declared fields (the selector carries the meaning), and an arm head's binding sequence
must equal them too (the pattern carries it). Both forms are checked against the declaration, so
neither consults the other's names — `M b a -> …` is not a swap, it is an arm that binds no declared
field.

`_` discards a field without naming it, so a partial pattern is `Cons _ rest -> rest` rather than an
abbreviated name. The underscore is therefore the _only_ binding that is not a field's name.

An arm that needs fewer values than fields writes every field's name (or `_`). A head binds
**nothing else**: the fold's `in:` value is not one of its bindings.

> **Scope.** This is the _fold_ arm's rule. An **unfold** arm binds the **seed**, which no variant
> declares, so its name is the author's choice —
> `unfold FromArray <in: List> / Empty arr -> arr isEmpty` binds the seed as `arr` because `List`
> has no field to agree with. A fold arm's fields come from a declaration and are therefore
> checkable; an unfold arm's seed does not and is not.

**The `in:` argument is machinery-supplied and read from the body.** A fold that declares `in:`
receives the value under the name `in`, which the body reads directly:

```lapis
fold add <in: Self, out: Self>
    Zero -> in
    Succ pred -> Succ pred: (pred add: in)
```

`in` appears in no arm head, exactly as `self` does not: both are names the machinery supplies and
the author only reads. The same word serves the spec record's key and a protocol default body's
scope (`elaboration.md` §3.3), so one name means one thing in all three positions — and because `in`
is a keyword, it cannot name a variant field, so no field can collide with it.

**The `in:` value is a lambda binding, not a handler binding.** The elaborated definition is
`λe:<declaring type>. λ<core-name>:<in-type>. fold_T e {…}` (`elaboration.md` §3.1), so the binder
encloses the whole fold and is visible in every arm's body. The handler's positional binding list
holds only the variant's fields — `Zero -> in` emits `Zero() -> <core-name>`, because the value is
already in scope from the enclosing lambda and the core's `E-Fold` supplies no value for it (`lc.md`
§3.1). The `<core-name>` is not `in`: the core reserves that word (`LC_RESERVED_WORDS`, its
`let … in` delimiter), so elaboration chooses a core-legal spelling that also avoids the arm's own
field names.

**The same hazard applies to `aux`.** `referenceProd` takes `aux` as a keyword followed by a bare
`ident`, and it is tried before a plain identifier, so `aux length` always reads the **auxiliary
fold** named `length` — never an arm binding that happens to be called `length`:

```lapis
fold f <aux: #size, out: Any>
    Nil -> Nil
    Cons length rest -> (aux length)     /* the aux fold, not the binding */
```

An arm binding a value as `length` therefore has no way to read it as `length` inside `aux length`.
Unlike `in`, this is not a name the language can reserve away: the collision is between an
_operation_ name and a _field_ name, both legitimate identifiers, and `aux`'s operand is syntax. A
program whose auxiliary fold and a field share a name needs one of them renamed —
`surface-grammar.md` §5.1's `aux` spelling (`#107`) is where the operand's form is decided.

Two consequences follow, and both are enforced at resolution:

- **The names must be the fields'.** Each of the `variant.fields.length` bindings must be that
  field's declared name (or `_`); a head matching the count but misspelling a field is reported, not
  silently rebound. `M y x -> …` is therefore an error, not a swap.
- **The count is exact.** An arm head binds exactly `variant.fields.length` names — no more, because
  the `in:` value is read from the body, and no fewer, because every field must be named. A mismatch
  is `arity-mismatch` rather than a silently dropped binding.

At most one `in:` is declared (`surface-syntax.md` §2.3: an operation takes the receiver and at most
one `in:` value), so a spec record repeating a key is `duplicate-spec-key` — `specRecord` is a
keyword list, and the second `in:` would otherwise be dropped without a diagnostic.

The motivating case is the quadratic formula, whose two roots share the discriminant and the `2a`
denominator. The discriminant is spelled as a **declared sibling operation** and fused into `roots`
via `<aux: …>`, rather than bound in the arm. The full worked file — with the result type, the
`sqrt` domain as a `demands:` contract, and the `Int`-pattern trap on `-b` — is
[`examples/quadratic.lapis`](../../examples/quadratic.lapis); the shape is:

```lapis
data Quadratic
    Coeffs a: Float b: Float c: Float

    fold discriminant <out: Float>
        Coeffs a b c -> (b * b) - (4 * a * c)

    fold roots <aux: #discriminant, out: QuadraticRoots>
        demands: self | self hasRealRoots
        Coeffs a b c -> Roots
            plus: (((b negate) + ((aux discriminant) sqrt)) / (2 * a))
            minus: (((b negate) - ((aux discriminant) sqrt)) / (2 * a))
```

Two details in that snippet are load-bearing rather than stylistic. `b negate` is a **suffix** send,
never `- b`: a symbol at the start of a token introduces data, so `-3` is one `Int` token (the
`-?[0-9]+` pattern) and `- b` would be that pattern failing to match `b`. Prefix position belongs to
constructors, which is why a unary operation is written as a message. And the `demands:` clause is
how `sqrt`'s partiality is handled — the principal square root is undefined over the reals for a
negative radicand, so `roots` is callable only on a value with a non-negative discriminant, which
makes the precondition checkable instead of a silent domain error.

**This example is a target, not runnable code.** `Float` and `sqrt` are deferred by the prelude
([`prelude.md`](./prelude.md) §5.3) because `sqrt`'s domain restriction needs `demands:` and
contract elaboration is not in the surface implementation's first cut; `Float`'s language
(`-?[0-9]*\.[0-9]+`) is disjoint from `Int`'s, so adding it later costs no collision. The `Int`
arithmetic it also depends on has its own blocker
([#119](https://github.com/lapis-lang/lapis-lang/issues/119)).

This is strictly better than a local would be, on four counts that an anonymous binder cannot match:

- **Type.** `discriminant` is declared `out: Float`; a local would carry only the type of its
  expression, and the surface has no binder that could introduce one in the first place (there is no
  `let`, and no block literal).
- **Reuse.** It is callable elsewhere (`q discriminant`) instead of being scoped to one body.
- **Laws and cost.** As an operation it holds a place in `Ω`, so it can carry `properties:` and a
  memoized cost summary (`cost.ts`); a local has neither.
- **Identity under substitution.** `E-Op` keeps the named form through elaboration so operation
  identity survives inlining (`lc.md` §3) — the property the optimizer's law-aware passes need.

The corpus bears this out: across every worked example in `_docs/`, no arm body computes an
intermediate it needs twice, except the two-root case above, which `<aux: …>` already serves.

---

## 5. Implementation Status

Per-production, against the core in `src/core/` and the surface pipeline in `src/surface/`. The core
grammar is the abstract base `AbstractLC` (`grammar.ts`); the semantic passes are its subclasses
`LCTypeCheck` (`typing_grammar.ts`) and `LCEval` (`eval_grammar.ts`). The surface language uses a
_different_ shape, explained below the table.

| Production group                                                                              | Status                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| --------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Core terms (`lc.md` §2.2)                                                                     | **Implemented** — `lambdaProd`, `foldProd`, `unfoldProd`, `cofoldProd`, `letProd`, `variantProd`, `patternTokenProd`, `patternMatchProd`, `obsProd`, `appProd`, `opProd`, `typeAbsProd`, `typeAppProd`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| Types (`lc.md` §2.1)                                                                          | **Implemented** — `typeProd`, `atomType`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| Surface layout (§4)                                                                           | **Implemented** — `src/surface/layout.ts`: exact-column `spaces(n)`, newline-excluding `hws`/`hws1`, `lineEnd`, nestable block comments, and `trivia`. Column threading is a `@rule` method parameter, the engine's documented answer for context-sensitive grammars.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Surface expressions                                                                           | **Partial** — `primary`, the three call forms, references, literals, spec records, and types are implemented in `src/surface/grammar.ts`. Not yet: array and record literals, contract-clause semantics (#110), and pattern-driven literals beyond the numeric subset. **Consequences.** `properties`'s `recordLiteral` value shape has no production, so every law spelling in the corpus is a parse failure (overview §12.35). Operator names are never resolved — an undeclared symbolic operator is passed into the emitted core text (§12.35), and the emitted infix form has no core production at all (§12.49). **Constructor position is resolved** (§2.8): a bare or qualified name must denote a declared variant, and a construction's keyword sequence must equal the variant's declared field sequence (#84). A qualified operation reference still has no grammar path and no core spelling (§12.39). A fold's `in:` value is bound by an arm's trailing binding (§4.1), so a two-argument operation's                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| signature and its definition agree (§12.48); a recursive one still cannot enter `Ω` (§12.50). |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| Surface declarations (§4, §5)                                                                 | **Partial** — `data` with named variants and an in-body `fold` (declarations and case arms) are implemented. Not yet: `behavior`, `protocol`, `relation`, `query`, `io`; variant inheritance — §4.1's `<:` is parsed, validated, then **discarded**, so `DataType.parent` is always `null` and no inherited variant exists ([#86](https://github.com/lapis-lang/lapis-lang/issues/86)); pattern members; `merge`/`scan`; `map`, which parses, is never validated, and is dropped (§12.40, [#124](https://github.com/lapis-lang/lapis-lang/issues/124)); `satisfies`. **Consequences.** Elaboration **has a verdict** (§12.47, closed): each emitted operation is checked against its declared signature by the core's own `opWellFormedness`, and `elaborateProgram` returns `ok`, per-operation `errors`, and an `opRegistry` holding only the operations that passed — so every elaborated operation is an `Ω` entry, checked by one implementation. A fold's `in:` parameter is compared against the definition's by the same check, so a declaration whose `in:` names something other than what the emitted lambda takes is `not-well-formed` (§12.58). A fold's `out:` is **declared or inferred** (`elaboration.md` §1.3): a declared one is a premise on every arm, checked case by case so a disagreement names the arm rather than the σ fixpoint's `Any`, and an omitted one is inferred as the arms' LUB — an inference that lands on `Any` from disagreement is reported, not admitted (§12.61). A **recursive** operation still cannot enter `Ω` — its body names itself, which `Ω`'s acyclicity rule rejects, and it surfaces as `not-well-formed` (§12.50, [#131](https://github.com/lapis-lang/lapis-lang/issues/131)); `Ω` is also flat, so two types cannot both declare `size`. Contract-clause bodies are parsed and dropped (§12.52), and duplicate field, binding, and transform names are accepted (§12.51). |
| Modules (§3)                                                                                  | **Not implemented** — Stage 7                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |

### The hybrid architecture

The surface language is **parse-to-AST plus tree-consuming passes**, while the core stays a one-pass
executable grammar. Two requirements force the difference:

1. **Whole-program knowledge before elaboration.** A declaration's meaning depends on every other
   declaration — which variants exist, which operations are in scope — and the surface has no
   declaration ordering rule. A one-pass production cannot know a later declaration.
2. **A representation to elaborate _from_.** The message chain has no core counterpart, so the
   parsed form must be held while the target is constructed. The core's terms are themselves
   concrete syntax (`OpSig.definition`), so elaboration emits LC source text and the core parses it.

The pipeline (`src/surface/index.ts`):

```
surface source
     │  SurfaceParse              (executable grammar → surface AST)
     ├─ resolveProgram            (declaration table, reserved names, name resolution)
     ├─ elaborateProgram          (AST → DataType + Ω operations, as LC source)
     └─ LCTypeCheck / LCEval      (the core's one-pass grammar)
```

**Why the AST and not the `DerivationTree`.** `parseToTree` retains _where a `@rule` matched_, not
the shape of a production: a repeated production yields nested same-label nodes carrying partial
values (`many()` over a rule produces `[as] → [as] → [as] → [one]`), and a fixed-arity `seq` yields
one node with no children. A pass dispatching on those labels fires once per repetition and cannot
distinguish a partial value from a complete one. The AST is built by the productions' own semantic
actions, which see each production exactly once. `parseToTree` remains available — and is the right
vehicle — for spans, diagnostics, and unparsing (#34).

**The implemented keyword set** for the core is `<:`, `cofold`, `fold`, `in`, `let`, `match`,
`unfold`; the surface adds `data` and `fold`. `in` and `let` are the core's terminator and former,
**not** surface keywords: the surface grammar has no `let` production (§4).

---

## 6. Open Questions

The questions this grammar does _not_ settle, with their owning finding in
[`overview.md`](../overview.md) §12:

| #                                                         | Question                                                                                                                                               | Finding |
| --------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------ | ------- |
| 1                                                         | The generator-arm payload's collision with the greedy keyword-send collection — the arm body needs its own restricted production                       | §12.2   |
| 2                                                         | `\|` as the generator separator — reserve it, or pick `=>`?                                                                                            | §12.2   |
| 3                                                         | Variant qualification at construction — **decided** (`src/surface/grammar.ts`); the remaining open half is the bare default for an _inherited_ variant | §12.7   |
| 4                                                         | `scan`'s surface spelling                                                                                                                              | §12.20  |
| 5                                                         | The module system's surface grammar                                                                                                                    | §12.20  |
| 6                                                         | The symbolic operator character set (whether `:` is an operator character)                                                                             | §2.1    |
| 7                                                         | `Family`'s reservation in type position (decided, but unenforced in the core)                                                                          | §12.16  |
| 8                                                         | The string-escape vocabulary (`\n`, `\t`)                                                                                                              | §1.4    |
| 9                                                         | Pattern captures: capture-vs-type-reference disambiguation, delimited regions, `\|` in patterns, and slice gating                                      | §12.8   |
| 10                                                        | The user-declared pattern member's surface syntax (the mixed-carrier form)                                                                             | §12.4   |
| 11                                                        | The `aux` reference's read spelling (`aux d` vs. `aux #d`)                                                                                             | §12.26  |
| 12                                                        | Partial application (sections): supplying some of an operation's arguments — spelling, elaboration, and effect on the cost algebra                     | §12.27  |
| 13                                                        | The law argument's spelling: `identity:` wants a value, `#name` is a reference, and a protocol's identity is an operation                              | §12.32  |
| 14                                                        | Operation aliasing (`.as(...)`): no surface spelling, and a protocol is where two naming conventions must coexist                                      | §12.33  |
| **Closed (recorded here so the numbering stays stable):** |                                                                                                                                                        |         |

- **The conditional's branch arity** — there is no conditional. `ifTrue:ifFalse:` is retired: no
  declaration, no sugar. `Bool` appears in result position only, and branching is structural
  dispatch (fold arms on variants, `guard | payload` arms on unfold seeds). A decision over a value
  with no discriminating variants belongs in an unfold over a declared seed type — `take` is the
  worked case (`syntax-design.md` §"Behavior"). See also `elaboration.md` §10.
- **Surface application** (`expr expr` vs. a `value:` send) — there is **no application
  production**, and no surface receiver of function type either: a type is `atomType`, so no
  declaration can state one. Application is a **core** rule (a send to a function-typed receiver
  applies it, exactly as μ-types eliminate by `fold` and ν-types by observation), reached by
  elaboration rather than written.
- **The top-level definition form** (`name = expr`) — there is none; see §4 and overview §12.6.
- **Arm-level bindings** — there is no `let`/definition/initialised-slot form in any body; see §4.1.
- **The block literal** (`[params | expr]`) — retired.
- **Type variables and type parameters** — there are none, by design and permanently; see §4.1, and
  overview §12.29.
- **Protocol members** — the kind keyword is required and so is the member's type (a spec record, or
  the `#name` form for `merge`/`scan`); `fold` and `map` members admit a default body,
  `unfold`/`merge`/`scan` do not; a default body binds `self` and (when `in:` is declared) `in`, and
  is an expression rather than an arm list. See overview §12.30. `between:and:` is retired: a
  selector has at most one keyword part.

---

## 7. See Also

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
