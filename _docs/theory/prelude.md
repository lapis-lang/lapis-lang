# Lapis Prelude

> **Status:** Draft v0.1. The prelude is the set of types and operations a Lapis program sees
> without declaring them. This document is the **single definition site**: every built-in type name,
> its declaration spelling, and every symbolic operator's declaration trace here, and no other
> document introduces one. Where a spelling below differs from `surface-syntax.md` §1.3 or
> `overview.md` §2.3, this document wins and those tables are derived from it.
>
> The prelude is bound by the same rules as a user declaration. It is **not** a set of primitives in
> the calculus: `design-decisions.md` §"No base types" eliminates base types, `elaboration.md` §2.4
> states that every operator is an operation application resolving to a fold, and `lc.md` §2.1
> leaves exactly one non-μ/ν type, `Token`, which belongs to the core and is not a prelude name
> (§2.1). The prelude is a _program_ — the one every other program is elaborated against.

## 1. Scope

**In.** The names a program needs to state and run a data declaration with a fold over it: the
character and text carriers, one integer carrier in its two spellings, `Bool`, the one container,
the lattice bounds, and the folds over each. `Token`, the core's one non-μ/ν type, is **not** a
prelude name (§2.1).

**Out — and deliberately.** Anything whose _implementation_ depends on machinery the language does
not yet have: contracts (`Result`), law attribution (`properties:`, protocols), and machine-number
lexing. §5 names each with its owner. A name is in the prelude only when its declaration is writable
**and** its operations are definable in the surface language today.

The scope test is one question: _can a fixture use this name without a construct the language has
not pinned?_ If not, it is not in the prelude yet, however canonical it looks in the corpus.

## 2. The types

Six type names resolve without a declaration, plus the two lattice bounds. Each is an ordinary
μ-declaration written in the prelude — no base types, no primitives (`design-decisions.md` §"No base
types").

| Type              | Form    | Declaration                          | Value spelling           |
| ----------------- | ------- | ------------------------------------ | ------------------------ |
| `Char`            | pattern | `'.'`                                | `'a'`                    |
| `String`          | pattern | `"<Char>*"`                          | `"hello"`                |
| `Bool`            | named   | `True`, `False`                      | `true`, `false`          |
| `Int`             | pattern | `-?[0-9]+`                           | `42`, `-7`               |
| `Nat`             | named   | `Zero`, `Succ pred: Family`          | `Nat Succ …`             |
| `List`            | named   | `Nil`, `Cons head: Any rest: Family` | `Cons head: 1 rest: Nil` |
| `Any` / `Nothing` | lattice | — (bounds, not declarations)         | —                        |

### 2.1 `Token` is not a prelude name

The calculus has exactly one non-μ/ν type, `@Token` — the raw matched text (`lc.md` §2.1 and its
notation table, §2.6). It is **not** in the prelude and is **not user-spellable**: a program never
names it.

**The sigil is what makes that total.** `typeName` is `[A-Z][A-Za-z0-9_]*`, so `@Token` is not a
name in the grammar at all. That is deliberate: it means `Token` is an ordinary identifier, a user
may declare `data Token`, and the two are _different types_ rather than one contested name. No
decision reserves `Token`; the spelling settles it structurally.

A pattern fold's handler binds the matched token under the fixed name `match`, and that binding's
type is `@Token` (`lc.md` §5.2, `src/surface/grammar.ts`) . A program consumes the binding; it never
writes the type. This is why `@Token` is absent from §2's table while `Any` and `Nothing` are
present: the bounds are admitted by `atomType` as _surface_ type syntax (`src/surface/grammar.ts`),
and `@Token` is admitted by the same production only so the core's own terms can be written.

**Decision.** `@Token` belongs to Lapis Core alone. Reflection or metaprogramming would be the first
construct that could give a program a reason to name it; until such a construct exists, the surface
language has no `@Token` in type position. The consequence for the surface checker is stated in §8 —
an unknown name must be rejected, and `@Token` is not an exception to that rule.

### 2.2 `Char` and `String`

```lapis
data Char
    '.'

data String
    "<Char>*"
```

`Char`'s pattern is the **quoted** form `'.'` — literal quote, any character, literal quote — not
the bare `.` that `surface-syntax.md` §1.3 still prints. The bare form is both stale (it does not
match its own `'a'` example) and illegal: a leading `.` fails the anchoring premise, so
`parsePattern(".")` is rejected by the term gate (`grammar.ts`'s `isResolvableAndAnchored`,
`case "any": return false`). This is finding §12.22's resolution, applied.

The two quoted built-ins own the `'` and `"` heads: no user pattern may match a string beginning
with either (`surface-syntax.md` §1.3).

### 2.3 `Bool`

```lapis
data Bool
    True
    False
```

`Bool` declares **variants, not patterns** — so it can be destructured by a fold's arm heads, which
is the only way a program reads a branch. Its value spellings `true` and `false` are fixed by the
language (§4.1 below), because `variantDecl` requires a `pascalIdent` and `true` therefore cannot be
a variant name.

`Bool` appears in **result position only**. There is no conditional (`overview.md` §12.28):
branching is structural dispatch — a fold's arms dispatch on variants, an unfold's arms decide on a
seed.

### 2.4 `Int` — the surface integer

```lapis
data Int
    -?[0-9]+
```

One pattern, one carrier, covering both signs. The two-pattern spelling (`-[0-9]+` and `[0-9]+`,
`surface-syntax.md` §1.3) is retired: it needs two pattern members where one suffices, and the
single pattern is what lets `Int` be the sole owner of the integer token language. `-?[0-9]+` is
anchored (the optional `-` is transparent for anchoring — a postfix wrapper anchors at its inner
atom) and disjoint from `Float`'s language at the text level: `42` and `-7` are `Int`, `3.14` and
`-3.14` are not.

**`Nat` is not declared.** With `Int` covering the token language, a pattern-declared `Nat` would
collide with it at `42` — the registry's pattern index is keyed by canonical source, so
`Nat = [0-9]+` and `Int = -?[0-9]+` would each claim `42` and the surface declaration machinery must
reject the pair. There is no `Nat <: Int` either: pattern subtyping requires the subtype to declare
every pattern source its super declares, and `[0-9]+` is not `-?[0-9]+`. One integer carrier, no
collision, no false subtype.

### 2.5 `Nat` — the executable integer

```lapis
data Nat
    Zero
    Succ pred: Family
```

A Peano carrier: named variants, no patterns, no collision with `Int`. It exists because the surface
language can **write** its operations and cannot yet write `Int`'s (§6).

`Nat` and `Int` are two spellings of the integer story with no subtyping relation claimed in either
direction. `Int` is what a reader writes and what the prelude documents; `Nat` is what runs today.
They converge when machine-number lexing lands (§5.5) — until then, treating them as interchangeable
is an error, not a convenience.

### 2.6 `List`

```lapis
data List
    Nil
    Cons head: Any rest: Family
```

The one container. `Array` is retired: it was the same type under a second name (`syntax-design.md`
§"Behavior" called `Array` "the prelude's list"), and `elaboration.md` §2.6 already elaborates the
`{a, b, c}` literal to nested `Cons` on `List`. One name owns the literal, the `,` operator, and the
accessors.

The element type is `Any`, and the element-type relation is carried by **subtyping**, not by a type
parameter (`overview.md` §12.29):

```lapis
data IntList <: List
    Cons head: Int rest: Family
```

`IntList` re-declares `Cons` narrowing `head: Any` to `head: Int`; the narrowing is covariant, so
`IntList <: List` holds and every `List` operation applies to an `IntList`.

### 2.7 `Any` and `Nothing`

The lattice bounds, not declarations: `Nothing <: σ <: Any` for every type `σ` (`lc.md` §2.1). Both
are admitted directly by `atomType` (`src/surface/grammar.ts`) and are the only two type names that
resolve before the registry is consulted.

Their _scope_ — whether a module sees them without a dependency — is the module system's decision
(`overview.md` §12.24), not this document's.

## 3. The operations

Symbolic and named operators are the same thing: a name for a declared fold (`surface-syntax.md`
§2.1). This section pins **which** folds the prelude has and what each is declared over;
`elaboration.md` §2.4 pins how the symbolic spelling elaborates.

### 3.1 `Int` — arithmetic and comparison

| Symbolic | Named         | Signature               | Laws                                                              |
| -------- | ------------- | ----------------------- | ----------------------------------------------------------------- |
| `+`      | `add`         | `<in: Self, out: Self>` | `associative`, `commutative`, `identity: 0`                       |
| `-`      | `subtract`    | `<in: Self, out: Self>` | —                                                                 |
| `*`      | `multiply`    | `<in: Self, out: Self>` | `associative`, `commutative`, `identity: 1`, `distributive: #add` |
| `/`      | `divide`      | `<in: Self, out: Self>` | —                                                                 |
| `=`      | `equals`      | `<in: Self, out: Bool>` | —                                                                 |
| `<`      | `lessThan`    | `<in: Self, out: Bool>` | —                                                                 |
| `<=`     | `atMost`      | `<in: Self, out: Bool>` | —                                                                 |
| `>`      | `greaterThan` | `<in: Self, out: Bool>` | —                                                                 |
| `>=`     | `atLeast`     | `<in: Self, out: Bool>` | —                                                                 |

`-` is infix subtraction and nothing else; `negate` is a **suffix** send. Prefix position belongs to
constructors (which is why `-7` is one `Int` token and not an operation), so `- expr` is not a
production and `b negate` is how a negation is written. `surface-syntax.md` §1.5's `not` row is
corrected the same way.

The law column is the **`primitive` tier**: the operations' law sets are language fiat, and they are
the axiom base the derivation engine discharges composite claims from (`design-decisions.md`
§"Laws"). The signature column is the whole of what this document pins; each definition is deferred
(§5.5).

### 3.2 `Nat` — the executable twin

`Nat` carries the same operations, with definitions the surface can write:

```lapis
data Nat
    Zero
    Succ pred: Family

    fold add <in: Self, out: Self>
        Zero -> in
        Succ pred -> Succ pred: pred
```

This is `users/rationale.md` §4's worked example, and it is the shape the law suite already
exercises. Five things about the spelling are load-bearing:

- **An arm head is a pattern, so it spells the fields' names.** The arm head's first bindings are
  the variant's fields, in declaration order, and each is written with that field's own name — that
  is what makes `Succ pred in` read as a destructuring of `Succ pred: Family`. `Succ p i` is not an
  alternative spelling, it is an error, and `_` is the only way to discard a field
  (`Cons _ rest -> rest`). A head binds nothing else; the `in:` value is read from the body.
- **The extra argument is read as `in`.** It is machinery-supplied, so it appears in no arm head —
  the body reads it the way it reads `self`. The word matches the spec record's key and a protocol
  default body's scope (`elaboration.md` §3.3), and being a keyword it can also name no variant
  field, so no field can collide with it.
- **The carrier is the first argument; `in` is the second.** `add` is declared inside `data Nat`, so
  its first parameter is the `Nat` being folded and `in: Self` declares a second one of the same
  type. The definition is `λe:Nat. λ<core-name>:Nat. fold_Nat e {…}` — a lambda enclosing every arm,
  never a handler binding.
- **A recursive field binds the fold's result, not a continuation.** `Succ`'s `pred` field holds the
  already-folded `pred`, so `add`'s recursion is `Succ pred: pred` — the arm rebuilds `Succ` around
  a field that is already a number. Data folds are bottom-up (`lc.md` §5.2): the arm runs _after_
  its children, so nothing is re-folded and the operation never names itself.
- **The recursive field is the whole recursion.** A variant arm binds a `Family` field to
  `fold [T] vⱼ {…}` (`lc.md` §5.2, `E-Fold`), a value of the fold's result type. The prototype's std
  agrees: `List.length` is `Cons({ tail }) { return 1 + tail; }`, and `List.combine` is
  `Cons({ head, tail }, other) { return Cons({ head, tail: tail(other) }); }` — `tail` is the folded
  result, so for a `family`-valued fold it is a value to apply, not a computation to redo. There is
  no partially applied continuation, and no `value:` form in the data path.
- **A construction's fields are its selector.** `Succ` declares one field, `pred`, so `Succ pred:`
  is the only spelling of a `Succ` construction; `Succ value: …` is a different, undeclared
  constructor.

> **Runnable.** `Succ pred: pred` needs no self-reference, so `Ω`'s acyclicity rule (`lc.md` §2.5)
> does not apply: the recursion is the fold's induction. `size <out: Nat>` over `List` reaches the
> same conclusion (`Cons head rest -> Succ pred: rest`), but is blocked for an unrelated reason —
> the type checker's capture parse binds a recursive field at the carrier. A binder named `in` has
> no core spelling (`LC_RESERVED_WORDS`), so the emitter renames it (§12.63).

### 3.3 `Bool` — connectives

| Symbolic | Named | Signature               | Notes                                                         |
| -------- | ----- | ----------------------- | ------------------------------------------------------------- |
| `&`      | `and` | `<in: Self, out: Self>` | `associative`, `commutative`, `idempotent`, `identity: true`  |
| `\|`     | `or`  | `<in: Self, out: Self>` | `associative`, `commutative`, `idempotent`, `identity: false` |
| `not`    | —     | `<out: Self>`           | keyword; a suffix send — `b not`                              |

`not` is a keyword and a getter (no `in:`), so `x not` is a unary send — the only form. There is no
prefix `not x`.

### 3.4 `Int` — numeric helpers

Declared because the corpus's canonical examples depend on them and none was ever declared:

| Name  | Signature               | Corpus site                     |
| ----- | ----------------------- | ------------------------------- |
| `abs` | `<out: Self>`           | `overview.md` §3.1's `balanced` |
| `max` | `<in: Self, out: Self>` | `overview.md` §3.1's `depth`    |
| `min` | `<in: Self, out: Self>` | —                               |

`max` is load-bearing: it is the body of the canonical auxiliary-fold example (`depth`,
`overview.md` §3.1), so a prelude without it leaves the `aux` story unillustratable.

### 3.5 `List` — accessors and construction

| Name       | Signature       | Notes                                                          |
| ---------- | --------------- | -------------------------------------------------------------- |
| `isEmpty`  | `<out: Bool>`   | `Nil -> true`, `Cons _ _ -> false`                             |
| `notEmpty` | `<out: Bool>`   | `<out: Bool>`, a default over `isEmpty`: `self isEmpty not`    |
| `first`    | `<out: Any>`    | partial on `Nil` — a `demands:` clause, so **deferred** (§5.1) |
| `tail`     | `<out: Family>` | partial on `Nil`, same                                         |
| `size`     | `<out: Int>`    | `Nil -> 0`, `Cons _ rest -> 1 + rest`                          |
| `length`   | `<out: Int>`    | alias of `size`, pending §12.33                                |
| `,`        | `cons`          | `a , b` builds `Cons head: a rest: b`                          |

`first`/`tail`'s partiality is the reason they are listed but not yet runnable: their domain
restriction is a `demands:` contract, and contracts are contract elaboration (`elaboration.md` §5),
which is not in the surface implementation's first cut. A program that needs them today destructures
with a fold instead.

`length` duplicating `size` is finding §12.33's aliasing gap: the corpus uses both names for one
fold, and until operation aliasing is pinned the prelude would have to declare two folds with
duplicated bodies. Listing both, marked, is more honest than silently picking one and leaving half
the corpus misspelled.

## 4. Two rules that are not declarations

Both are language rules the prelude depends on. Neither is expressible as a declaration, and neither
is stated anywhere else.

### 4.1 `Bool`'s value spellings

`true` and `false` are `Bool`'s `True` and `False` variants, spelled lowercase, and are **not
keywords** (`surface-syntax.md` §1.6 lists them as special values). Because
`variantDecl ::= pascalIdent ( ident ":" typeExpr )*` requires a PascalCase head, the variants must
be declared `True`/`False` and the lowercase spellings supplied by the language. A fold's arm head
therefore names the variant (`True -> …`), and an expression uses the value spelling (`true`).

### 4.2 `Int` equality is structural, not numeric

`Int`'s values are tokens carrying text, and token equality compares **the type name and the text**
(`values.ts`'s `TokenVal.equals`). So `00` and `0` are distinct `Int` values, and `=` over `Int`
cannot be the token equality — it must be the numeric one, defined with `Int`'s other operations
(§5.5).

This is worth stating loudly rather than leaving to the definition, because it is the one place
where the prelude's _documented_ meaning and its _current_ implementation differ in a way that would
silently corrupt law sampling: the law engine enumerates `Int`'s language as ~120 strings at length
≤ 2 (`0`, `00`, `01`, … `-9`), each a distinct inhabitant under text equality, while the surface
type currently has two possible values (§6).

## 5. Not in the prelude

Each of these appears in the corpus as if it existed. Each is deferred **with an owner**, so the
deferral is a decision rather than an omission.

### 5.1 Contracts: `Result`, `Error`

`rescue:`/`ensures:` elaborate to `Result`-typed core terms (`elaboration.md` §5.3, sum of
success/failure), and `Error signal: "…"` constructs a failure. The type cannot be declared before
contract elaboration exists, and contract elaboration belongs to the contracts stage. **Owner:** the
contracts stage; it gates `first`/`tail`'s partiality (§3.5) and the quadratic example's `sqrt`
domain.

### 5.2 Protocols: `Eq`, `Ordered`, `Semigroup`, `Monoid`

The corpus declares protocols whose members carry `properties:` and whose conformers carry
`satisfies:`. Both are law-system features (`overview.md` §12.30, §6.3). **Owner:** the laws stage.
Until then, comparison operations are declared directly on their carriers (§3.1) rather than
required by a protocol.

The consequence to note: `<` `<=` `>` `>=`'s `Ordered` requirement in `elaboration.md` §2.4 is not
yet expressible, so the prelude declares them on `Int` outright. When `Ordered` lands they move
behind it.

### 5.3 `Float`, `sqrt`, `squared`

The quadratic example needs all three (`examples/quadratic.lapis`), and `sqrt`'s partiality is a
`demands:` contract (§5.1). `Float`'s language (`-?[0-9]*\.[0-9]+`) is disjoint from `Int`'s, so
adding it later costs no collision. **Owner:** the same contracts stage as §5.1, plus the numeric
discussion below.

### 5.4 `String` operations

`String` appears only as a field type (`Assign name: String`); no corpus example concatenates or
compares one. Declaring operations nothing uses would be prelude debt with no fixture to justify it.
**Owner:** whoever first needs one.

### 5.5 Machine numbers — the deferred discussion

`Int`'s operation **definitions** are not writable today, and this is the prelude's one real gap.
Verified against the implementation (`LCTypeCheck`/`LCEval` with `Int = -?[0-9]+` registered):

| Source              | Types as | Evaluates to                |
| ------------------- | -------- | --------------------------- |
| `match("-?[0-9]+")` | `Int`    | `TokenVal(Int, "-?[0-9]+")` |
| `Int` (bare atom)   | `Int`    | `TokenVal(Int, "Int")`      |
| `match("42")`       | —        | **no parse**                |
| `42`                | —        | **no parse**                |

Two facts follow, both load-bearing:

1. **A numeric literal is not spellable.** The bare-atom route fixes the token's text to the type
   name (`matchedToken(name, name)`), and `match("p")` requires `p` to be a _declared pattern
   source_ — `42` is a member of the language, not a source. There is no lexer that matches input
   text and stamps it onto a token: the grammar-based realization's "matched text" is the atom's
   convention, with the text chosen at evaluation time.
2. **`Int` has two inhabitants, not infinitely many.** The type is _documented_ as its pattern
   language and _implemented_ as one token per introduction route.

So `+`'s body cannot call anything: `OpSig.definition` is LC source and `LCEval.evalOp` parses and
applies it (`ops.ts`, `eval_grammar.ts`), with no host-function escape. Making `Int` arithmetic real
requires either a real lexer that stamps matched text (which then needs numeric equality, §4.2) or a
primitive-definition form in `Ω`. `semantics.md` sanctions the second as the `primitive` tier's
business, but the mechanism does not exist and choosing between them is a design decision, not a
documentation one.

**Owner:** its own issue, filed before `data` implementation begins — it is the one prelude item on
the first-runnable-program critical path.

## 6. Implementation status

What a program can use **today**, against `src/core/`:

| Prelude entry                           | Parses          | Type-checks | Evaluates       |
| --------------------------------------- | --------------- | ----------- | --------------- |
| `Any`, `Nothing`                        | yes             | yes         | yes             |
| Pattern types (`Char`, `String`, `Int`) | yes             | yes         | yes — as tokens |
| `Int` literals (`42`)                   | **no**          | —           | —               |
| `Int` operations (§3.1)                 | signatures only | —           | **no**          |
| Named types (`Bool`, `Nat`, `List`)     | yes — `data`    | yes         | yes             |
| `Nat`/`List` operations                 | yes             | **no**      | **no**          |

The core's `Token` is excluded from this table because it is not a prelude name (§2.1). The
surface's `atomType` rejects it too, as it rejects any name nothing declares — verified:
`P1 x:
Token` is `unknown-type` at resolution (`src/surface/resolve.ts`), so the `Token` gap this
document used to record is closed.

The last two rows are the point: the core calculus runs folds and unfolds over `DataType`s built
through the builder API, and `test/fixtures.ts` already constructs `Nat`, `Bool`, `Stack`, `Queue`,
and `Stream`. The surface `data` production now parses and builds those types, so source reaches the
core. What is missing is the rest of the operation pipeline — an operation's emitted definition does
not enter `Ω` unless it checks against its declared signature, and a recursive one is rejected when
it tries (`overview.md` §12.47 closed, §12.48 open, §12.50 open). A fold whose declaration and
definition agree now elaborates, checks, and installs; the recursive folds this document declares
(`add`, `size`) are blocked by `Ω`'s acyclicity and flat keying, not by elaboration. `add` is
blocked twice: §12.48, because its `in:` declares a second operand the emitter does not yet curry.

So the executable tier is `Nat` + `List` _in the core_: a fixture can declare them and fold over
them, with no new evaluation machinery. Source-level folds do not yet run. The documented tier is
`Int`, which needs §5.5.

## 7. What this document supersedes

Two tables claimed to enumerate the built-ins, and they disagreed:

| Document                 | Listed                             | Missing                                |
| ------------------------ | ---------------------------------- | -------------------------------------- |
| `surface-syntax.md` §1.3 | `Char` `String` `Nat` `Int` `Bool` | `Float`, `Any`/`Nothing`, `List`       |
| `overview.md` §2.3       | `Char` `String` `Nat` `Float`      | `Int`, `Bool`, `Any`/`Nothing`, `List` |

`Int` and `Float` each appeared in exactly one of them, and the corpus used both. Both are now
**derived** from §2 above; neither introduces a name this document does not define.

**Applied.** `surface-syntax.md` §1.3 now carries `Char`'s quoted pattern (`'.'`), `Int`'s single
pattern (`-?[0-9]+`), `Nat` as a named carrier, and a row for `List`; `overview.md` §2.3 lists `Int`
instead of `Nat` and points at this document as the definition site. The `Nat`-as-pattern row is
gone from both, per §2.4–§2.5. Neither table's omission of `Token` is a defect — it is not a prelude
name (§2.1).

## 8. Acceptance

- [ ] No document uses a type name absent from §2
- [ ] Every symbolic operator in any example traces to a §3 row
- [ ] `surface-syntax.md` §1.3 and `overview.md` §2.3 are derived from §2
- [ ] `_docs/index.md` lists this document in the theory table
- [ ] `overview.md` §12.18 (`Number`) and §12.23 (`Symbol`) are closed
- [ ] The machine-numbers decision is its own filed issue (§5.5), linked from here
- [ ] The surface checker rejects `Token` in type position, exactly as any other unknown name (§2.1;
      this closes the `Token` question in #116's acceptance)

## 9. See Also

- [`lc.md`](./lc.md) §2.1, §2.5 — the calculus's type grammar and `Token`'s status as its one
  non-μ/ν type.
- `src/surface/grammar.ts` — `atomType`, the resolution chain that admits the bounds, and the
  no-type-variables decision.
- [`surface-syntax.md`](./surface-syntax.md) §1.3 — the built-ins table derived from §2.
- [`elaboration.md`](./elaboration.md) §2.4 — how a symbolic operator elaborates to an operation
  application.
