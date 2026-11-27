# Lapis Language Syntax Design

## Overview

This document sketches the surface syntax of the Lapis programming language.

The syntax is heavily influenced by **Self** and **Smalltalk**: operation-application forms, keyword
arguments, blocks as the universal building block, uniform access, and `self` always in scope. Like
Python, significant indentation defines block scope — eliminating explicit delimiters around
declaration bodies and case tables, with newlines as statement separators. The departure from
vanilla Smalltalk is that Lapis replaces conditionals with **fold-based structural dispatch** and
adds first-class bialgebraic constructs — `data`, `behavior`, `relation`, and `query` — as the
primary declaration forms.

---

## Core Syntax Conventions

| Convention               | Description                                                                                                                            |
| ------------------------ | -------------------------------------------------------------------------------------------------------------------------------------- |
| Indentation              | Defines block extent; replaces `[...]` for multi-line declaration bodies and case tables                                               |
| Newline                  | Statement separator                                                                                                                    |
| `double` / `Int double`  | Function value — an operation reference, optionally type-qualified; there is no block literal                                          |
| `Variant fields -> body` | Pattern case in fold/unfold: `->` separates the pattern from the body; single-expression bodies inline, multi-line bodies indent below |
| `(key: val, ...)`        | Inline spec / named-argument record                                                                                                    |
| Keyword message          | Multi-argument send: `size: 3` or `contains: 2`                                                                                        |
| Unary message            | Zero or single argument: `instance size`, `Color Red toHex`                                                                            |
| Uniform access           | No call/getter distinction — `size`, `toHex`, `head` are all unary messages                                                            |
| `self`                   | Always in scope; the current object instance                                                                                           |
| `Family`                 | Self-referential type placeholder in `data` blocks                                                                                     |
| `Self`                   | Coalgebraic self-reference in `behavior` blocks                                                                                        |
| Last expression          | Implicit result — no explicit `return` keyword                                                                                         |
| PascalCase               | Variant names (used as case keys in fold/unfold tables)                                                                                |
| camelCase                | Operations, spec clauses, and field names                                                                                              |

---

## Algebraic Data Types (`data`)

### Simple Enumeration

```lapis
data Color
    Red Green Blue

    fold toHex <out: String>
        Red -> "#FF0000"
        Green -> "#00FF00"
        Blue -> "#0000FF"

    fold isWarm <out: Bool>
        Red -> True
        Green -> False
        Blue -> False

Color Red toHex                       /* "#FF0000" */
Color Red isWarm                      /* True */
```

Each case arm uses `->` to separate the pattern from the body. Single-expression bodies appear on
the same line; multi-line bodies indent below.

---

### Structured Variants

```lapis
data Point
    Point2D x: Int y: Int
    Point3D x: Int y: Int z: Int

    fold distanceFromOrigin <out: Float>
        Point2D x y -> (x squared + y squared) sqrt
        Point3D x y z -> (x squared + y squared + z squared) sqrt

    fold asString <out: String>
        Point2D x y -> "(" , x printString , ", " , y printString , ")"
        Point3D x y z -> "(" , x printString , ", " , y printString , ", " , z printString , ")"

Point Point2D x: 3 y: 4
    distanceFromOrigin      /* 5.0 */
    asString                /* "(3, 4)" */
```

Each handler case binds the variant's fields on the left-hand side of `->`, in declaration order,
and **each binding is written with its field's declared name**: `Point3D x y z` is the only spelling
for a `Point3D x: Int y: Int z: Int`, and `Point3D p q r` is rejected. A case arm is a
pattern-matching form, so it reads as a destructuring of the declared variant rather than as a fresh
set of bindings that happens to have the right arity; `_` discards a field without naming it. For
non-recursive fields the binding is the raw stored value. See `surface-grammar.md` §4.1.

---

### Recursive ADT

`Family` is the implicit self-referential type. Fold results for recursive fields contain the
already-folded value.

```lapis
data Stack
    Empty
    Push value: Any rest: Family

    fold size <out: Int>
        Empty -> 0
        Push _ rest -> 1 + rest

    fold peek
        Empty -> Empty
        Push value -> value

    fold toArray <out: List>
        Empty -> Nil
        Push value rest -> {value} , rest

    fold contains <in: Any, out: Bool>
        Empty in -> False
        Push value rest in -> value = in | (rest contains: in)

    unfold FromArray <in: List>
        Empty arr -> arr isEmpty | Nil
        Push arr -> arr notEmpty | value: arr first rest: arr tail

Stack Push value: 3 rest: (Stack Push value: 2 rest: Stack Empty)
    /* then: size 2, peek 3, toArray [3, 2], contains: 2 */
```

---

### Paramorphism (`<para>`)

A paramorphism gives each handler both the folded result _and_ the raw original sub-node
(`old field`). This eliminates the need for `self`/`this`-based back-references in recursive
operations.

```lapis
data Stack
    Empty  Push value: Any rest: Family

    fold pop <para>
        Empty -> Empty
        Push value rest -> value , old rest

/* value    — the fold result for the "value" field (raw Any) */
/* rest     — the fold result for "rest" (already folded) */
/* old rest — the raw pre-fold "rest" sub-node (the original Push instance) */

s pop    /* [3, Push(value:2, rest:Empty)] */
```

---

### Course-of-Values Recursion — Histomorphism (`<histo>`)

```lapis
data Fib
    Zero One  Succ pred: Family

    fold fib <histo, out: Int>
        Zero -> 0
        One -> 1
        Succ pred -> pred + prev pred
```

In `<histo>` folds, fields bind the current fold result; `prev fieldName` steps back one level in
the course of values.

---

### Zygomorphism — Auxiliary Fold (`<aux: ...>`)

```lapis
data List
    Nil  Cons head: Any tail: Family

    fold length <out: Int>
        Nil -> 0
        Cons _ tail -> 1 + tail

    fold average <aux: #length, out: Int>
        Nil -> 0
        Cons head tail -> head + tail / aux length
```

---

## ADT Extension (Subtyping)

```lapis
data ExtendedColor <: Color
    Yellow Orange Purple

    fold toHex
        Yellow -> "#FFFF00"
        Orange -> "#FFA500"
        Purple -> "#800080"

    fold isWarm
        Yellow -> True
        Orange -> True
        Purple -> False

ExtendedColor Yellow toHex            /* "#FFFF00" */
Color Red toHex                       /* "#FF0000" — inherited */
```

Inherited variants and their handlers are resolved automatically. New variants require only the new
cases.

---

## Field Transformation (`map`)

```lapis
data Box
    Box contents: Any

    map double <in: Int>
        Box contents -> Family Box contents: (contents * 2)

(Box Box contents: 5) double   /* Box(contents: 10) */
```

---

## Merge / Deforestation

```lapis
data List
    Nil  Cons head: Any tail: Family

    fold sum <out: Int>
        Nil -> 0
        Cons head tail -> head + tail

    fold double <out: Family, properties: (distributive: #sum)>
        Nil -> Family Nil
        Cons head tail -> Family Cons head: head * 2 tail: tail

    /* Horner pair — single traversal when "distributive: #sum" is detected */
    merge doubleSum <#double, #sum>
```

---

## Behavior (`behavior`) — Final Coalgebras

```lapis
behavior Stream
    head: <out: Any>
    tail: <out: Self>

    unfold From <in: Int>
        head -> self
        tail -> self + 1

    unfold Constant <in: Int>
        head -> self
        tail -> self

    map map
        head x -> (x * 2)

(Stream From: 0) head                      /* 0 */
(Stream From: 0) tail head                /* 1 */
((Stream From: 0) map: double) head       /* 0 */
```

`Self` in the observer spec declares a continuation (lazy self-reference). Observations are memoized
— accessing `(Stream From: 0) tail` twice returns the same instance.

There is no top-level binding form, so the stream is constructed where it is used rather than named.
`double` is an operation reference — the surface's only function value (a block literal would have
been an anonymous binder).

### Taking a prefix: a decision on a seed, not on a variant

Bounding a stream to `n` elements is not a decision any `Stream` variant can express — `Stream` is
codata, so it has no variants at all. It is a decision on a **numeric seed**, and that places it in
an `unfold`, whose arms decide by `guard | payload` (`src/surface/grammar.ts`, `unfoldArm`). The
seed carries both of the values the decision needs, so no product type and no conditional is
involved:

```lapis
data Slice
    Slice remaining: Int source: Stream

/* `List` is the prelude's list; its variants are `Nil` and `Cons`. */
data List
    Nil
    Cons head: Any rest: Family
        Cons slice ->
            slice remaining > 0
                | head: slice source head
                  rest: Slice remaining: slice remaining - 1 source: slice source tail

List Take: (Slice remaining: 5 source: (Stream From: 0))    /* [0, 1, 2, 3, 4] */
```

The unfold is declared inside `List` because an unfold produces the type that encloses it — the
result type is the declaration site, never a parameter. Reading the arms as a decision table: the
base arm produces `Nil` when the seed's budget is spent, and the step arm produces a `Cons` whose
rest is the next seed (the budget one smaller, the source one observation further along). That is
the `IntList Range` shape from `overview.md` §3.2, with a two-field seed.

This is why branching needs no conditional: **fold arms dispatch on a variant, unfold arms decide on
a seed.** A decision that is neither — one computed over a value with no discriminating variants —
is a decision on a seed, and belongs here.

---

## Protocols

```lapis
protocol Eq
    fold equals <in: Self, out: Bool>
    fold notEquals <in: Self, out: Bool>
        (self equals: in) not

protocol Ordered <: Eq
    fold compare <in: Self, out: Int>
    fold lessThan <in: Self, out: Bool>
        (self compare: in) < 0
    fold greaterThan <in: Self, out: Bool>
        (self compare: in) > 0

/* Declare conformance */
data Num
    N value: Int

    satisfies: Ordered
    fold equals <in: Self, out: Bool>
        N value -> value = in value
    fold compare <in: Self, out: Int>
        N value -> value - in value

(Num N: 3) lessThan: (Num N: 5)    /* true */
```

A member is a signature — `fold`, `unfold`, `map`, `merge`, or `scan`, with its type stated (a spec
record, or the `#name` form for `merge`/`scan`) — and an indented body below it supplies a
**default** implementation. Conformance is declared with `satisfies:` and verified structurally; a
member neither declared by the type nor carrying a default is a conformance error.

The default body is an expression, not an arm list: a protocol cannot see its conformers' variants,
so a default can only compose operations over `self`. Those bodies may read `self` and, when the
member declares `in:`, `in` — the two names the machinery supplies. `notEquals` above derives from
`equals`, and `lessThan`/`greaterThan` derive from `compare`, which is the whole point of a default:
an operation a conformer gets for free from one it declared.

`Unfold` members declare a constructor each conformer must supply, so they take no default;
`merge`/`scan` are fusion directives and take none either.

Conformance is a typing fact (`Num <: Ordered`), not a value-level query, so there is no
`instanceof`-style operation in the surface. A program that wants to ask declares its own fold.

### Algebraic protocols: a monoid

A protocol can require a constructor as well as folds, which is what makes the algebraic hierarchy
expressible. `Monoid` extends `Semigroup` and adds an identity _value_ — an `unfold`, because it
produces its type rather than eliminating it:

```lapis
protocol Semigroup
    fold combine <in: Self, out: Self, properties: (associative)>

protocol Monoid <: Semigroup
    unfold Identity
    fold combine <in: Self, out: Self, properties: (associative, identity: Identity)>

data Nat
    Zero
    Succ pred: Family

    satisfies: Monoid
    unfold Identity
        Zero -> True
    fold combine <in: Self, out: Self>
        Zero -> in
        Succ pred -> Succ pred: pred
```

Two things are load-bearing here.

**`Monoid` re-declares `combine`.** It inherits `Semigroup`'s member wholesale, so re-declaring
looks redundant — but a law is attached to an operation, and the child needs `identity` added.
Properties union through inheritance (`elaboration.md` §6.2), so the effective set is
`(associative, identity: Identity)` and the repeated `associative` is only for readability. A child
can add a property but never remove one.

**`Identity` is a seedless unfold.** It takes no `in:`, so its arms carry no bindings: the arm head
is the variant the conformer produces and the guard alone decides. That is a constant constructor,
which is exactly what an identity element is — one value, no recursion input, no default body
possible, because a protocol cannot name a constructor it cannot see.

---

## Algebraic Property Annotations

Properties are declared inside the fold spec block and enable the runtime to verify and exploit
algebraic laws automatically.

```lapis
data Num
    N value: Int

    fold add <in: Self, out: Self, properties: (commutative, associative, identity: (Num N: 0))>
        N value -> Num N: value + in value

    fold multiply <in: Self, out: Self, properties: (commutative, associative, identity: (Num N: 1), distributive: #add)>
        N value -> Num N: value * in value
```

Declared properties trigger `LawError` at runtime when violated on random samples, and enable the
Horner-rule merge optimisation when `distributive:` is present.

---

## Design by Contract

Contract clauses are keyword parts of the fold spec — a binding head and an indented body, the same
body form as a case arm, no special language forms.

```lapis
data Stack
    Empty  Push
        invariant: self | self size >= 0
        value: Any
        rest:  Family

    fold pop <out: List>
        demands: self | self size > 0
        ensures: self old result | result size = 2
        rescue:  self err args retry | retry value: 0
        Empty -> (Error signal: "Cannot pop empty stack")
        Push value rest -> value , old rest

    fold append <in: Any, out: Family>
        demands: self | in notNil
        ensures: self old result | result size = old size + 1
        Empty in -> Family Push value: in rest: Family Empty
        Push value rest in -> Family Push value: value rest: (rest append: in)
```

| Clause       | Meaning                                            |
| ------------ | -------------------------------------------------- |
| `invariant:` | Checked on every mutation; declared per-variant    |
| `demands:`   | Precondition; checked before fold executes         |
| `ensures:`   | Postcondition; `old` is the pre-call snapshot      |
| `rescue:`    | Structured recovery; `retry` re-runs with new args |

---

## Relation (`relation`) — Allegory / Span

```lapis
relation Ancestor
    Direct from: String to: String
    Transitive hop: Family rest: Family

    fold origin <out: String>
        Direct from _ -> from
        Transitive hop _ -> hop

    fold destination <out: String>
        Direct _ to -> to
        Transitive _ rest -> rest

    fold depth <out: Int>
        Direct -> 1
        Transitive hop rest -> hop + rest

base = {
    Ancestor Direct from: "alice" to: "bob"
    Ancestor Direct from: "bob"   to: "carol"
    Ancestor Direct from: "carol" to: "dave"
}

closed = Ancestor closure: base
Ancestor reachableFrom: closed from: {"alice"}    /* {"bob", "carol", "dave"} */
Ancestor reachingTo: closed to: {"dave"}          /* {"alice", "bob", "carol"} */
```

The join invariant for `Transitive` (`hop destination = rest origin`) is auto-generated from the
declared `origin` and `destination` projections.

---

## Query (`query`) — Cospan / Coalgebraic Search

```lapis
query PathFinder
    path:    List
    solved:  Bool
    done:    Bool
    next:    Self
    output:  #path
    accept:  #solved
    done:    #done

    unfold Search <in: SearchSeed>
        path -> {s start}
        solved -> s start = s goal
        done -> s exhausted
        next -> s advanceSearch

PathFinder explore: (start: "a", goal: "e", graph: myGraph)
PathFinder explore: (start: "a", goal: "e", graph: myGraph) options: (maxResults: 1)
```

The seed is a declared type, not an inline record shape — the surface has no record type production
(`src/surface/grammar.ts`), and a multi-value seed is spelled the same way `Slice` is:

```lapis
data SearchSeed
    SearchSeed start: String goal: String graph: Any
```

`[output: #path]`, `[accept: #solved]`, `[done: #done]` are cospan projection declarations — they
name the observer fields that serve each coalgebraic role. `explore:` drives the greatest-fixpoint
coinductive loop.

---

## IO — Mealy Machine

```lapis
io Counter
    state: Int

    Increment state -> (state: state + 1, output: state + 1)
    Reset _ -> (state: 0, output: 0)
    Read state -> (state: state, output: state)

Counter run: (Increment, Increment, Increment, Read) from: (state: 0)
/* [1, 2, 3, 3] */
```

IO programs are synchronous descriptions of state transitions; the runtime drives them
asynchronously.

---

## Syntax Summary

| Lapis construct                            | Description                                                                                                                                                                               |
| ------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `data` + indented body                     | Algebraic data type: variants and operations                                                                                                                                              |
| `behavior` + indented body                 | Final coalgebra: observers, unfolds, folds, maps, merges                                                                                                                                  |
| `fold name <spec>` + indented cases        | Structural dispatch — catamorphism; arms dispatch on variants, so the arm keying is the decision                                                                                          |
| `unfold Name <spec>` + indented generators | Corecursion constructor — anamorphism; arms decide on a seed by `guard \| payload`                                                                                                        |
| `merge name <#a, #b>`                      | Fold-fold fusion (single-traversal composition)                                                                                                                                           |
| `protocol` + indented body                 | Trait / interface with optional default method bodies                                                                                                                                     |
| `relation` + indented body                 | Data ADT with allegory / Datalog operations                                                                                                                                               |
| `query` + indented body                    | Behavior with cospan structure / Prolog-style search                                                                                                                                      |
| `io` + indented body                       | Mealy machine: state fields + PascalCase step handlers                                                                                                                                    |
| `double` / `Int double`                    | Function value — an operation reference, optionally type-qualified; no block literal                                                                                                      |
| `(key: val, ...)`                          | Inline spec or named-argument record                                                                                                                                                      |
| `Variant fields -> body`                   | Pattern case: `->` separates pattern from body; single-expression bodies inline, multi-line bodies indent below                                                                           |
| `in: Type`                                 | Declares the fold's one extra argument (the carrier is always the first). The arm names it with a binding after the variant's fields; the name is a curried lambda, not a handler binding |
| `old fieldName`                            | Raw pre-fold sub-node (paramorphism)                                                                                                                                                      |
| `prev fieldName`                           | Previous fold result, one step back (histomorphism)                                                                                                                                       |
| `aux foldName`                             | Auxiliary fold result (zygomorphism)                                                                                                                                                      |
| `self`                                     | Current instance, always in scope                                                                                                                                                         |
| `Family` / `Self`                          | Recursive self-reference (data / behavior)                                                                                                                                                |
