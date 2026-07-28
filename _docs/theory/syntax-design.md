# Lapis Language Syntax Design

## Overview

This document sketches the surface syntax of the Lapis programming language.

The syntax is heavily influenced by **Self** and **Smalltalk**: message sends, keyword arguments,
blocks as the universal building block, uniform access, and `self` always in scope. Like Python,
significant indentation defines block scope — eliminating explicit delimiters around declaration
bodies and case tables, with newlines as statement separators. The departure from vanilla Smalltalk
is that Lapis replaces conditionals with **fold-based structural dispatch** and adds first-class
bialgebraic constructs — `data`, `behavior`, `relation`, and `query` — as the primary declaration
forms.

---

## Core Syntax Conventions

| Convention               | Description                                                                                                                            |
| ------------------------ | -------------------------------------------------------------------------------------------------------------------------------------- |
| Indentation              | Defines block extent; replaces `[...]` for multi-line declaration bodies and case tables                                               |
| Newline                  | Statement separator                                                                                                                    |
| `[params \| expr]`       | First-class block value (lambda) — used for callbacks, guards, and contract clauses                                                    |
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
        Red -> '#FF0000'
        Green -> '#00FF00'
        Blue -> '#0000FF'

    fold isWarm <out: Boolean>
        Red -> true
        Green -> false
        Blue -> false

Color Red toHex                       "=> '#FF0000'"
Color Red isWarm                      "=> true"
Color Red instanceof: Color           "=> true"
```

Each case arm uses `->` to separate the pattern from the body. Single-expression bodies appear on
the same line; multi-line bodies indent below.

---

### Structured Variants

```lapis
data Point
    Point2D x: Number y: Number
    Point3D x: Number y: Number z: Number

    fold distanceFromOrigin <out: Number>
        Point2D x y -> (x squared + y squared) sqrt
        Point3D x y z -> (x squared + y squared + z squared) sqrt

    fold asString <out: String>
        Point2D x y -> '(' , x printString , ', ' , y printString , ')'
        Point3D x y z -> '(' , x printString , ', ' , y printString , ', ' , z printString , ')'

p = Point Point2D x: 3 y: 4
p distanceFromOrigin      "=> 5.0"
p asString                "=> '(3, 4)'"
```

Each handler case binds the variant's fields as named parameters on the left-hand side of `->`, in
declaration order. `x` is the fold result for field `x`; for non-recursive fields that is the raw
stored value.

---

### Recursive ADT

`Family` is the implicit self-referential type. Fold results for recursive fields contain the
already-folded value.

```lapis
data Stack
    Empty
    Push value: Any rest: Family

    fold size <out: Number>
        Empty -> 0
        Push _ rest -> 1 + rest

    fold peek
        Empty -> nil
        Push value -> value

    fold toArray <out: Array>
        Empty -> {}
        Push value rest -> {value} , rest

    fold contains <in: target Object, out: Boolean>
        Empty -> false
        Push value rest -> value = target | (rest value: target)

    unfold FromArray <in: arr Array>
        Empty -> arr isEmpty | {}
        Push -> arr notEmpty | (value: arr first, rest: arr tail)

s = Stack Push value: 3 rest: (Stack Push value: 2 rest: Stack Empty)
s size            "=> 2"
s peek            "=> 3"
s toArray         "=> [3, 2]"
s contains: 2     "=> true"
```

---

### Paramorphism (`<para>`)

A paramorphism gives each handler both the folded result _and_ the raw original sub-node
(`old field`). This eliminates the need for `self`/`this`-based back-references in recursive
operations.

```lapis
data Stack
    Empty  Push value: Object rest: Family

    fold pop <para>
        Empty -> nil
        Push value rest -> value , old rest

"value    — the fold result for the 'value' field (raw Object)"
"rest     — the fold result for 'rest' (already folded)"
"old rest — the raw pre-fold 'rest' sub-node (the original Push instance)"

s pop    "=> [3, Push(value:2, rest:Empty)]"
```

---

### Course-of-Values Recursion — Histomorphism (`<histo>`)

```lapis
data Fib
    Zero One  Succ pred: Family

    fold fib <histo, out: Number>
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
    Nil  Cons head: Object tail: Family

    fold length <out: Number>
        Nil -> 0
        Cons _ tail -> 1 + tail

    fold average <aux: #length, out: Number>
        Nil -> 0
        Cons head tail -> head + tail / aux length
```

---

## ADT Extension (Subtyping)

```lapis
data ExtendedColor <: Color
    Yellow Orange Purple

    fold toHex
        Yellow -> '#FFFF00'
        Orange -> '#FFA500'
        Purple -> '#800080'

    fold isWarm
        Yellow -> true
        Orange -> true
        Purple -> false

ExtendedColor Yellow instanceof: Color          "=> true"
ExtendedColor Yellow instanceof: ExtendedColor  "=> true"
Color Red instanceof: ExtendedColor             "=> false"
```

Inherited variants and their handlers are resolved automatically. New variants require only the new
cases.

---

## Field Transformation (`map`)

```lapis
data Box
    Box contents: Object

    map double <typeParam: Number> [v | v * 2]

(Box Box contents: 5) double   "=> Box(contents: 10)"
```

---

## Merge / Deforestation

```lapis
data List
    Nil  Cons head: Object tail: Family

    fold sum <out: Number>
        Nil -> 0
        Cons head tail -> head + tail

    fold double <out: Family, properties: (distributive: #sum)>
        Nil -> Family Nil
        Cons head tail -> Family Cons head: head * 2 tail: tail

    "Horner pair — single traversal when 'distributive:sum' is detected"
    merge doubleSum <#double, #sum>
```

---

## Behavior (`behavior`) — Final Coalgebras

```lapis
behavior Stream
    head: <out: Object>
    tail: <out: Self>

    unfold From <in: n Number>
        head -> n
        tail -> n + 1

    unfold Constant <in: n Number>
        head -> n
        tail -> n

    fold take <in: n Number, out: Array>
        _ head tail ->
            n = 0
                ifTrue:  [{}]
                ifFalse: [{head} , (tail take: n - 1)]

    map map <in: transform Block, typeParam: Object>
        head -> transform value: head

nats = Stream From: 0
nats head                     "=> 0"
nats tail head                "=> 1"
nats take: 5                  "=> [0, 1, 2, 3, 4]"
(nats map: [n | n * 2]) take: 3   "=> [0, 2, 4]"
```

`Self` in the observer spec declares a continuation (lazy self-reference). Observations are memoized
— accessing `nats tail` twice returns the same instance.

---

## Protocols

```lapis
protocol Eq
    equals: <in: other Self, out: Boolean>
    notEquals: <in: other Self, out: Boolean>
        (self equals: other) not

protocol Ordered <: Eq
    compare: <in: other Self, out: Number>
    lessThan: <in: other Self, out: Boolean>
        (self compare: other) < 0
    greaterThan: <in: other Self, out: Boolean>
        (self compare: other) > 0
    between:and: <in: lo Self, hi Self, out: Boolean>
        (self lessThan: hi) & (self greaterThan: lo)

"Declare conformance"
data Num
    N value: Number

    satisfies: Ordered
    fold compare <in: other Self, out: Number>
        N value -> value - other value

(Num N: 3) lessThan: (Num N: 5)    "=> true"
(Num N: 3) instanceof: Ordered     "=> true"
```

Abstract methods declare a signature with `<spec>`; an indented body below provides the default
implementation. Conformance is declared with `satisfies:` and verified structurally.

---

## Algebraic Property Annotations

Properties are declared inside the fold spec block and enable the runtime to verify and exploit
algebraic laws automatically.

```lapis
data Num
    N value: Number

    fold add <in: other Self, out: Self, properties: (commutative, associative, identity: (Num N: 0))>
        N value -> Num N: value + other value

    fold multiply <in: other Self, out: Self, properties: (commutative, associative, identity: (Num N: 1), distributiveOver: #add)>
        N value -> Num N: value * other value
```

Declared properties trigger `LawError` at runtime when violated on random samples, and enable the
Horner-rule merge optimisation when `distributiveOver:` is present.

---

## Design by Contract

Contract clauses are keyword parts of the fold spec — the same block mechanism, no special language
forms.

```lapis
data Stack
    Empty  Push
        invariant: [self | self size >= 0]
        value: Object
        rest:  Family

    fold pop <out: Array>
        demands: [self | self size > 0]
        ensures: [self old result | result size = 2]
        rescue:  [self err args retry | retry value: 0]
        Empty -> (Error signal: 'Cannot pop empty stack')
        Push value rest -> value , old rest

    fold append <in: val Object, out: Family>
        demands: [self | val notNil]
        ensures: [self old result | result size = old size + 1]
        Empty -> Family Push value: val rest: Family Empty
        Push value rest -> Family Push value: value rest: (rest append: val)
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

    fold depth <out: Number>
        Direct -> 1
        Transitive hop rest -> hop + rest

base = {
    Ancestor Direct from: 'alice' to: 'bob'
    Ancestor Direct from: 'bob'   to: 'carol'
    Ancestor Direct from: 'carol' to: 'dave'
}

closed = Ancestor closure: base
Ancestor reachableFrom: closed from: {'alice'}    "=> {'bob', 'carol', 'dave'}"
Ancestor reachingTo: closed to: {'dave'}          "=> {'alice', 'bob', 'carol'}"
```

The join invariant for `Transitive` (`hop destination = rest origin`) is auto-generated from the
declared `origin` and `destination` projections.

---

## Query (`query`) — Cospan / Coalgebraic Search

```lapis
query PathFinder
    path:    Array
    solved:  Boolean
    done:    Boolean
    next:    Self
    output:  #path
    accept:  #solved
    done:    #done

    unfold Search <in: s (start: String, goal: String, graph: Object)>
        path -> {s start}
        solved -> s start = s goal
        done -> s exhausted
        next -> s advanceSearch

PathFinder explore: (start: 'a', goal: 'e', graph: myGraph)
PathFinder explore: (start: 'a', goal: 'e', graph: myGraph) options: (maxResults: 1)
```

`[output: #path]`, `[accept: #solved]`, `[done: #done]` are cospan projection declarations — they
name the observer fields that serve each coalgebraic role. `explore:` drives the greatest-fixpoint
coinductive loop.

---

## IO — Mealy Machine

```lapis
io Counter
    state: Number

    Increment state -> (state: state + 1, output: state + 1)
    Reset _ -> (state: 0, output: 0)
    Read state -> (state: state, output: state)

Counter run: (Increment, Increment, Increment, Read) from: (state: 0)
"=> [1, 2, 3, 3]"
```

IO programs are synchronous descriptions of state transitions; the runtime drives them
asynchronously.

---

## Syntax Summary

| Lapis construct                            | Description                                                                                                     |
| ------------------------------------------ | --------------------------------------------------------------------------------------------------------------- |
| `data` + indented body                     | Algebraic data type: variants and operations                                                                    |
| `behavior` + indented body                 | Final coalgebra: observers, unfolds, folds, maps, merges                                                        |
| `fold name <spec>` + indented cases        | Structural dispatch — catamorphism; replaces `ifTrue:ifFalse:`                                                  |
| `unfold Name <spec>` + indented generators | Corecursion constructor — anamorphism                                                                           |
| `merge name <#a, #b>`                      | Fold-fold fusion (single-traversal composition)                                                                 |
| `protocol` + indented body                 | Trait / interface with optional default method bodies                                                           |
| `relation` + indented body                 | Data ADT with allegory / Datalog operations                                                                     |
| `query` + indented body                    | Behavior with cospan structure / Prolog-style search                                                            |
| `io` + indented body                       | Mealy machine: state fields + PascalCase step handlers                                                          |
| `[params \| expr]`                         | First-class block value (lambda) — used for callbacks, guards, and contract clauses                             |
| `(key: val, ...)`                          | Inline spec or named-argument record                                                                            |
| `Variant fields -> body`                   | Pattern case: `->` separates pattern from body; single-expression bodies inline, multi-line bodies indent below |
| `in: paramName Type`                       | Names the `in:` argument for use across all case arms of a fold or unfold                                       |
| `old fieldName`                            | Raw pre-fold sub-node (paramorphism)                                                                            |
| `prev fieldName`                           | Previous fold result, one step back (histomorphism)                                                             |
| `aux foldName`                             | Auxiliary fold result (zygomorphism)                                                                            |
| `self`                                     | Current instance, always in scope                                                                               |
| `Family` / `Self`                          | Recursive self-reference (data / behavior)                                                                      |
