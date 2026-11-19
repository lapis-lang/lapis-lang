# Lapis Elaboration: Surface → Core

> **Status:** Draft v0.1. This document defines the elaboration (desugaring) from the Lapis surface
> language to the Lapis Core (LC) calculus defined in [`lc.md`](./lc.md). Every surface construct
> maps to a core term. The surface is rich (six declaration forms, specs, contracts,
> recursion-scheme modifiers); the core is small (μ/ν types, fold, unfold, observation, lambda,
> bounded polymorphism).

## 1. Elaboration Principles

### 1.1 Surface vs Core

The **surface language** is what the programmer writes: `data`, `behavior`, `protocol`, `relation`,
`query`, `io`, `fold`, `unfold`, `map`, `merge`, `scan`, specs, contracts, `properties`, message
sends, blocks, case arms.

The **core calculus (LC)** is what the compiler type-checks and evaluates: μ-types, ν-types, variant
construction, fold, observation, unfold, cofold, lambda, application, bounded type
abstraction/application, let, subsumption.

Elaboration is a **syntax-directed translation** `ℰ : SurfaceAST → CoreTerm` that:

1. Resolves names (variant references, operation names, protocol names).
2. Inserts coercions (subsumption via `T-Sub`).
3. Desugars sugar (relation → data, query → behavior, io → Mealy record).
4. Elaborates contracts to `Result`-typed terms.
5. Elaborates recursion-scheme modifiers to fold/unfold combinations.

### 1.2 Elaboration is Type-Preserving

**Goal:** If the surface program type-checks, the elaborated core program type-checks, and the types
are preserved:

```
If  Γ ⊢_surface s : σ   then   ℰ(Γ) ⊢_core ℰ(s) : σ
```

This is the **type-preservation theorem** for elaboration. It ensures that the type checker only
needs to handle the core calculus, not the full surface language.

### 1.3 Elaboration is Semantics-Preserving

**Goal:** The meaning of the surface program equals the meaning of the elaborated core program:

```
〚s〛_surface = 〚ℰ(s)〛_core
```

This is the **adequacy theorem** for elaboration. It ensures that the evaluator only needs to handle
the core calculus.

## 2. Expression Elaboration

### 2.1 Literals and References

Base types are eliminated (see [`design-decisions.md`](../design-decisions.md) §"No base types").
Literals are pattern-matched or named constructors of `data` types.

| Surface                             | Core                                 | Notes                                                                                                                                                                                            |
| ----------------------------------- | ------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `'a'` (single char, spelled quoted) | `match("a") : Char`                  | Pattern-matched constructor of `Char = μ α. .` (any single character); the surface Char value is single-quoted — `surface-syntax.md` §1.4 — and the core form's payload is the matched character |
| `42`                                | `match("42") : Int`                  | Pattern-matched constructor of `Int = μ α. -?[0-9]+`                                                                                                                                             |
| `-3`                                | `match("-3") : Int`                  | Pattern-matched constructor of `Int = μ α. (-[0-9]+ \| [0-9]+)`                                                                                                                                  |
| `"hello"`                           | `match("hello") : String`            | Pattern-matched constructor of `String = μ α. "<Char>*"` (type reference)                                                                                                                        |
| `nil`                               | `nil`                                | A built-in value of type `Any` (or `Nothing` in a strict reading)                                                                                                                                |
| `true`                              | `True`                               | Named variant construction of `Bool = μ α. (True \| False)`                                                                                                                                      |
| `false`                             | `False`                              | Named variant construction of `Bool`                                                                                                                                                             |
| `self`                              | `self`                               | The current instance variable (in scope in fold/unfold handlers)                                                                                                                                 |
| `Family`                            | `α` (the μ-bound type variable)      | Resolved to the recursive self-reference                                                                                                                                                         |
| `Self`                              | `α` (the ν-bound type variable)      | Resolved to the corecursive self-reference                                                                                                                                                       |
| `old f`                             | see §4.1 (paramorphism elaboration)  | Not a direct core term                                                                                                                                                                           |
| `prev f`                            | see §4.2 (histomorphism elaboration) | Not a direct core term                                                                                                                                                                           |
| `aux fold`                          | see §4.3 (zygomorphism elaboration)  | Not a direct core term                                                                                                                                                                           |

**Pattern-matched construction:** When the lexer matches input against a pattern `pₖ` of type `T`,
the matched text (a `Token`) is introduced as a value of type `T` via T-Pattern. The `Token` is
carried as the implicit `match` field, accessible in fold handlers.

### 2.2 Variables and Identifiers

| Surface               | Core    | Notes                                                 |
| --------------------- | ------- | ----------------------------------------------------- |
| `x` (camelCase ident) | `x`     | Variable reference; resolved by name resolution pass  |
| `Color` (PascalCase)  | `Color` | Type or variant reference; resolved to a type binding |

### 2.3 Function Values

There is no block literal. A function value is an operation reference, and its type is the
operation's curried signature (`FunType` chain, `ops.ts`'s `OpSig.signature`). That type is read
from `Ω`, not written: `typeExpr` is `atomType` (`surface-grammar.md` §3.8), so a declaration cannot
state `σ -> τ` and cannot declare a parameter, field, or result of function type. Since nothing in
the surface binds a name at top level or in a body (`overview.md` §12.6), an unbound camelCase
`ident` in `primary` position can only denote an operation, so no new resolution rule is needed.

| Surface      | Core                            | Notes                                                  |
| ------------ | ------------------------------- | ------------------------------------------------------ |
| `double`     | the operation's definition term | Function value; resolved through `Ω` when unbound in ρ |
| `Int double` | the same                        | Qualified: disambiguates a colliding name (§2.5)       |

A function value has type `σ → τ` — the operation's curried signature (`ops.ts`'s
`OpSig.signature`). There is no separate function-value type in the prelude: a function value is the
`FunType` it declares, and an operation reference is not an instance of some wrapper type — it is
the operation's definition, which _has_ type `σ → τ` directly. The core applies it by juxtaposition;
the surface does not, because no surface position can be of function type.

**Contract clauses are not function values.** `demands:`, `ensures:`, `invariant:`, and `rescue:`
take an indented body (`surface-grammar.md` §5.1) whose expression the fold machinery forces at its
own chosen moment. No thunk value is created, so no function value appears.

**Partial application** (a section: `(NatList append 3)`) has no surface spelling yet — see
`overview.md` §12.27 and [#109](https://github.com/lapis-lang/lapis-lang/issues/109).
Under-application at a normal expression site is an arity error, not a silently produced function.

### 2.4 Binary Operators

Binary operators are **operation applications** on the receiver. Each operator maps to a fold on the
appropriate type. All binary operators have **uniform precedence** (left-to-right, no hierarchy —
see [`surface-syntax.md`](./surface-syntax.md) §2.1):

| Surface  | Core                   | Notes                                                             |
| -------- | ---------------------- | ----------------------------------------------------------------- |
| `a + b`  | `add(ℰ(a), ℰ(b))`      | `add` is a fold on `Int`/`Complex`                                |
| `a - b`  | `sub(ℰ(a), ℰ(b))`      | Similarly                                                         |
| `a * b`  | `mul(ℰ(a), ℰ(b))`      |                                                                   |
| `a / b`  | `div(ℰ(a), ℰ(b))`      |                                                                   |
| `a = b`  | `equals(ℰ(a), ℰ(b))`   | `equals` is a fold (structural for data, bisimulation for codata) |
| `a < b`  | `lessThan(ℰ(a), ℰ(b))` | Requires `Ordered` protocol                                       |
| `a \| b` | `or(ℰ(a), ℰ(b))`       | Fold on `Bool`                                                    |
| `a & b`  | `and(ℰ(a), ℰ(b))`      | Fold on `Bool`                                                    |
| `a , b`  | `cons(ℰ(a), ℰ(b))`     | List/structure cons; a built-in or fold                           |

**Key principle:** There are no primitive operators in the core. Every operator is an operation
application that resolves to a fold on the appropriate type. For pattern-matched types (`Int`,
`String`), these are folds with pattern- matched handlers that transform the `Token`; for user
types, they are user-declared folds.

**Symbolic operation names:** Operators can be symbolic (`+`, `*`, `<`, `<=`) or named (`add`,
`mul`, `lessThan`). Symbolic operators are recognized by longest match among declared operators.
Position discriminates: symbolic prefix (no whitespace) = pattern-matched data; symbolic infix
(between tokens) = operation.

### 2.5 Unary and Keyword Applications

| Surface         | Core                                     | Notes                                   |
| --------------- | ---------------------------------------- | --------------------------------------- |
| `recv selector` | `fold_T recv {Cᵢ → hᵢ}` (applied)        | Unary call = parameterless fold access  |
| `recv key: arg` | `fold_T recv {Cᵢ → hᵢ}` (applied to arg) | Keyword call = parameterized fold       |
| `- expr`        | `negate(ℰ(expr))`                        | Prefix negation = operation application |
| `not expr`      | `not(ℰ(expr))`                           | Negation = fold on `Bool`               |

**A selector has one keyword part at most.** A fold takes the receiver and at most one `in:` value,
so a two-part selector (`recv k1: a k2: b`) can name no declared operation — it is an arity error,
not a differently-grouped call. The surface grammar collects keyword parts greedily
([`surface-grammar.md`](./surface-grammar.md) §3.3), so the parse is unambiguous; the arity rule is
what makes the two-part case unsatisfiable. A multi-argument operation is spelled by currying
through the result, not by a longer selector.

**Uniform access principle:** A unary call `recv selector` where `selector` is a parameterless fold
is _not_ a function call — it is a property access (the fold is applied with no arguments, producing
a value). A keyword call `recv key: arg` is a method call (the fold takes an argument). The
distinction is made by the fold's spec: if it has no `in` parameter, it's a getter; if it has `in`,
it's a method.

**The elimination form is fixed by the receiver's kind.** `fold_T` is data's elimination; the codata
dual is **observation** (`E-Obs`); a function type's elimination is **application**, and its
selector is the fixed keyword `value:`.

| Surface | Core  | Notes                                                                                             |
| ------- | ----- | ------------------------------------------------------------------------------------------------- |
| `f`     | `f`   | The function value itself                                                                         |
| `f x`   | `f x` | Core application — reached by elaboration, not by a surface send (§3.6.1 of `surface-grammar.md`) |

**The surface has no receiver of function type.** A surface type is `atomType` (`surface-grammar.md`
§3.8) — a name, never a shape — so no declaration can state `σ -> τ` and no expression can acquire
one. An operation reference still _has_ a function type (`Ω`'s declared `FunType` chain), and the
core applies it by juxtaposition; but there is no surface position that receives a function value,
so `value:` names no surface declaration. Application is a core rule, derived from the elimination
principle, not a surface form.

**Parentheses re-open the chain.** A parenthesised expression is a `primary`, so `(f k: x) k: y` is
two sends. The core's application is single-argument (a curried `FunType` chain), so a
multi-argument function value is curried by nesting — the same shape `Observer`'s single type slot
supports.

### 2.6 Arrays and Records

| Surface            | Core                                      | Notes                                     |
| ------------------ | ----------------------------------------- | ----------------------------------------- |
| `{}`               | `Nil` (empty array)                       | Or a built-in empty-array value           |
| `{a, b, c}`        | `Cons(ℰ(a), Cons(ℰ(b), Cons(ℰ(c), Nil)))` | List literal = nested cons                |
| `(k1: v1, k2: v2)` | `{k1 = ℰ(v1), k2 = ℰ(v2)}`                | Record = product type (built-in or sugar) |

Arrays are elaborated to a built-in `List` type (a μ-type with `Nil` and `Cons` variants). Records
are elaborated to built-in product types.

### 2.7 Variant Construction

| Surface                       | Core                       | Notes                                                     |
| ----------------------------- | -------------------------- | --------------------------------------------------------- |
| `Color Red`                   | `Red` (variant of `Color`) | Simple variant (no fields)                                |
| `Point Point2D x: 3 y: 4`     | `Point2D(3, 4)`            | Named-argument construction → positional                  |
| `Stack Push value: 3 rest: s` | `Push(3, s)`               | Named-argument → positional (fields in declaration order) |

Variant construction is `Cᵢ(t₁, ..., tₙ)` in the core. The surface syntax
`Type Variant field1: val1 field2: val2` is desugared to positional construction in declaration
order. Named arguments are resolved by matching field names to the variant's declared fields.

## 3. Declaration Elaboration

### 3.1 `data` → μ-type + fold/unfold declarations

A surface `data` declaration elaborates to:

1. A **μ-type definition**: `T = μ α. Σᵢ Cᵢ(Fᵢ(α))` where `Fᵢ` encodes the field types and `α` is
   the recursive self-reference (`Family`).
2. **Fold declarations**: each `fold opName <spec> { arms }` becomes a core fold:
   `fold_T e {Cᵢ(xⱼ) → ℰ(tᵢ)}`.
3. **Unfold declarations**: each `unfold ConstructorName <spec> { arms }` becomes a core unfold:
   `unfold_T s {oⱼ → ℰ(gⱼ)}`.
4. **Map declarations**: see §4.4.
5. **Merge declarations**: see §4.5.
6. **Satisfies clause**: see §3.5.

**Example:**

```lapis
data Stack
    Empty
    Push value: Any rest: Family
    fold size <out: Int>
        Empty -> 0
        Push _ rest -> 1 + rest
```

Elaborates to:

```
Stack = μ α. (Empty | Push(Any, α))

size = fold_Stack e {
    Empty() → 0,
    Push(_, rest) → 1 + rest
}
```

Where `rest` in the `Push` handler is the already-folded result (of type `Int`), because `Family`
positions are recursively folded.

**A seedless unfold is a constant constructor.** When an unfold's spec record omits `in:`, it takes
no seed, so its arms carry no bindings and the guard alone decides which arm produces:

```lapis
unfold Identity
    Zero -> true
```

Elaborates to an unfold whose generator takes no argument — `Identity = unfold_T { Zero → true }` —
and whose evaluation yields the nullary variant when its guard holds. Because there is no seed,
there is no recursion input either: a seedless unfold produces one value, and a recursive field in
its payload has no next seed to carry. That is why the shape is confined to constant constructors (a
monoid's identity, a lattice's top) and why a protocol requires one from each conformer rather than
defaulting it — the protocol cannot see the variants the arm would name.

### 3.2 `behavior` → ν-type + unfold/fold declarations

A surface `behavior` declaration elaborates to:

1. A **ν-type definition**: `T = ν α. Πⱼ oⱼ(Gⱼ(α))` where `Gⱼ` encodes the observer types and `α` is
   the corecursive self-reference (`Self`).
2. **Unfold declarations**: each `unfold ConstructorName <spec> { arms }` becomes a core unfold.
3. **Fold declarations**: each `fold opName <spec> { _ → body }` becomes a core cofold (codata
   elimination with a single handler for the observation product).
4. **Map/merge**: as in data.

**Example:**

```lapis
behavior Stream
    head: <out: Int>
    tail: <out: Self>
    unfold From <in: Int>
        head n -> n
        tail n -> n + 1
```

Elaborates to:

```
Stream = ν α. (head: Int, tail: α)

From = unfold_Stream s {
    head → λn. n,
    tail → λn. n + 1
}
```

Where `tail`'s generator produces the next seed (`n + 1`), and the runtime lazily constructs the
next `Stream` value from that seed.

### 3.3 `protocol` → qualified type constraints

A surface `protocol` declaration elaborates to a **qualified type constraint**: a set of operation
signatures that a type must satisfy. Conformance is checked structurally.

```lapis
protocol Eq
    fold equals <in: Self, out: Bool>
    fold notEquals <in: Self, out: Bool>
        (self equals: other) not
```

Elaborates to a constraint `Eq` requiring a fold `equals : Self → Bool` on the conforming type, and
a fold `notEquals : Self → Bool` whose **default** is the body above. The `satisfies:` clause on a
data/behavior declaration adds the constraint: `τ satisfies Eq` becomes `τ <: Eq` (intersection type
in the core, see [`lc.md`](./lc.md) §4).

**A member is a signature; the body is optional.** The kind keyword is required (`fold`, `unfold`,
`map`, `merge`, `scan`) because the kind fixes what may be defaulted — see the table in
[`surface-grammar.md`](./surface-grammar.md) §4.3. A member with no body must be provided by every
conforming type; a member with a body is satisfied by that body when the conforming type does not
declare the operation itself.

**An `unfold` member is a constructor the conformer supplies**, so it takes no default and no seed:
`unfold Identity` requires each conforming type to declare a constant constructor for its identity
element (§3.1). A `merge`/`scan` member is a fusion directive and elaborates to nothing of its own.

**A default body's scope is `self` and `other`.** A default body is not an arm — the protocol cannot
see its conformers' variants — so it has no arm head and no bindings. It may read `self` (the
receiver) and, when the member declares `in:`, `other` (that input value). Both names are supplied
by the machinery, exactly as a fold arm's bindings are supplied by its variant. A body that mentions
`other` when the member declares no `in:` is an unbound-name error
([`surface-grammar.md`](./surface-grammar.md) §3.7).

**A default may carry contract clauses**, and they are enforced around it: an installed default runs
its `demands:` before the body and its `ensures:`/`rescue:` after, exactly as a declared operation
does (§5). A default is not a weaker operation.

**A default body elaborates to a core fold** over the conforming type, with the body as its handler.
Installation is an elaboration-time step: the conforming type's constraint gains the default's
operation only when the type does not declare one, so a declared operation always wins over a
default and an inherited one always wins too. Only `fold` and `map` members may be defaulted; an
`unfold` default is rejected at declaration because it would have to name a constructor the protocol
cannot see, and `merge`/`scan` are fusion directives rather than computations.

**Conformance is structural and transitive.** `protocol Ordered <: Eq` requires every `Ordered`
conformer to satisfy `Eq`'s members as well; a member re-declared in the child keeps the parent's
laws and unions the child's. There is no runtime "is this an `Ordered`?" test in the surface —
conformance is a typing fact (`τ <: Ordered`), not a value-level query. A program that wants such a
question declares its own fold for it.

### 3.4 `relation` → data + span projections

A `relation` is sugar over `data` with two required fold operations:

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
```

Elaborates to:

1. A **data type** `Ancestor = μ α. (Direct(String, String) | Transitive(α, α))`.
2. Two **fold operations** `origin` and `destination` (the span projections).
3. An **auto-generated join invariant** on `Transitive`:
   `invariant: self | self hop destination = self rest origin`.
4. **Auto-generated operations**: `closure()` (semi-naive fixpoint), `reachableFrom()`,
   `reachingTo()` — these are library operations provided for all relations, parameterized by the
   span projections.

The `closure()` operation is a fused unfold+fold (hylomorphism): the unfold derives new proof trees
by composing facts through recursive constructors; the fold collapses each tree to its endpoint pair
for deduplication.

### 3.5 `query` → behavior + cospan projections

A `query` is sugar over `behavior` with three required cospan projections:

```lapis
query PathFinder
    path: List
    solved: Bool
    done: Bool
    next: Self
    unfold Search <in: SearchSeed>
        path -> {s start}
        solved -> s start = s goal
        done -> s exhausted
        next -> s advanceSearch
```

The seed is a declared type, not an inline record shape — the surface has no record type production
(`surface-grammar.md` §3.8), and a multi-value seed is spelled the same way `take`'s is
(`syntax-design.md` §"Behavior"):

```lapis
data SearchSeed
    SearchSeed start: String goal: String graph: Any
```

Elaborates to:

1. A **behavior type** `PathFinder = ν α. (path: List, solved: Bool, done: Bool, next: α)`.
2. Three **cospan projections** (field references, not folds):
   - `output = path` (extracts the result)
   - `accept = solved` (which observations are successes)
   - `done = done` (when to stop stepping)
3. The `self` continuation (`next`) is auto-detected as the stepping mechanism.
4. **Auto-generated operation**: `explore(seed, options?)` — the greatest- fixpoint driver that
   steps through the behavior, collecting accepted outputs until done or limits reached. Includes
   tabling (cycle detection on outputs).

### 3.6 `io` → Mealy machine record

An `io` declaration elaborates to a **Mealy machine data value** — a pure record
`{init, request, respond}`:

```lapis
io Counter
    state: Int
    Increment state -> (state: state + 1, output: state + 1)
    Reset _ -> (state: 0, output: 0)
```

Elaborates to:

```
Counter = {
    init = { state: 0 },
    request = λs. case s.event of
        Increment → IORequest.Write({ message: s.output })
        Reset     → IORequest.Write({ message: 0 })
        ...,
    respond = λs. λres. case s.event of
        Increment → { state: s.state + 1, output: s.state + 1 }
        Reset     → { state: 0, output: 0 }
}
```

The step handlers become the transition function. The `request` function maps state to an
`IORequest` (a data type describing the IO to perform); the `respond` function maps a state and an
`IOResponse` to the next state. The runtime (`run()`) drives the loop:
`request → execute → respond → repeat`.

**The core sees only the data record.** IO is data, not an effect. The runtime is an external
interpreter.

### 3.7 `satisfies:` → intersection type / constraint

A `satisfies: ProtocolName` clause on a data/behavior declaration adds a conformance constraint:

```lapis
data Num
    N value: Int
    satisfies: Ordered
    fold equals <in: Self, out: Bool>
        N value other -> value = other value
    fold compare <in: Self, out: Int>
        N value other -> value - other value
```

Elaborates to:

1. The type `Num` is declared with an intersection: `Num <: Ordered` (i.e., `Num` is a subtype of
   the `Ordered` protocol type).
2. At conformance checking (elaboration time), the required operations are verified: each of
   `Ordered`'s members is either declared by `Num` or carries a default body. A member with neither
   is a conformance error naming the missing operation.
3. Where a member has a default and `Num` does not declare it, the default's fold is installed on
   `Num` at elaboration time — never at runtime, and never over a declared or inherited
   implementation.

Conformance is a typing fact (`Num <: Ordered`), not a value-level query: the surface has no
`instanceof`-style operation. A program that needs one declares a fold for it.

## 4. Recursion Scheme Elaboration

The surface language offers `<para>`, `<histo>`, `<aux:>`, `map`, `merge`, `scan`. These are **not
core constructs** — they elaborate to fold/unfold combinations.

### 4.1 Paramorphism (`<para>`)

A paramorphism gives the handler both the folded result _and_ the raw sub-node (`old field`).

**Surface:**

```lapis
fold pop <para>
    Empty -> nil
    Push value rest -> value , old rest
```

**Elaboration:** The fold's result type becomes a pair `(Result, Raw)`:

```
pop = fold_Stack e {
    Empty() → (nil, Empty),
    Push(value, rest) → (value , rest_raw, rest_raw)
}
```

Where `rest` is the already-folded result (the first component of the pair), and `old rest` accesses
the raw sub-node (the second component). The final result is the first component: `fst(pop(e))`.

More precisely, the paramorphism elaborates to a fold where:

- The result type σ is a pair: `σ = (ResultType, RawType)`.
- Each handler returns a pair: `(computed_result, raw_substructure)`.
- `old field` is elaborated to `snd(field)` — the raw component of the pair.
- The fold machinery threads both components through the recursion.

### 4.2 Histomorphism (`<histo>`)

A histomorphism gives the handler access to all prior fold results (`prev field`).

**Surface:**

```lapis
fold fib <histo, out: Int>
    Zero -> 0
    One -> 1
    Succ pred -> pred + prev pred
```

**Elaboration:** The fold's result type becomes a stream of results:

```
σ = HistoStream    (a declared ν-type carrying one fold result and the prior stream)
```

A histomorphism needs a result that carries the prior results, and the surface has no type
parameters with which to write `Stream<σ>` (`surface-grammar.md` §3.8) — so the stream is a
**declared** codata type whose `result` observer is typed by the fold's own result, exactly the way
`Self` types a continuation:

```lapis
behavior HistoStream
    result: <out: Any>
    prior:  <out: Self>
```

Each handler produces a `HistoStream` node: the current result consed onto the stream of previous
results. `prev field` steps back one level in this stream:

```
fib = fold_Fib e {
    Zero() → HistoStream(0, Nil),
    One() → HistoStream(1, HistoStream(0, Nil)),
    Succ(pred) → HistoStream(pred_result + prev_pred, HistoStream(pred_result, pred_stream))
}
```

Where:

- `pred` is the stream of results from the predecessor (the already-folded `HistoStream`).
- `prev pred` is `pred.prior.result` — the second element of the stream, which is the result of
  folding the predecessor's predecessor (fib(n-2)).
- The final result is `fib(e).result` — the first element of the stream.

### 4.3 Zygomorphism (`<aux: name>`)

A zygomorphism fuses a primary fold with an auxiliary fold.

**Surface:**

```lapis
fold average <aux: #length, out: Int>
    Nil -> 0
    Cons head tail -> head + tail / aux length
```

**Elaboration:** The fold's result type becomes a pair `(PrimaryResult, AuxResult)`:

```
average = fold_List e {
    Nil() → (0, 0),                                    — (sum=0, length=0)
    Cons(head, tail) → (head + sum_tail, 1 + length_tail)
}
```

Where:

- `tail` is the pair `(sum_tail, length_tail)` — both results from the recursive fold.
- `aux length` is `snd(tail)` — the auxiliary (length) component.
- The final result is `fst(average(e))` — the primary (sum) component, divided by the auxiliary
  (length) component.

The auxiliary fold (`length`) must be declared on the same type. The zygomorphism computes both in a
single traversal.

### 4.4 Map

**Data map (eager, O(n)):**

```lapis
map double <in: Int, out: Family>
    Box contents x -> Family Box contents: (contents * x)
```

Elaborates to a fold whose result type is the data type itself (`σ = T`):

```
double = fold_T e {
    Cᵢ(fields) → Cᵢ(transform(fields))    — for each variant, reconstruct with transformed fields
}
```

For recursive fields, the fold recurses automatically (the field is already folded to a transformed
`T`). For non-recursive fields, the transform function is applied.

**Codata map (lazy, O(1)):**

```lapis
map map
    head x -> (x * 2)
```

Elaborates to an unfold that wraps each observation with the transform:

```
map = unfold_T s {
    oⱼ → λseed. transform(gⱼ(seed))    — for simple observers
    oₖ → λseed. gₖ(seed)               — for continuation observers (thread same seed)
}
```

The map is lazy: the transform is applied at observation time, not at map creation time. O(1) to
create; the transform is deferred.

### 4.5 Merge (Deforestation)

`merge opName <#op1, #op2, ...>` composes operations into a single fused operation. The elaboration
depends on the composition pattern:

**Unfold + Fold (Hylomorphism):** `merge(#unfold, #fold)`

```
hylo = fold_T (unfold_T s {oⱼ → gⱼ}) {Cᵢ → hᵢ}
```

The unfold generates a structure from the seed; the fold consumes it. Fusion eliminates the
intermediate structure: the generators feed directly into the handlers without materializing the
data.

**Map + Fold (Prepromorphism):** `merge(#map, #fold)`

```
prepro = fold_T (map_T e {field → transform}) {Cᵢ → hᵢ}
```

The map transforms fields; the fold consumes. Fusion pre-applies the transform to the fold's field
access: `hᵢ(transform(fields))` instead of `fold(map(e))`.

**Fold + Unfold (Metamorphism):** `merge(#fold, #unfold)`

```
meta = unfold_T (fold_T e {Cᵢ → hᵢ}) {oⱼ → gⱼ}
```

The fold reduces to an intermediate value; the unfold generates from it. The intermediate value is
essential and cannot be eliminated (this is the one case where fusion doesn't remove the
intermediate).

**Map-Map Fusion:** `merge(#map1, #map2)`

```
fused_map = map_T e {field → transform2(transform1(field))}
```

Consecutive maps compose into a single map with composed transforms.

**Inverse Elimination:** If `map2` is declared as the inverse of `map1` (`inverse: 'map1'`), then
`merge(#map1, #map2)` eliminates to identity (the operations cancel).

**Involutory Cancellation:** If an operation is declared `properties: [involutory]`, consecutive
pairs in a merge pipeline cancel: `merge(#f, #f, #rest)` → `merge(#rest)`.

**Horner Fusion:** If a fold `foldInner` declares `properties: [distributive:foldOuter]` and
`out: Family`, then `merge(#foldInner, #foldOuter)` is a validated Horner pair. The composition is
sequential: `foldInner(args)` runs first (producing an intermediate structure), then `foldOuter()`
is applied to the result. This is algebraically equivalent to `instance.foldInner(args).foldOuter()`
but grouped under a single named operation.

### 4.6 Scan (Scan Lemma)

`scan foldName` applies a fold at every recursive subterm, returning all results in an array
(root-first).

**Elaboration:** The scan elaborates to a fold whose result type is an array of the fold's result
type:

```
scanSum = fold_T e {
    Cᵢ(fields) → [fold_result_for_this_node, ...flatten(fold_results_for_children)]
}
```

The fold accumulates sub-results in an array, ordered root-first. For a list of length n, the scan
array has n+1 elements (the last is the fold of the base case).

## 5. Contract Elaboration

### 5.1 Demands (Precondition)

**Surface:**

```lapis
fold pop <out: List>
    demands: self | self size > 0
    Empty -> Error signal: 'Cannot pop empty stack'
    Push value rest -> value , old rest
```

**Elaboration:** The fold body is wrapped in a guard:

```
pop = fold_Stack e {
    Cᵢ(fields) →
        if demands_check(self) then
            handler_body
        else
            raise DemandsError
}
```

Where `demands_check(self)` is the elaborated clause body `self size > 0` applied to the current
instance with `self` bound. The `if` is a fold over `Bool` (see [`elaboration.md`](./elaboration.md)
§7). `raise` elaborates to a `Result` typed term: `VError(DemandsError)`.

**DemandsError is never caught by rescue** — it propagates directly to the caller. This is enforced
by the elaboration: the `rescue` handler wraps the body, but the demands check is _outside_ the
rescue wrapper.

### 5.2 Ensures (Postcondition)

**Surface:**

```lapis
fold append <in: Any, out: Family>
    ensures: self old result | result size = old size + 1
    ...
```

**Elaboration:** After the body runs, the ensures clause is checked:

```
append = fold_Stack e {
    Cᵢ(fields, val) →
        let old = snapshot(self) in
        let result = handler_body in
        if ensures_check(self, old, result, val) then
            result
        else
            raise EnsuresError
}
```

`snapshot(self)` captures the pre-call state. `ensures_check` is the elaborated clause body applied
to `(old, result)` with `self` bound. EnsuresError _is_ caught by rescue.

### 5.3 Rescue (Structured Recovery)

**Surface:**

```lapis
fold pop <out: List>
    rescue: self err args retry | retry value: 0
    ...
```

**Elaboration:** The body is wrapped in a `try`/`catch` (elaborated to `Result`):

```
pop = fold_Stack e {
    Cᵢ(fields) →
        let attempt = try handler_body in
        case attempt of
            Ok(result) → result
            Error(err) → rescue_handler(self, err, args, retry_fn)
}
```

Where `retry_fn` is a closure that re-invokes the body with new arguments:
`retry(newArgs) = pop_with_new_args(self, newArgs)`. A retry counter (max 100) prevents infinite
retry loops.

The `try`/`catch` elaborates to `Result`-typed core terms: the body returns `Ok(result)` on success
or `Error(err)` on failure. The core remains effect-free.

### 5.4 Invariant

**Surface:**

```lapis
data Stack
    Empty
    Push
        invariant: self | self size >= 0
        value: Any
        rest: Family
```

**Elaboration:** The invariant is checked at construction time _and_ around every fold/unfold
operation:

- **At construction:** After the variant is constructed, `invariant_check(self)` is evaluated. If
  false, `InvariantError` is raised.
- **Around operations:** Before a fold runs, `invariant_check(self)` is verified (pre-check). After
  the fold produces a result, if the result is a value of the same type, `invariant_check(result)`
  is verified (post-check).

The invariant is AND-composed through the comb-inheritance hierarchy: if both parent and child
declare invariants, both must hold.

### 5.5 Contract Assessment Flow (Elaborated)

The full elaborated form of a contracted operation, in evaluation order:

```
1. invariant_pre = invariant_check(self)        — if false: InvariantError
2. demands_check = demands(self, args)           — if false: DemandsError (caller's fault)
3. old = snapshot(self)
4. body_result = try handler_body(self, args)
5. case body_result of
     Ok(result):
       6a. ensures_check = ensures(self, old, result, args)  — if false: EnsuresError
       6b. invariant_post = invariant_check(result)          — if false: InvariantError
       7. return result
     Error(err):
       6'. rescue_result = rescue(self, err, args, retry)
       case rescue_result of
         Ok(recovered):
           6'b. invariant_post = invariant_check(recovered)  — if false: InvariantError
           7'. return recovered
         Error(err'):
           6'c. invariant_post = invariant_check(self)       — if false: InvariantError
           7''. raise err'
```

**DemandsError bypasses rescue:** Step 2 is outside the `try` in step 4, so rescue never sees a
DemandsError.

## 6. Properties Elaboration

### 6.1 Algebraic Contracts

`properties: (prop1, prop2, ...)` in a spec elaborates to **algebraic contract claims** — a sibling
category to the execution contracts (`demands`/`ensures`/`invariant`/`rescue`). Both are contracts
(claims about an operation made at its declaration), but they differ in what they constrain:

- **Execution contracts** constrain one invocation: preconditions, postconditions, recovery.
- **Algebraic contracts** relate _multiple invocations_: `associative` is a claim about
  `f(f(a,b),c)` vs `f(a,f(b,c))` — not expressible as a single-call postcondition.

This is why laws do not elaborate into `ensures:` clauses; they need their own claim category.

**The provenance chain.** A law's authority comes from the contract system, not from the optimizer:

```
surface: properties: (associative, commutative, identity: e)
    ↓ elaboration
algebraic contract claims (validated against the closed vocabulary)
    ↓ law-checking pass (regime-based — semantics.md §5.4)
    ├─ falsified → LawError (declaration rejected)
    ├─ discharged (exhaustion or derivation) → axioms in E, established
    └─ screened (residual regime) → axioms in E, asserted (evidence, not proof)
                      Ω carries the operation's signature + defining LC term
    ↓ optimizer (directed rewrites licensed by E, per lc.md §7)
    ↓ live observation (checked mode): continuous re-screening against
      actual usage; observed counterexample withdraws the axiom from E
```

Every law in `E` carries its **provenance tag** (`primitive` | `discharged` | `asserted`).
Provenance is evidence about the axiom, never a gate on declaring it.

The properties are validated against the closed vocabulary (`associative`, `commutative`,
`identity:e`, `distributive:g`, `involutory`, `idempotent`, `absorbing:z`). No arbitrary equations —
user-declared laws are membership claims in a fixed catalog of algebraic structures, which is what
keeps rewriting terminating and the `≡` theory well-behaved.

**Intrinsic vs. relational claims.** `associative`, `commutative`, `identity:e`, `idempotent`,
`involutory`, `absorbing:z` are claims about one operation. `distributive:g` is a claim about a
_relation_ between two operations — elaboration checks that `g` names a declared operation on the
same type and that both signatures exist in `Ω`. The elaborated representation keeps the two
distinct.

**At elaboration time:**

1. The properties are validated against the closed vocabulary.
2. The law-checking pass applies the regime-based check (finite/machineFinite/derivable →
   `discharged`; residual → `asserted`) — see [`semantics.md`](./semantics.md) §5.4.
3. If discharged, the axioms are installed in `E` **established**. If screened (residual), the
   axioms are installed in `E` **asserted** — trusted evidence, not proof (the screen falsifies; it
   never establishes).
4. If any check falsifies a claim, `LawError` is thrown with the counterexample and the declaration
   is rejected.

**At runtime (for screened axioms — each is an optimizer-chosen direction of an `≡` axiom):**

- `identity:e` axiom `f(e, a) ≡ a`: the eliminating direction short-circuits — if an argument is
  `e`, return the other argument without entering the fold. Must not skip `demands` checks.
- `absorbing:z` axiom `f(z, a) ≡ z`: same shape — if an argument is `z`, return `z`.
- `idempotent` axiom `f(a, a) ≡ a`: if both arguments are identical (by reference), return the
  argument.
- `distributive:g` axiom: unlocks Horner fusion in merge pipelines.
- `involutory` axiom `f(f(a)) ≡ a`: enables pair cancellation in merge pipelines.

### 6.2 Property Inheritance

Properties inherit through `extend` (comb inheritance). When a child redeclares an operation,
properties from the parent are **unioned** — a child cannot remove a parent's properties (preserves
the Liskov Substitution Principle).

```
parent: properties: [associative]
child:  properties: [commutative]
→ child's effective properties: [associative, commutative]
```

If the child does not redeclare the operation, the parent's properties are inherited wholesale.

## 7. Elaboration of Subtyping

### 7.1 `extend` (Comb Inheritance)

**Surface:**

```lapis
data ExtendedColor <: Color
    Yellow Orange Purple
    fold toHex
        Yellow -> '#FFFF00'
        ...
```

**Elaboration:**

1. `ExtendedColor` is a new μ-type:
   `ExtendedColor = μ α. (Red | Green | Blue | Yellow | Orange | Purple)`. The parent's variants are
   inherited.
2. Subtyping: `ExtendedColor <: Color` (μ-width subtyping — more variants = subtype). Inherited
   variants construct through the child (`ExtendedColor.Red`) and belong to both types; membership
   is asymmetric — every child value is a parent value, but a parent value is not a child value
   (μ-width subtyping adds constructors; it never widens).
3. Fold inheritance: `toHex` on `ExtendedColor` = parent's `toHex` handlers for
   `Red`/`Green`/`Blue` + child's handlers for `Yellow`/`Orange`/`Purple`. This is **polymorphic
   recursion**: the fold dispatches to the appropriate handler based on the variant tag, and
   inherited handlers are resolved via the comb-inheritance delegation chain.
4. `instanceof`: `ExtendedColor.Yellow instanceof Color` is true (the delegation chain connects
   them).

### 7.2 Field Narrowing

**Surface:**

```lapis
data IntList <: List
    Cons head: Int tail: Family
```

**Elaboration:**

1. `IntList` is a subtype of `List` (μ-depth subtyping — `head: Int <: head: Any`). The narrowing
   rules at declaration time: each re-specified field's type must be a subtype of the parent's
   (covariant), no new fields may be introduced, and unmentioned fields are inherited unchanged.
2. `IntList.Cons` instances are `instanceof List.Cons` and `instanceof List` (comb inheritance:
   prototype chain + delegation chain).
3. Operations on `List` accept `IntList` instances (subsumption via `T-Sub`).

## 8. Elaboration Summary Table

| Surface Construct    | Core Elaboration                                                  | Section |
| -------------------- | ----------------------------------------------------------------- | ------- |
| `data T`             | `T = μ α. Σᵢ Cᵢ(Fᵢ(α))`                                           | §3.1    |
| `behavior T`         | `T = ν α. Πⱼ oⱼ(Gⱼ(α))`                                           | §3.2    |
| `protocol P`         | Qualified type constraint                                         | §3.3    |
| `relation R`         | `data` + span projections + join invariant + closure/reachability | §3.4    |
| `query Q`            | `behavior` + cospan projections + explore                         | §3.5    |
| `io M`               | Mealy machine record `{init, request, respond}`                   | §3.6    |
| `satisfies: P`       | Intersection type `τ <: P`                                        | §3.7    |
| `fold op <spec>`     | `fold_T e {Cᵢ → hᵢ}`                                              | §3.1    |
| `unfold Ctor <spec>` | `unfold_T s {oⱼ → gⱼ}`                                            | §3.2    |
| `map op <spec>`      | fold (data) or unfold (codata) with transform                     | §4.4    |
| `merge op <#a, #b>`  | Composed fold/unfold (fusion rules)                               | §4.5    |
| `scan foldName`      | fold with array-accumulating result type                          | §4.6    |
| `<para>`             | fold with pair result type `(Result, Raw)`                        | §4.1    |
| `<histo>`            | fold with a declared stream result type (`HistoStream`)           | §4.2    |
| `<aux: name>`        | fold with pair result type `(Primary, Aux)`                       | §4.3    |
| `demands: <body>`    | Guard before body; DemandsError bypasses rescue                   | §5.1    |
| `ensures: <body>`    | Guard after body; EnsuresError caught by rescue                   | §5.2    |
| `rescue: <body>`     | try/catch elaborated to Result; retry counter                     | §5.3    |
| `invariant: <body>`  | Check at construction + around operations                         | §5.4    |
| `properties: (...)`  | Law constraints; verified + exploited                             | §6.1    |
| `extend` (`<:`)      | μ-width subtyping + fold inheritance                              | §7.1    |
| Field narrowing      | μ-depth subtyping                                                 | §7.2    |
| Binary operators     | Message sends → folds on the operand type                         | §2.4    |
| `double` (op ref)    | The operation's definition term (a `FunType`)                     | §2.3    |
| `f value: x`         | `f x` — apply the function-typed receiver                         | §2.5    |
| `{a, b, c}`          | Nested cons on built-in List                                      | §2.6    |

## 9. Open Questions

1. **Fold dispatch in the core.** The surface uses dynamic dispatch (comb inheritance: the fold
   handler is resolved via the delegation chain at runtime). The core calculus as written uses
   static dispatch (handlers keyed on variant name). The elaboration must reconcile: either (a) the
   core models fold as a method dispatch (adding an OO flavor to the core), or (b) the elaboration
   resolves inherited handlers at compile time, producing a static match with all handlers inlined.
   Option (b) is simpler for the soundness proof but may produce large code; option (a) is more
   faithful to the runtime but complicates the core. _Decision needed._

2. **`old` in paramorphism — snapshot or reference?** The paramorphism's `old
   field` gives the
   raw pre-fold sub-node. Is this a reference to the original (shared, not copied) or a snapshot?
   For immutable data (which Lapis data is), a reference is safe and efficient. The elaboration
   should use a reference, not a copy.

3. **`snapshot(self)` in ensures — what is captured?** For immutable data, the "old" state is just
   the original reference (nothing changed). For codata (which is lazy), the snapshot may need to
   force some observations to capture a meaningful "old" state. The elaboration needs to specify
   what `snapshot(self)` means for codata.

4. **Multi-sorted mutual recursion elaboration.** When two `data` types reference each other
   (cross-sort fields), the elaboration must handle simultaneous μ-bindings: `μ α₁. ..., μ α₂. ...`.
   The current core calculus handles single μ-types; the elaboration needs to extend this to mutual
   recursion. Deferred materialization (declare all, then materialize) is the strategy from
   lapis-js.

5. **Record elaboration.** Records `(k1: v1, k2: v2)` are used for specs, named-argument
   construction, and Mealy state transitions. Are records a built-in product type in the core, or do
   they elaborate to something else (e.g., a data type with one variant per record shape)? The core
   calculus doesn't currently have a record type. _Decision needed:_ add records to the core, or
   elaborate to ad-hoc data types.

   Note the standing rule this question now rests on: **a decision needing more than one value in
   scope is expressed by a declared seed type**, not by packing a product and projecting it. A
   `data` declaration is the surface's answer to "I need two things at once," and it composes with
   every recursion scheme (`syntax-design.md` §"Behavior"'s `TakeSeed`).

6. **Operator resolution.** Binary operators elaborate to folds on the operand type. But which fold?
   `a + b` where `a : Num` elaborates to `Num.add(a, b)`, but the surface syntax doesn't name the
   fold — the compiler must resolve `+` to the `add` fold on `Num` by convention. This requires a
   standard library of operator-to-fold mappings, or a way to declare operator bindings in the
   surface language.

## 10. No Conditional Construct

There is **no conditional** in LC or in the surface language — no primitive `if`, and no named
eliminator for `Bool`. `Bool = μ α. (True | False)` is an ordinary data type, and it appears in
**result position only**: a predicate eliminates a meaningful type and produces a verdict.

```lapis
fold isWarm <out: Bool>
    Red -> true
    Green -> false
    Blue -> false
```

Branching is **structural dispatch**, in exactly two forms:

- **Fold arms** dispatch on a variant. The arm keying _is_ the decision — `Red -> true` needs no
  guard, because `Red` is the condition.
- **Unfold arms** decide on a seed: `guard | payload`, first match wins (`surface-grammar.md` §5.2).

A decision that is neither — a predicate computed over a value with no discriminating variants —
belongs in an unfold over a declared seed type, not in a fold arm's body. `take` is the worked case
(`syntax-design.md` §"Behavior"): its recursion is primitive recursion on a numeric seed whose step
observes a `Stream`, so it is an anamorphism, not a catamorphism with a conditional inside.

Two structural reasons the conditional has no home here:

- **A `Bool`-declared eliminator inverts the declaration-site rule.** Every operation is declared
  inside the type it eliminates, and its arms match that type's variants. An operation that discards
  its eliminated structure and takes its outcomes as parameters has nothing to dispatch on.
- **Fold arms stay order-free.** Their meaning is a total function from variants, which is what
  makes exhaustiveness checkable, keeps `derivation.ts`'s per-variant induction skeleton intact, and
  lets an extending type re-declare arms for its new variants alone (#86). Guards would make arms a
  first-match chain and spend all three properties. `unfold` escapes this because generators are
  first-match _by construction_ and carry no exhaustiveness premise.

## 11. Contracts and Blame

Contract clauses (`demands`, `ensures`, `rescue`, `invariant`) are **not core constructs**. They
elaborate to core terms (see §5 above). The core remains effect-free: `raise` and `try/catch`
elaborate to `Result`-typed terms (sum of success/failure), and the runtime interprets `Result`
values.

**Connection to Wadler's blame calculus.** The current design treats contracts as pure elaboration —
they desugar to folds over `Bool` and `Result`, with no calculus-level support for blame. Wadler's
blame calculus ("Well-typed programs can't be blamed", 2009) takes a different approach: blame
labels are first-class core entities carried by casts, and the blame theorem (well-typed components
can never be blamed) is proved at the calculus level alongside Progress and Preservation.

Lapis's contracts are richer than Wadler's casts — they include `rescue` (recovery) and are tied to
the subtyping lattice (LSP subcontracting: preconditions weaken, postconditions strengthen). The
interaction of subtyping + DbC + blame is hard to formalize purely in elaboration, because
subcontracting is already in LC and the blame theorem needs to talk about which side of a subtyping
relationship is at fault. A future refinement may promote blame labels to the calculus level (see
`design-decisions.md` open question #7).
