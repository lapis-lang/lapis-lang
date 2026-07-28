# Lapis: A Rationale

> For the curious programmer. This is a narrative, not a reference. It starts from something you
> already know — `fold` — and follows the thread to where it leads: a language where fold and unfold
> are the only recursion, where totality is free, where the compiler exploits algebraic laws, and
> where Datalog and Prolog fall out as special cases.
>
> The formal treatment lives in the companion documents. This one is the journey.

## 1. The Universality of Fold

You already know `fold`. In Haskell:

```haskell
sum     = foldr (+) 0
product = foldr (*) 1
length  = foldr (\_ n -> 1 + n) 0
map f   = foldr (\x xs -> f x : xs) []
filter p = foldr (\x xs -> if p x then x : xs else xs) []
reverse = foldr (\x xs -> xs ++ [x]) []
```

Each of these is a different function, but they all share a shape: walk the list from right to left,
replace `[]` with a base value, and replace `(:)` with a combining function. The shape is `fold`.

Graham Hutton's tutorial, _"A tutorial on the universality and expressiveness of fold"_ (1999),
makes a striking claim: **fold is universal**. Every total function on lists that respects the
structure of lists — that is, every function that "does the same thing" to `[]` and to `x : xs` —
can be written as a fold. Not "can be written as a fold with enough cleverness" — _is_ a fold, by
definition. The fold is the unique function that replaces the constructors with operations.

This is not a curiosity. It is a deep fact: **fold is the universal consumer of a data type.** Every
way of consuming a list factors through fold. The same is true for trees, for natural numbers, for
any algebraic data type: fold is the universal observation. (In category theory, this is the
statement that a data type is the _initial algebra_ of its shape functor, and fold is the unique
homomorphism from it.)

Hutton also shows the **fusion law**: if `h` is strict and `h b = v` and `h (f x y) = g x (h y)`,
then:

```
h . foldr f b = foldr g v
```

This is the law that lets you _fuse_ a fold with a function into a single fold. It's the foundation
of deforestation — eliminating intermediate structures. And it's the first place where _algebra_
enters the picture: fusion works because of an equation between functions, an algebraic identity.

## 2. The Dual: Unfold

If fold is the universal _consumer_, there is a dual: **unfold**, the universal _producer_. Where
fold takes a structure apart, unfold builds one up.

```haskell
unfoldr :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr f s = case f s of
  Nothing     -> []
  Just (x, s') -> x : unfoldr f s'
```

From a seed `s`, unfold applies a step function `f` that either says "stop" (`Nothing`) or "produce
a value and a new seed" (`Just (x, s')`). Examples:

```haskell
nats      = unfoldr (\n -> Just (n, n + 1)) 0          -- [0, 1, 2, ...]
iterate f = unfoldr (\x -> Just (x, f x))              -- x, f x, f (f x), ...
downFrom n = unfoldr (\n -> if n == 0 then Nothing else Just (n, n - 1)) n
```

Unfold generates potentially infinite structures. It is the universal _generator_ — the dual of
fold. (In category theory, this is the _final coalgebra_, and unfold is the unique homomorphism into
it.)

Fold and unfold are duals. Fold consumes finite structure; unfold generates potentially infinite
structure. Together, they cover the two fundamental computational activities: **consuming** and
**generating**.

## 3. The Turn: What If the Language Only Had Fold and Unfold?

Here is the turn. You've seen that fold is universal — every total function on a data type _is_ a
fold. You've seen that unfold is its dual — every way of generating a structure _is_ an unfold. So
here's the question:

> **What if a programming language only allowed fold and unfold as recursion?**

No general recursion. No `fix`. No self-reference. Just fold (to consume data) and unfold (to
generate codata).

This is not a new idea — it's the idea behind Charity (Cockett & Fukushima, 1992), and behind the
"recursion is the goto of functional programming" motto (Meijer, Fokkinga & Paterson, 1991). But it
has a consequence that is easy to miss:

**Totality is free.**

If the only recursion is fold (which consumes finite data, bottom-up, and therefore terminates) and
unfold (which generates codata, top-down, one step at a time, and is therefore productive), then
**every program terminates or productively produces output forever.** There is no way to write a
function that loops forever without producing anything. The language is total by construction.

You don't need a termination checker. You don't need sized types. You don't need a fuel monad. The
structure of the language _guarantees_ totality, because the only recursion forms are the ones whose
termination/productivity is built into their definition.

This is the first payoff: **a language where every program terminates, without a termination
checker, because the language doesn't have general recursion.**

## 4. The Second Payoff: The Compiler Can Trust Your Laws

Now here is the payoff that Charity didn't get, and that Haskell can't get.

In Haskell, you can write:

```haskell
add :: Nat -> Nat -> Nat
add Zero     n = n
add (Succ m) n = Succ (add m n)
```

And you can _say_ in a comment: "`add` is associative." You can even write a QuickCheck property.
But the compiler doesn't _know_ it's associative. It can't _use_ it. If you write
`sum (map (add x) xs)`, the compiler can't rewrite it to `add x (sum xs)` — because it can't trust
your claim, and it can't verify it from the definition (verifying associativity of arbitrary
recursive functions is undecidable).

In a language where every operation is a fold, the situation is different. If `add` is declared as a
fold:

```lapis
data Nat
    Zero
    Succ pred: Family

    fold add <in: other Nat, out: Nat, properties: (associative, commutative, identity: Zero)>
        Zero -> other
        Succ pred -> Succ (pred other)
```

The `properties: (associative, commutative, identity: Zero)` is not a comment. It is a
**declaration**. And because `add` is a fold — because the language _enforces_ that every operation
is a fold — the compiler can:

1. **Verify** the law at declaration time, by testing it against generated samples. If `add` weren't
   associative, the compiler would catch it before the declaration entered the program.

2. **Exploit** the law at runtime. When it sees `three add Zero`, it knows from `identity: Zero`
   that the result is `three` — without traversing the structure. The fold is short-circuited.

3. **Fuse** based on the law. When it sees `merge(#scaleEach, #sum)` and `scaleEach` declares
   `distributive: sum`, it knows the two folds can be sequenced as a single Horner-rule operation.

This is the key: **enforcement makes exploitation reliable.** The compiler can trust every law
declaration because every operation is a fold, and every fold respects the algebra. In Haskell, laws
are conventions; in Lapis, laws are _facts the compiler can use_.

This is the contribution that Lapis makes that no existing language makes. Coal enforces fold/unfold
(and gets totality), but its laws are conventions — the manual says "these laws aren't enforced by
the compiler." Haskell has laws, but doesn't enforce fold — so it can't trust them. Lapis does both:
the cage (enforced fold/unfold) and the key (exploitable laws).

## 5. Calculating Programs, Not Scheming Them

There is a deeper reason the laws matter. It goes back to Richard Bird and Meertens — and to a
critique by Philip Wadler.

Most programming today is **scheming**: you write a program by intuition, follow a pattern, test it,
debug it, and hope it's correct. The program is _constructed_ — assembled from pieces you believe
will work — and then _verified_ after the fact, by testing or by proof. The specification and the
program are separate things, and the gap between them is bridged by human effort.

Bird and Meertens proposed a different way: **calculating** the program from its specification. You
start with a clear statement of _what_ you want — a relation or function describing the desired
result — and you _calculate_ the program by applying algebraic laws: fusion, distributivity, the
Horner rule, the scan lemma. Each step is an equation; the program is _derived_, not written. The
result is correct by construction, because every step preserves the meaning.

Philip Wadler, in his 1987 paper _"Why calculating is better than scheming"_ (a critique of Abelson
and Sussman's SICP), made the case sharply: the scheming approach — write a program, then test and
debug it into correctness — is how most programming is taught and practiced, but it leaves
correctness as an afterthought. The calculating approach — derive the program from the specification
by algebraic manipulation — makes correctness the _starting point_, not the ending hope. The program
is a calculation; the calculation is the proof.

A classic example (from Bird's _"An Introduction to the Theory of Lists"_ and the BMF tradition):
you want to compute the sum of the squares of the first `n` natural numbers. The _specification_ is:

$$\text{sumsq}(n) = \sum_{i=0}^{n-1} i^2$$

The naive program generates the list `[0, 1, ..., n-1]`, squares each element, and sums the result —
two traversals, one intermediate list. But by calculation, using the fusion law and the fact that
squaring distributes over summation in a suitable sense, you can derive a single-fold program that
computes the same result in one pass, with no intermediate list. The calculation is a sequence of
equations; the final equation _is_ the efficient program.

This is beautiful. But it has a problem: **it happens on paper, not in the compiler.**

In Haskell, you can perform this calculation by hand and write the resulting program. But the
compiler doesn't know you did it. It can't _check_ that your fused program is equivalent to the
naive one. It can't _perform_ the fusion itself, because it can't trust the laws (they're comments,
not declarations). And it can't _verify_ the laws, because verifying algebraic properties of
arbitrary recursive functions is undecidable.

In Lapis, the calculation _is_ the program. You declare the laws; the compiler verifies them; and
the fusion happens automatically. The `merge` operation is literally program calculation made into a
language construct:

```lapis
merge scaledSum <#scaleEach, #sum>
```

This says: "compose `scaleEach` and `sum` into a single operation." The compiler checks that
`scaleEach` declares `distributive: sum` (the law that makes the fusion valid), verifies the law,
and performs the fusion. You wrote the specification (two separate operations); the compiler
_calculated_ the efficient program (one fused operation). The calculation is not on paper — it's in
the language.

This is the deepest payoff of the enforced structure: **it makes Bird's vision of program
calculation practical.** Not because the language can prove arbitrary theorems (it can't), but
because it restricts programs to a shape (fold/unfold) where the laws are _declarable_,
_verifiable_, and _exploitable_. The cage doesn't just give you totality — it gives you a space
where calculation is possible, because the structure is known and the laws are trusted.

The contrast with conventional languages is sharp:

|                         | Scheming (conventional)               | Calculating (Bird's vision, Lapis's goal)                         |
| ----------------------- | ------------------------------------- | ----------------------------------------------------------------- |
| How you get the program | Write it by intuition, test, debug    | Derive it from a specification by algebraic laws                  |
| Where the laws live     | In papers, in comments, in QuickCheck | In the language, as declarations                                  |
| Who verifies the laws   | You (by proof or testing)             | The compiler (at declaration time)                                |
| Who exploits the laws   | You (by hand, if you remember)        | The compiler (automatically: fusion, short-circuit, cancellation) |
| Correctness             | Hoped for, tested after               | By construction, calculated from the spec                         |

Bird showed that calculating is better than scheming. Lapis is the attempt to make the calculation
happen in the compiler, not in the margins of a paper.

## 6. A Little Tutorial

Enough theory. Let's write some Lapis.

### 5.1 A Stack

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

    fold pop <para>
        Empty -> nil
        Push value rest -> value , old rest
```

`Stack` is a data type with two variants: `Empty` (no fields) and `Push` (a value and a recursive
rest). `Family` is the self-reference — it marks `rest` as a recursive field.

`fold size` is a catamorphism. Each case arm matches a variant and binds its fields. In the `Push`
arm, `rest` is the _already-folded_ result — the size of the rest of the stack, not the raw
sub-stack. The fold descends into `Family` fields automatically, bottom-up.

`fold pop <para>` is a paramorphism. The `<para>` flag gives the handler access to both the folded
result (`rest` — the size) and the raw sub-node (`old rest` — the original sub-stack). `pop` returns
the value paired with the original remaining stack.

### 5.2 A Stream

```lapis
behavior Stream
    head: <out: Number>
    tail: <out: Self>

    unfold From <in: n Number>
        head -> n
        tail -> n + 1

nats = Stream From: 0
nats head                     "=> 0"
nats tail head                "=> 1"
nats tail tail head           "=> 2"
```

`Stream` is a behavior type — a final coalgebra. `Self` marks `tail` as a continuation: observing
`tail` produces the _next_ stream value, lazily. The `unfold From` is an anamorphism: from a seed
`n`, it generates `head = n` and `tail` from seed `n + 1`.

The stream is potentially infinite. But each observation is finite — `nats head` produces `0` and
stops. `nats tail` produces a new stream (memoized — observing it twice returns the same value). The
laziness is not a flag you set; it's built into `behavior`, just as eagerness is built into `data`.

### 5.3 Laws in Action

```lapis
data Nat
    Zero
    Succ pred: Family

    fold add <in: other Nat, out: Nat, properties: (associative, commutative, identity: Zero)>
        Zero -> other
        Succ pred -> Succ (pred other)

three = Nat Succ pred: (Nat Succ pred: (Nat Succ pred: Nat Zero))

three add Nat Zero           "=> three — the identity guard fires, no traversal"
Nat Zero add three           "=> three — same guard, other side"
```

When the compiler sees `three add Zero`, it checks: does `add` have an `identity:` property? Yes —
`identity: Zero`. Is one of the arguments `Zero`? Yes. So it returns the other argument _without
entering the fold_. The traversal is eliminated entirely.

This is not a peephole optimization the compiler stumbled on. It is a _guaranteed_ optimization,
triggered by a _declared_ law, _verified_ at declaration time. The law is a fact; the compiler uses
it.

### 5.4 Fusion

```lapis
data NumList
    Nil
    Cons head: Number tail: Family

    fold sum <out: Number>
        Nil -> 0
        Cons head tail -> head + tail

    fold scaleEach <in: x Number, out: Family, properties: (distributive: sum)>
        Nil -> Family Nil
        Cons head tail -> Family Cons head: head * x tail: (tail x)

    merge scaledSum <#scaleEach, #sum>
```

`scaleEach` multiplies every element by `x` and rebuilds the list. `sum` adds up the elements.
`merge scaledSum <#scaleEach, #sum>` composes them.

Normally, this would build an intermediate scaled list, then sum it — two traversals, one
intermediate allocation. But `scaleEach` declares `distributive: sum`, which means: scaling each
element and then summing is the same as summing and then scaling the total. The compiler recognizes
this as a Horner-rule pair and sequences them as a single named operation.

The `properties` declaration is what unlocks the fusion. Without it, the compiler would have to
assume the two folds are independent. With it, the compiler _knows_ they compose — because the law
was declared and verified.

## 7. The Duality: Data and Codata

You've now seen both halves:

- **Data** (`data`, `fold`) — finite structures, consumed bottom-up. Eager. Terminating.
- **Codata** (`behavior`, `unfold`) — potentially infinite structures, generated top-down. Lazy.
  Productive.

These are duals. Data is defined by its constructors (how to build it); codata is defined by its
observers (how to observe it). Fold is the universal consumer; unfold is the universal generator.
Data is the initial algebra (μ); codata is the final coalgebra (ν).

This duality is not decorative. It means:

- **Every program is a composition of folds and unfolds.** A hylomorphism (unfold then fold)
  generates a structure and immediately consumes it — without materializing the intermediate. A
  metamorphism (fold then unfold) consumes a structure into a value and generates a new structure
  from it.
- **The two sides cover the whole computational space.** Consumption and generation. Termination and
  productivity. Finite and infinite. Eager and lazy.

The language doesn't make you choose between eager and lazy — it gives you both, fixed by
declaration kind. `data` is eager; `behavior` is lazy. The user picks a _kind_, and the strategy
follows. The eager/lazy question is invisible because the kind answers it.

## 8. Where Datalog Comes From

Here is where it gets interesting. The bialgebraic structure doesn't just give you data and codata —
it gives you _relational programming_ for free.

A **relation** is a data type with two projections: an _origin_ and a _destination_. Think of a
graph edge: `Direct from: String to: String`. Or a path: `Transitive hop: Family rest: Family` — a
composition of two sub-relations.

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

The `origin` and `destination` folds project each variant to its endpoints. For `Transitive`, the
origin is the origin of the first hop, and the destination is the destination of the last rest. This
is a **span**: `A ← R → B`.

Now, the join invariant: for `Transitive`, the destination of the first hop must equal the origin of
the second rest. The language generates this invariant automatically from the projections — you
don't write it.

And from this structure, a familiar operation falls out: **transitive closure**.

```lapis
base = {
    Ancestor Direct from: 'alice' to: 'bob'
    Ancestor Direct from: 'bob'   to: 'carol'
    Ancestor Direct from: 'carol' to: 'dave'
}

closed = Ancestor closure: base
Ancestor reachableFrom: closed from: {'alice'}    "=> {'bob', 'carol', 'dave'}"
```

`closure` computes the transitive closure: all pairs reachable by composing base facts through
`Transitive`. This is **Datalog** — bottom-up, exhaustive, fixpoint computation. The language
generates it from the span structure.

How? `closure` is a fused unfold+fold (a hylomorphism): the unfold derives new proof trees by
composing existing facts through recursive constructors; the fold collapses each tree to its
endpoint pair for deduplication. The fixpoint iteration is semi-naive (the standard Datalog
evaluation strategy), and it terminates because the number of endpoint pairs is bounded by |domain|
× |codomain|.

You didn't write a Datalog engine. You declared a relation with two projections, and the engine
appeared.

## 9. Where Prolog Comes From

If Datalog falls out of the data side (relations, spans, least fixpoint), then **Prolog** falls out
of the codata side (behaviors, cospans, greatest fixpoint).

A **query** is a behavior type with three projections: an _output_ (what to collect), an _accept_
(which observations are successes), and a _done_ (when to stop). Think of a search process: you
observe the current state, decide if it's a solution, decide if you're done, and step to the next
state.

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

`explore` drives the search: unfold the seed into an initial state, observe `accept` — if true,
collect `output`; observe `done` — if true, stop; follow `next` to the next state; repeat. This is a
**greatest fixpoint** — the dual of `closure`'s least fixpoint. It's **Prolog-style search**:
top-down, lazy, stops after finding results.

`maxResults: 1` is Prolog's _cut_ — commit to the first solution and stop. The tabling (cycle
detection) is automatic: the search tracks visited outputs and terminates a branch when it revisits
one.

So: **relations give you Datalog (bottom-up, exhaustive, least fixpoint); queries give you Prolog
(top-down, lazy, greatest fixpoint).** And both are sugar — they elaborate to `data` + span
projections and `behavior` + cospan projections. The bialgebraic structure produces both halves of
logic programming from the same two constructs (fold and unfold) that produce everything else.

This is not a coincidence. Datalog is the data side of logic programming (initial algebra, least
fixpoint, "what is provably true?"); Prolog is the codata side (final coalgebra, greatest fixpoint,
"what can I find by searching?"). The duality of fold and unfold _is_ the duality of Datalog and
Prolog.

## 10. Contracts: Correctness Without Effects

One more thing falls out of the structure: a story for correctness that doesn't require an effect
system.

In Haskell, you track effects with monads: `IO a`, `State s a`, `Except e a`. The type tells you
what effects a computation performs. This is powerful, but it burdens the programmer: every function
that might fail needs `Except`, every function that does IO needs `IO`, and the composition rules
are monadic.

Lapis takes a different position, following Meyer's Design by Contract: instead of tracking _what a
function does_, declare _what it requires and guarantees_.

```lapis
data Stack
    Empty
    Push
        invariant: [self | self size >= 0]
        value: Object
        rest: Family

    fold pop <out: Array>
        demands: [self | self size > 0]
        ensures: [self old result | result size = 2]
        rescue:  [self err args retry | retry value: 0]
        Empty -> Error signal: 'Cannot pop empty stack'
        Push value rest -> value , old rest
```

- `demands:` — a precondition. If the caller violates it, it's the caller's fault (`DemandsError`).
  The body never runs.
- `ensures:` — a postcondition. If the implementer violates it, it's the implementer's fault
  (`EnsuresError`).
- `invariant:` — checked at construction and around every operation.
- `rescue:` — structured recovery. If the body throws, rescue can return a fallback or `retry` with
  new arguments.

The blame model is binary and local: demands = caller's fault, ensures = implementer's fault. No
monadic plumbing, no effect tracking in types. The contracts are equational — "if P before, Q after"
— which fits the bialgebraic foundation (equational reasoning about obligations, not monadic
reasoning about effect plumbing).

And there's something unique: **fault-tolerant folds**. If a handler throws for one node in a fold
traversal, `rescue` handles it _for that node_, and the traversal continues. The rest of the tree is
unaffected. This is per-node recovery — something effect systems can't easily do, because they wrap
the _entire_ computation, not individual nodes.

## 11. What You Get

Let me summarize what the thread from fold to Lapis produces:

| From                                   | You get                                                                                                                      |
| -------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| Fold is universal (Hutton)             | Every total function on a data type is a fold                                                                                |
| Unfold is the dual                     | Every way to generate a structure is an unfold                                                                               |
| Only fold/unfold, no general recursion | **Totality by construction** — no termination checker needed                                                                 |
| Every operation is a fold              | The compiler can **trust law declarations**                                                                                  |
| Trust + verify + exploit               | **Law-driven optimization** — identity short-circuits, Horner fusion, involutory cancellation                                |
| Laws in the language, not in comments  | **Program calculation** (Bird) — the compiler derives efficient programs from specifications, not just hopes they're correct |
| Data (μ) + codata (ν)                  | The eager/lazy question is answered by declaration kind — invisible to the user                                              |
| Relation = data + span                 | **Datalog** falls out — transitive closure, reachability, least fixpoint                                                     |
| Query = behavior + cospan              | **Prolog** falls out — lazy search, greatest fixpoint, cut, tabling                                                          |
| Contracts, not effects                 | Correctness with equational reasoning, binary blame, fault-tolerant folds                                                    |

All of this from one decision: **the only recursion is fold and unfold.** The cage (enforcement)
gives you totality. The key (exploitation) gives you law-driven optimization. The duality (μ/ν)
gives you data/codata, eager/lazy, Datalog/Prolog. And contracts give you correctness without the
monadic burden.

## 12. The Honest Part

This is a working prototype, not a shipping language. The semantics are implemented and tested in
[`lapis-js`](https://github.com/lapis-lang/lapis-js) — every claim above (totality, law
verification, law exploitation, relations, queries, contracts) runs today. But the native language
(the parser, type checker, evaluator) is early. The surface syntax is denser than Haskell; the type
system is subtyping-based (no parametric polymorphism, so no free theorems — laws must be declared
explicitly); the ecosystem is nonexistent.

The bet is that the _exploitation_ (law-driven optimization) and the _practicality_ (subtyping,
contracts, IO as data, Datalog/Prolog from the structure) are what Charity was missing. Charity had
the cage (enforced fold/unfold, totality) but no key (no law exploitation) and no practical story
(no subtyping, no contracts, no IO, no relations). Lapis builds both.

Whether the bet pays off is unproven at scale. The prototype is evidence; the native language is the
test. But the thread from Hutton's tutorial to a language where fold and unfold are the only
recursion, where totality is free, where the compiler exploits your algebra, and where Datalog and
Prolog are special cases — that thread is real, and it leads somewhere worth going.

## Further Reading

- **Hutton, G.**, "A tutorial on the universality and expressiveness of fold" (1999) — where the
  thread starts
- **Wadler, P.**, "Why calculating is better than scheming" (1987) — the critique of scheming; the
  case for calculation
- **Bird, R.**, "An Introduction to the Theory of Lists" (1987) / **Bird & de Moor**, _Algebra of
  Programming_ (1997) — calculating programs from specifications
- **Meijer, Fokkinga & Paterson**, "Functional Programming with Bananas, Lenses, Envelopes and
  Barbed Wire" (1991) — "recursion is the goto of FP"
- **Turi & Plotkin**, "Towards a Mathematical Operational Semantics" (1997) — the bialgebraic
  foundation
- **Cockett & Fukushima**, "About Charity" (1992) — the enforced-structure precedent
- **Meyer, B.**, "Object-Oriented Software Construction" (1997) — subtyping subsumes generics;
  Design by Contract
- **von Thun, M.**, "Rationale for Joy" — the narrative structure this document imitates

For the formal treatment: [`lc.md`](../theory/lc.md), [`semantics.md`](../theory/semantics.md). For
the implementation plan: [`language-design.md`](../theory/language-design.md). For the defense (why
this deserves to exist): [`why-lapis.md`](../theory/why-lapis.md). For the comparison with the
closest existing language: [`lapis-vs-coal.md`](../theory/lapis-vs-coal.md).
