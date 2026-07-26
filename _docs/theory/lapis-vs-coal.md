# Lapis vs Coal: A Comparative Study

> [Coal](https://coal-lang.org/) is the closest existing language to Lapis in
> spirit. Both are total functional languages that enforce structural recursion,
> embrace the bialgebraic duality of data and codata, and draw inspiration from
> the Mathematics of Program Construction. This document compares them honestly
> to sharpen what Lapis contributes that Coal does not, and to acknowledge where
> Coal's choices are sound.

## The Shared Ground

Coal and Lapis agree on the foundational bet:

| Principle | Coal | Lapis |
|---|---|---|
| Total functional programming | Yes — "recursion is the goto of FP" | Yes — same motto (Meijer et al.) |
| Enforced structural recursion | `fold` is a keyword; general recursion rejected at compile time | `fold` is a declaration form; no general fixpoint in the core |
| Codata / coalgebras | `Machine` type, streams, `cofix` | `behavior` type, `unfold`, `Self` continuations |
| Bialgebraic duality | Explicit: "data and codata are two sides of the same coin"; initial algebras and final coalgebras | Explicit: data = μF (initial algebra), behavior = νF (final coalgebra); Turi-Plotkin semantics |
| Pattern functors and fixed points | Documented: `ListF<t,a>`, `List ≅ μF` | Core calculus: `μ α. Σᵢ Cᵢ(Fᵢ(α))` |
| Termination by construction | `@`-patterns only inside constructors (structurally smaller) | Fold substitutes result type for recursive position; structure is the measure |
| Productivity for codata | `cofix` must be productive (observe before recursing) | Unfold is guarded by construction (each generator produces one observation) |

Both languages cite the same lineage: Meertens, Bird, Malcolm, the Squiggol
community. Both recognize that the μ/ν duality is the organizing principle. Both
reject general recursion in favor of structured fold/unfold. This is the shared
thesis, and it is correct.

## Where They Diverge

The divergence is not in the *enforcement* (both enforce) but in what comes
*after* enforcement — what you *do* with the structure you've guaranteed.

### 1. Law Verification and Exploitation (the central difference)

This is the single most important distinction.

**Coal:** Laws are documented but neither enforced nor exploited. From the Coal
manual, on functor laws:

> "These laws aren't enforced by the compiler, but following them is always a
> good idea."

Coal has traits (type classes) with law *conventions* — the same position Haskell
takes. The compiler does not verify that a `Functor` instance satisfies the
identity and composition laws. It does not exploit laws for optimization. There
is no notion of `associative` or `distributive` as declarations the compiler can
trust and use.

**Lapis:** Laws are first-class declarations that are *verified* and *exploited*.

- `properties: [associative, commutative, identity:Zero]` on a fold triggers
  automatic sample-based testing at declaration time. A false claim throws
  `LawError` with a counterexample.
- Declared `identity:E` installs a runtime guard that short-circuits the fold
  when the identity is encountered — no traversal.
- Declared `distributive:sum` unlocks Horner fusion in a `merge` pipeline.
- Declared `involutory` causes consecutive pairs to cancel in a merge pipeline.

This is the contribution Lapis makes that Coal does not: **the enforced structure
is not just a termination guarantee (Coal has that) but a foundation for the
compiler to trust and exploit algebraic laws.** Coal's cage is Lapis's cage too —
but Lapis also has the key.

**Why Coal can't easily add this:** Coal's laws are conventions on type-class
instances, which are ordinary functions. The compiler would need to analyze
arbitrary function bodies to verify laws — the same undecidable problem Lapis
avoids by having laws be declarations on *folds* (whose structure is known). The
enforcement of fold/unfold is what makes law exploitation tractable; Coal has the
enforcement but hasn't connected it to law exploitation.

### 2. Subtyping vs Parametric Polymorphism

**Coal:** System-F with parametric polymorphism and type inference
(Hindley-Milner lineage). Higher-kinded traits (`Functor<f>`, kind `* → *`).
Generics are the primary abstraction mechanism. Row polymorphism for records.

**Lapis:** F<: with subtyping. No higher-kinded polymorphism. Comb inheritance
and field narrowing subsume generics (Meyer). Protocols are predicates over the
subtyping lattice, not type-constructors.

| Aspect | Coal | Lapis |
|---|---|---|
| Polymorphism | Parametric (System-F) | Subtyping (F<:) |
| Type inference | Hindley-Milner (automatic) | Bounded quantification (more annotation) |
| Higher-kinded traits | Yes (`Functor<f>`) | No (protocols are structural predicates) |
| Row polymorphism | Yes (extensible records) | No (records are named-argument sugar) |
| Parametricity | Yes (free theorems) | No (lost; recovered via `properties`) |
| Subtyping | No | Yes (comb inheritance, field narrowing) |

**Honest assessment:** Coal's choice is more conventional and better-understood.
Parametric polymorphism with type inference is the ML/Haskell tradition, and it
gives you free theorems. Lapis's choice (subtyping over generics) is riskier — it
sacrifices parametricity and type inference — but it aligns with Meyer's
philosophy and avoids type-parameter ceremony. The parametricity loss is the real
cost; Lapis pays it back with explicit `properties`, but that is a trade, not a
win. Coal keeps parametricity for free.

**Where Lapis's subtyping shines:** Comb inheritance with fold inheritance — an
extended ADT inherits parent fold handlers and adds new ones, with polymorphic
recursion. This is natural in Lapis (`ExtendedColor <: Color` with inherited
`toHex`) and awkward in Coal's type-class model (you'd need a new type and a new
instance, with no inheritance of handlers). But this is a *practical* advantage,
not a *theoretical* one.

### 3. Effects: IO Monad vs Contracts + Mealy Data

**Coal:** IO monad, identical to Haskell. `IO<a>` is a type describing effectful
computation; `do`-notation sequences monadic operations; `and_then` (bind) is the
composition operator. The runtime executes `IO` values.

**Lapis:** No effect type. IO is a Mealy machine — a pure data value
`{init, request, respond}` that a runtime interprets. Contracts (demands/ensures/
rescue/invariant) provide the correctness layer that effects would in another
language.

| Aspect | Coal | Lapis |
|---|---|---|
| IO model | Monad (`IO<a>`, `do`-notation, `bind`) | Mealy machine (data value, runtime interpreter) |
| Effect tracking | Type-level (`IO<a>` in the type) | None (core is effect-free) |
| Error handling | `Result<a, e>` type + monadic chaining | `rescue`/`retry` contracts (elaborate to `Result`) |
| Correctness obligations | None (conventions only) | Contracts (demands/ensures/invariant, LSP subcontracting) |
| Syntactic burden | `do`-notation, `and_then` chains | None (IO is just data) |

**Honest assessment:** Coal's IO monad is well-understood and has massive
ecosystem support (Haskell's 30 years). Lapis's Mealy-machine IO is elegant but
unproven at scale. The contracts-vs-effects debate (see
[lapis-js#113](https://github.com/lapis-lang/lapis-js/issues/113)) is genuinely
open — contracts provide equational reasoning about obligations, but effects
provide type-level tracking that contracts don't. Lapis's position (contracts
cover the 80%, the rest is `query`/future `Amb`) is reasoned but not yet
battle-tested. Coal's position (just use a monad) is safe and proven.

**Where Lapis's approach shines:** Fault-tolerant folds — `rescue` handles
per-node failures during a fold traversal while the rest of the tree continues.
This is unique to Lapis and has no Coal equivalent. The Mealy-machine IO also
keeps the program *pure* without monadic syntactic overhead, which is a genuine
ergonomic win.

### 4. Relations and Queries

**Coal:** No notion of relations or queries. Data is data; codata is streams/
machines. There is no Datalog-style or Prolog-style layer.

**Lapis:** `relation` (data + span projections + `closure()` = semi-naive Datalog
fixpoint) and `query` (behavior + cospan projections + `explore()` = greatest-
fixpoint Prolog-style search with tabling). These are first-class declaration
forms that elaborate to data/behavior.

This is a *scope* difference, not a *foundational* one. Lapis's relations and
queries are sugar over the bialgebraic core — they could in principle be a
library on top of Coal too. But Lapis's choice to make them first-class reflects
the BMF vision: program calculation includes relational program calculation
(Bird's work on relations, the Bird-Meertens *relational* calculus), and logic
programming is the codata dual of Datalog. Coal stops at data + codata; Lapis
extends to the relational/cospan layer.

### 5. Conditionals

**Coal:** Primitive `if-then-else`. Both branches must be present and produce the
same type. Guards (`when`/`otherwise`) in pattern matching.

**Lapis:** No primitive `if`. `Boolean` is a data type (`μ α. True | False`);
`ifTrue:ifFalse:` is a fold over it. Branching is fold-based dispatch.

**Honest assessment:** Coal's `if-then-else` is pragmatic and familiar. Lapis's
"no primitive if" is philosophically consistent (everything is fold/unfold) but
adds friction for simple conditionals. The honest truth is that Coal's `if` is
sugar for a fold over `Bool` — Lapis just makes the desugaring explicit and
forbids the sugar. Whether this is a feature or an annoyance depends on the
audience.

### 6. Syntax

**Coal:** ML/Haskell-family syntax. `fn`, `let ... in`, `match`, `if-then-else`,
`fun`, `type`, `trait`, `instance`. Curried functions. Reverse-application
pipelining (`|.`). Familiar to FP programmers.

**Lapis:** Self/Smalltalk-family syntax. Message sends, keyword arguments, blocks
`[params | expr]`, indentation-significant, `->` case arms. `self` always in
scope. Uniform access principle. Familiar to Smalltalk/Self programmers, less so
to FP programmers.

**Honest assessment:** Per Atanassow's advice, syntax should not be the
contribution. Both languages have made a syntax choice and should get it out of
the way. Coal's choice is safer (ML syntax is well-understood); Lapis's choice is
more distinctive but riskier (denser, steeper learning curve). Neither syntax is
the point of either language.

### 7. Recursion Scheme Coverage

**Coal:** `fold` (catamorphism) with `@`-patterns. `cofix` for corecursive
machines. Mutual recursion via named top-level folds. No histomorphism,
zygomorphism, paramorphism, hylomorphism, or metamorphism as language constructs.

**Lapis:** `fold` (cata), `unfold` (ana), `map`, `merge` (deforestation: hylo,
meta, prepro, postpro), `scan` (scan lemma), plus `<para>` (paramorphism),
`<histo>` (histomorphism), `<aux:>` (zygomorphism) as spec modifiers on fold.

**Honest assessment:** Lapis covers more of the recursion-scheme lattice, but
Coal's position is defensible — most practical programs need only fold and
unfold, and the advanced schemes can be encoded (as Coal's `fib` example shows,
using a pair-returning fold to simulate histomorphism). Lapis's choice to make
them first-class is a *convenience* and a *declarative* win (the compiler knows
you're doing a histomorphism and can optimize accordingly), but it is not a
*foundational* difference. The schemes elaborate to fold/unfold in both
languages; Lapis just names them.

## Summary Table

| Dimension | Coal | Lapis | Advantage |
|---|---|---|---|
| Enforced structural recursion | Yes (`fold` keyword) | Yes (`fold` declaration) | Tie |
| Codata / coalgebras | Yes (`Machine`, `cofix`) | Yes (`behavior`, `unfold`) | Tie |
| Bialgebraic duality | Yes (documented) | Yes (core calculus) | Tie |
| Totality | Yes | Yes | Tie |
| **Law verification** | **No** (conventions) | **Yes** (`LawError`, sample-checking) | **Lapis** |
| **Law exploitation** | **No** | **Yes** (identity guards, Horner fusion, involutory cancellation) | **Lapis** |
| Polymorphism | Parametric (System-F) | Subtyping (F<:) | Coal (parametricity, inference); Lapis (no generics ceremony) |
| Type inference | Hindley-Milner | Bounded quantification (more annotation) | Coal |
| Higher-kinded traits | Yes | No | Coal |
| Subtyping / inheritance | No | Yes (comb inheritance) | Lapis |
| IO | Monad (`IO<a>`, `do`) | Mealy data (`{init, request, respond}`) | Coal (proven); Lapis (elegant, unproven) |
| Contracts | No | Yes (demands/ensures/rescue/invariant, LSP) | Lapis |
| Relations (Datalog) | No | Yes (`relation`, `closure()`) | Lapis (scope) |
| Queries (Prolog) | No | Yes (`query`, `explore()`) | Lapis (scope) |
| Conditionals | Primitive `if` | Fold over `Boolean` | Coal (pragmatic); Lapis (philosophically consistent) |
| Recursion schemes | fold, cofix | fold, unfold, map, merge, scan, para, histo, zygo | Lapis (coverage); Coal (simpler) |
| Syntax | ML/Haskell | Self/Smalltalk | Tie (preference) |
| Ecosystem | Growing (LLVM backend) | None (prototype only) | Coal |

## What the Comparison Reveals

The comparison confirms the thesis of [`why-lapis.md`](./why-lapis.md) in `theory/`:

**Coal is the "enforcement without exploitation" case study.** It proves that
enforced structural recursion is practical (it has a compiler, an LLVM backend, a
standard library, documentation). It proves the cage is habitable. But it also
demonstrates the *limit* of enforcement alone: Coal's laws are conventions, its
functor laws "aren't enforced by the compiler," and there is no mechanism for the
compiler to exploit algebraic properties for optimization.

**Lapis's unique contribution is the exploitation half.** The enforced structure
(enforced fold/unfold, no general recursion) is the *foundation* that makes law
exploitation *reliable* — the compiler can trust every law declaration because
every operation is a fold, and every fold respects the algebra. Coal has the
foundation but hasn't built the exploitation on top of it. Lapis builds both.

The other differences (subtyping vs generics, contracts vs monads, relations/
queries, syntax) are *design choices* that shape the language's character but are
not the *reason* Lapis exists. They could go either way. The law verification +
exploitation is the one thing that is irreducibly Lapis and cannot be a library —
because it requires the enforcement, and enforcement is a language-level decision.

## What Lapis Can Learn from Coal

1. **Coal is further along practically.** It has a compiler, an LLVM backend, a
   standard library, and real documentation. Lapis has a prototype and design
   docs. The implementation plan in [`language-design.md`](./language-design.md)
   should be executed with Coal's pragmatism as a model — get a working compiler — get a working compiler
   for a minimal subset before expanding scope.

2. **Coal's `@`-pattern syntax is elegant.** The `@` prefix on a pattern variable
   marks it as "the result of recursively folding this position." This is a clean
   surface syntax for the fold mechanism — worth studying as Lapis refines its own
   case-arm syntax. Lapis's `Variant fields -> body` with implicit recursion into
   `Family` fields is more declarative but less explicit about *which* fields
   recurse.

3. **Coal's `Machine` abstraction is well-designed.** The separation of internal
   state from observable output, the `observe`/`receive` interface, and the
   `compose`/`zip`/`duplicate` combinators are a clean codata API. Lapis's
   `behavior` with `Self` continuations is more declarative but less compositional
   — the `Machine` combinators are worth studying for Lapis's codata standard
   library.

4. **Coal keeps it simple.** No contracts, no relations, no queries, no law
   exploitation — just data, codata, fold, and traits. This minimalism is a
   feature for a first implementation. Lapis's seven-stage plan should resist the
   temptation to build everything at once; Coal's example shows that the core
   (data + fold + codata + traits) is already a usable language.

## References

- Coal language: [coal-lang.org](https://coal-lang.org/), [source on Codeberg](https://codeberg.org/laserpants/coal)
- Coal data and codata: [coal-lang.org/data-and-codata](https://coal-lang.org/data-and-codata/)
- Meijer, Fokkinga & Paterson, "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire" (1991) — the "recursion is the goto of FP" motto
- See also: [`why-lapis.md`](./why-lapis.md) §3 (other solutions), [`core-calculus.md`](./core-calculus.md) in `theory/`