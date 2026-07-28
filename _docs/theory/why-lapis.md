# Why Lapis?

> An introductory document on the motivation, rationale, and justification for the Lapis programming
> language. Written to rediscover the original impulse after years of design and false starts, and
> to test it against the hard questions a new language must answer.

## The Feeling

Before the formal argument, the feeling: something _should exist_ that doesn't.

You can write a program in Haskell that uses `foldr` and `map` and composes them with fusion rules
you learned from Squiggol. But the compiler doesn't know your `add` is associative. It doesn't know
your `multiply` distributes over `add`. It can't apply Horner's rule for you. You can _say_ these
things in comments, or in QuickCheck properties, or in Coq proofs — but the language doesn't _hear_
them. The algebra is decoration, not structure.

You can write a program in Charity where fold and unfold are the only recursion, and termination is
guaranteed by construction. But Charity died, because it was too restrictive — no subtyping, no
practical IO, no contracts, no way to exploit the laws it enforced. The structure was there, but it
was a cage.

You can write a program in Scala with Cats and recursion-schemes and type classes, and get partway.
But the recursion schemes are a library, not the language. You can still write unstructured
recursion. The laws are conventions, not guarantees. The fusion is manual, not automatic.

The feeling is: **the Bird-Meertens Formalism should be a programming language, not a theory. And
the reason it isn't yet is that nobody has made the enforcement of algebraic structure _practical_ —
nobody has combined the cage (enforced fold/unfold) with the key (exploitable laws, subtyping,
contracts, IO).**

That is what Lapis is for.

## Atanassow's Test

Frank Atanassow's advice to language designers is brutal and correct. Before building a language,
answer five questions honestly. If the answer to any is "it's cleaner" or "I don't know," stop. What
follows is an honest attempt.

### 1. What problem does this language solve?

**The problem:** Program calculation — deriving correct programs from specifications by algebraic
manipulation — is a well-developed theory (Bird-Meertens Formalism, Squiggol) with no practical
programming language home.

In BMF, you reason about programs as compositions of folds and unfolds, and you _calculate_ correct
programs by applying algebraic laws: fusion, the Horner rule, the scan lemma, distributivity. The
laws are the _method_. A fold that distributes over another fold can be fused into a single
traversal. An involutory operation applied twice cancels. An identity element short-circuits. These
are not optimizations applied after the fact — they are _how you derive the program in the first
place_.

In every existing language, this theory is either:

- **Absent.** Most languages have no notion of fold/unfold as universal arrows, no law declarations,
  no fusion. You write loops and recursion by hand and hope.
- **Optional.** Haskell, Scala, OCaml have recursion-schemes _libraries_. You can use folds, but you
  don't have to. You can write general recursion that violates the algebra. The laws are comments or
  test properties, not language-level facts. The compiler cannot exploit them because it cannot
  trust them.
- **Impractical.** Charity enforced fold/unfold as the only recursion but had no subtyping, no
  contracts, no practical IO, no law exploitation. It was a cage without a key. Coq and Agda have
  the mathematics but are proof assistants, not programming languages — you don't _deploy_ a Coq
  program.

**The precise problem statement:** How do you make a language where (a) the algebraic structure of
computation (fold/unfold, their laws) is _enforced_, not optional, so that the laws are universally
applicable; and (b) that enforcement is _practical_ — with subtyping, contracts, IO, modules, and a
story for law _exploitation_ (optimization), not just law _verification_?

### 2. How can you show it solves this problem?

**Evidence: the `lapis-js` prototype.**

The prototype is not a sketch. It is a working, published, tested implementation that demonstrates
every claim:

- **Enforced structure works.** Fold and unfold are the only recursion forms. General recursion is
  not available. The circular-fold protection guard catches attempts to re-enter a fold on the same
  node. Structural recursion is stack-safe (iterative post-order traversal, not JS call-stack
  recursion).
- **Law verification works.** `properties: [associative, commutative,
  identity:Zero]` on a fold
  triggers automatic sample-based testing at declaration time. A false claim throws `LawError` with
  a counterexample before the declaration enters the module graph.
- **Law exploitation works.** Declared `identity:E` installs a runtime guard that short-circuits the
  fold when the identity element is encountered — no traversal. Declared `distributive:sum` unlocks
  Horner fusion in a `merge` pipeline. Declared `involutory` causes consecutive pairs to cancel in a
  merge. These are not manual optimizations — the compiler applies them from the declarations.
- **Subtyping works.** Comb inheritance (NewtonScript-style dual delegation) gives
  `ExtendedColor <: Color` with inherited and overridable fold handlers. Field narrowing gives
  `NumList <: List` without generics.
- **Contracts work.** Demands/ensures/rescue/invariant with LSP subcontracting (demands OR-weaken,
  ensures AND-strengthen). Fault-tolerant folds where rescue handles per-node failures while the
  traversal continues.
- **IO works.** Mealy machine — pure `{init, request, respond}` data value, async runtime
  interpreter. Sync program, async runtime.
- **Relations and queries work.** `relation` + `closure()` = semi-naive Datalog fixpoint. `query` +
  `explore()` = greatest-fixpoint Prolog-style search with tabling.

The feedback cycle is short: the prototype _is_ the proof of concept, and it runs.

### 3. Is there another solution? Do other languages solve this?

Yes, partially. Here is the honest survey:

| Language       | Enforced structure                           | Law verification          | Law exploitation     | Subtyping                                  | Practical IO                     | Contracts |
| -------------- | -------------------------------------------- | ------------------------- | -------------------- | ------------------------------------------ | -------------------------------- | --------- |
| **Coal**       | **Yes** (fold keyword, no general recursion) | No (laws are conventions) | No                   | No (parametric polymorphism)               | Monadic (`IO<a>`, `do`-notation) | No        |
| Haskell        | No (optional libraries)                      | QuickCheck (library)      | Manual rewrite rules | No (type classes ≠ subtyping)              | Monadic (syntactic burden)       | No        |
| Charity        | **Yes** (fold/unfold only)                   | No                        | No                   | No                                         | No (dead)                        | No        |
| Coq/Agda       | Yes (termination)                            | Yes (proofs)              | Partial (extraction) | No                                         | No (proof assistant)             | No        |
| Scala + Cats   | No (optional)                                | ScalaCheck (library)      | No                   | Yes (but generics, not subtyping-subsumes) | Effect systems (ZIO/Cats Effect) | No        |
| OCaml/ML       | No (optional)                                | No                        | No                   | No (modules ≠ subtyping)                   | No                               | No        |
| Smalltalk/Self | No                                           | No                        | No                   | Yes (prototypes)                           | No                               | No        |
| Erlang         | No                                           | No                        | No                   | No                                         | Actor model                      | No        |
| Prolog/Datalog | No (unification)                             | No                        | No                   | No                                         | N/A                              | No        |

> **Coal is the closest language in spirit** — see [`lapis-vs-coal.md`](./lapis-vs-coal.md) for a
> detailed comparison. Both enforce structural recursion and embrace the bialgebraic duality. The
> critical difference: Coal's laws are conventions ("aren't enforced by the compiler"), while
> Lapis's laws are verified and exploitable declarations. Coal is the "enforcement without
> exploitation" case study — it proves the cage is habitable but doesn't hand you the key.

**No existing language combines enforced algebraic structure with practical law exploitation and a
practical ecosystem.** Charity came closest on enforcement but failed on everything else. Haskell
comes closest on ecosystem but doesn't enforce or exploit the structure. Coq has the math but isn't
a programming language.

**Advantages of Lapis's solution:**

- Enforcement + exploitation together: the laws are _applicable_ because the structure is
  _guaranteed_. You can't write a non-fold that would violate the algebra, so the compiler can trust
  every law declaration.
- Subtyping subsumes generics (Meyer): no type-parameter ceremony, comb inheritance gives subtyping
  for free.
- Contracts not effects (DbC): equational reasoning about obligations, not monadic reasoning about
  plumbing. Blame is binary and local.
- IO as data (Mealy): pure program, no monadic syntactic overhead.

**Disadvantages of Lapis's solution:**

- Enforced structure is restrictive. No general recursion means some algorithms are harder to
  express (though fold/unfold + the advanced schemes cover most cases). This is the same trade-off
  Charity made, and it is the _point_ — the restriction is what buys the guarantees.
- Loss of parametricity (subtyping over generics). Free theorems are gone; laws must be declared
  explicitly. This is a real cost, paid back as explicit algebraic properties.
- Smaller ecosystem. Haskell has 30 years of libraries; Lapis has none. This is the practical
  barrier, not the theoretical one.
- The surface syntax is dense. The Self/Smalltalk message-send style + the recursion-scheme
  modifiers (`<para>`, `<histo>`, `<aux:>`) create a steep learning curve for anyone outside the
  FP/CT audience.

**Advantages of their solutions:**

- Haskell's optional structure means you can _escape_ when fold/unfold are awkward. Lapis doesn't
  let you escape. This is sometimes painful.
- Haskell's monadic IO is well-understood and has massive library support. Lapis's Mealy-machine IO
  is elegant but unproven at scale.
- Coq's proofs are _complete_ — every law is proved for all inputs. Lapis's sample-based law
  checking is _probabilistic_ — it can miss counterexamples. (The "static where possible, dynamic
  when needed" philosophy accepts this trade-off; a future static analysis pass may discharge more
  laws.)

### 4. What is the unique property lacking in others?

**The unique property: enforced structural recursion combined with first-class, verifiable, and
exploitable algebraic laws.**

The two halves are inseparable:

- **Enforcement without exploitation** is Charity — a cage. You can't write general recursion, but
  the compiler doesn't do anything with the structure you are forced to maintain. The laws are
  implicit and unused.
- **Exploitation without enforcement** is Haskell + rewrite rules — a library. You can declare laws,
  but the compiler can't trust them universally because nothing prevents you from writing
  unstructured recursion that violates them. The laws are optional and therefore unreliable.
- **Enforcement + exploitation together** is Lapis. The compiler _can_ trust every law declaration
  because the structure _guarantees_ the law is applicable. `distributive:sum` is safe to exploit
  because every operation on this type is a fold, and every fold respects the algebra. The cage and
  the key are one thing.

**Why this cannot be a library:** Enforcement is a language-level decision. A library cannot prevent
you from writing `fix`. A library cannot make the compiler apply Horner fusion automatically. A
library cannot guarantee that every function on a type is a fold. The _enforcement_ is what makes
the _exploitation_ reliable, and enforcement is the one thing you cannot get from a library.

This is the answer to Atanassow's question 4, and it is the reason Lapis is a language and not a
library.

### 5. What parts are essential to that unique property?

**Essential (remove any one and the unique property is lost):**

1. **Fold and unfold as the only recursion forms.** This is the enforcement. Without it, laws are
   optional and exploitation is unreliable. This is the non-negotiable core — the one thing that
   makes Lapis a language rather than a library.

2. **First-class algebraic law declarations (`properties`).** This is the exploitation interface.
   Without it, the enforced structure is a cage (Charity). The laws must be _declarable_,
   _verifiable_, and _exploitable_ — all three. Remove verifiability and you have unchecked claims
   (Haskell comments). Remove exploitability and you have a theorem prover without optimization (Coq
   without extraction). Remove declarability and the compiler can't know what to verify or exploit.

3. **The bialgebraic duality (data = μ, behavior = ν).** This is what makes the structure
   _complete_. Fold alone gives you consumption of finite structures. Unfold alone gives you
   generation of potentially-infinite structures. Together, they cover the full computational space
   — every program is a composition of folds and unfolds (hylomorphism, metamorphism, etc.). Without
   the duality, you have half a language: you can consume but not generate (or vice versa). The
   duality is what makes "everything is fold/unfold" literally true rather than an aspiration.

**Not essential (could be removed or made library/sugar without losing the unique property):**

- **The surface syntax.** The Self/Smalltalk message-send style is a choice, not the contribution.
  Per Atanassow's advice: "don't indulge in syntax design." The syntax should serve the semantics,
  not be the point. (The current syntax is pleasant and coherent, but it is not _why_ Lapis exists.)

- **Relation, query, IO.** These are sugar. `relation` = data + span projections + Datalog fixpoint.
  `query` = behavior + cospan projections + Prolog search. `io` = Mealy machine data value. They are
  useful and they demonstrate the duality's reach, but they elaborate to data/behavior. They could
  be libraries on top of the core.

- **Contracts (demands/ensures/rescue/invariant).** These are valuable — they provide the
  correctness layer that effects would in another language — but they are not _essential_ to the
  unique property. You could have Lapis without contracts and the fold/unfold enforcement + law
  exploitation would still work. Contracts are the _practicality_ layer, not the _uniqueness_ layer.
  (They could be a library; the reason they are in the language is that they compose with the
  bialgebraic structure — fault-tolerant folds, LSP subcontracting on fold inheritance — in ways
  that a library would struggle to match. But the core contribution stands without them.)

- **The module system.** Bracha's "ban on imports" is elegant but orthogonal. It could be added to
  any language.

- **Subtyping (comb inheritance).** This is _valuable_ — it subsumes generics and avoids
  parametricity loss — but it is not _essential_ to the unique property. You could have Lapis with
  generics instead of subtyping and the fold/unfold enforcement + law exploitation would still work.
  Subtyping is a _design choice_ that shapes the language's character (Meyer's influence), not the
  _reason_ the language exists. (The parametricity cost and its recovery via `properties` is a
  consequence of this choice, not a motivation for the language.)

**The honest answer to question 5:** Three things are essential — enforced fold/unfold, first-class
exploitable laws, and the μ/ν duality. Everything else — the syntax, the sugar forms, the contracts,
the modules, the subtyping — is valuable infrastructure that makes the language _practical_, but
could in principle be refactored into a library or an existing language. The three essentials
cannot, because enforcement is a language-level decision.

## The Asymptotic Argument

Atanassow asks to think about language features in terms of asymptotic complexity — "not of space or
time, but of, well, complexity." A good feature changes complexity from $O(n^2)$ to $O(n)$ or
$O(n \log n)$. It localizes something that was global.

**What does Lapis localize?**

In a conventional language, _algebraic correctness is global_. If you want to know that
`sum(map(double, xs)) == 2 * sum(xs)`, you must reason about the entire composition — the definition
of `sum`, the definition of `map`, the definition of `double`, and their interaction. The proof is
$O(\text{program size})$ in complexity, and it is _global_ — it spans multiple definitions.

In Lapis, the law `distributive:sum` on `double` _localizes_ this fact. The compiler knows, from a
single declaration on a single operation, that `double` distributes over `sum`. The fusion is
automatic. The correctness is $O(1)$ in complexity — one declaration — and it is _local_ — it lives
on the operation it describes.

This is the $O(n^2) \to O(n)$ shift: algebraic reasoning about program composition goes from
"analyze the entire composition" to "cite the law on each component." The laws are the local facts;
the compiler composes them globally.

**What does enforcement buy in complexity terms?**

Without enforcement, the compiler must _verify_ that a function is a fold before applying a law —
this is $O(\text{function complexity})$ analysis, and it may be undecable (does this recursive
function terminate? is it structurally recursive?). With enforcement, the verification is $O(1)$ —
everything is a fold by construction. The enforcement reduces the _compiler's_ reasoning complexity
from "analyze arbitrary recursion" to "trust the structure."

This is the same kind of complexity reduction that type systems provide: without types, the compiler
must analyze the whole program to know if a variable is an int; with types, it's $O(1)$ — the
declaration says so. Lapis does for _algebraic structure_ what type systems do for _types_: it makes
a global property local and declarable.

## What Lapis Is Not

To sharpen the motivation, it helps to state what Lapis is _not_ trying to be:

- **Not "a cleaner Haskell."** Haskell is a fine language. Lapis is not an incremental improvement
  on Haskell's syntax or libraries. It is a different _contract_ with the programmer: the language
  enforces structure that Haskell leaves optional.

- **Not "a practical Charity."** Charity had the right idea (enforced fold/unfold) but no practical
  story. Lapis is not Charity-with-IO — it adds law _exploitation_ (which Charity never had) and a
  practical type discipline (subtyping, not generics) and contracts. The relationship is
  acknowledged, but Lapis's contribution is the _exploitation_, not the enforcement alone.

- **Not "a simpler Coq."** Coq is a proof assistant. Lapis is a programming language. Laws in Lapis
  are _declarations_ that are checked (statically where possible, dynamically when needed), not
  _proofs_ that must be constructed. The philosophy is "static where possible, dynamic when needed,"
  not "prove everything."

- **Not "Smalltalk with ADTs."** The Self/Smalltalk influence is real (message sends, uniform
  access, `self` always in scope), but the contribution is not "Smalltalk syntax on algebraic data."
  The contribution is the bialgebraic structure and the exploitable laws. The syntax serves that.

- **Not "a library."** This is the crucial one. The lapis-js prototype _is_ a library (an embedded
  DSL), and it demonstrates the semantics. But the _enforcement_ — preventing general recursion —
  cannot be done in a library. The prototype _chooses_ not to expose general recursion, but it
  cannot _prevent_ the host language (JavaScript/TypeScript) from using it. The native language is
  what makes the enforcement real and the exploitation reliable.

## The Original Motivation, Restated

Working through the evidence — the prototype, the references, the years of persistence, the design
decisions that survived the false starts — the original motivation emerges as:

> **The Bird-Meertens Formalism describes a way to build correct programs by algebraic calculation —
> composing folds and unfolds, applying laws like fusion and distributivity, deriving the program
> from its specification. This theory has existed for decades. It has never been a programming
> language. Lapis is the attempt to make it one — not by adding folds to an existing language (a
> library), but by making fold and unfold the _only_ recursion, so that the algebraic laws are not
> optional decorations but enforced, verifiable, and exploitable facts.**

The three essentials — enforced fold/unfold, first-class exploitable laws, the μ/ν duality — are the
irreducible core. Everything else is in service of making that core _practical_: subtyping (Meyer)
avoids generic-type ceremony; contracts (DbC) provide correctness without effects; IO as Mealy data
keeps the program pure; the Self/Smalltalk syntax makes the message-send uniform-access model
natural. But strip all of that away and the three essentials remain, and they are the reason Lapis
exists and not a library.

The years of false starts, I suspect, were the search for the practical layer — the subtyping, the
contracts, the IO, the syntax — that would make the cage habitable. The prototype proves it is
habitable. The native language makes the cage real.

## A Note on Honesty

Atanassow's test demands honesty. The honest assessment:

- **The unique property is real.** Enforced structural recursion + exploitable laws is not
  "cleaner." It is a different complexity class for algebraic reasoning — $O(1)$ local law
  declarations vs. $O(n)$ global composition analysis. No existing language provides this.

- **The unique property is essential to the language, not a library.** Enforcement is a
  language-level decision. This survives question 4.

- **The practical layer is not yet proven at scale.** The prototype proves the _semantics_; it does
  not prove the _ecosystem_. The surface syntax density is a real risk. The loss of parametricity is
  a real cost. The sample-based law checking is probabilistic, not complete. These are honest
  disadvantages.

- **The language may still fail.** Charity had the right idea and died. Lapis's bet is that the
  _exploitation_ (law-driven optimization) and the _practicality_ (subtyping, contracts, IO) are
  what Charity was missing. That bet is reasoned but unproven at scale. The prototype is evidence;
  the native language is the test.

What is _not_ in doubt is that the problem is real, the solution is unique, and the essential
features are identified. The rest is execution.

## References

- Bird, R., "An Introduction to the Theory of Lists" (1987) / Meertens, L., "Algorithmics — Towards
  Programming as a Mathematical Activity" (1986) — BMF/Squiggol
- Turi, D. & Plotkin, G., "Towards a Mathematical Operational Semantics" (1997) — bialgebraic
  semantics
- Hutton, G., "Fold and Unfold for Program Semantics" (1998) — fold = denotational, unfold =
  operational
- Meertens, L., "Calculate Universally!" (1995) — program calculation
- Malcolm, G., "Algebraic Data Types and Program Transformation" (1990) — homomorphisms and fusion
- Koopman, P. & Plasmeijer, R., "Efficient Combinator Parsers" (2001) / "Iterative Fold" — the
  Charity lineage
- Cockett, R. & Fukushima, T., "About Charity" (1992) — the enforced-structure precedent
- Meyer, B., "Object-Oriented Software Construction" (1997) — subtyping subsumes generics, Design by
  Contract
- Bracha, G., "Pluggable Type Systems" / "Executable Grammars in Newspeak" (2007) — optional types,
  grammar subtyping
- Atanassow, F., "Before you go off inventing new programming languages..." (LtU) — the test this
  document applies
