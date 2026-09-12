# Lapis vs Verse: A Comparative Study

> [Verse](https://dev.epicgames.com/documentation/en-us/uefn/verse-language-reference) is Epic
> Games' language for UEFN/Fortnite, designed by Simon Peyton Jones, Daan Leijen, and Simon Marlow
> with Tim Sweeney's two-decade design trajectory behind it. It is not a total functional language
> and shares no lineage with Lapis — but it is the most credible recent example of a
> logic-functional language reaching a mass audience, and its terms-only conception of types is
> the strongest existing contrast with Lapis's types-as-shapes foundation. This document compares
> them honestly: where they converge, where the foundations are incompatible, and why.
>
> Sources: the Verse Calculus paper ("A Unified Calculus for Verse," Peyton Jones, Leijen,
> Marlow, et al., 2023); Sweeney's "The Next Mainstream Programming Language" (POPL 2006 invited
> talk); Sweeney's 2003/2002 LtU/mailing-list writings on Ontic and type inference; Paul Snively's
> LambdaConf 2025 "Chapter and Verse" overview; the λℵ (Lambda-Aleph) paper (Sweeney et al.,
> Intel). Where this document disagrees with secondary sources, the primary papers win.

## The Lineages

The two languages descend from opposite wings of the same 1980s–2000s program-derivation era:

- **Lapis** descends from Bird–Meertens: types are initial algebras/final coalgebras; programs are
  homomorphisms (folds/unfolds); laws are the calculation rules. The lineage is *algebraic*.
- **Verse** descends from Sweeney's twenty-year arc through **Ontic** (McAllister's
  set-theoretic logic language — types as predicates, `either` as committed choice), **λℵ**
  (Sweeney's proto-Verse at Intel: a single-term language where types are identity functions over
  values), and **CUE**-style value lattices, arriving at an *untyped* unified calculus in which
  success/failure, unification, and lenient evaluation are ambient. The lineage is
  *logical/set-theoretic*.

Both are "everything is data/relations" answers to mainstream languages. Neither descends from the
other; the convergence points below are independent arrivals.

## Where They Converge

Two independent convergences worth recording, because they validate design instincts:

1. **No primitive conditional.** Verse's `if` is not a boolean test — the condition is a
   pattern/goal that *succeeds or fails*, and failure is the branching mechanism. Lapis's
   `ifTrue:ifFalse:` is a fold over `Bool = μ α. (True | False)` — branching is elimination. Two
   opposite lineages (failure-as-control vs elimination-as-dispatch) arriving at "no primitive
   `if`" from completely different directions.
2. **Totality as a property worth engineering for.** Verse encodes it per-effect (`<converges>` vs
   `<computes>`); Lapis has it unconditionally. But both treat termination as a *designed-in
   property*, not an accident — and both have explicit machinery for reasoning about which
   programs have it.

## The Fundamental Contrast: Types as Predicates vs Types as Shapes

This is the irreducible difference, and it is not a style choice — the two conceptions are
*mathematically different objects*.

|                       | Verse / Ontic / λℵ                         | Lapis                                             |
| --------------------- | ------------------------------------------ | ------------------------------------------------- |
| A type **is**         | a set of values (often a fallible identity function — `is 2 (a-number)` succeeds) | a **shape**: `μF` / `νG` — an initial algebra / final coalgebra of a functor |
| Membership           | primary — types are executed as predicates  | derived — pattern-matched data runs a fold over the token |
| Recursion principle  | none intrinsic — sets have no recursion structure | **definitional** — fold/unfold are the recursion *principles* of the shape |
| Type checking        | executing the predicate (undecidable in general — λℵ proved this) | structural, on derivations (decidable — F<:)     |
| What it buys         | open-world verification; `is`; "no power granted to the designer that isn't granted to the user"; a planned verifier written in Verse | unconditional totality; mechanical induction; the law-discharge fragment; the cost algebra |

**Why it is incompatible as a foundation for Lapis:** a set has no recursion structure; a functor
has no membership test. T-Fold is only well-defined because `F_i` is *generative* — the fold
handler types come from the functor's structure. Over "the set of even integers" there is no
`F_i` to extract, no recursion tree, no catamorphism, and therefore no bialgebra, no fold-based
laws, no `≡`-licensed optimization. The terms-only foundation does not complicate Lapis — it
*deletes the thing Lapis exists to build*: the chain **enforcement → homomorphism → law →
exploitation** has no first link.

**The historical caution:** λℵ *was* the terms-only foundation, done seriously — and its own paper
reports the wall: set-theoretic semantics "unfortunately not realisable on a conventional
computer," function equality undecidable, type checking undecidable, multivaluedness vs effects
unknown. Verse survived by retreating to an untyped core, demoting totality to a per-effect
property, and deferring the proof story to a sublanguage plus a future verifier. That is not
terms-only winning — that is terms-only buying open-world expressiveness with undecidability, and
then re-purchasing tractability elsewhere.

**The honest counterpoint:** Lapis's shapes cannot express `is 2 (a-number)`-style open-world
membership — conformance questions are answered by structural rules plus runtime folds
(`instanceof`, contracts, law screens), not by executing a type. The shape discipline is a closed
world. That is the price Lapis pays, and it is real.

## Where the Architectures Diverge

### 1. Ambient vs Stratified

| Concern  | Verse (ambient — in the calculus)                | Lapis (stratified — as data/fragments)                     |
| -------- | ------------------------------------------------- | ---------------------------------------------------------- |
| Failure  | an effect (`<decides>`); failing `if` = branching | a value (`Result`-typed contract elaboration)              |
| Logic    | unification + backtracking everywhere            | `relation`/`query` sugar: fixpoint fragments over μ/ν       |
| Time     | `<suspends>` + `sync`/`race`/`spawn`             | outside the core — Mealy-machine IO, runtime as driver     |
| Mutation | `var` under mandatory `<transacts>` (rollback)   | none in the core (eager data is frozen; codata is lazy)     |
| Choice   | `1 | 0 | 1` multivalues, `all`/`one`, committed choice | none — a choice is just a sum type; enumeration is a fold  |

Verse's answer to the expressiveness/control trade: **put everything in one unified calculus and
track it with a fixed, closed effect vocabulary** (no user-defined effects — so the guarantee
cannot be subverted, the same instinct behind Lapis's closed law vocabulary). Lapis's answer:
**keep the core minimal; make everything else data (Result, Mealy) or a stratified fragment
(relation/query)**.

**Honest assessment:** Verse's approach is more *expressive per core-concept* — one mechanism
(success/failure) covers branching, logic search, and choice. Lapis's is more *analyzable* —
nothing in the core needs an effect row, and every layer outside it is data the compiler can
treat uniformly (screen it, cost it, exploit its laws). Verse needs confluence proofs for its
lenient reduction (still in progress); Lapis inherits confluence from eager/lazy standard results
within each strategy.

### 2. Totality: per-effect vs unconditional

Verse: `<converges>` marks a guaranteed-terminating *sublanguage* — suitable, by design, for
formal proof via Curry–Howard, with a planned verifier written in Verse itself. The full language
(`<computes>`) may not terminate. **Totality is opt-in, per annotation.**

Lapis: totality holds for the whole language by construction. There is no `<computes>` fragment
because there is nothing else. **Totality is the ambient property**; the cost algebra then
*certifies feasibility* within it (#52).

This is the deepest practical divergence: Verse can write the busy-beaver program (and flag it
with `computes`); Lapis cannot write it at all (but flags Ackermann-shaped *cost* growth).
Neither answer dominates — Verse trades totality for open-endedness, Lapis trades open-endedness
for totality — but they make the two languages suitable for different programs.

### 3. Law story: absent vs central

Verse has no algebraic-law machinery: no declared properties, no equational theory, no
rewrite-based exploitation, nothing corresponding to `≡`/`↝`. Its verification energy is aimed at
the *type/predicate* level (the planned verifier) rather than the *algebraic* level. Lapis's
entire thesis is that the algebraic level is the exploitable one. The exploitation tier remains
unoccupied by even a Haskell-royalty-designed modern language — Coal's laws are conventions,
Verse's are absent, GHC RULES are exploitation-without-verification. This is the clearest
statement of Lapis's open lane.

### 4. Types: inference humility vs subtyping

Verse deliberately avoids Hindley–Milner (Sweeney concluded as early as 2002 that inference
research "dead-ends around... Haskell" and that unification was the more promising export).
Types are checked where written, inferred where obvious — a usability choice for a mass audience.
Lapis also rejects HM, but by *subsumption*: subtyping (bounded quantification, comb inheritance)
replaces type parameters. Both languages land on "no full HM" from opposite directions — Verse for
usability at scale, Lapis for a semantic principle (Meyer). Notably, both use unification-like
machinery *inside* rather than on top: Verse in the logic engine, Lapis in the type-registry
lookups and the prospective microKanren work (#35).

### 5. Audience and deployment

Verse is a *production* language: hundreds of thousands of Fortnite creators, a $32B company
betting on a billion-user metaverse, an open standard as the goal, a Haskell reference
implementation pending release. Lapis is a *research thesis*: a prototype proving that enforced
fold/unfold + exploitable laws is realizable. Verse optimizes for the working scripter; Lapis for
the calculation. These are different jobs, and the comparison should not pretend otherwise.

## What Each Can Learn (Without Adopting)

**Lapis can take, as confirmations or runtime-layer ideas:**
- The *phase distinction* framing (Snively's reading of Sweeney): terms vs types is really
  elaboration-time vs runtime. Lapis already does this implicitly — contracts-as-terms, laws
  screened by running programs, `instanceof` as a runtime fold, live-image re-checking. The
  Verse insight licenses stating it explicitly: **types-as-shapes govern elaboration;
  types-as-predicates (contracts, law screens) govern the live runtime.** The live system is what
  makes that one language rather than two.
- The closed-vocabulary instinct (`no user-defined effects` so guarantees can't be subverted)
  rhymes with Lapis's closed law vocabulary — recorded as convergent design evidence.

**Verse-style terms-only is not adoptable as a Lapis foundation** — per the §"Fundamental
Contrast" above. An Ontic-style `is` predicate is expressible *as a library fold* in Lapis (a
total, fold-based membership test — stronger than Verse's `<decides>`, which cannot promise its
own predicates terminate), which is the compatible residue of the idea.

**Verse could take (if it ever wanted a law story):** the pattern that laws must attach to
*shapes the compiler trusts* (folds), not arbitrary functions — the Coal post-mortem applies
there too. Nothing in Verse's calculus gives a fold analog to hang laws on; that absence is why
the exploitation tier is open.

## Summary Table

|                            | Verse                                     | Lapis                                             |
| -------------------------- | ----------------------------------------- | ------------------------------------------------- |
| Lineage                     | Ontic → λℵ → unified untyped calculus     | Bird–Meertens → bialgebraic μ/ν core             |
| Types                       | predicates (sets), executed               | shapes (μF/νG), structural                        |
| Core                        | untyped; effects fixed (`decides`, `transacts`, ...) | typed F<: + μ/ν; effect-free                      |
| Totality                    | per-effect (`converges` sublanguage)      | unconditional (the whole language)               |
| Branching                   | failure (goal-driven)                     | elimination (fold over `Bool`)                   |
| Logic                       | ambient unification/backtracking          | stratified `relation`/`query` fragments          |
| Failure                     | effect                                   | data (`Result`)                                  |
| Time/concurrency            | `<suspends>`, `race`/`spawn`             | external Mealy driver; runtime                   |
| Laws                        | none                                      | central: `E`, `≡`, provenance ladder, `↝`         |
| Algebraic exploitation      | none                                      | identity elimination, fusion, reassociation     |
| Cost analysis               | none                                      | cost algebra, certified/flagged (#52)            |
| Audience                    | millions of creators (production)         | PL research (thesis experiment)                  |
| Status                      | shipped subset in UEFN; calculus in progress | prototype; core + laws in development       |

## The One-Sentence Positions

- **Verse:** one unified calculus, conservative syntax, types-as-predicates at the edges,
  totality where annotated — built to let a million strangers' code interoperate in a live world.
- **Lapis:** one minimal shape calculus, everything else as data, types-as-shapes at the
  foundation, totality everywhere — built to make algebraic structure enforced, verifiable, and
  *exploitable*.

They are not rivals; they are opposite ends of the same era's ambition — Verse asks "how much can
one unified calculus express safely for everyone," and Lapis asks "how much can one enforced
structure buy for the compiler." The comparison's value is calibration: Lapis's lane (law
exploitation) is empty in both directions.