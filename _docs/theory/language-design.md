# Lapis Language Design

> **Status:** Draft v0.1 — living document. Inference rules and design decisions are
> preliminary, intended to be refined through implementation.

## 1. Vision

Lapis is a bialgebraic programming language where **fold and unfold are the primary
control structures**. Data types are initial algebras (μF); behavior types are final
coalgebras (νF). Programs are built by composing folds (consumption) and unfolds
(generation) — the Bird-Meertens Formalism (Squiggol) made into a user-facing
language rather than a library.

The semantic prototype [`lapis-js`](https://github.com/lapis-lang/lapis-js)
demonstrates that this is implementable: ADTs with comb-inheritance subtyping,
final coalgebras with lazy observers, recursion schemes (cata/ana/histo/zygo/para/
hylo/meta), algebraic property annotations with automatic law checking, Design by
Contract with LSP subcontracting, relations (Datalog-style spans), queries
(Prolog-style cospans), and IO as Mealy machines — all composable.

This document series is the transition from embedded DSL to native language: it
formalizes the syntax, semantics, type system, and evaluation model, and defines
an iterative implementation plan.

## 2. Key Design Decisions

### 2.1 Subtyping Subsumes Generics (not Fω)

Lapis avoids parametric polymorphism (generics) in favor of a sufficiently
expressive subtyping discipline. Following Meyer (OOSC) and Bracha (Pluggable Type
Systems), bounded quantification over a subtyping lattice recovers most of what
generics buy you: `NumList <: List` *is* `List<Number>` expressed as a subtype
rather than a type parameter. Comb inheritance + field narrowing is the mechanism.

**Core calculus:** F<: (System F with subtyping) + μ/ν types + guarded fold/unfold
+ qualified types (protocols as bounded constraints). **Not** Fω — no higher-kinded
polymorphism. Protocols are predicates over the subtyping lattice, satisfied
structurally, not type-constructors of kind `* → *`.

**Cost — named explicitly:** Subtyping-over-generics sacrifices *parametricity*
(the free theorems of parametric polymorphism). A function `∀α. List α → Int`
cannot inspect its elements — that's a theorem in F, and it's *false* in F<:.
Lapis recovers parametricity *by declaration* via `properties` annotations: you
state `associative`/`idempotent`/`commutative` as laws precisely because the type
system can no longer derive them for free. This reframes `properties` not as a
nice-to-have but as the price paid for choosing subtyping, paid back as explicit
algebraic laws.

### 2.2 Eager Data, Lazy Codata (invisible to the user)

Data (μ-types) are **eager**: fields are evaluated at construction; instances are
frozen. Codata (ν-types) are **lazy**: continuations are thunks evaluated on
observation; instances can be infinite.

The eager/lazy choice is **not a knob the user turns** — it is fixed by declaration
kind (`data` vs `behavior`). The user picks a *kind*, and the strategy follows.

**Church–Rosser justification:** Within each strategy, confluence guarantees that
reduction order doesn't affect the observable result (for terminating reductions).
This lets the compiler reorder, memoize, short-circuit, and CSE freely *within*
each strategy without changing semantics. The user never sees the difference.

**Boundary the user must know:** data is strict in its fields (constructing
`Push value: f() rest: g()` evaluates `f()` and `g()` now); codata is lazy in its
continuations (`Stream.From(0).tail` is not computed until observed). This boundary
is a *semantic fact* encoded by the `data`/`behavior` keyword, not an efficiency
switch.

**Caveat — codata contracts are observation-gated:** `rescue`/`demands` on a
behavior unfold fire when the observation is forced, not when the behavior is
constructed. If the caller never asks for `head`, the rescue never runs. This is
correct (it matches codata's own laziness) but must be stated as a feature, not a
surprise.

### 2.3 No General Recursion — Only Fold/Unfold

The core calculus has **no general fixpoint operator**. Recursion is exclusively
through:
- **Fold** (catamorphism): structural recursion over data, terminating by
  construction (the data is finite).
- **Unfold** (anamorphism): guarded corecursion generating codata, productive by
  construction (each step produces one observation before recursing).

This is the soundness lever: termination of folds and productivity of unfolds
follow from the F-structure being the termination/productivity measure — no
separate termination checker is needed. This is the sized-types story (Abel)
specialized to the bialgebraic setting.

Advanced recursion schemes (histomorphism, zygomorphism, paramorphism,
hylomorphism, metamorphism) are *elaborations* over the basic fold/unfold, not
core constructs.

### 2.4 Contracts, Not Effects

Following the analysis in [lapis-js#113](https://github.com/lapis-lang/lapis-js/issues/113),
Lapis uses Design by Contract (demands/ensures/rescue/invariant) as the primary
correctness mechanism, not an effect system. The core calculus is **effect-free**.

- `rescue`/`retry` elaborate into `Result`-typed core terms (sum of success/failure
  with a retry counter), not core effects.
- IO is a **Mealy machine** — a pure data value `{init, request, respond}` that a
  runtime interprets. IO is *data*, not an effect.
- The 20% gap (deferred execution, multi-shot continuations, nondeterminism) is
  parked in `query` (codata + search) and future `Amb`, not in an effect type.

The core needs to be sound for pure fold/unfold + contracts-elaborated-to-results
— a much easier Progress/Preservation target than a calculus with effects.

### 2.5 Static Where Possible, Dynamic When Needed

Following the "Static Typing Where Possible, Dynamic Typing When Needed" philosophy
([LtU discussion](http://lambda-the-ultimate.org/node/834); Meijer, Bracha,
Strongtalk lineage):

- **Type soundness** (Progress/Preservation) is static and total — proved for the
  typing of fold/unfold, independent of whether declared laws are true.
- **Law soundness** ("declared laws hold for all inputs") is a *separate* theorem,
  best-effort: the compiler discharges what it can statically, falls back to
  runtime sample-checking (the `LawError` mechanism) for the rest.
- The core calculus carries law *declarations* as constraints, not law *proofs*.
  The checking strategy is a per-law, per-compilation-mode decision.

This leaves room for Lapis as a **Programming Language System** (Smalltalk/DBMS
family): a live-image mode where types and laws are checked at runtime, a batch
compiler that proves what it can and rejects what it can't, or a hybrid. The core
calculus doesn't choose; the *system* does.

### 2.6 No Primitive Conditional — Boolean is Data

The design doc says fold-based dispatch replaces conditionals. To make this
literally true: `Boolean` is a data type with two variants (`True`, `False`), and
`ifTrue:ifFalse:` is an ordinary fold over it. There is no primitive `if` in the
core. The `n = 0 ifTrue: [{}] ifFalse: [...]` in the Stream example is a keyword
message send on a Boolean — a fold, not a language primitive.

## 3. Document Structure

This is the master document. The formal details live in companion documents:

| Document | Contents | Status |
|---|---|---|
| `language-design.md` (this file) | Vision, decisions, structure, implementation plan | Draft |
| [`../users/rationale.md`](../users/rationale.md) | Narrative for prospective users: fold/unfold → totality → laws → Datalog/Prolog → contracts | Draft |
| `why-lapis.md` | Defense (Atanassow's questions): why this language deserves to exist | Draft |
| `lapis-vs-coal.md` | Comparative study with Coal (closest existing language) | Draft |
| `core-calculus.md` | Core calculus (F<: + μ/ν + fold/unfold): design rationale, commentary, elaboration of surface constructs, contracts, Boolean-as-data, open questions | Draft |
| `lc.md` | LC in TAPL style: syntax, evaluation rules, typing rules, subtyping rules, soundness — the formal specification | Draft |
| `semantics.md` | Denotational (fold) and operational (unfold) semantics; bialgebraic laws (Turi-Plotkin); attribute-grammar equations; evaluation strategy; contracts; equality | Draft |
| `elaboration.md` | Surface → core desugaring: relation/query/io → data/behavior; rescue → Result; map/merge/scan → fold/unfold; contracts; properties; subtyping | Draft |
| `grammar-as-semantics.md` | Implementation architecture: grammar subclassing as compiler pipeline, `chain` for one-pass type checking, contracts as inference-rule encoding | Draft |
| `evaluation-model.md` | Eager data / lazy codata; Church–Rosser; graph reduction / super-combinators; GC | Planned |
| `contracts-and-laws.md` | Contract assessment flow; LSP subcontracting; law checking (static + runtime); effects position | Planned |
| `surface-syntax.md` | Railroad diagrams; precedence ladder; indentation strategy; lexical structure; declaration forms | Draft |

## 4. Core Calculus Summary

> Full formal treatment: [`core-calculus.md`](./core-calculus.md)

The core calculus — **Lapis Core (LC)** — is F<: with recursive and corecursive
types, where fold and unfold are the only recursion forms.

**Types:**

```
σ, τ ::= α              type variable
       | σ → τ          function type (blocks, predicates, transforms)
       | μ α. Σᵢ Cᵢ(σᵢ)    recursive data type (sum of named variants)
       | μ α. Σᵢ pᵢ        pattern-matched data type (sum of pattern constructors)
       | ν α. Πⱼ oⱼ(σⱼ)    corecursive codata type (product of named observers)
       | Token           raw matched text (the one non-μ/ν primitive)
       | Any            top
       | Nothing        bottom
       | σ ∧ τ          intersection type (protocol conformance)
```

Base types (`ι`) are eliminated — `Nat`, `Int`, `String`, `Bool`, etc. are all
`μ` types (pattern-matched or named constructors). See
[`core-calculus.md`](./core-calculus.md) §2.1 and
[`design-decisions.md`](../design-decisions.md) §"No base types".

**Terms:**

```
t, u ::= x                          variable
       | λx. t                      lambda (block)
       | t u                        application
       | Cᵢ(t₁, ..., tₙ)            variant construction (data introduction)
       | fold_T t {Cᵢ(xⱼ) → tᵢ}      fold — data elimination (catamorphism)
       | e.oⱼ                       observation — codata elimination (destructor)
       | unfold_T t {oⱼ → tⱼ}        unfold — codata introduction (anamorphism)
       | cofold_T t {oⱼ(xⱼ) → t}     cofold — codata elimination
```

**Key typing rules (preview):**

```
T = μ α. Σᵢ Cᵢ(Fᵢ(α))
Γ ⊢ e : T       Γ ⊢ hᵢ : Fᵢ(σ) → σ   (for each variant Cᵢ)
────────────────────────────────────────────────────────
Γ ⊢ fold_T e {Cᵢ → hᵢ} : σ

T = ν α. Πⱼ oⱼ(Gⱼ(α))
Γ ⊢ s : Σ       Γ ⊢ gⱼ : Σ → Gⱼ(Σ)   (for each observer oⱼ)
────────────────────────────────────────────────────────
Γ ⊢ unfold_T s {oⱼ → gⱼ} : T
```

Where `Fᵢ(σ)` substitutes the fold result type σ for recursive positions in
variant Cᵢ's fields, and `Gⱼ(Σ)` substitutes the seed type Σ for Self in observer
oⱼ's type.

## 5. Iterative Implementation Plan

The plan is staged so a runnable subset appears early, with the type system and
elaboration honest from Stage 1 (avoiding the trap of bolting types onto a working
evaluator after the fact).

### Stage 0: Resolve Foundational Questions (doc-only)

**Goal:** Pin down decisions that are cheap to make and expensive to change.

- [ ] Confirm eager-data / lazy-codata as the evaluation model (§2.2)
- [ ] Confirm Boolean-as-data, no primitive `if` (§2.6)
- [ ] Confirm F<: (not Fω) as the core (§2.1)
- [ ] Confirm contracts-not-effects (§2.4)
- [ ] Draft core calculus typing rules ([`core-calculus.md`](./core-calculus.md))
- [ ] Draft soundness sketch (Progress/Preservation statements)

**Deliverable:** `core-calculus.md` with typing rules and soundness sketches.

### Stage 1: Minimal Core — data + fold + behavior + unfold

**Goal:** Parse → typecheck → evaluate a Stack/Stream example end-to-end.

- [ ] Core calculus: μ-types, ν-types, fold, unfold, observation, lambda, application
- [ ] Type checker: typing rules for the above, subtyping (reflexive, transitive, top, bottom, function, μ/ν width+depth)
- [ ] Tree-walking evaluator (no graph reduction yet): eager data, lazy codata
- [ ] Elaboration: surface `data`/`fold` → core μ/fold; surface `behavior`/`unfold` → core ν/unfold
- [ ] Test: Stack (data + fold), Stream (behavior + unfold + observation)

**Deliverable:** Runnable Stack and Stream programs, type-checked and evaluated.

### Stage 2: Subtyping and Protocols

**Goal:** Comb inheritance, field narrowing, protocol conformance.

- [ ] Subtyping: μ-width (more variants = subtype), μ-depth (field narrowing), ν-width (more observers = subtype), ν-depth (observer widening)
- [ ] Fold inheritance: extended fold = parent fold + new handlers (polymorphic recursion)
- [ ] Protocols: qualified types (`τ satisfies P`), structural conformance checking, `instanceof` across hierarchy
- [ ] `satisfies:` clause in surface syntax
- [ ] Test: ExtendedColor (data extension), Ordered protocol conformance

**Deliverable:** Extended types with inherited operations, protocol conformance checked.

### Stage 3: Recursion Schemes and Composition

**Goal:** map, merge, scan, and the advanced fold modifiers.

- [ ] `map` as elaboration over fold (data) / unfold (codata)
- [ ] `merge` as operation composition (deforestation): unfold+fold (hylo), map+fold (prepro), fold+unfold (meta)
- [ ] `scan` (scan lemma)
- [ ] `<para>` (paramorphism): `old field` — raw pre-fold sub-node
- [ ] `<histo>` (histomorphism): `prev field` — course-of-values
- [ ] `<aux: name>` (zygomorphism): auxiliary fold result
- [ ] Test: Factorial (hylo), sliding-window sum (scan), tree depth+balance (zygo)

**Deliverable:** All recursion schemes as elaborations, fusion rules applied.

### Stage 4: Relation, Query, IO — Sugar

**Goal:** The remaining declaration forms, desugared to data/behavior.

- [ ] `relation` → data + `[origin]`/`[destination]` span projections + auto join-invariant
- [ ] `relation closure()` → semi-naive fixpoint (fused unfold+fold)
- [ ] `query` → behavior + `[output]`/`[done]`/`[accept]` cospan projections
- [ ] `query explore()` → greatest-fixpoint driver with tabling
- [ ] `io` → Mealy machine record `{init, request, respond}` + runtime interpreter
- [ ] Test: Ancestor relation (closure, reachability), PathFinder query, Counter IO

**Deliverable:** All six declaration forms runnable.

### Stage 5: Contracts and Laws

**Goal:** Design by Contract and algebraic property annotations.

- [ ] Contract clauses: `demands`, `ensures`, `rescue` (with `retry`), `invariant`
- [ ] Contract assessment flow: invariant-pre → demands → body → ensures → invariant-post; rescue on throw
- [ ] LSP subcontracting: demands OR-weaken, ensures/invariant AND-strengthen, rescue override-or-inherit
- [ ] `rescue`/`retry` elaboration to `Result`-typed core terms
- [ ] `properties` annotations: closed vocabulary, declaration-time validation
- [ ] Automatic law checking: sample generation, `LawError` on violation
- [ ] Runtime optimization exploitation: identity/absorbing/idempotent guards, involutory cancellation, Horner fusion
- [ ] Test: Stack with contracts, Num with algebraic laws, fault-tolerant tree fold

**Deliverable:** Contracts enforced, laws checked, optimizations applied.

### Stage 6: Graph-Reduction Back End

**Goal:** Replace tree-walking evaluator with graph reduction (super-combinators).

- [ ] Compile core terms to super-combinators (per `TODO.md`)
- [ ] Graph reduction with sharing (lazy codata thunks shared, data nodes shared)
- [ ] Garbage collection
- [ ] Church–Rosser-justified optimizations: CSE, memoization, short-circuiting within each strategy
- [ ] Test: large structures (100k-element list fold — stack safety), infinite streams

**Deliverable:** Efficient evaluator with graph reduction and GC.

### Stage 7: Module System and Language System Mode

**Goal:** Modules as values, optional live-image mode.

- [ ] Module system: `module(spec, body)` — Bracha's "ban on imports" (modules are dependency→export functions)
- [ ] Module contracts: demands/ensures/invariant on module instantiation
- [ ] Module extension: `extend` with LSP subcontracting
- [ ] `system()` — programs as Mealy machines (compose modules → IO program)
- [ ] Live-image mode (research): runtime type/law checking, REPL, incremental recompilation

**Deliverable:** Module system, IO programs, foundation for language-system mode.

## 6. Open Questions

These must be settled before the core calculus is fully well-defined:

1. **Equality.** Structural equality for μ-types (frozen objects); observational
   equality (bisimulation) for ν-types. `instanceof` across the comb-inheritance
   chain does double duty as subtype test and structural identity. Write down `=`
   for μ and `≈` for ν explicitly.

2. **Strictness annotations on data fields.** If a data field needs laziness (e.g.,
   a potentially-infinite structure stored in a data variant), is that an explicit
   type (`Lazy τ` or a `behavior`-typed field), or a silent switch? Recommendation:
   explicit — keeps the eager side total-by-construction.

3. **Parametricity recovery.** How much of the lost parametricity can `properties`
   recover? Is there a static analysis that can discharge some laws from the
   fold/unfold structure alone (e.g., "a fold whose handlers are all projections is
   a homomorphism")?

4. **Observation-gating of codata contracts.** Formalize: `demands`/`rescue` on a
   behavior unfold fire at observation time, not construction time. State as a
   feature.

5. **Fold dispatch model.** Is fold dynamic-dispatch (OO method on variant
   prototype, inherited through comb chain) or static-dispatch (pattern match
   keyed on variant tag)? The prototype uses dynamic; the core calculus needs to
   model this. Affects soundness proof.

6. **Multi-sorted algebras.** Multiple `data` declarations referencing each other
   (cross-sort fields). The core handles this naturally (types reference other
   types), but the elaboration and type-checking need to handle mutual recursion
   and deferred materialization.

## 7. References

- Turi & Plotkin, "Towards a Mathematical Operational Semantics" (1997) — bialgebraic semantics
- Hutton, "Fold and Unfold for Program Semantics" (1998) — fold = denotational, unfold = operational
- Amadio & Cardelli, "Subtyping Recursive Types" (1993) — μ-type subtyping
- Cardelli & Wegner, "On Understanding Types, Data Abstraction, and Polymorphism" (1985) — F<:
- Abel, "Foetus — Termination Checker for Simple Types" (1998) / sized types — termination via structure
- Meyer, "Object-Oriented Software Construction" (1997) — subtyping subsumes generics, DbC
- Bracha, "Executable Grammars in Newspeak" (2007) / "Pluggable Type Systems" — grammar subtyping, optional types
- Meijer & van Drunen, "Static Typing Where Possible, Dynamic Typing When Needed" — LtU
- Darragh & Adams, "Parsing with Zippers" (ICFP 2020) — derivative-parser algorithm
- Wadler & Blott, "How to Make Ad-hoc Polymorphism Less Ad-hoc" (1989) — qualified types
- Jones, "A System of Constructor Classes" (1995) / "Qualified Types" (1994)