# Lapis and Theorem Provers — Position Statement

> **Status:** Working position note. This document states Lapis's relationship to proof assistants
> (Agda, Coq, Lean) precisely: what the enforced data/codata + fold/unfold representation gives
> _for free_, what it _cannot express_, and in which practical niches Lapis can substitute for a
> prover — and where it must hand off. Companion to [`why-lapis.md`](./why-lapis.md) (the defense)
> and [`lapis-vs-coal.md`](./lapis-vs-coal.md) (the sibling-language comparison).

## 1. The Two Machines

Proof assistants and Lapis are different machines, not different points on one axis.

**Provers (Agda, Coq, Lean)** admit arbitrary recursion and arbitrary propositions, then spend
their entire machinery *checking* that the recursion is well-founded and the proofs are
well-formed. Termination checkers, guardedness checkers, universe checks, canonicity proofs — a
proof assistant largely **is** these checkers. The trusted computing base is a small kernel
(~1000 lines); in exchange, arbitrary mathematical claims can be *stated* and *certified*.

**Lapis** never admits anything that would need checking. Recursion is fold/unfold only; the
claim vocabulary is closed. The checkers' work becomes *theorems about the language*:

| Property | In a prover | In Lapis |
| -------- | ----------- | -------- |
| Totality of data code | termination *checker* (a side condition; can fail; needs redesign) | **free by construction** — no recursion except fold |
| Productivity of codata | guardedness *checker* | **free** — no corecursion except unfold |
| Canonicity (closed terms reduce to values) | proved once for the kernel | **immediate** from strong normalization |
| Definitional equality on closed terms | `compute` tactic | **the evaluator itself** — run both sides; both terminate |
| Induction principle | you supply the elimination motive | **fixed by the fold schema** — the motive is the fold's result type |

The last row is the deepest: because *every* data elimination is a fold, every induction is
mechanical — the motive is never a choice. A prover must check that your induction is legitimate;
in Lapis, inductions are legitimate **by grammar**. This is the precise sense in which the
representation constraint (data/codata + fold/unfold only) "gives some things for free": the
properties provers work for are structural facts of Lapis, not obligations checked per program.

The trade is deliberate and symmetric: the same enforcement that makes totality free makes other
things *unrepresentable* (§3). Every row of the table has a mirror-image exclusion.

## 2. What the Cage Gives — and Where Lapis Substitutes in Practice

Can Lapis be used as an alternative to theorem provers, practically? Split by claim type:

1. **Catalog claims** (algebraic laws, `respect:` claims, contracts, fusion conditions). Yes —
   and better than a prover for working code. An O(1) local declaration, screened automatically
   (sampling falsifies with minimal counterexamples; never proves), trusted as an axiom in `E`,
   and immediately **load-bearing**: the compiler exploits it (identity elimination, reassociation,
   fusion, canonicalization). A prover certifies the same claim at high expert cost with no
   executable payoff.

2. **Quantifier-free claims on closed terms.** Decidable *for free*: run the evaluator on both
   sides. The evaluator is a decision procedure **only because** totality is enforced — in a
   general-purpose language this "check" may not terminate.

3. **Schematic universal claims over folds** (the `identity:e` shape, commutativity of a
   two-handler fold). Checkable *algorithmically* by finite schema batteries, precisely because
   the induction motive is fixed by the fold schema — and for finite-domain types, checkable
   **completely** by exhaustive enumeration (a proof, not a screen).

4. **Logic fragments as data.** `relation`/`query` already make Lapis a Datalog engine
   (semi-naive fixpoint over proof trees as a μ-type); microKanren is under evaluation for
   unification-based search (#35). An embedded logic checker is itself a fold — and its totality
   is guaranteed, where a general-purpose implementation of the same checker would need a
   termination argument.

5. **Arbitrary mathematical claims.** No — not "hard" but **unstatable** natively (§3). The
   design hands off: either deep-embed a logic (TCB moves to the library, §3.2) or export the
   obligation as a lemma for Coq/Agda/Lean and import the certificate (the Model B bridge, §5).

The market observation behind this split: Agda-grade verification has near-zero adoption in
shipped software because its cost profile (expert time × theorem difficulty, paid up front, per
theorem) does not fit working programmers. The middle of the spectrum is unoccupied:

```
unit tests ──► property testing ──► Lapis laws ──► schematic discharge ──► proof assistants
(instances)     (screening)         (screened claims   (Model A+)           (certificates)
                                    + exploitation)
no guarantee ────────────────────────────────────────────────► full certification
```

GHC `RULES` sits at the "exploitation" position **without** the screening — it is Model A minus
the checking, and notoriously able to break programs. Lapis's bet is that vocabulary-constrained,
screened, enforced-only-on-folds claims can occupy the middle tier *trustworthily*: ambient
verification for the code that will never see Agda.

## 3. What Cannot Be Represented in data/codata + fold/unfold Form

The honest boundary, in three parts:

### 3.1 Unbounded, non-productive computation

No `fix`/`Y` means LC captures only total functions. This class is large — F<: subsumes System F,
which contains far more than primitive recursion (Gödel's T, System F ⊇ all functions provably
total in second-order arithmetic, per Girard) — but provably not all computable functions, and
not even exactly all total computable ones (that set is undecidable; no syntax captures it).

**The escape is already in the design:** IO is a Mealy machine — a pure data value
`{init, request, respond}` driven by an external `run()` loop (see
[`elaboration.md`](./elaboration.md) §3.6). Unbounded search generalizes the same way: model it
as a ν-type (`codata Search = solved: Result | next: Self`) and let the runtime be the driver.
Unbounded computation lives **in the driver, outside the calculus** — the same move Coq makes
with extraction, but first-class in Lapis's IO design. The calculus stays total; the runtime is
untrusted in exactly the sense an operating system is.

### 3.2 Propositions with binding and dependency

The real ceiling. `∀n. add(n, e) ≡ n` cannot be *stated* natively — no identity types, no
types-that-mention-terms, no universe. Dependent types are excluded by design (F<:, not Fω or
MLTT; subtyping subsumes generics — see [`design-decisions.md`](../design-decisions.md)).

A logic can be **deep-embedded**: `Formula` and `Proof` (natural-deduction derivations) as
μ-types, `check : Proof → Formula → Bool` as a fold. Because Lapis is total, the checker
terminates — a nontrivial property requiring proof in a general-purpose language. But then:

- **HOAS is unavailable** (functions-in-data would need the very escape hatch the cage closed),
  so embedded logics use de Bruijn indices — first-order encodings only.
- **The TCB moves.** A prover's soundness rests on a small kernel; an embedded Lapis prover rests
  on "the library author was right." That is the irreducible difference in trust architecture —
  Lapis cannot and should not claim kernel-grade certification for embedded logics.

### 3.3 Coinductive proof

Bisimulation on codata is runtime bounded-observation (see [`semantics.md`](./semantics.md) §7.2) —
a heuristic, not a proof. There is no internal coinduction inference rule deriving two codata
equal. This is the dual of the totality gap: data reasoning is *free*, codata reasoning is
*bounded*.

**Summary of the boundary:** partiality (driven outside, §3.1), dependent/HOAS propositions
(embedded at library-grade trust, §3.2), coinductive proof (bounded, §3.3). None of these are
flaws; they are the price paid for §1's free row — and they should be stated as a theorem-shaped
boundary, never glossed as "Lapis can do what provers do."

## 4. The Provenance Ladder (no external certification)

Because claims are catalog-constrained and recursion is fold-shaped, law verification admits a
ladder unavailable to general provers — **without ever adding dependent types**, and without
attaching third-party certificates:

- **`asserted` (screening, the floor):** sample the claim; falsification rejects the declaration;
  passing is evidence, not proof. Authority: programmer-declared axiom in `E`.
- **`discharged` (compiler-established):** three mechanisms —
  1. *Finite-domain exhaustion* (genuinely finite types: the entire input space is checked —
     **proof**);
  2. *Bounded-domain exhaustion* (machine-finite types: `Float`/`Int` are pattern-matched data
     over fixed encodings — binary64 has exactly 2⁶⁴ inhabitants including `Inf`/`NaN`, so
     full-domain enumeration is possible in principle and sub-space enumeration **certifies
     the checked space**);
  3. *Derivation* from primitive laws via fold-induction skeletons (the BMF calculus as the
     discharge engine).
  The theorems were never arbitrary propositions; they are second-order schemas the cage already
  fixed. **No other language can run this ladder this cheaply**, because no other language
  restricts recursion to shapes where induction is algorithmic.
- **`primitive` (language fiat):** builtin operations carry pinned law sets as part of the
  language definition; the TCB is the language implementation — the same trust already granted
  for totality and evaluation. The primitive tier doubles as the **axiom base** for derivations.

**On Rice-style undecidability (corrected):** Rice's theorem proper characterizes partial
computation; it does not directly apply to a total, structurally recursive calculus. Totality
alone does not restore decidability of extensional properties (program equivalence remains
undecidable for expressive total calculi) — but the correct question is *which* extensional
properties of this particular calculus are decidable, and the cage carves out the non-empty
fragments above that no general-purpose language possesses. The undecidability bounds the
discharge fragment; it does not erase it.

**The residual** — laws on unbounded-depth types whose handlers fall outside the derivation
fragment — carries visible `asserted` provenance and is covered by the live-observation channel:
a live system can continuously re-screen declared laws against actual usage and **withdraw** a
falsified axiom at runtime. For this window, observation is the only additional evidence channel
that exists — something neither Coq (batch) nor Haskell (unverified RULES) can offer.

**Rejected:** Model B as external proof-assistant certificates attached to library code. The
trust anchors are the language definition and the programmer's own declarations — the same trust
already extended by using the language at all. Provenance upgrades evidence; it never gates
declaration: no law ever requires a proof to be *declared*.

## 5. Position Statement

**Agda proves programs *correct*; Lapis makes programs *calculable*.** The provers descend from
Martin-Löf (proofs as guarantees); Lapis descends from Bird-Meertens (laws as leverage). These
are complementary lineages, and Lapis's winning move is not beating Agda at theorems — it is:

1. Making verified-and-exploited algebra the **default state** of ordinary code (catalog claims
   at O(1) cost, §2.1).
2. Making the claims provers *are asked about* — "is this fold associative?", "does this rewrite
   preserve meaning?" — answerable by exhaustion and schematic checking (§2.3, §4).
3. **Refusing the certificate game**, not competing in it: the provenance ladder's trust
   anchors are the language definition and the programmer's own declarations; the residual is
   made self-limiting by live observation (runtime re-screening and withdrawal), not by
   external proof.

We never claim: dependent types (excluded by F<:), kernel-grade TCB for embedded logics (§3.2),
unconditional soundness of law-directed rewrites licensed by `asserted` laws (sound relative to
the declared axioms — a false-but-screened law corrupts rewrites; this residual is priced
honestly via visible provenance, the discharge ladder, and live observation).

## References

- Constable, R. L. et al., _Implementing Mathematics with the Nuprl Proof Development System_
  (1986) — proof obligations for quotients/well-definedness; the checking model
- Girard, J.-Y., _Proofs and Types_ (1989) — System F ⊇ provably-total functions of PA²;
  normalization = canonicity's engine
- Bertot, Y. & Castéran, P., _Interactive Theorem Proving and Program Development_ (2004) —
  Coq's extraction model (the "driver outside the calculus" pattern)
- Norell, U., "Towards a practical programming language based on dependent type theory" (2007) —
  Agda's design; termination/guardedness checking
- Peyton Jones, S. et al., "Playing by the Rules" (2001) — GHC rewrite rules: exploitation
  without verification (the cautionary Model-A-minus case)
- Bird, R. & de Moor, O., _Algebra of Programming_ (1997) — the calculational lineage Lapis
  extends