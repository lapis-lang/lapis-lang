# Law Testing — the Grammar is the Arbitrary

> **Status:** Draft v0.1. This document specifies the property-based law-testing pattern: how the
> checking of an algebraic law becomes a `forAll` over a grammar-rooted `ValueGenerator`. The
> executable harness lives in [`src/core/law_testing.ts`](../../src/core/law_testing.ts)
> (`DerivativeGenerator` — promoted from the test-local harness, with ∂T-based structural shrinking)
> and [`test/laws.test.ts`](../../test/laws.test.ts) (the "Property-based law screening" section);
> this document is the specification the harness implements.

## 1. The pattern

A law declaration quantifies universally over an operand space:

```
E(⊕) ∋ idempotent:   ⊢ ⊕(a, a) ≡ a     (for all a ∈ carrier)
```

Checking such a claim generatively means instantiating the universal as a property: generate a
well-formed operand `a`, evaluate both sides of the axiom, and compare. The law is then exactly a
property test —

> **A law is a `forAll` over a `ValueGenerator`; the grammar is the arbitrary.**

"Arbitrary" is a noun here, not a dangling adjective: property-testing jargon for the value supplier
behind a property (QuickCheck's `Arbitrary<T>`, fast-check's arbitraries) — the component that
decides which values the property runs on. The slogan is a complete sentence: the grammar plays the
role of the value generator; no hand-written `Arbitrary` is written alongside it.

lang-forma provides the harness natively: `Grammar.toGenerator(options)` yields a `ValueGenerator`
whose `sample(seed)` produces well-formed values of the grammar and whose
`forAll(property, options)` runs the generation/property loop on failure. No third-party framework,
and — because the generator owns the grammar — every sample is syntactically valid by construction,
and every shrunk counterexample stays well-formed.

**Shrinking (∂T-based, issue #64).** The promoted harness (`src/core/law_testing.ts`,
`DerivativeGenerator`) replaces re-generation shrinking with McBride's one-hole contexts:
lang-forma's `GrammarGenerator.shrink` minimizes by re-generating at shallower depths — structurally
smaller, but derived from the GENERATOR, never from the failing value. The ∂T shrinker enumerates
the failing value's context paths (`derivative(T)` over the carrier, `type_algebra.ts`), plugs
strictly-smaller fillers into the holes (the carrier's sampled vocabulary plus the failing value's
own subvalues — reuse), and renders the plugged candidates. The counterexample thus shrinks along
the actual value's structure, monotone toward a minimal falsifier. Counterexamples that do not
evaluate to a structured value (tokens, closures) delegate to the regeneration strategy — a strict
upgrade, never a regression of coverage.

## 2. Rejection quality, not assurance quality

The harness targets **rejection quality**: it falsifies (rejects declarations with a minimal
counterexample) but never establishes. A property that survives N runs is _evidence_, not proof —
for the residual regime (unbounded-depth μ-types) no finite sample space can establish a universal
claim.

This is the authority rule of `E` (see `_docs/design-decisions.md`, "Laws", and `semantics.md`
§5.4): laws entering the theory environment carry a provenance tier (`primitive` > `discharged` >
`asserted`), and sampling-based screening can only ever support the `asserted` tier. Passing runs
install nothing stronger than evidence; a failing run throws `PropertyFailure` with the shrunk
counterexample, and the declaration is rejected outright.

The mirror is the Cartesian sweep of `screenLaw` (`law_checking.ts`): the screen enumerates a
_bounded, exhaustive_ sample space per operand position — now a **certified prefix** (the complete
size-≤ kᵢ class set, counted independently by the type equation's coefficients; `type-algebra.md`
§3). `forAll` complements it with _random_ samples deeper into the space: same
falsify-never-establish contract, different coverage profile (the certificate upgrades the sweep's
claim, not its provenance).

## 3. The generator root problem

The natural instinct is to root the generator at the full `LCEval` grammar — generate random LC
terms, check the law on each. This does not work for law screening, and the reason is worth stating
precisely:

- The law schemas quantify over **operand values of a fixed type** (`a, b, c ∈
  carrier(⊕)`).
- A generator rooted at the term grammar samples the whole term space — which is overwhelmingly
  lambdas and applications (measured: 0 of 100 depth-4 samples evaluated to a data value), not
  carrier inhabitants.

The harness therefore roots a **dedicated value grammar at the operand carrier**: for `Nat`, the
production `nat = Zero() | Succ(nat)` whose semantic action emits the LC source string. The grammar
IS the arbitrary, specialized to the carrier — samples are exactly the law's intended domain, and
embedding them into law instances (`mul(${src}, ${src})`) yields well-typed instances by
construction.

Two implementation notes that the tests depend on:

1. **`@rule` decoration is load-bearing.** Productions must be declared with the `@rule` decorator
   (as the LC grammar does). An undecorated method bypasses lang-forma's recursion-depth machinery,
   and a recursive production would infinitely recurse during generation instead of respecting
   `maxRecursion`.
2. **`sample` throws escape `forAll`.** `forAll` invokes `sample` outside its own try/catch, so a
   `GenerationError` propagates uncaught. The generation budgets (`maxDepth`, `maxRecursion`,
   `maxBacktracks`, `maxSteps`) must stay within the grammar's ability to terminate. For a
   finite-path grammar like the `Nat` value grammar this is trivially satisfied; for the full term
   grammar it required the budgets tuned in `counterexamples.test.ts`.

## 4. Semantics of the property body

The property receives a generated operand source and must decide the law instance. The convention
depends on how closed the generator's domain is — the two mechanisms differ deliberately:

- **Evaluate both sides** of the axiom through the same evaluator (`makeEvalTerm` bound to the op
  fixtures).
- **Open sample spaces skip; closed domains fail loudly.** The residual screen's Cartesian sweep
  draws from a registry-swept sample space that can legitimately contain instances which do not
  evaluate (an ill-typed embedding, an eval-error sentinel); those are sampling artifacts carrying
  no evidence against the law, so the screen skips them (`law_checking.ts`). A dedicated carrier
  grammar like the `Nat` value grammar is the opposite: it generates only well-formed `Nat` sources,
  and well-formed embeddings of them are well-typed by construction. Failure to evaluate there means
  evaluation itself is broken — a parse/eval regression — and must fail the run, never pass
  vacuously. LCEval reports evaluation failures two ways, and `mustEval` rejects both: an empty
  parse forest (`undefined`) and the `EvalErrorValue` sentinel (a proper `Value` subclass that would
  otherwise flow into the comparison and be reported as a falsification).
- **Throw, don't return `false`, for non-falsifications.** `forAll` reports both failure modes as
  `PropertyFailure`, but they mean different things: `false` is a mathematical falsification (the
  shrunk counterexample is the artifact), while a thrown error's message becomes the failure reason
  ("law instance did not evaluate: …") — an environment/tooling bug, not a law claim to reject.
  Keeping them distinct preserves the rejection signal's meaning.
- **Compare structurally** with `valueEquals` — the same comparison primitive the screen uses, so
  the two mechanisms agree on what "holds" means.

## 5. The worked example

The harness's two anchor laws (see `test/laws.test.ts`):

| Law                 | Property                                                    | Verdict                                                                        |
| ------------------- | ----------------------------------------------------------- | ------------------------------------------------------------------------------ |
| identity fold       | `fold [Nat] e { Zero() -> Zero(), Succ(p) -> Succ(p) } ≡ e` | holds for every generated `e` — 200 reproducible runs pass                     |
| idempotent on `mul` | `mul(a, a) ≡ a`                                             | falsified; shrunk counterexample `Succ(Succ(Zero()))` (2 — `mul(2,2) = 4 ≠ 2`) |

The falsification demonstrates the rejection-quality contract end to end: `Zero()` and
`Succ(Zero())` satisfy the axiom (0·0 = 0, 1·1 = 1); the first falsifier found at seed 42 is shrunk
by re-generation at shallower depths to the minimal violator `Succ(Succ(Zero()))`. Fixed seed ⇒ the
failure is reproducible — the shrunk counterexample is a permanent, minimal reproducer, which is
exactly the artifact a law declaration's rejection should carry.

## 6. What this is not

- **Not establishment.** No number of passing runs upgrades `asserted` to `discharged`. The
  discharge mechanisms (exhaustion, BMF derivation) are separate work built on the same generator
  substrate.
- **Not exploitation.** The law-driven rewriting/optimization (identity elimination etc.) is the
  `E`-side machinery; this harness is the verification side. The two meet at the declaration
  boundary: `forAll` decides what enters `E`, the exploit consumes what `E` contains.
- **Not type-level law checking.** The generator here produces term-level operands. Type-level laws
  (a `LCTypeCheck`-rooted generator) would follow the same pattern with a type grammar root.
