# PBI #65 — Coefficient-Certified Screen Coverage: Implementation Plan

> **Status:** Implemented (337 tests green — `deno check` / `test` / `lint` / `fmt` clean). Two
> deviations from this draft surfaced during implementation, both noted in §7/§8 below: (1) the
> mutual-fixpoint iteration needed the "currentFor" discipline (recursive fields read the carrier's
> previous round through the memo — a naive recursive solve diverges), and the strictly-alternating
> system (A = mkA(B), B = mkB(A)) turned out to have NO finite inhabitants at all — the honest
> zeros, not the alternation-counting series the draft's test guessed; (2) the budget interplay
> pinned a RAISE_LIMIT probe (2·MAX_SCREEN_SIZE+1) for carriers whose smallest class sits beyond
> MAX_SCREEN_SIZE, and carriers whose raised class exceeds PREFIX_BUDGET (e.g. the 18-Bool record,
> 2¹⁸) now decline loudly instead of installing `asserted` on a masquerading sample — the risk in §8
> realized and resolved toward strictness (as D2's fallback anticipated). Implements the acceptance
> items of [issue #65](https://github.com/lapis-lang/lapis-lang/issues/65): `coefficients(T, k)`
> from the type equation, and the residual screen's upgrade from an opaque instance count to a
> **certified prefix**. Design source: [`type-algebra.md`](./theory/type-algebra.md) §3. Companion
> PBIs: #62 (declared encodings — the pattern language-equation reading lands there), #63 (the
> `derivable` regime — shares the provenance plumbing, not this module).

## 1. Summary

The residual screen (`screenLaw`) enumerates a bounded sample space per operand position and reports
"checked N instances" — an opaque count that cannot distinguish full-prefix coverage from an
enumeration hole. This PBI makes the coverage a **theorem**: `coefficients(T, k)` computes
$c_0 \dots c_k$ (inhabitants of size $n$ = constructor-node count) **independently from the type's
generating function**, the screen enumerates the full size-≤ k prefix per position, and the two
counts are asserted equal. The coverage report states the theorem:

> all inhabitants of size ≤ k per operand position — exactly N, verified.

A mismatch between the enumerated sweep and the computed coefficients is a loud
`LawDeclarationError` — an enumeration hole would otherwise masquerade as full-prefix coverage.

The motivation is concrete in the current sampler: for a carrier `Zero() | One(b: Bool)`, the screen
samples `One(True())` **only** (`construct` takes `fieldSamples[0]`), so `One(False())` is never
exercised; for a branching carrier (`Leaf | Node(l, r)`) the depth-2 sweep contains one size-5 tree
while omitting the other. Neither sweep can state a size-prefix theorem. Certification requires the
sampler itself to become a size-bounded complete enumerator.

## 2. Current state

| Piece                          | Where                                                | Note                                                                                                                                                                                                                                     |
| ------------------------------ | ---------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Residual screen                | `screenLaw` (`law_checking.ts`)                      | Depth-bounded sampler (`samplesFor`, `MAX_SAMPLE_DEPTH = 2`); `checked` count is the only coverage measure — **implemented: the certified prefix replaced the depth-bounded screen path, and its dead `maxDepth` parameter was removed** |
| Regime routing                 | `screeningRegime` (`law_checking.ts`)                | Exact sweep arithmetic over per-position exponents; `finite` → exhaustion, else residual — **unchanged by this PBI**                                                                                                                     |
| Exhaustion (the finite regime) | `exhaustLaw` + `inhabitantsOf`/`cartesian`/`spaceOf` | Lazy full-space enumeration with per-type memo — the machinery the size-bounded enumerator generalizes                                                                                                                                   |
| Counting reading               | `finiteInhabitants` (`law_checking.ts`)              | Saturating count; recursive/function/`Any` fields ⇒ unbounded                                                                                                                                                                            |
| Contexts reading               | `derivative(T)` (`type_algebra.ts`)                  | `ContextSpec` shapes, implicit differentiation at the μ-bound                                                                                                                                                                            |
| Size measure                   | `valueSize` (`law_testing.ts`)                       | Node count: variant = 1 + Σ field sizes; tokens/atoms = 1                                                                                                                                                                                |
| Pattern samples                | `patternSamples` (`law_checking.ts`)                 | The singleton name-token per pattern type (the size-1 prefix)                                                                                                                                                                            |
| Coefficients                   | —                                                    | Does not exist                                                                                                                                                                                                                           |

**The gap this PBI closes.** `type-algebra.md` §3 claims the depth-bounded sampler "already
enumerates exactly the c≤2 prefix". That holds **only for chain carriers** (Nat, List: depth d ⇒
exactly the sizes 1..d+1). For branching carriers the depth sweep is neither a prefix nor complete
within size classes; for wide-flat records it takes one field sample per variant. The coefficient
reading requires a sweep whose space is a genuine size prefix.

## 3. Design decisions

### D1 — Module placement: the third reading joins its siblings

- **`type_algebra.ts` (pure type level)** — `coefficients(type, k)`: the coefficient reading of the
  type equation. No evaluator, no values; fully unit-testable. This completes the "one module, three
  readings" consolidation the #64 plan anticipated (count lives in `law_checking.ts` as
  `finiteInhabitants`, contexts in `type_algebra.ts`, coefficients now beside contexts).
- **`law_checking.ts` (value level)** — the size-bounded enumerator, the per-position certification,
  and the coverage report, next to the sweep machinery they certify.
- Exports via `src/core/index.ts`.

### D2 — The certified prefix is SIZE-based, not depth-based (the central decision)

The theorem we want: "checked **all** inhabitants of size ≤ k per operand position". Size =
`valueSize`'s node count — the measure already used by the ∂T shrinker, so the certificate and the
shrinker agree on what "smaller" means. Today's sampler is depth-bounded, which is a different axis:
the screen is upgraded to enumerate the **full size-≤ kᵢ class set** per position.

Alternatives considered and rejected:

- **Depth-certified (mirror recurrence).** Keep the sampler; compute the count its construction
  _would_ produce from a recurrence that encodes the sampler's shape (one sample per recursive
  variant per shallower sample). Honest, zero regression risk — but the theorem is about the
  _sampler_, not the _type_: it couples the certificate to the depth sampler's internals (a sampler
  change silently re-bases the theorem) and cannot state the size-prefix claim for branching
  carriers at all. Rejected: the certificate must be sampler-independent to be worth anything.
- **Both samplers (certified where feasible, depth-sampled elsewhere).** Preserves today's
  screenable universe but keeps two mechanisms and lets the uncertified positions keep masquerading
  (labeled, not silent). Held as the fallback if the strict decline (below) proves too aggressive in
  practice — see §8.

### D3 — The kᵢ policy: bounded, complete, per position

For operand position i with carrier type T:

1. Compute the smallest nonempty size class $\min S(T) = \min \{ n \mid c_n > 0 \}$ (via
   `coefficients`).
2. Let $\text{prefix}(k) = \sum_{n \le k} c_n$. Candidate
   $k_i = \min(\text{MAX\_SCREEN\_SIZE}, \max \{ k \mid \text{prefix}(k) \le \text{PREFIX\_BUDGET} \})$,
   **raised to** $\min S(T)$ when $\min S(T) > \text{MAX\_SCREEN\_SIZE}$ (the wide-record escape:
   without it every record wider than three fields would decline — a
   `Triple(a: Bool, b: Bool,
   c: Bool)` has no inhabitants below size 4).
3. If the raised $k_i$'s prefix exceeds `PREFIX_BUDGET`, or the **projected sweep**
   ($\prod_i \text{prefix}(k_i)^{\text{exponent}_i} \times \text{instancesPerAssignment}$ — the same
   exponent arithmetic `screeningRegime` runs) exceeds `SWEEP_BUDGET`, the certification
   **declines**: `LawDeclarationError` naming the blocking size class and its count. Honest zero —
   today such a law installs `asserted` on ~1 masquerading instance; after this PBI it is rejected
   with a diagnostic pointing at the exhaustion route.
4. Constants: `MAX_SCREEN_SIZE = 3` (parity with today's chain reach: `MAX_SAMPLE_DEPTH = 2` ⇒ sizes
   ≤ 3 — chain-carrier sweeps keep their current counts exactly); `PREFIX_BUDGET = 2⁸`,
   `SWEEP_BUDGET = 2¹⁶` (measured constants, the same discipline as
   `MAX_FINITE_INHABITANTS`/`MAX_EXHAUSTION_INSTANCES`; tuned at implementation time with timings
   recorded in this document).

### D4 — Coefficients from the type equation, never from the enumeration

The certificate's value is **independence**: the coefficients are computed by a different method
than the sweep, so agreement is evidence about the world, not about the sampler.

The GF reading of the `Type` AST (size = `valueSize`'s node count):

$$T(x) \;=\; \sum_{\text{variants } C_i} x \cdot \prod_{\text{fields } j} G_{ij}(x)$$

where the field's generating function $G_{ij}$ is:

| Field type                                                        | $G_{ij}$       | Rationale                                                                                             |
| ----------------------------------------------------------------- | -------------- | ----------------------------------------------------------------------------------------------------- |
| recursive (`Field.isRecursive`)                                   | $x \cdot T(x)$ | a subtree of the carrier                                                                              |
| another data type $B$                                             | $B(x)$         | the field's own class (chain rule)                                                                    |
| pattern type                                                      | $x$            | the singleton token (declared fallback, D6)                                                           |
| function / `Any` / `Nothing` / `Token` / `TypeVar` / intersection | $0$            | the variant contributes nothing — the same unsampleable rule `construct` and `screenableDomain` apply |

**Truncated fixpoint, no equation solving.** Represent each type's GF as an array $c_0 \dots c_k$;
iterate all equations of the (possibly mutually recursive) system from zero vectors until fixpoint
up to degree $k$ — each round the minimal nonzero degree of a productive system advances, so ≤
$k{+}1$ rounds; cycles that never become productive converge to zeros (honest: the variant is
unsampleable). Saturating arithmetic at a named ceiling — declared encodings (#62) will bring counts
like $2^{64}$, past `Number.MAX_SAFE_INTEGER`; past the ceiling a prefix certifies only up to the
ceiling, loudly.

The rational/algebraic split `type-algebra.md` §3 asks the design to state falls out for free: chain
types (`Nat`, `List`) yield linear recurrences (rational GFs, Chomsky–Schützenberger for patterns
later), branching μ-types yield the quadratic/Catalan-shaped iteration — one mechanism, no closed
forms, no per-type case analysis. The same "differentiate/differentiate-equation directly, never
solve" discipline `derivative` established.

### D5 — Holes change sides: construction loud, evaluation skippable

- **Sample-construction failures now reject.** The certified prefix claims the sweep HOLDS all $N_i$
  samples; a variant whose constructor fails to evaluate is a hole in the certificate, so the
  declaration is rejected (`LawDeclarationError`) — the same completeness rule exhaustion applies.
  This deliberately kills the sampler's silent drop ("the sampler drops it" in `construct`).
- **Instance-evaluation holes stay skippable.** `checkInstance`'s `"nonEval"` → skip keeps its
  evidence semantics: the samples are certified, the instances drawn from them may still not
  evaluate, and `checked` remains the honest instance count. The zero-coverage rejection in
  `declareCheckedLaw` is unchanged and still the backstop.

### D6 — Pattern carriers: the declared fallback, language equations deferred

> **Superseded by the pattern language-equation reading (#62, implemented).** The singleton-token
> fallback below was a stopgap; pattern types now get their coefficients from their language
> equations (`pattern_lang.ts` — concatenation multiplies, alternation sums, Kleene star inverts
> $(1-P)$), and token size is the text length. The rest of this PBI's machinery (certified prefix,
> saturation, budget declines) is unchanged.

A pattern type's certified prefix is its **declared fallback**: the singleton name-token
(`patternSamples` already produces exactly this), so $c_1 = 1$ when the pattern set is nonempty and
all coefficients are 0 otherwise (empty pattern set ⇒ the existing decline path). The
language-equation reading (concatenation multiplies, alternation sums, Kleene star inverts $(1-P)$)
needs the pattern as a first-class surface AST — that is #62's declared encodings/alphabet machinery
(v0.4.0's pattern work feeds it). The fallback is honest: the certificate states exactly the
singleton prefix the sweep exercises.

### D7 — Provenance is UNCHANGED: certification upgrades evidence, not authority

Certified coverage is still **evidence, never proof**: the residual screen continues to install
`asserted`. `discharged` means full coverage — the prefix is partial by construction for unbounded
types, and the finite regime already discharges via `exhaustLaw` (whose full sweep this PBI does not
touch). Nothing in the provenance ladder, `screeningRegime`'s routing, or `E`'s semantics changes.
The upgrade is strictly to the _coverage claim_ the screen's evidence carries.

### D8 — The coverage report

`ScreenOutcome` gains the certificate (a breaking shape change — the two raw-screen shape assertions
in `test/discharge.test.ts` are updated):

```ts
{ outcome: "passed", checked: number, coverage: CertifiedCoverage }
interface CertifiedCoverage {
    positions: { typeName: string; k: number; expected: number; actual: number }[]
    claim: string // "all inhabitants of size ≤ 3 per position — exactly 3, verified"
}
```

`declareCheckedLaw`'s return gains `coverage` (additive — existing destructures keep working). The
certificate is emitted **before** the schema sweep (fail fast at sample generation), and the
per-position certification is shared by `screenLaw`'s raw entry — no path installs an uncertified
claim.

## 4. Implementation steps

1. **`src/core/type_algebra.ts`** —
   `coefficients(type: DataType | PatternDataType, k: number):
   readonly number[]` (c₀..cₖ,
   saturating; typed rejections — not `undefined` swallowing — for intersection-headed carriers and
   codata, consistent with `derivative`'s boundary rules). Pure; no imports beyond `types.ts`.
2. **`test/type_algebra.test.ts`** — coefficient unit tests (§5).
3. **`src/core/law_checking.ts`** — the size-indexed enumerator
   (`inhabitantsUpToSize(type, k, eval_)`: bottom-up DP over (type, size), reusing the exhaustion
   machinery's lazy-product/memo discipline and `construct`'s evaluate-through-the-evaluator rule);
   the kᵢ policy + certification; `screenLaw` rewired (per-position certification, coverage in the
   outcome); `declareCheckedLaw` plumbs coverage. `samplesFor` stays for the ∂T shrinker's filler
   vocabulary (re-scoping it is out of scope — the shrinker's contract is size-relative already).
   **Post-implementation cleanup:** the dead `maxDepth` parameters on
   `screenLaw`/`declareCheckedLaw` and the `MAX_SAMPLE_DEPTH` constant were removed (the certified
   screen has no depth knob); `samplesFor`/`construct` remain solely as the ∂T shrinker's filler
   vocabulary.
4. **`src/core/index.ts`** — export `coefficients`, `CertifiedCoverage`, `inhabitantsUpToSize`.
5. **`test/discharge.test.ts`** — certification tests (§5); update the two `ScreenOutcome` shape
   assertions.
6. **Docs** — `type-algebra.md` §3 (design → implemented, the split stated) + §7 status table;
   `semantics.md` §5.4 implementation-status paragraph (the screen's coverage is now a certified
   prefix; routing unchanged); `law-testing.md` §2 (the Cartesian sweep's coverage is now certified;
   `forAll`'s random deep samples unchanged); this document's status header;
   `_docs/lc-core-implementation-plan.md` (a PBI #65 pointer entry; fix the stale `#22` status while
   there).

## 5. Tests

**Coefficients (`test/type_algebra.test.ts`):**

- Bool: `c₁ = 2` (the exact product count), `c₀ = 0`.
- Nat: `cₙ = 1` for all n ≤ k (the chain — one inhabitant per size).
- `Pair(a: Bool, b: Bool)`: `c₃ = 4` (a record type's exact count).
- NS (`Zero | One(b: Bool) | Succ(p)`): `c = [0, 1, 3, 3, 3]` — One contributes BOTH field values
  (the coefficient reading sees `One(False)`, which the old sampler never generated).
- Tree (`Leaf | Node(l, r)`): the Catalan shape — `c₁ = 1, c₂ = 0, c₃ = 1, c₄ = 0, c₅ = 2` (the
  algebraic-iteration case).
- A mutually recursive pair (A references B, B references A): the system converges to the hand-
  computed coefficients.
- A variant with a function-typed field contributes 0 (consistent with the sampler's drop).
- Pattern type: `c₁ = 1` (fallback); empty pattern set → all zeros.
- Intersection-headed carrier / codata: typed rejections.
- Saturation: counts past the ceiling saturate loudly (prefix certifies only up to the ceiling).

**Enumerator (`test/discharge.test.ts`):**

- `inhabitantsUpToSize(Nat, 3)` is exactly `{Zero, Succ(Zero), Succ(Succ(Zero))}` — the size prefix,
  deduped, no gaps.
- `inhabitantsUpToSize(Tree, 3)` = `{Leaf, Node(Leaf, Leaf)}` — the size-5 stragglers the old depth
  sampler produced are gone (prefix semantics).
- `inhabitantsUpToSize(NS, 4)` includes `One(False())` — the field-product upgrade.
- Unsampleable variants (function/`Any` fields) absent.

**Certification (`test/discharge.test.ts`):**

- A Nat op's screen: `coverage.positions = [{ k: 3, expected: 3, actual: 3 }]` and the rendered
  claim; provenance still `asserted`; `checked` semantics unchanged (instance-eval holes still
  skipped).
- A mixed op `(Bool, Nat)`: position 0 certified at `k = 1, expected 2`; position 1 at
  `k = 3,
  expected 3`; commutative sweep = 2 × 3 = 6 instances.
- A pattern-carrier op: `{ k: 1, expected: 1, actual: 1 }` (the declared fallback).
- A wide-flat record op (7-Bool record + unbounded co-position): the min-class raise kicks in — the
  record position certifies its full size-8 class (128).
- **The acceptance test:** a registry/evaluator inconsistency that makes one variant unconstructible
  ⇒ the enumerated count (N−1) mismatches the coefficient count (N) ⇒ loud `LawDeclarationError` —
  the enumeration hole no longer masquerades.
- A carrier whose min size class exceeds `PREFIX_BUDGET`: decline with the class named.
- A projection beyond `SWEEP_BUDGET`: decline.
- Existing exact counts unchanged: exhaustion 8/4, pattern screen 1/2, `declareCheckedLaw` return
  shape additive.

## 6. Acceptance mapping (issue #65)

| Acceptance item                                                                                     | Covered by      |
| --------------------------------------------------------------------------------------------------- | --------------- |
| `coefficients(T, k)` — c₀..cₖ from the type equation for regular μ-types                            | Steps 1–2 (D4)  |
| Pattern-type coefficients (declared fallback; later replaced by the language-equation reading, #62) | D6              |
| The screen's coverage report states the certified prefix                                            | Steps 3, 5 (D8) |
| A sweep/coefficient mismatch is a loud error                                                        | Steps 3, 5 (D5) |
| Tests: Bool exact count, record exact count, pattern-carrier prefix                                 | §5              |

## 7. Deferred items — with reasons

- **Pattern language-equation coefficients.** Requires the pattern as a first-class surface (v0.4.0)
  and, for bounded sub-space sweeps, #62's declared encodings/alphabets. The declared fallback
  (singleton token) is exact for what the evaluator can exercise today. **Landed in #62** — the
  language-equation reading is implemented (`pattern_lang.ts`) and replaced the fallback; sub-space
  scopes (the encoding/alphabet declarations as originally imagined were dropped in #62's rescope).
- **`forAll` certification.** The random-sample harness keeps its regeneration/∂T profile — its
  value is _deep_ falsification, not prefix completeness (`law-testing.md` §2: different coverage
  profile, same falsify-never-establish contract).
- **Structural fingerprint assertion** (hashing the enumerated prefix against a GF-derived canonical
  form, beyond counts). Stretch — count equality already catches the realistic hole shapes; revisit
  if a counterexample shows count-equal but set-different sweeps.
- **The `derivable` (#63) and cost (#52) regimes.** Different mechanisms; only the provenance
  plumbing is shared.

## 8. Risks

- **Expressiveness regression (the strict decline).** Carriers whose smallest nonempty size class
  exceeds `PREFIX_BUDGET` (giant flat records) lose their screen entirely — today such laws install
  `asserted` on ~1 masquerading instance. This is deliberate (the same strictness as the
  zero-coverage rejection), and the diagnostic names the blocking class and the exhaustion route.
  Fallback if too aggressive in practice: D2's mixed-coverage alternative (certify what fits, label
  the rest uncertified) — a one-flag switch left to the maintainer's call.
- **Screen instance-count inflation** for field-carrying/wide carriers (`One(False)` appears; a
  7-Bool record position sweeps 128 samples). Bounded by the budget constants; the existing tests
  deliberately avoid pinning screen internals (the `nsOr` test asserts `instances > 0`, not 216), so
  no pinned contract breaks — verified against `test/discharge.test.ts`.
- **Coefficient iteration divergence** on adversarial mutual systems — bounded by construction (≤
  k+1 rounds; each productive round advances the minimal degree; non-productive cycles converge to
  zeros) and covered by the mutual-system test.
- **`ScreenOutcome` shape break** — two test assertions updated deliberately (D8); the type is
  exported, so any external consumer sees a compile error, not a silent change.
