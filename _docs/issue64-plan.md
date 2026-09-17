# PBI #64 — ∂T Machinery: Implementation Plan

> **Status:** Implemented (core acceptance items; stretch deferred — see §7). Implements the first
> two acceptance items of [issue #64](https://github.com/lapis-lang/lapis-lang/issues/64):
> `derivative(T)` over regular μ-types, and ∂T-based structural shrinking wired into the property
> harness. The two stretch items (`old`/paramorphism typing, observation-channel evidence typing)
> are deferred — see §7. Design source: [`type-algebra.md`](./theory/type-algebra.md) §4.

## 1. Summary

Implement McBride's one-hole contexts over the `Type` AST and use them to shrink property-based
counterexamples along the _value's actual structure_ instead of by re-generation. One new pure
module (`type_algebra.ts`), one promoted harness module (`law_testing.ts`), and a measurable quality
win on the existing anchor law test.

## 2. Current state

| Piece                      | Where                                                        | Note                                                                                                                                                                                                       |
| -------------------------- | ------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Counterexample shrinking   | lang-forma `GrammarGenerator.shrink`                         | Re-generates at shallower depths with fresh seeds (`shrinkAttempts` per depth, deduped by structural key). Not structure-derived: it never inspects the failing value.                                     |
| Property harness           | `test/fixtures.ts` (`createLawHarness`), `test/laws.test.ts` | Generator emits LC **source strings**; `forAll`/shrink work on strings.                                                                                                                                    |
| Shrink contract test       | `test/laws.test.ts` ("idempotent on mul is FALSIFIED")       | Pins: minimal violator is `Succ(Succ(Zero()))`, all shallower Nats satisfy. Safe to extend, must not regress.                                                                                              |
| `Type` AST                 | `src/core/types.ts`                                          | `DataType` (μ: variants = sum, fields = product, `Field.isRecursive` marks the μ-bound), `PatternDataType`, `CodataType`, `FunType`, `AnyType`, `NothingType`, `IntersectionType`, `TokenType`, `TypeVar`. |
| Value structure            | `src/core/values.ts`                                         | `VariantVal` (eager fields map) / `TokenVal` (atomic).                                                                                                                                                     |
| `src/core/type_algebra.ts` | —                                                            | Does not exist yet.                                                                                                                                                                                        |

## 3. Design decisions

### D1 — Module placement

`src/core/type_algebra.ts` (issue-designated home), exported from `src/core/index.ts`. Two
cooperating layers, deliberately split:

- **`type_algebra.ts` — pure type level.** `derivative(T)`: structural recursion over the `Type` AST
  producing context _shapes_. No evaluator, no values, no I/O. Fully unit-testable.
- **`law_testing.ts` — value level (harness promotion).** Context _enumeration_ over concrete
  `VariantVal`s, filler generation, plugging, source rendering, and the `ValueGenerator` adapter.
  The harness leaves `test/fixtures.ts`; its generic machinery lands in `src/` (as type-algebra.md
  §4.2 anticipates: "promotion into `src/` rides on this"), with the test-specific
  grammars/evaluator staying in the test fixtures.

### D2 — What "the μ-bound" means in the AST: implicit differentiation for free

The doc's implementation key — differentiate the μ-equation directly, never solve for `T` — is
already encoded in Lapis's AST: `Field.isRecursive` **spells** the μ-bound occurrence. A
self-referential field _is_ an occurrence of the recursion variable, so "differentiate the equation
w.r.t. its own recursion" reduces to ordinary structural recursion over `Type` with recursive fields
treated as hole atoms:

$$\partial_a\, \text{const} = 0, \qquad \partial_a(F + G) = \partial_a F + \partial_a G, \qquad \partial_a(F \cdot G) = \partial_a F \cdot G + F \cdot \partial_a G, \qquad \partial_a\, a = 1$$

No equation solving, no quotient rule. `derivative` never follows a recursive field (that occurrence
_is_ the hole), so the traversal terminates by construction.

### D3 — The derivative's shape: `ContextSpec`, not a synthesized type

The acceptance item says "`derivative(T)` over regular μ-types (structural recursion, implicit
differentiation at the μ-bound)". We return **context descriptions** rather than a synthesized
`Type`:

```ts
interface ContextSpec {
    /** The variant whose field is punched. */
    variantName: string
    /** The punched field. */
    fieldName: string
    /** The hole's type — what plugs into it. */
    holeType: Type
    /** Types of the sibling fields forming the surroundings (Leibniz's "everything else"). */
    surroundTypes: Type[]
}
```

Unfolding rule (the module's core function):

```
derivative(T: DataType) =
  Σ over variants C of T.allVariants()
    Σ over fields f of C
      if f.isRecursive            → ContextSpec { holeType: T (self), surroundTypes: others }
      else if f.type is DataType  → chain rule: the hole may sit inside f's own structure
                                    → ContextSpec { holeType: per derivative(f.type)…, surroundTypes: others }  (see D5)
      else                        → no context (function fields, Any, Token, patterns, Nothing)
```

Rationale for specs-over-synthesis: every consumer (shrinking now; `old` typing and
observation-typing later) needs _which positions can be punched and what surrounds them_ — exactly
the spec. A synthesized context _type_ would immediately need deconstruction back into paths to be
usable. The list/zipper closed forms (∂L = L² etc.) remain derivable from the specs; they are a
rendering choice, not the representation.

### D4 — Value-level shrinking: contexts are paths

A one-hole context of a _concrete_ `VariantVal` is a **path**: the sequence of
`(variantName, fieldName)` steps from the root to a punched field. Enumeration is a plain tree walk
guided by `derivative(T)`'s specs (a path is admissible iff it descends through a spec's hole). For
`Nat`: exactly one spec (`Succ`/`pred`) ⇒ the contexts of `Succ(Succ(Zero()))` are the two `pred`
positions. Sanity invariant for tests: a value of node-count _n_ has exactly _n_ admissible paths
when all fields are data-typed.

### D5 — Chain rule depth (first cut: depth ≤ 1)

The chain rule says a hole inside a field of another data type `B` decomposes through ∂B. First cut:
recurse **one level** — a spec's `holeType` is a field's own `DataType` (so the shrinker can punch
_into_ that field's subtree using ∂B's specs at the next path step). Two consequences:

- Rose-shaped recursion (`R = a · L(R)`, recursion under a list-like field) is partially covered:
  paths descend into the `List`-typed field's _direct_ fields, but ∂ of the field type w.r.t. **R**
  (the multivariate derivative) is out of scope — `derivative` differentiates each type w.r.t. its
  own μ-bound only. This is the expressiveness boundary type-algebra.md §4.3 states; the plan states
  it in the module doc rather than extending `Field.isRecursive`.
- Deeper nesting (a hole two data-types down) is a follow-up, not a correctness risk: the shrinker
  simply finds no admissible path there and leaves the subtree untouched.

### D6 — Fillers: strictly-smaller inhabitants of the hole's type

For a hole of type `F`, candidate fillers are **strictly smaller** inhabitants
(`size < size(subtree
at hole)`, size = node count): (a) depth-0/base samples of `F` (the promoted
`samplesFor` machinery from `law_checking.ts`), (b) shallower recursive samples, (c) values already
present elsewhere in the failing value (McBride-style reuse). Deduped with `valueEquals`. Budget:
the existing `MAX_SAMPLE_DEPTH` semantics (≤ 2). If `F` has no sample vocabulary (function, `Any`,
pattern/token, `Nothing`), the hole yields **no candidates** — honest zero, consistent with
`screenableDomain`. A hole whose subtree is already minimal (e.g. `Zero()`) yields no candidates.

Plugging is pure tree surgery: rebuild the spine from the path with the filler substituted — no
re-evaluation needed to _construct_ the candidate (values are eager `VariantVal`s).

### D7 — Rendering candidates back to source

The harness's property domain is LC **source strings**. Candidates are rendered by a small recursive
`renderValue` (`Variant(fields…)` → `Name(src₁, …, srcₙ)`); `TokenVal` subtrees render as **no
candidates** in the first cut (pattern carriers route residual; their shrnking is out of scope here
— see §7). This is a ~20-line value renderer, not the full unparser (#34, v0.4.0).

### D8 — Wiring into lang-forma's `forAll`

The library's internal property runner calls `gen.shrink(best)` on the generator instance, and
`GrammarGenerator` exposes `sample`/`shrink`/`forAll` as an overridable class. Therefore:

```ts
class DerivativeGenerator extends GrammarGenerator<string> {
    override shrink(src: string): string[] // eval → paths → plug → render
}
```

`sample` and `forAll` are inherited untouched; only the shrink strategy changes. Fallback: a
counterexample that does not evaluate to a `VariantVal` (token, closure, parse hole) delegates to
`super.shrink` (the regeneration strategy) — the ∂T path is a strict upgrade, never a regression of
coverage. `PropertyFailure`/seed-reproducibility semantics are inherited unchanged, so the existing
contract tests keep their meaning.

## 4. Implementation steps

1. **`src/core/type_algebra.ts`** — `ContextSpec`, `derivative(type: DataType): ContextSpec[]`
   (total over regular μ-types; typed rejection — not `undefined` swallowing — for
   `IntersectionType`-headed carriers, consistent with the screen's `screenableDomain` rule;
   boundary conditions documented per type-algebra.md §4.3). Export from `src/core/index.ts`.
2. **`test/type_algebra.test.ts`** — rules-level unit tests (§5 below).
3. **`src/core/law_testing.ts`** — promoted harness: path enumeration, filler generation, plug,
   `renderValue`, `DerivativeGenerator`. The shrinker takes an `EvalTerm` (to parse the
   counterexample source into a value) and the carrier's `DataType`.
4. **`test/fixtures.ts`** — `createLawHarness` rebuilt on `DerivativeGenerator` (fixture grammars
   unchanged; the harness type stays `LawHarness`).
5. **`test/laws.test.ts`** — the existing shrink-contract test must still pass unchanged; add the
   quality instrumentation (§5).
6. **Docs** — `type-algebra.md` §7 status rows (`∂T machinery` → implemented-for-shrinking;
   `old`/observation rows stay pending); `law-testing.md` §1/§5 (shrinking is now ∂T-derived,
   regeneration demoted to fallback); `_docs/lc-core-implementation-plan.md` PBI entry.

## 5. Tests

**Type level (`type_algebra.ts`):**

- `derivative(Nat)` → exactly one spec: `Succ`/`pred`, empty surroundings.
- `derivative(Bool)` → `[]` (no fields anywhere — no contexts).
- `derivative(Pair(a: Bool, b: Bool))` → two specs (Leibniz: each field's surroundings is the other
  field's type).
- Chain rule: a `Tree`-like carrier whose field is another `DataType` yields specs whose `holeType`
  is that field's type (punchable at the next path step).
- Boundaries: intersection carrier → typed error; function-typed/`Any`/pattern fields → no spec;
  codata never enters (assert ν is untouched by construction).

**Value level (`law_testing.ts`):**

- Path enumeration: a tree of node-count _n_ admits exactly _n_ paths; plugging each path with an
  unchanged filler round-trips to the original value.
- Fillers: for a `Succ(k)` hole, candidates are exactly the Nats of smaller node count;
  `TokenVal`/unsampleable holes yield none.
- Shrink quality (the acceptance item "improves measurably"): run the falsified
  `idempotent`-on-`mul` property through `DerivativeGenerator` and assert (a) the minimal falsifier
  is still `Succ(Succ(Zero()))` (existing contract), and (b) the property invocations consumed
  during shrinking are ≤ the baseline regeneration shrinker's count (instrument by counting property
  calls; the regeneration baseline is captured in the same test run for comparison, so the assertion
  is relative, not absolute).
- Minimality: shrinking a Bool-carried falsification (size-1 value) yields zero candidates — already
  minimal, no churn.
- Fallback: a counterexample that is not a `VariantVal` still produces regeneration-shrunk
  candidates.

## 6. Acceptance mapping (issue #64)

| Acceptance item                                                                                          | Covered by                      |
| -------------------------------------------------------------------------------------------------------- | ------------------------------- |
| `derivative(T)` over regular μ-types (structural recursion, implicit differentiation at the μ-bound)     | Steps 1–2 (D2, D3)              |
| Structural shrinking wired into the property harness; minimal-counterexample quality improves measurably | Steps 3–5 (D6–D8, quality test) |
| (stretch) `old` typing derived from the fold functor                                                     | Deferred — §7                   |
| (stretch) observation-channel coverage quantified by context shape                                       | Deferred — §7                   |

## 7. Deferred (stretch) items — with reasons

- **`old`/paramorphism typing.** The `old` keyword does not exist anywhere in the codebase (no
  fold-elimination surface for it); this is a _language feature_ (grammar + typing rule +
  evaluator), not a library addition — a PBI of its own. The `ContextSpec`/`derivative` shape this
  PBI ships is exactly the substrate its typing rule would consume (surroundings = context).
- **Observation-evidence typing.** The runtime re-screening channel is design-stage
  (`design-decisions.md` "Laws"); there is no evidence accumulator to type. The `ContextSpec` shape
  is the future evidence vocabulary ("contexts of shape ≤ k").

## 8. Risks

- **Shrink-quality metric brittleness** — mitigated by the relative assertion (new vs. baseline in
  the same run) rather than a magic constant.
- **lang-forma internals** — the plan relies on the internal runner calling `gen.shrink` (verified
  in lang-forma 1.2.0's source: `const candidates = gen.shrink(best)`); a library bump that changes
  this contract would surface as the fallback test failing, not as silent behavior.
- **Renderer scope** — `renderValue` covers `VariantVal` only; pattern carriers and closures refuse
  honestly (no candidates / fallback) rather than emitting malformed source.
