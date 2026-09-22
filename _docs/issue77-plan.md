# PBI #77 — Persistent Type structures: Implementation Plan

> **Status:** Implemented. Implements
> [issue #77](https://github.com/lapis-lang/lapis-lang/issues/77) — persistent
> `DataType`/`CodataType` construction (immutable, builder-knotted self-reference), deleting the
> two-phase `seal()` ceremony and `TypeAlgebra`'s `requireSealedCarrier` precondition machinery.
> Gate verified after implementation (`deno check` / 456 tests / lint / fmt, branch
> `mlhaufe/issue77`).

## 1. Summary

Replace the two-phase construction protocol (`new` → `addVariant`/`addObserver` → `seal()`) with
**persistent construction**: `DataType.define(name, parent?)` returns a builder; `addVariant`/
`addObserver` on the builder return a NEW immutable builder; `build()` returns a frozen, immutable
carrier instance. Direct self-reference — the design's crux — resolves through the **builder knot**:
a field may reference the builder handle, resolved at `build()` time. There is no `seal()`, no
`isSealed()`, no construction-phase mutator on the type, and no `requireSealedCarrier` guard: with
every intermediate object immutable by construction, instance identity is a valid cache key
unconditionally, and the judgment layer's identity-keyed memos (`TypeAlgebra`'s
derivative/spec/inhabitants/coefficient caches) are sound without any precondition.

Readings are untouched: `derivative`/`coefficients`/`inhabitants` results, `equals`/`toString`/
`dispatch`/`map`/`resolveFamily`, the `TypeCases` protocol, the `Family` μ-bound representation
(#74), and `PatternDataType` (already immutable) all stay exactly as they are. Only the construction
protocol and the cache-soundness story change.

## 2. Review of the PBI against the current tree

### 2.1 Verified claims

| PBI claim                                                | Current tree (verified)                                                                                                                                                                                                                                                                                                                                                                                                                   |
| -------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Two-phase protocol with a `seal()` ceremony              | `types.ts` — `DataType._variants` private + `sealed` flag, `addVariant` throws post-seal and rejects a re-used (frozen-fields) variant, `seal()` freezes the array and every variant's fields, `isSealed()`. `CodataType` mirrors with `_observers`/`addObserver` (no variant-reuse check).                                                                                                                                               |
| `TypeAlgebra` guards every memo entry                    | **Partially true — a gap exists.** `requireSealedCarrier` fires at `derivative` (line ~346), `specFor` (~405), and `inhabitants` (~464). `coefficients` does NOT call it — the fixpoint's system collection and the `coefficientsMemo` entries are keyed on an unguarded carrier. Persistence closes the gap by construction (no guard to add); the plan notes this in `type-algebra.md` §1's keying sentence rather than dramatizing it. |
| ~20 unsealed fixtures found once the precondition landed | Consistent with the tree: `test/type_algebra.test.ts` still carries the double-seal idiom (`inner.seal(); inner.seal()`) from that migration, and `discharge.test.ts` has several (`self.seal(); self.seal()`, `b.seal(); b.seal()`, `wrapped.seal(); wrapped.seal()`) — mechanical artifacts that disappear under `build()`.                                                                                                             |
| Sentinel tests pin the sealed contract                   | **The PBI over-assumes.** Two sentinel tests exist (post-seal `addVariant` throws; frozen-array alias rejection, `type_algebra.test.ts` lines 33–64) but they pin `DataType`'s own ceremony, NOT the memo precondition. No test anywhere asserts `requireSealedCarrier`'s TypeError. So acceptance item 6 is "add persistent-shape tests", not "replace precondition tests".                                                              |
| All 59 `addVariant`/`addObserver` call sites             | 59 test-side call statements across 6 files (`cost.test.ts` 1, `discharge.test.ts` ~27, `fixtures.ts` 6, `law_testing.test.ts` 1, `type_algebra.test.ts` ~20, `type_algebra_class.test.ts` ~10) plus ONE src-side construction: `law_checking.ts` `makeTrueValue()` (~1954, the `Bool` verdict carrier). ~66 `.seal()` statements across the same files.                                                                                  |
| `PatternDataType` already immutable                      | Confirmed — readonly patterns array, no construction phase. Untouched.                                                                                                                                                                                                                                                                                                                                                                    |
| Registry holds the final built instance                  | Confirmed — `TypeRegistry.register` (`grammar.ts` ~139) reads `allVariants()`/`allObservers()` at registration; it takes `DataType                                                                                                                                                                                                                                                                                                        |
| #74's `Family` representation is orthogonal              | Confirmed — `FamilyType` is an immutable singleton; the recursive position is `field.type instanceof FamilyType` across 30+ sites (`cost.ts`, `derivation.ts`, `eval_grammar.ts`, `law_checking.ts`, `typing_grammar.ts`, `type_algebra.ts`). Nothing in the construction protocol touches it.                                                                                                                                            |

### 2.2 What the review adds

1. **The thunk alternative fails on initialization ordering.** The PBI demands an explicit choice
   between a lazy type reference and the builder knot. A thunk field (`Field("inner", () => self)`)
   forces `self` to be read by `build()` BEFORE the assignment `self = …build()` completes — a
   TDZ/undefined read at build time — unless the design adds a post-build fixup ceremony
   (`t.resolveBackrefs()`), which is exactly the two-phase ceremony this PBI deletes, reintroduced.
   The builder handle is an inert object created by `define()`, resolvable in one walk, and its
   presence in a `Field`'s type slot is a compile-time-visible union distinct from `Type`. Decision:
   **builder knot**, trade-offs documented in `types.ts`'s module doc (acceptance item 3).
2. **One vocabulary, not two.** A value-style `new DataType(name, variants, parent)` constructor
   could survive alongside the builder — but that is the "two construction vocabularies" complaint
   the Problem section raises, kept alive. The constructor becomes private; `define(…)` is the only
   entry point for both classes. The one src call site (`makeTrueValue`) migrates mechanically.
3. **The builder must be persistent too** ("the mutation-based API is gone" applied consistently):
   `addVariant` returns a NEW builder; the receiver's lineage stays unchanged. This is what makes
   "two builds from one base are distinct identities with distinct caches" — the PBI's own
   persistent-shape test — expressible at all.
4. **JSR slow-types discipline**: the builder classes (`DataTypeBuilder`/`CodataBuilder`) appear in
   `define()`'s public return type, so they must be exported (and re-exported from
   `src/core/index.ts`) — JSR's no-slow-types rule rejects an unexported referenced class.
5. **A `parent`-mutation audit**: no call site in `src/` or `test/` assigns `.parent` after
   construction (the only `.parent` writes are the constructors). `withParent` has no consumer
   today; parent becomes a `define()`-time `readonly` constructor argument. A `withParent` method is
   a non-goal until a use exists (it would be a persistent builder derivation if ever needed).

## 3. Current state

| Piece                                   | Where                                                 | Form today                                                                                                   |
| --------------------------------------- | ----------------------------------------------------- | ------------------------------------------------------------------------------------------------------------ |
| `DataType`                              | `src/core/types.ts` ~296                              | create → `addVariant` (mutating, throws post-seal, rejects frozen-field variants) → `seal()`                 |
| `CodataType`                            | `src/core/types.ts` ~449                              | same, `addObserver` (no variant-reuse check)                                                                 |
| `Variant.seal()`                        | `src/core/types.ts` ~274                              | freezes the fields array in place; idempotent                                                                |
| `isSealed()`                            | `types.ts` ~376/~503                                  | accessor consumed by `TypeAlgebra`                                                                           |
| `requireSealedCarrier`                  | `src/core/type_algebra.ts` ~296                       | guards `derivative`/`specFor`/`inhabitants`; **not** `coefficients`                                          |
| Identity-keyed memos                    | `type_algebra.ts` ~241                                | 4 `WeakMap`s (derivative, specIndex, inhabitants w/ null sentinel, coefficients w/ degree)                   |
| Src-side construction                   | `law_checking.ts` ~1954                               | `makeTrueValue()`: `new DataType("Bool", [True, False])` + `seal()`                                          |
| Test factories                          | `test/fixtures.ts` ~45–118                            | 6 factories, all ending in `.seal()`                                                                         |
| Sentinel tests                          | `type_algebra.test.ts` ~33–64                         | post-seal throws; alias frozen-array                                                                         |
| Memo-identity tests (STAY, still valid) | `type_algebra_class.test.ts` ~41–89                   | same-instance memo hit; distinct instances → distinct verdicts; per-instance memos; null-sentinel round-trip |
| Docs                                    | `grammar-as-semantics.md` §10.3; `type-algebra.md` §1 | describe the sealed two-phase protocol / "sound because types are sealed"                                    |

## 4. Design decisions

### D1 — Persistent classes, private constructors, `define` as the single entry

```ts
export class DataType extends Type {
    private constructor(
        readonly name: string,
        private readonly _variants: readonly Variant[],
        readonly parent: DataType | null, // readonly — comb inheritance is an immutable chain
    ) {
        super()
    }

    static define(name: string, parent: DataType | null = null): DataTypeBuilder

    static buildAll(...builders: DataTypeBuilder[]): DataType[] // the mutual-recursion group form

    get variants(): readonly Variant[]
    // equals/toString/dispatch/map/allVariants/findVariant: UNTOUCHED
}

export class DataTypeBuilder {
    // module-internal construction; carries the lineage token shared by every derived builder
    addVariant(...variants: Variant[]): DataTypeBuilder // persistent: returns a NEW builder
    build(): DataType // resolves handles, freezes, fresh instance
}
```

`CodataType` mirrors exactly (`define`/`CodataBuilder`/`addObserver`/`build`). `build()` twice on
one builder returns two DISTINCT frozen instances — identity tracks construction, which is the
property the identity-keyed memos consume. `Object.freeze` applies to the variants array and every
variant's fields array (the same alias guarantees `seal()` provided, at `build()` time instead).

### D2 — The self-reference knot (the design's crux)

`define()` returns the initial builder, whose identity is the lineage handle. A field may reference
ANY builder of the same lineage; `build()` walks the accumulated variants and rewrites builder-typed
field slots to the constructed instance:

```ts
const Self = DataType.define("Self") // handle AND initial builder
const self = Self
    .addVariant(new Variant("Base", []))
    .addVariant(new Variant("Wrap", [new Field("inner", Self)]))
    .build() // `inner` IS `self` — the genuine re-entrant field
```

- The rewritten fields produce NEW `Field`s and a NEW frozen `Variant` — the unresolved construction
  objects are discarded; post-build, `field.type: Type` always (all 52+ consumer sites —
  `field.type instanceof FamilyType`, `.dispatch`, `.resolveFamily` — see real types, no widening
  leaks).
- A foreign-lineage handle reaching `build()` (or `buildAll`) throws a loud `TypeError` naming the
  unresolved reference — the same loud-boundary discipline as
  `requireType`/`requireSemiringCarrier`.
- Mutual recursion (`A = baseA() | mkA(b: B)`, `B = mkB(a: A)` — both live test fixtures) uses the
  group form: `DataType.buildAll(aBuilder, bBuilder)` resolves cross-lineage handles among the group
  in one pass (duplicate lineages in a group reject).
- Why not the thunk: §2.2 item 1 — the thunk cannot be initialized before `build()` consumes it
  without a post-build fixup ceremony; the knot has no ordering hazard and no closure per field.

### D3 — `Field`/`Observer` type slots widen for construction only

`Field`'s constructor accepts `Type | DataTypeBuilder | CodataBuilder` and stores it in a private
slot; the public `get type(): Type` throws loudly if read while unresolved. Builders expose no
variant-reading API, so an unresolved read is unreachable through the API — the throw catches only a
retained pre-build `Field`. `Observer` mirrors it. Post-`build()`, every field's `.type` is a
genuine resolved `Type` (the resolution rewrites, never wraps — no lazy type kind enters the closed
universe, and `TypeCases`/`RequiredCases` stay untouched).

### D4 — `Variant` immutable at construction

`Variant.seal()` dies; the constructor freezes `fields` in place (the caller-retained array cannot
mutate the definition — the alias test's guarantee, moved to construction time). Variants become
freely shareable values (the frozen-field reuse rejection dies with the ceremony it served). `Field`
needs no change beyond D3 (already immutable by construction).

### D5 — `TypeAlgebra` loses the precondition, keeps the keying

`requireSealedCarrier` and its 3 call sites delete; the memo fields, null-sentinel discipline
(`null` stored → read back as `undefined` at every read site), degree-keyed coefficients memo, and
`setLookup` invalidation are untouched — they never depended on `seal()` except through the guard.
Doc comments that cite the sealed precondition ("intrinsic to the sealed carrier", module-doc
sentences) restate the soundness story: **immutable by construction — identity = shape, no
precondition, no invalidation path**. `coefficients`' missing guard (§2.1) closes by construction;
one clause in `type-algebra.md` §1 records it without a history lesson.

### D6 — Docs: the construction protocol's new story

- `grammar-as-semantics.md` §10.3 → "Types are values (persistent construction)": define/build
  chain, the builder knot for self-reference, identity = shape with no enforced precondition, and
  the compiler-enforced separation (builder ≠ `Type`; the registry holds built instances).
- `types.ts` module doc: a "Construction protocol" section stating the chosen knot design and its
  trade-offs (vs. thunks — §2.2 item 1), per the PBI's acceptance item 3.
- `type-algebra.md` §1: the keying sentence becomes "sound because types are immutable by
  construction (persistent builders — identity = shape, no precondition)".

## 5. Implementation plan (phases, file-level deltas)

Order preserves `deno check src/index.ts` greenness until the test migration sweep (repo memory:
check catches cross-module errors first via `src/index.ts`).

### Phase 1 — `src/core/types.ts`: the persistent core

- `DataType`/`CodataType`: private constructors; `readonly parent`; `define`/`buildAll` statics;
  delete `addVariant`/`addObserver`/`seal`/`isSealed`/`sealed` from the classes.
- New `DataTypeBuilder`/`CodataBuilder` classes (persistent `addVariant`/`addObserver`, `build` with
  knot resolution + freeze, lineage token).
- `Variant`: ctor-freezes `fields`; delete `seal()`.
- `Field`/`Observer`: D3's widened slots + throwing getters.
- Module doc: the construction-protocol section (D6).
- Export the builders alongside the classes.

### Phase 2 — `src/core/type_algebra.ts`: delete the precondition

- Delete `requireSealedCarrier` + its 3 call sites; refresh the memo doc comments (D5).
- No behavioral change: every reading's output is byte-identical.

### Phase 3 — src migration (the one site)

- `law_checking.ts` `makeTrueValue()`: `new DataType("Bool", [True, False])` + `seal()` →
  `DataType.define("Bool").addVariant(True, False).build()`.
- `src/core/index.ts`: re-export the builders.

### Phase 4 — test migration (mechanical, grep-driven)

Checklist targets ZERO post-migration matches for `\.seal\(\)|isSealed|requireSealedCarrier` and for
`new DataType|new CodataType` outside the new API:

| File                              | Deltas                                                                                                                                                                                                                                           |
| --------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `test/fixtures.ts`                | 6 factories → `define(…).addVariant/addObserver(…).build()` chains (shorter than today; the rebinding dance disappears)                                                                                                                          |
| `test/type_algebra.test.ts`       | fixtures (~8) → chains; DELETE the two sentinel tests; ADD the persistent-contract set (below); `natPos()` comb via `define("NatPos", n)`                                                                                                        |
| `test/type_algebra_class.test.ts` | fixtures (~10) → chains; keep the memo-identity tests verbatim (still valid); the codata boundary probe `new CodataType("Stream", […])` → `define().addObserver().build()`; ADD persistent-shape tests                                           |
| `test/discharge.test.ts`          | ~27 sites → chains (incl. the direct self-ref `Self` fixture — the knot exercises for real; the double-seal artifacts vanish); `impostor_variants_helper`'s inline `new DataType("Unused", [])` field type → `DataType.define("Unused").build()` |
| `test/cost.test.ts`               | 1 site → chain                                                                                                                                                                                                                                   |
| `test/law_testing.test.ts`        | 1 site → chain                                                                                                                                                                                                                                   |

New persistent-shape tests (the PBI's acceptance item 6, plus the reworked sentinels):

1. **persistent builder**: `addVariant` returns a new builder; the receiver still builds WITHOUT the
   added variant; two builds from one builder are distinct instances with distinct spec arrays and
   distinct verdicts (the memo story, asserted directly).
2. **freeze at build**: `Object.isFrozen(type.variants)` and every variant's `fields` frozen; a
   retained pre-build `Variant` fields array cannot mutate the built definition.
3. **the knot**: `Self = Base | Wrap(inner: Self)` — the Wrap field's type IS the built instance;
   `coefficients(self, 3)` = `[0, 1, 1, 1]` (today's discharge-test verdict, unchanged).
4. **mutual group**: `buildAll` resolves A↔B; a foreign handle outside the group rejects loudly.
5. **no mutation**: `b0.addVariant(v)` twice on one builder → two independent lineages, neither
   containing the other's variants.

### Phase 5 — docs (D6's three deltas)

### Phase 6 — gate

`deno check src/index.ts` && `deno test` && `deno lint` && `deno fmt` (fmt re-sorts import blocks —
re-read after fmt before further import edits, per repo memory).

## 6. Acceptance mapping (PBI checkboxes → plan)

| PBI acceptance item                                                                      | Where                                                                                         |
| ---------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------- |
| Immutable post-construction; builder equivalents return new instances; mutation API gone | D1/D2 + Phase 1/4 (private ctors; persistent builders; zero `new DataType`/`seal` call sites) |
| `seal()`/`isSealed()` deleted; `requireSealedCarrier` deleted                            | Phase 1/2; §2.1 records the coefficients-gap closure                                          |
| Self-reference knot chosen + documented in `types.ts`'s module doc                       | D2 (builder knot; thunk rejected §2.2) + Phase 1 module doc                                   |
| `parent` immutability                                                                    | D1 (`readonly parent`, define-time; `withParent` deferred — §2.2 item 5)                      |
| All 59 call sites migrated; sentinel tests reworked                                      | Phase 4 (grep-driven zero-target checklist; §2.1 corrects the sentinel-test premise)          |
| Memo-precondition tests → persistent-shape tests                                         | Phase 4's new test set (nothing to delete — no precondition tests existed)                    |
| Docs: §10.3 rewritten; `type-algebra.md` §7/§1 memo-soundness note                       | Phase 5 (D6)                                                                                  |

## 7. Risks

- **Missed call sites** → runtime `TypeError` at the judgment boundary in a cold path. Mitigation:
  the Phase 4 grep checklist targets zero residual matches; `deno check` catches every signature
  break on the src side first.
- **Field-slot union leaking into public types** (JSR slow-types or consumer friction) → the union
  exists only in `Field`/`Observer` constructor parameters; the `type` getter stays `Type`. Check
  with a `deno publish --dry-run` if the publish gate is exercised.
- **fmt/lint churn** on migrated chains → run the gate after each phase; re-read after fmt.
- **No PBI IDs in code comments** (repo instruction) — the doc deltas carry the rationale;
  `types.ts` comments explain the knot on its own terms.
