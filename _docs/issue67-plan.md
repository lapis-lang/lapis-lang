# PBI #67 — TypeAlgebra judgment class: Implementation Plan (revised)

> **Status:** Implemented. This plan revises
> [issue #67](https://github.com/lapis-lang/lapis-lang/issues/67) after a review against the current
> tree (branch `mlhaufe/issue67`, post-#74). The PBI was written before #65, #52, and #74 landed;
> its dependency table and several premises are stale. The core proposal — a first-class judgment
> class over `Type` syntax — stands, and the review identified four additional opportunities the
> original did not (§2.2). Design source: [`type-algebra.md`](./theory/type-algebra.md) §1/§3/§4,
> [`grammar-as-semantics.md`](./theory/grammar-as-semantics.md) §7.3.

## 1. Summary

Consolidate the type-level judgments — `derivative`, `coefficients`, `finiteInhabitants` (counting)
— into a `TypeAlgebra` judgment class in `src/core/type_algebra.ts`, with identity-keyed memoization
as a first-class seam (absorbing the four hand-rolled caches the judgments currently carry), the
`ContextSpec` chain rule as a data edge (collapsing `law_testing.ts`'s three synchronized
spec-walkers into one), and shared traversal infrastructure for the field-kind case tables the
judgments re-implement per module. A sibling value-side change puts `equals`/`size` where the value
data lives (virtual methods on `Value`), mirroring `Type.equals`.

## 2. Review of the PBI against the current tree

### 2.1 What landed after the PBI was written

| PBI claim at write time                      | Current state                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| -------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `coefficients(type, k)` — "#65, pending"     | **Landed** (#65): free function in `type_algebra.ts` with its own `GFState` memo.                                                                                                                                                                                                                                                                                                                                                                                                      |
| cost algebra "#52, planned free fn"          | **Landed** (#52) — and NOT as free functions: `CostEngine extends AbstractLC<CostShape>` + `CostPass extends SemanticPass`. The sibling-judgment-class outcome the PBI wanted already exists; only the thin API wrappers (`analyzeOp`/`analyzeOps`/`analyzeTerm`) are free functions.                                                                                                                                                                                                  |
| "termination argument (`Field.isRecursive`)" | **Superseded** (#74): `Field.isRecursive` is gone; `FamilyType` spells the μ-bound. The termination argument is now "the walk never follows a `Family` field" — the same shape, new vocabulary.                                                                                                                                                                                                                                                                                        |
| "the judgment layer had no memoization seam" | The seam exists mechanically: lang-forma 1.2.0 exports `rule`, but **`@rule` memoizes only on `Grammar` subclasses** (verified empirically: the decorator delegates to `Grammar._ruleSlot`/`_paramRuleSlot`; a plain class throws `this._paramRuleSlot is not a function`). Since the PBI's own boundary says "the class is NOT a grammar subclass", the caching seam must be hand-rolled identity keying — the same `WeakMap`-keyed scheme `treeKey` v3.0.1 uses for class instances. |

### 2.2 What the review adds (opportunities the PBI did not identify)

1. **Five field-kind case tables, one traversal.** The "classify a variant's field kind" case table
   is re-implemented as `foldType` ladders or raw `instanceof` chains in: `derivative`
   (spec-or-undefined), `fieldGF` (coefficients), `coefficients`' `collect` (system collection),
   `finiteInhabitants` (hand-rolled ladder, `law_checking.ts` ~1466–1477), `inhabitantsUpToSize`'s
   variant filter + field-space dispatch (~1059–1092), the sample dispatch in `samplesFor`
   (~165–173), and `cost.ts`'s `typeKind`. Each is the same structural recursion over the same AST
   with a different answer type — exactly the shape the judgment class exists to host: shared
   scaffolding (`allVariants`, the field-kind dispatch, system collection, the memo), per-judgment
   actions.
2. **Three value-level spec-walkers.** `law_testing.ts` resolves context specs three times:
   `contextPaths` rebuilds a `specIndex` per node, and `holeTypeAt` re-walks the spec chain per path
   (plus `subtreeAt` walking the value). The PBI's `ContextSpec.derivative()` data edge collapses
   all of these; the review confirms the collapse is now mechanical.
3. **Four hand-rolled caches.** `GFState.memo` (coefficients), `finiteInhabitants`' per-call `Map`
   (a persistent memo is sound — a type's finiteness verdict is intrinsic), `inhabitantsUpToSize`'s
   `spaces`/`degrees` (per-certification by design — stays), and `DerivativeGenerator.sampleCache`
   (value-level, eval-driven — stays). The first two are the judgment layer's own caching; the class
   absorbs them.
4. **The process-global `setPatternLookup` hook.** A mutable module global with a save/restore
   protocol in `law_checking.ts` — the pain instance state removes. The class carries the lookup as
   constructor-injected instance state; the global becomes a facade over the module default
   instance.
5. **Value-side polymorphism gap.** `Value` is an abstract class whose only member is `kind`;
   `valueEquals`, `valueSize`, and two diverging `renderValue` functions (`law_checking.ts` renders
   tokens as `Type("text")` for display; `law_testing.ts` renders bare text for round-trip
   re-parsing) are `instanceof`-ladder free functions. Equality and size are intrinsic
   representation concerns (the same tier as `Type.equals` and `toString`) — they belong on the
   subclasses. The two renderers are genuinely different judgments (display vs source round-trip)
   and stay separate — documented, not merged.

### 2.3 What the review re-scopes

- **`screeningRegime` is not a judgment over `Type` syntax** — it is a router over `(law, op)` whose
  counting _calls_ consult `finiteInhabitants`. It stays in `law_checking.ts`; only its call sites
  route through the class. The PBI's table row conflated the two; this plan draws the line.
- **The `inhabitantsUpToSize` enumeration** is a third reading of the same equations (materialized
  values rather than counts), but it is value-level, `eval_`-driven, and memory-bound by design (the
  per-certification memo is the honest price of full enumeration — `MAX_FINITE_INHABITANTS`' doc).
  It stays in `law_checking.ts`; the class hosts the type-level readings. A future PBI may promote
  it.
- **`CostEngine` is already the sibling judgment class** the PBI wanted for #52 — over terms, not
  over types. `TypeAlgebra` cross-references it; nothing is absorbed. `typeKind` (the 3-way kind
  classification) may delegate to the class as the cheapest of the shared case tables.
- **Typed rejections are scattered** — `derivative` guards intersection via one `instanceof`,
  `coefficients` via three sequential ones. The class unifies them behind one
  `requireSemiringCarrier(type, caller)` boundary following the lattice's `requireType` discipline
  (`subtyping.ts`): the thrown message names the calling judgment. Sentinel tests pin each caller's
  exact prefix — the review finding from #74 applies.

## 3. Current state

| Piece                          | Where                 | Form        | Cache                           |
| ------------------------------ | --------------------- | ----------- | ------------------------------- |
| `derivative(type)`             | `type_algebra.ts`     | free fn     | none (re-walked per call)       |
| `coefficients(type, k)`        | `type_algebra.ts`     | free fn     | `GFState.memo` per call         |
| `finiteInhabitants(type)`      | `law_checking.ts`     | free fn     | per-call `Map` + `inProgress`   |
| `screeningRegime(law, op)`     | `law_checking.ts`     | free fn     | none (routes finiteInhabitants) |
| `inhabitantsUpToSize(type, k)` | `law_checking.ts`     | free fn     | `spaces`/`degrees` per call     |
| `setPatternLookup`             | `type_algebra.ts`     | global hook | —                               |
| `specIndex(carrier)`           | `law_testing.ts`      | free fn     | rebuilt per node / per path     |
| `holeTypeAt(path)`             | `DerivativeGenerator` | method      | re-walks spec chain             |
| `ContextSpec`                  | `type_algebra.ts`     | interface   | no recursive edge               |
| `valueEquals` / `valueSize`    | `values.ts`           | free fns    | —                               |
| `Type.equals` (the model)      | `types.ts`            | virtual     | —                               |

Consumers of the export surface: `law_testing.ts` (`ContextSpec`, `derivative`), `law_checking.ts`
(`coefficients`, `setPatternLookup`), `src/core/index.ts` (re-exports), `test/type_algebra.test.ts`
(`coefficients`, `ContextSpec`, `derivative`), `test/discharge.test.ts` (`finiteInhabitants`,
`screeningRegime` from `law_checking.ts`).

## 4. Design decisions

### D1 — Class shape: plain class, NOT a `Grammar` subclass

The PBI's boundary already says "the class is NOT a grammar subclass"; the review adds the
mechanical reason: `@rule` memoization is implemented on `Grammar.prototype`
(`_ruleSlot`/`_paramRuleSlot`) and is unusable outside a `Grammar` hierarchy. `TypeAlgebra` is a
plain class whose memoization is the same keying scheme (`WeakMap` identity keying per instance per
method — D2), documented as the "@rule-style" seam the PBI anticipated, minus the decorator's
grammar precondition. This is a deliberate deviation from the PBI's `@rule` letter, justified by the
measured decorator behavior.

### D2 — Memoization: identity-keyed, instance-carried

- Method memos are `WeakMap<DataType, …>` instance fields — sound because `DataType` is immutable by
  construction (persistent builders; PBI #77 replaced the two-phase `seal()` ceremony, so instance
  identity is a valid cache key unconditionally). The `treeKey` v3.0.1 precedent (identity via
  `WeakMap<object, number>`) is the keying model.
- `derivative(type)` memoizes per carrier; `coefficients` absorbs `GFState` (the fixpoint's `memo`
  becomes the class's — the system set is derived per call as today, but a repeat call at the same
  degree reads the memo); `finiteInhabitants`' verdict memo becomes persistent (a type's finiteness
  is intrinsic; cycles resolve to the `undefined` verdict, cached).
- Cache growth is bounded by the number of distinct `DataType` instances — registries are finite and
  types are immutable values. No eviction.

### D3 — `ContextSpec` gains the recursive edge (the chain rule as data)

`ContextSpec` becomes a class (constructed only by `TypeAlgebra`; the constructor is module-private)
carrying a lazily memoized `derivative(): ContextSpec[]` — defined when `holeType` is a `DataType`
(the chain rule's one-level reading), `undefined` otherwise (token, function, `Any`, `Nothing`,
pattern, intersection fields contribute no context). `law_testing.ts` collapses onto it:

- `specIndex` → the class's indexed accessor (`specFor(carrier)`, memoized per carrier);
- `holeTypeAt(path)` → walk the path through the specs' `holeType`s (the walk itself stays
  value-side — it is the shrinker's, not the algebra's);
- `contextPaths`'s per-node `specIndex` rebuilds and its chain-rule condition
  (`fieldValue.dataType === spec.holeType`) read from the same spec objects.

Boundary unchanged (`type-algebra.md` §4.3): rose-shaped recursion stays out; the data edge is
exactly the depth-≤ 1 chain rule restated as data.

### D4 — Shared traversal infrastructure, per-judgment case tables

The class hosts the skeleton: `allVariants()` iteration, the field-kind dispatch (a protected
`foldType`-based `fieldKind(field, actions)` helper over the `TypeCases` protocol), mutual-system
collection (the `collect` walk), and the memo fields. Each judgment supplies its own per-kind
actions as today — `derivative`'s spec-or-undefined, `fieldGF`'s coefficient table, the counting
ladder — so the case tables stop re-implementing the scaffolding while the readings stay independent
(no shared semiring: the counting's ∞-saturating arithmetic and the coefficients' truncated
polynomial fixpoint are genuinely different algorithms on the same equations; unifying them would
break the honest saturation contracts each caller pins).

### D5 — Module default instance; the export surface never shrinks

`type_algebra.ts` exports a module-level default `TypeAlgebra` instance and keeps
`derivative`/`coefficients`/`setPatternLookup`/`MAX_COEFFICIENT`/ `Coefficients`/`ContextSpec` as
working delegates (zero-fixture purity preserved: `derivative(type)` stays a plain call).
`finiteInhabitants`/ `screeningRegime` keep their `law_checking.ts` exports (the `discharge.test.ts`
imports) but delegate to the class. `src/core/index.ts` gains `TypeAlgebra`; nothing shrinks (the
PBI's no-behavior-change condition).

### D6 — Typed-rejection boundary

One `requireSemiringCarrier(type, caller)` (the `requireType` pattern): intersection-headed and
ν-typed carriers reject with the calling judgment's name in the message (`derivative`,
`coefficients`); the pattern arm and degree-≥ 0 checks route through the same entry. Existing
`TypeError` messages are preserved verbatim — the sentinel tests in `test/type_algebra.test.ts` pin
them.

### D7 — Value-side: `Value.equals` / `Value.size` / `Value.renderSource` virtuals

`valueEquals` and `valueSize` became virtual methods on `Value` (`VariantVal`, `TokenVal`, plus the
closure/codata/error subclasses), mirroring `Type.equals`; the pass-through delegates were then
REMOVED entirely (the free-function "surface" was indirection — call sites invoke the methods
directly). The round-trip renderer's per-kind arms also moved into the classes as
`Value.renderSource()` (base: decline; `VariantVal`: recursive `Name(field, …)` with decline
propagation; `TokenVal`: bare type name, declining on text ≠ name); `law_testing.ts`'s `renderValue`
remains as the harness's call-surface function over that ladder. The two renderers stay
judgment-level with their documented divergence (display quoting vs round-trip source).
`SpanClosure.equals` keeps the identical-reference rule its comment states; `PlaceholderValue`/
`EvalErrorValue` keep `kind`-based fallbacks.

### D8 — The lookup hook becomes instance state

`TypeAlgebra` takes the pattern-type lookup as a constructor parameter (defaulting to the rejecting
hook); `setPatternLookup` becomes a facade that installs the hook on the module default instance and
returns the prior — `law_checking.ts`'s save/restore pattern keeps working unchanged. New instances
(tests) can carry their own lookup without process-global mutation.

## 5. Implementation steps (each independently green)

1. **The class shell + delegates.** `TypeAlgebra` with `derivative` and `coefficients` migrated as
   methods (absorbing `GFState`), the module default instance, free-function delegates, D6 boundary.
   Existing tests pass unmodified; new tests pin memo identity behavior.
2. **`ContextSpec` data edge.** The class form with the memoized `derivative()` edge;
   `law_testing.ts`'s walkers collapse; the ∂T shrinker tests pin unchanged shrink behavior (the
   idempotence counterexample test must not regress).
3. **Counting migrates.** `finiteInhabitants` moves to the class (persistent memo),
   `law_checking.ts` re-exports the delegate, `screeningRegime`'s call sites route through the
   instance. `discharge.test.ts` passes unmodified.
4. **Value-side virtuals.** `Value.equals`/`Value.size`, free-function delegates, parity tests.
5. **Docs.** `type-algebra.md` §1 note ("three readings → one judgment class") + §7 rows;
   `grammar-as-semantics.md` §7.3 gains the type-level-judgment-class row (input: `Type` objects;
   mechanism: judgment class, not a grammar subclass); this plan's status flip.

## 6. Test plan

- **Unmodified pass** is the acceptance bar: `test/type_algebra.test.ts`, `test/discharge.test.ts`,
  `test/law_testing.test.ts` run green without edits (their imports keep working through the
  delegates).
- New tests: identity-keyed memo (same instance → memoized; two distinct `DataType` instances with
  the same name → separate verdicts — the `holeTypeAt` identity discipline's mirror);
  `ContextSpec.derivative()` data-edge shape (hole types that are `DataType`s carry the edge; token/
  function/pattern fields carry none); `Value.equals`/`Value.size` parity with the delegates; the D6
  boundary messages.
- `deno check src/index.ts` + `deno lint` + `deno fmt` clean; 440-test baseline (2 ignored) must not
  regress.

## 7. Boundary conditions (carried forward, plus review additions)

- Pure decision procedures stay pure — zero-fixture tests preserved via the module default instance
  (10 zero-fixture `derivative` tests stay green).
- Codata (ν) stays untouched; the coalgebraic dual remains a typed rejection.
- Not a `@rule`-production over the term grammar, and now also not a `Grammar` subclass — plain
  class with identity-keyed memos.
- `screeningRegime`, `inhabitantsUpToSize`, and `CostEngine` stay put (§2.3); the class hosts the
  type-level readings only.
- No issue-tracker references in code comments (repo instruction).
