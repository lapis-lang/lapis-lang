# LC Core Implementation Plan — zipper-grammar v4.1.0

> **Status:** Active plan. zipper-grammar v4.1.0 is installed and all 58 existing tests pass. This
> plan tracks the remaining work via the GitHub issue tracker (PBIs #19–#26).
>
> **v4.0.2 note (issues #28, #30):** The duplicate-parse-results bug is **resolved**. v4.0.1 (issue
> #28) fixed the cross-`DelayedExp` sharing but left a base case that compounded to 2ⁿ for multi-arg
> variant construction via `sepBy` (reported as issue #30). v4.0.2 (PR #31) introduces **derivation
> paths** — each parse value carries a path string identifying its derivation through `AltExp`
> branches; values sharing a path are cosmetic duplicates (collapsed at the top-level forest),
> values with distinct paths are genuine ambiguity (kept). Our grammar now produces
> `result.size === 1` for all unambiguous inputs. The last remaining duplicate
> (`fold
> [Stack] Empty() { ... }` under the eval grammar) was traced to a **redundant `.opt()` on
> a `sepBy`** in `foldHandler`/`spanFoldHandler`: `sepBy(p, sep)` already matches zero elements via
> `epsilon([])`, so `.opt()` adds a second empty-matching path (returning `undefined`), producing
> two distinct derivation paths that map to the same object value — `Set` keeps both by reference.
> Removing the redundant `.opt()` (zipper-grammar issue #32 investigation) resolved it. All tests
> now assert `result.size === 1`.

## Current State

### What Works (58 tests passing, v4.1.0)

| Component                                          | Status                                                                                                        | Files                                  |
| -------------------------------------------------- | ------------------------------------------------------------------------------------------------------------- | -------------------------------------- |
| Types                                              | ✅ Complete                                                                                                   | `types.ts`                             |
| Terms                                              | ✅ Complete                                                                                                   | `terms.ts`                             |
| Values (incl. `SpanClosure`, `SpanCodataVal`)      | ✅ Complete                                                                                                   | `values.ts`                            |
| Subtyping (S-Refl through S-And-Elim)              | ✅ Complete                                                                                                   | `subtyping.ts`                         |
| `join` / `meet` lattice operations                 | ✅ Complete                                                                                                   | `subtyping.ts`                         |
| Concrete syntax grammar (AbstractLC + LCAST)       | ✅ Complete                                                                                                   | `grammar.ts`                           |
| TypeRegistry with reverse lookups                  | ✅ Complete                                                                                                   | `grammar.ts`                           |
| Type-checking grammar (LCTypeCheck)                | ✅ T-Var, T-Abs, T-App, T-Let, T-Variant, T-Obs, T-Fold, T-Unfold, T-TAbs, T-TApp, T-Cofold, T-Sub (implicit) | `typing_grammar.ts`                    |
| Evaluation grammar (LCEval)                        | ✅ E-App, E-Let, E-Fold, E-Unfold, E-Obs, E-Cofold, E-TApp via `_forward`                                     | `eval_grammar.ts`                      |
| `parseToFixpoint` for fold σ                       | ✅ Complete — wired into `foldProd` (line 539)                                                                | `typing_grammar.ts`                    |
| Contract metadata (`@requires`/`@ensures`/`@rule`) | ✅ Complete — all rules have `rule` + `formula` metadata                                                      | `typing_grammar.ts`, `eval_grammar.ts` |
| `toInference()` + `InferenceRule`                  | ✅ Complete — generates rules from `Symbol.metadata`                                                          | `typing_grammar.ts`                    |
| `@ensures` Progress contracts                      | ✅ Complete — each production encodes its Progress case                                                       | `typing_grammar.ts`                    |
| `DerivationTree` + `SemanticPass`                  | ✅ Validated — `parseToTree` + tree-consuming passes work on LC grammar                                       | `grammar.ts`, test files               |
| Grammar ambiguity (single parse tree)              | ✅ Resolved (v4.0.2) — all tests assert `result.size === 1`                                                   | all test files                         |

> **Note:** There are no `typing.ts`, `eval.ts`, or `soundness.ts` files. The grammar-based
> `LCTypeCheck` and `LCEval` are the sole implementations; soundness is encoded directly in
> `@ensures` contracts (Progress) and the grammar structure (Preservation).

### What's Missing or Incomplete

| Component                    | Status              | Notes                                                                                                | PBI          |
| ---------------------------- | ------------------- | ---------------------------------------------------------------------------------------------------- | ------------ |
| `Nothing` propagation        | ❌ Not implemented  | Grammar-based checker doesn't propagate `Nothing` in `variantCon`, `obs`, `fold`, `unfold`           | #19          |
| T-Sub (subsumption)          | ⚠️ Implicit         | Applied at use sites via `isSubtype` in `@requires`; decide if explicit rule is needed               | #20          |
| `@ensures` for Progress      | ⚠️ Present but weak | Contracts exist with Progress comments; need to verify they fully encode the Progress theorem        | #21          |
| Law/properties machinery     | ❌ Not started      | Algebraic laws are one of the three irreducible essentials of Lapis; no operational exploitation yet | #22          |
| T-FoldMatch + E-FoldMatch    | ❌ Not implemented  | `fold [T] e {pᵢ → tᵢ}` — pattern-matched fold (elimination)                                          | #23          |
| T-Pattern                    | ❌ Not implemented  | `match(pₖ)` — pattern-matched construction (introduction)                                            | #24          |
| Surface language elaboration | ❌ Not started      | `DerivationTree` + `SemanticPass` pipeline for surface → LC core                                     | #25          |
| Dead code / consolidation    | ❌ Not started      | Remove or justify LCAST AST builder, consolidate `index.ts` exports                                  | #15–#17, #26 |

## Plan — PBI Roadmap

The 8-phase plan has been replaced by the GitHub issue tracker. Each PBI below links to its issue
with the current status, milestone, and dependencies.

### Milestone v0.1.1 — Clean core

#### PBI #15: Cleanup — Fix CodataType observers construction API

- **Status:** Open
- **Assignee:** @mlhaufe
- **Scope:** Fix the CodataType observer construction API.
- **Files:** `src/core/types.ts`, `src/core/grammar.ts`

#### PBI #16: Cleanup — Consolidate `index.ts` export surface

- **Status:** Open
- **Assignee:** @mlhaufe
- **Scope:** Consolidate the public API exports in `src/core/index.ts`.
- **Files:** `src/core/index.ts`

#### PBI #17: Cleanup — Remove or justify LCAST AST builder and Term hierarchy

- **Status:** Open
- **Assignee:** @mlhaufe
- **Scope:** Evaluate whether the `LCAST` AST builder and `Term` hierarchy are still needed given
  the grammar-based approach. Remove if dead; justify if not.
- **Files:** `src/core/grammar.ts`, `src/core/terms.ts`

#### PBI #18: Cleanup — Update stale `lc-core-implementation-plan.md` _(this document)_

- **Status:** Open → in progress
- **Assignee:** @mlhaufe
- **Scope:** Rewrite this document to match the current codebase state (this revision).

### Milestone v0.2.0 — Sound core

#### PBI #19: `Nothing` propagation in grammar-based type checker

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Propagate `Nothing` (bottom type) through the grammar-based checker. When a sub-term has
  type `Nothing`, the surrounding term should also be `Nothing` (or handled per the rule), not
  silently treated as well-typed.
- **Tasks:**
  1. Add `Nothing` checks to `variantCon`, `obs`, `fold`, `unfold` in `typing_grammar.ts`.
  2. Add tests: a term with a `Nothing`-typed sub-term should produce `Nothing` (or fail gracefully)
     rather than a spurious type.
- **Files:** `src/core/typing_grammar.ts`, test files
- **Depends on:** Nothing (can start immediately).

#### PBI #20: T-Sub (subsumption) — decide explicit vs implicit and implement

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Decide whether T-Sub needs an explicit grammar production or whether the current
  implicit subsumption (via `isSubtype` in `@requires` at each use site) is sufficient. If explicit,
  implement; if implicit, document the decision and add tests.
- **Current state:** `isSubtype` is called in `app`, `variantCon`, `obs`, `fold`, `unfold`, and
  `typeApp` `@requires`/premises. Subsumption is built in.
- **Files:** `src/core/typing_grammar.ts`, test files
- **Depends on:** #19 (Nothing propagation should land first so subsumption tests cover the bottom
  case).

#### PBI #21: Strengthen `@ensures` contracts to encode Progress theorem

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Make `@ensures` contracts strong enough that a successful parse _is_ a Progress proof
  for the parsed term. The `@requires`/`@ensures` split mirrors the premise/conclusion structure of
  the inference rule; Progress is a consequence of the premises, not a separate postcondition.
- **Current state:** `@ensures` contracts exist on all productions with Progress comments (e.g.,
  `lam`: `result instanceof FunType`; `app`: follows from `@requires`; `variantCon`: value or step;
  `obs`: step; `fold`: step; `unfold`: value). Need to verify contract composition and add a
  Progress proof test.
- **Tasks:**
  1. Verify contract composition — sub-term Progress implies super-term Progress across the grammar
     hierarchy.
  2. Add Progress proof test — parse a term, verify `@ensures` contracts were checked (via
     metadata), verify Progress holds.
- **Files:** `src/core/typing_grammar.ts`, `src/core/eval_grammar.ts`, test files
- **Depends on:** #19, #20 (Nothing and subsumption should be settled so Progress covers all cases).

### Milestone v0.3.0 — Laws

#### PBI #22: Law/properties machinery — make algebraic laws operationally exploitable

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Laws are one of the three irreducible essentials of Lapis (types, terms, laws). Design
  and implement machinery that makes algebraic laws (e.g., functor laws, monoid laws) operationally
  exploitable — not just documentation, but checked/applied by the language.
- **Scope:** TBD — this is a design-heavy PBI. Likely involves:
  1. A law declaration syntax or metadata mechanism.
  2. A law-checking pass (possibly via `SemanticPass` over `DerivationTree`).
  3. Integration with the type system (e.g., law-based rewriting, law-driven optimization).
- **Files:** TBD
- **Depends on:** #21 (Progress contracts must be solid before laws can build on them).

### Milestone v0.4.0 — Patterns & surface

#### PBI #23: T-FoldMatch + E-FoldMatch — pattern-matched fold (elimination)

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Implement `fold [T] e {pᵢ → tᵢ}` — pattern-matched fold for data types. Each handler
  binds `match` (the `Token`) and produces σ.
- **Tasks:**
  1. Add `T-FoldMatch` to `typing_grammar.ts` — type-check pattern handlers.
  2. Add `E-FoldMatch` to `eval_grammar.ts` — scrutinee is `MatchVal`, handler binds `match` to the
     token.
  3. Add productions + semantic actions for `patternFold` in the grammar (AST builder, type checker,
     evaluator).
  4. Add tests.
- **Files:** `src/core/grammar.ts`, `src/core/typing_grammar.ts`, `src/core/eval_grammar.ts`, test
  files
- **Depends on:** #24 (T-Pattern introduces the patterns that FoldMatch matches).

#### PBI #24: T-Pattern — pattern-matched construction (introduction)

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Implement `match(pₖ)` — pattern-matched construction. Patterns are introduced by the
  lexer and used by `T-FoldMatch` (#23).
- **Tasks:**
  1. Add pattern syntax to the lexer/grammar.
  2. Add `T-Pattern` to `typing_grammar.ts`.
  3. Add tests.
- **Files:** `src/core/grammar.ts`, `src/core/typing_grammar.ts`, test files
- **Depends on:** Nothing (can start immediately, but #23 depends on it).

#### PBI #25: Surface language elaboration pipeline (`DerivationTree` + `SemanticPass`)

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Use `DerivationTree` + `SemanticPass` for the surface language elaboration pipeline. The
  LC core keeps the one-pass grammar approach; the surface language uses parse-to-tree +
  tree-consuming passes.
- **Current state:** `parseToTree` and `SemanticPass` are validated on the LC grammar (see
  `test/derivation.test.ts`). The surface language pipeline is not yet built.
- **Tasks:**
  1. Design the surface language pipeline:
     - Surface grammar parses to `DerivationTree` (structural)
     - `NameResolverPass extends SemanticPass` resolves names (tree-consuming)
     - `ElaboratorPass extends SemanticPass` elaborates to LC terms (tree-consuming)
     - LC terms are then type-checked/evaluated via the one-pass grammar
  2. Implement the surface grammar (structural phase).
  3. Implement `NameResolverPass` and `ElaboratorPass`.
  4. Document the hybrid architecture — one-pass for LC core, two-phase for surface language.
- **Files:** New `src/surface/` directory, `_docs/theory/`, test files
- **Depends on:** #23, #24 (patterns are part of the surface language).

#### PBI #26: Cleanup — Remove dead code and consolidate after surface language

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Remove redundant code and consolidate after the surface language lands.
- **Tasks:**
  1. Remove or justify any remaining dead code from `src/core/`.
  2. Generate `lc.md` inference rules from `toInference()` — the formal specification and
     implementation generated from the same source.
  3. Update `index.ts` exports to reflect the final API surface.
- **Files:** All `src/` files, `_docs/theory/lc.md`
- **Depends on:** #25 (surface language must land first).

## Dependency Graph

```
v0.1.1 — Clean core
  #15 (CodataType observers API)
  #16 (consolidate index.ts)
  #17 (remove/justify LCAST + Term)
  #18 (this document) ← in progress
      ↓
v0.2.0 — Sound core
  #19 (Nothing propagation)      ← no dependency, do first
      ↓
  #20 (T-Sub subsumption)        ← depends on #19
      ↓
  #21 (Progress @ensures)        ← depends on #19, #20
      ↓
v0.3.0 — Laws
  #22 (law/properties machinery) ← depends on #21
      ↓
v0.4.0 — Patterns & surface
  #24 (T-Pattern)                ← no dependency, can start anytime
      ↓
  #23 (T-FoldMatch + E-FoldMatch) ← depends on #24
      ↓
  #25 (surface elaboration)      ← depends on #23, #24
      ↓
  #26 (final cleanup)            ← depends on #25
```

## Success Criteria

- [x] Every valid LC input produces exactly one parse tree (v4.0.2)
- [x] Fold handler bodies type-checked under correct σ via `parseToFixpoint`
- [x] Every contract has `ContractMeta` with rule name + formula
- [x] `toInference()` generates rules matching `lc.md` §5
- [x] `DerivationTree` + `SemanticPass` validated on LC grammar
- [ ] `Nothing` propagation in grammar-based checker (#19)
- [ ] T-Sub subsumption decided and implemented/documented (#20)
- [ ] `@ensures` contracts fully encode the Progress theorem (#21)
- [ ] Law/properties machinery designed and implemented (#22)
- [ ] T-Pattern: pattern-matched construction (#24)
- [ ] T-FoldMatch + E-FoldMatch: pattern-matched fold (#23)
- [ ] Surface language elaboration pipeline (#25)
- [ ] Dead code removed, `lc.md` generated from grammar, exports consolidated (#15–#17, #26)
- [ ] All tests pass, lint clean, format clean
