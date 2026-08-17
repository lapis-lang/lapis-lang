# LC Core Implementation Plan — lang-forma v1.1.0

> **Status:** Active plan. `@lapis-lang/lang-forma@1.1.0` is installed (migrated from
> `@lapis-lang/zipper-grammar@4.1.0` — a compatible superset) and all 57 existing tests pass. This
> plan tracks the remaining work via the GitHub issue tracker (PBIs #19–#26, #30–#35).
>
> **lang-forma migration note:** The grammar engine was migrated from `zipper-grammar` to its
> successor `lang-forma` (drop-in API-compatible). `lang-forma` adds six feature families that
> subsume or accelerate existing PBIs — first-class inference rules (#30), metatheory verification
> (#31), generative counterexample search (#32), property-based testing (#33), unparse (#34), and a
> microKanren logic system (#35). See the PBI entries below for how each maps onto the roadmap.
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

#### PBI #30: Adopt lang-forma first-class inference rules (`Grammar.rules` / `collectRules`)

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Replace the hand-rolled `LCTypeCheck.toInference()` with the library's
  `Grammar.rules()` / `collectRules()`. The library `FormattedInferenceRule` shape is richer (side
  conditions, frame conditions, per-clause method linkage) and standardized, and `formatRule()`
  gives us the `lc.md` rule renderer that #26 needs.
- **Files:** `src/core/typing_grammar.ts`, `src/core/index.ts`, `test/metadata.test.ts`
- **Depends on:** Nothing. Unblocks #21, #26, #31.

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

#### PBI #31: Metatheory verification — mechanize Progress + Preservation via `lang-forma`

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Use `lang-forma`''s metatheory engine (`Grammar.metatheory()`, `verifyMetatheory`,
  `checkProgress`, `checkPreservation`) to _verify_ Progress and Preservation over the LC grammar''s
  dynamic-semantics rules, instead of arguing them by hand. Subsumes the "add a Progress proof test"
  task in #21 and adds Preservation (which #21 does not cover).
- **Tasks:**
  1. Add `@requires`/`@ensures` + `rule`/`formula`/`role` metadata to `LCEval` (the eval grammar
     currently has none) — this is the encoding work #21 was already going to do for the type
     checker, extended to the evaluator.
  2. Add `test/metatheory.test.ts` — call `verifyMetatheory(LCEval, LCTypeCheck)`, assert
     `report.progress.holds` and `report.preservation.holds`.
- **Files:** `src/core/eval_grammar.ts`, `test/metatheory.test.ts`, `_docs/theory/`
- **Depends on:** #30 (library rule shape), #19, #20 (core must be sound first). Subsumes the
  verification half of #21.

#### PBI #32: Generative counterexample search — dynamically test Progress + Preservation

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Use `lang-forma`''s `findCounterexamples(evalGrammar, typeCheckGrammar, options)` to
  _generate_ well-formed terms and check Progress/Preservation dynamically — the dynamic complement
  to the static metatheory in #31. Catches soundness bugs the static analysis misses (e.g., an
  underspecified `@requires` premise).
- **Files:** `test/counterexamples.test.ts`, `test/fixtures.ts`
- **Depends on:** #31 (do the static check first), #19, #20. Companion to #31 in v0.2.0.

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

#### PBI #33: Property-based testing — `GrammarGenerator` / `ValueGenerator` (`forAll` + shrinking) for LC laws

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Use `lang-forma`''s native property-testing adapter (`Grammar.toGenerator()`,
  `ValueGenerator.forAll()`) as the _verification harness_ for #22. Algebraic laws are
  universally-quantified properties over well-formed terms; the library generates, checks, and
  shrinks them with grammar-aware shrinking (no hand-written `Arbitrary<T>`).
- **Tasks:**
  1. `test/laws.test.ts` — scaffold + identity-fold law as proof-of-concept.
  2. Tune `GeneratorOptions` (`maxDepth`, `maxRecursion`, `branchStrategy: "random"`).
  3. Document the law-as-property pattern in `_docs/theory/`.
- **Files:** `test/laws.test.ts`, `test/fixtures.ts`, `_docs/theory/`
- **Depends on:** #22 (law declarations), #19, #20, #21 (core soundness). Belongs in v0.3.0.

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

#### PBI #34: Unparse + pretty-print — `UnparsePass` / `Grammar.unparse` for round-tripping and error reporting

- **Status:** Open
- **Assignee:** @mlhaufe
- **Goal:** Use `lang-forma`''s unparse facility (`Grammar.unparse(tree)`, `UnparsePass`) for (a)
  round-trip verification (parse → tree → unparse → parse, assert equality) — valuable for the
  surface elaboration in #25 — and (b) error reporting that surfaces the exact source span of a
  type/eval error (the `Counterexample.source` field from #32 is already unparsed).
- **Tasks:**
  1. `test/unparse.test.ts` — round-trip tests over representative LC inputs.
  2. Re-export `UnparsePass`, `unparse` from `src/core/index.ts`.
  3. (Optional) store span/tree on `EvalErrorValue` for unparse-on-demand.
- **Files:** `test/unparse.test.ts`, `src/core/index.ts`, (optional) `src/core/eval_grammar.ts`
- **Depends on:** None for the round-trip test; #32 for the error-reporting wiring. Belongs in
  v0.4.0 (most valuable once #25 lands, but the core round-trip can land earlier).

#### PBI #35: Unification-based type inference — evaluate `lang-forma` microKanren for law-solving

- **Status:** Open (design evaluation)
- **Assignee:** @mlhaufe
- **Goal:** Evaluate `lang-forma`''s microKanren logic system (`Var`, `Term`, `unify`, `fresh`,
  `conj`, `disj`, `run`) for two uses: (1) strengthening Preservation via the `unification` field of
  `checkPreservation` (#31), and (2) law-_solving_ for #22 (expressing a law as a relation and using
  `run` to find the fused form). This is a _design evaluation_, not an implementation — the current
  design avoids unification by requiring declared types + subtyping (#20).
- **Tasks:**
  1. Inspect `report.preservation.unification` in the metatheory test (#31) — is it populated?
  2. Prototype a law-as-relation spike (`test/laws-prototype.test.ts`).
  3. Decision gate: integrate the logic system into #22, or keep subtyping-only? Document in
     `_docs/theory/`.
- **Files:** `test/metatheory.test.ts` (extends #31), `test/laws-prototype.test.ts` (exploratory),
  `_docs/theory/`
- **Depends on:** #31. Informs #22. No milestone — land the evaluation before v0.3.0 design is
  finalized.

## Dependency Graph

```
v0.1.1 — Clean core
  #15 (CodataType observers API)
  #16 (consolidate index.ts)
  #17 (remove/justify LCAST + Term)
  #18 (this document) ← in progress
  #30 (adopt Grammar.rules)      ← no dependency; unblocks #21, #26, #31
      ↓
v0.2.0 — Sound core
  #19 (Nothing propagation)      ← no dependency, do first
      ↓
  #20 (T-Sub subsumption)        ← depends on #19
      ↓
  #21 (Progress @ensures)        ← depends on #19, #20, #30
      ↓
  #31 (metatheory verification)  ← depends on #30, #19, #20; subsumes #21 verification
      ↓
  #32 (generative counterexamples) ← depends on #31, #19, #20
      ↓
v0.3.0 — Laws
  #22 (law/properties machinery) ← depends on #21
      ↓
  #33 (property-based testing)   ← depends on #22, #19, #20, #21
      ↓
  #35 (unification evaluation)   ← depends on #31; informs #22 (no milestone)
      ↓
v0.4.0 — Patterns & surface
  #24 (T-Pattern)                ← no dependency, can start anytime
      ↓
  #23 (T-FoldMatch + E-FoldMatch) ← depends on #24
      ↓
  #25 (surface elaboration)      ← depends on #23, #24
      ↓
  #34 (unparse + round-trip)     ← no dependency for core; #32 for error reporting
      ↓
  #26 (final cleanup)            ← depends on #25
```

## Success Criteria

- [x] Every valid LC input produces exactly one parse tree (v4.0.2)
- [x] Fold handler bodies type-checked under correct σ via `parseToFixpoint`
- [x] Every contract has `ContractMeta` with rule name + formula
- [x] `toInference()` generates rules matching `lc.md` §5
- [x] `DerivationTree` + `SemanticPass` validated on LC grammar
- [x] Migrated to `@lapis-lang/lang-forma@1.1.0` (compatible superset of `zipper-grammar`)
- [ ] Adopt `Grammar.rules()` / `collectRules()` — replace hand-rolled `toInference()` (#30)
- [ ] `Nothing` propagation in grammar-based checker (#19)
- [ ] T-Sub subsumption decided and implemented/documented (#20)
- [ ] `@ensures` contracts fully encode the Progress theorem (#21)
- [ ] Progress + Preservation mechanized via `verifyMetatheory` (#31)
- [ ] Generative counterexample search via `findCounterexamples` (#32)
- [ ] Law/properties machinery designed and implemented (#22)
- [ ] Property-based law testing via `forAll` + grammar-aware shrinking (#33)
- [ ] Unification evaluation for law-solving (#35)
- [ ] T-Pattern: pattern-matched construction (#24)
- [ ] T-FoldMatch + E-FoldMatch: pattern-matched fold (#23)
- [ ] Surface language elaboration pipeline (#25)
- [ ] Unparse + round-trip verification (#34)
- [ ] Dead code removed, `lc.md` generated from grammar, exports consolidated (#15–#17, #26)
- [ ] All tests pass, lint clean, format clean
