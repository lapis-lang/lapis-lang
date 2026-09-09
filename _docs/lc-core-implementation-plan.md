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

### What Works (117 tests passing, lang-forma v1.1.0)

| Component                                                      | Status                                                                                                                     | Files                                        |
| -------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------- |
| Types                                                          | ✅ Complete                                                                                                                | `types.ts`                                   |
| Terms                                                          | ✅ Complete                                                                                                                | `terms.ts`                                   |
| Values (incl. `SpanClosure`, `SpanCodataVal`)                  | ✅ Complete                                                                                                                | `values.ts`                                  |
| Subtyping (S-Refl through S-And-Elim)                          | ✅ Complete                                                                                                                | `subtyping.ts`                               |
| `join` / `meet` lattice operations                             | ✅ Complete                                                                                                                | `subtyping.ts`                               |
| Concrete syntax grammar (AbstractLC + LCAST)                   | ✅ Complete                                                                                                                | `grammar.ts`                                 |
| TypeRegistry with reverse lookups                              | ✅ Complete                                                                                                                | `grammar.ts`                                 |
| Type-checking grammar (LCTypeCheck)                            | ✅ T-Var, T-Abs, T-App, T-Let, T-Variant, T-Obs, T-Fold, T-Unfold, T-TAbs, T-TApp, T-Cofold, T-Sub (implicit)              | `typing_grammar.ts`                          |
| Evaluation grammar (LCEval)                                    | ✅ E-App, E-Let, E-Fold, E-Unfold, E-Obs, E-Cofold, E-TApp via `_forward`; `@requires`/`@ensures` contracts on all 9 rules | `eval_grammar.ts`                            |
| `parseToFixpoint` for fold σ                                   | ✅ Complete — wired into `foldProd` (line 539)                                                                             | `typing_grammar.ts`                          |
| Contract metadata (`@requires`/`@ensures`/`@rule`)             | ✅ Complete — all typing + eval rules have `rule` + `formula` + `type` metadata                                            | `typing_grammar.ts`, `eval_grammar.ts`       |
| First-class inference rules (`Grammar.rules` / `collectRules`) | ✅ Complete — lang-forma rule model replaces hand-rolled `toInference()`                                                   | `typing_grammar.ts`, `eval_grammar.ts`       |
| `@ensures` Progress contracts                                  | ✅ Complete — each production encodes its Progress case; verified by `checkProgress`                                       | `typing_grammar.ts`, `eval_grammar.ts`       |
| Metatheory verification (`verifyMetatheory`)                   | ✅ Complete — Progress + Preservation (static + unification) all hold                                                      | `eval_grammar.ts`, `test/metatheory.test.ts` |
| `DerivationTree` + `SemanticPass`                              | ✅ Validated — `parseToTree` + tree-consuming passes work on LC grammar                                                    | `grammar.ts`, test files                     |
| Grammar ambiguity (single parse tree)                          | ✅ Resolved (v4.0.2) — all tests assert `result.size === 1`                                                                | all test files                               |

> **Note:** There are no `typing.ts`, `eval.ts`, or `soundness.ts` files. The grammar-based
> `LCTypeCheck` and `LCEval` are the sole implementations; soundness is encoded directly in
> `@ensures` contracts (Progress) and the grammar structure (Preservation).

### What's Missing or Incomplete

| Component                        | Status             | Notes                                                                                                                                        | PBI          |
| -------------------------------- | ------------------ | -------------------------------------------------------------------------------------------------------------------------------------------- | ------------ |
| `Nothing` propagation            | ✅ Complete        | `variantCon`, `obs`, `fold`, `unfold` propagate the bottom type (explosion semantics)                                                        | #19          |
| T-TApp premise enforcement       | ✅ Complete        | `typeAppProd` override rejects non-polymorphic bodies and bound violations (no `undefined` in forest)                                        | #39          |
| Type-variable reference          | ✅ Complete        | `typeAbsProd` binder uses `typeName` (uppercase); bound type vars can appear in annotations                                                  | #42          |
| Type-variable lexical scoping    | ✅ Complete        | `Δ` (TypeVarEnv) threaded through type productions; bound type vars resolve to `TypeVar` with declared bound; reserved binder names rejected | #44          |
| T-Sub (subsumption)              | ✅ Complete        | Implicit subsumption at use sites via `isSubtype` in `@requires`; T-Let premise 1 enforced in `letProd` override                             | #20          |
| `@ensures` for Progress          | ✅ Complete        | Contracts on all typing rules encode Progress cases; verified by `checkProgress` (no gaps)                                                   | #21          |
| Metatheory verification          | ✅ Complete        | `verifyMetatheory(LCEval, LCTypeCheck)` — Progress + Preservation (static + unification) all hold; 12 tests in `metatheory.test.ts`          | #31          |
| Generative counterexample search | ✅ Complete        | `findCounterexamples(LCEval, LCTypeCheck)` — 500 generated terms, 0 counterexamples; 5 tests in `counterexamples.test.ts`                    | #32          |
| Law/properties machinery         | ❌ Not started     | Algebraic laws are one of the three irreducible essentials of Lapis; no operational exploitation yet                                         | #22          |
| T-FoldMatch + E-FoldMatch        | ❌ Not implemented | `fold [T] e {pᵢ → tᵢ}` — pattern-matched fold (elimination)                                                                                  | #23          |
| T-Pattern                        | ❌ Not implemented | `match(pₖ)` — pattern-matched construction (introduction)                                                                                    | #24          |
| Surface language elaboration     | ❌ Not started     | `DerivationTree` + `SemanticPass` pipeline for surface → LC core                                                                             | #25          |
| Dead code / consolidation        | ❌ Not started     | Remove or justify LCAST AST builder, consolidate `index.ts` exports                                                                          | #15–#17, #26 |

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

- **Status:** Complete
- **Assignee:** @mlhaufe
- **Goal:** Replace the hand-rolled `LCTypeCheck.toInference()` with the library's `Grammar.rules()`
  / `collectRules()`. The library `FormattedInferenceRule` shape is richer (side conditions, frame
  conditions, per-clause method linkage) and standardized, and `formatRule()` gives us the `lc.md`
  rule renderer that #26 needs.
- **Files:** `src/core/typing_grammar.ts`, `src/core/index.ts`, `test/metadata.test.ts`
- **Depends on:** Nothing. Unblocks #21, #26, #31.
- **Breaking change (v0.1.x):** The exported `InferenceRule` type changed shape —
  `premises: string[]` → `RuleClause[]`, `conclusion: string` → `RuleClause[]`, `production: string`
  → `production?: string` (plus new `sideConditions`, `frameConditions`, `methods`).
  `LCTypeCheck.toInference()` is removed; use the static `LCTypeCheck.rules` getter or
  `collectRules(LCTypeCheck)`. Note for #26: `Grammar.rules` recomputes on every access (walks the
  inheritance chain) — cache the result in the doc generator.

### Milestone v0.2.0 — Sound core

#### PBI #19: `Nothing` propagation in grammar-based type checker

- **Status:** Complete
- **Assignee:** @mlhaufe
- **Goal:** Propagate `Nothing` (bottom type) through the grammar-based checker. When a sub-term has
  type `Nothing`, the surrounding term should also be `Nothing` (or handled per the rule), not
  silently treated as well-typed.
- **Result:** `variantCon`, `obs`, `fold` (both the semantic action and `evalFoldFixpoint`, the live
  path), `unfold`, and `cofold` now return `Nothing` when an eagerly-evaluated sub-term has type
  `Nothing` (principle of explosion — matches TAPL `rcdsubbot`'s `TyBot` propagation). Since
  `Nothing <: σ` for all σ, the result still flows anywhere via subsumption. Ordering guarantee:
  propagation applies only when the term is otherwise well-typed — genuine premise violations
  (unknown name, non-exhaustive handlers, field type mismatch) still yield the pre-existing failure
  signal for that rule (rejection or `Any`, depending on the site), never a spurious `Nothing`.
  Boundary: `app` in the fn position rejects a `Nothing` function (empty forest); `app`/`let` in the
  arg/def positions do not propagate (the sub-term is consumed, not observed).
  `test/nothing.test.ts` covers propagation through all five productions, non-masking of errors,
  boundary positions, and nested composition.
- **Files:** `src/core/typing_grammar.ts`, `test/nothing.test.ts`
- **Depends on:** Nothing (can start immediately).

#### Bug #39: `typeApp` on a non-polymorphic body puts `undefined` in the parse forest

- **Status:** Complete
- **Assignee:** @mlhaufe
- **Goal:** Enforce the T-TApp premises in the production path. The base `typeAppProd` folds over
  `[τ]` suffixes without checking, so a failed premise fell through to the `typeApp` semantic
  action, which cast the body and read `.body` off a non-polymorphic type — putting `undefined` in
  the parse forest. The `@requires` premise is declarative metadata (for the rule model), not a
  runtime check.
- **Result:** `typeAppProd` is overridden in `LCTypeCheck` with the same chain formulation as the
  `appProd` override: parse atom → parse `[τ]` → check
  `body instanceof PolymorphicType ∧
  argType <: body.bound` → `ε(τ[α:=argType])` on success, `∅`
  (rejection) on failure. Each application in a chain `t[τ₁][τ₂]` is checked individually.
  Rejections: `Zero()[Stack]`, bound violations (`(^α <: Stack. …) [Nat]`), chaining past a
  non-polymorphic result. Well-formed cases (bound satisfied, chained applications) are unchanged.
- **Files:** `src/core/typing_grammar.ts`, `test/polymorphism.test.ts`
- **Depends on:** Nothing (found during the #19 review; verified pre-existing on `master`).

#### Bug #42: Type variables cannot be referenced in type annotations

- **Status:** Complete
- **Assignee:** @mlhaufe
- **Goal:** Align the type-variable binder and reference grammars. `typeAbsProd` bound the type
  variable via the lowercase-first `ident` production, but type positions (`atomType` → `typeName`)
  only accept uppercase-first identifiers — so a bound type variable could never be referenced in a
  type annotation (`\x:alpha. x` didn't parse). This made `substituteTypeVar` dead code for any term
  that mentioned α, and blocked meaningful subsumption tests for #20.
- **Result:** `typeAbsProd` now uses `typeName` (uppercase-first) for the binder, matching the
  type-position grammar. An unregistered uppercase name already resolves to a `TypeVar` in
  `atomType`, so the binder and reference sites share one identifier grammar. Type variables are now
  uppercase (e.g. `^A <: Any. \x:A. x`), consistent with the TAPL `fullfsub` convention
  (`lambda X. lambda x:X. x`). The `substituteTypeVar` machinery is now exercisable:
  `(^A <: Any. \x:A. x) [Nat]` yields `Nat → Nat`.
- **Files:** `src/core/grammar.ts`, `test/polymorphism.test.ts`
- **Depends on:** Nothing (found during the #39 fix; verified pre-existing on `master`). Unblocks
  meaningful #20 subsumption tests.

#### Bug #44: Type variable name clashing with a registered type name resolves to the DataType

- **Status:** Complete
- **Assignee:** @mlhaufe
- **Goal:** Ensure references to bound type variables resolve to `TypeVar` with the declared bound,
  not to a registered `DataType` of the same name. Previously `atomType` resolved names via
  `this.registry.lookup(name)` before falling through to `TypeVar`, so a type variable sharing a
  name with a registered type would silently resolve to the wrong thing.
- **Result:** `Δ` (TypeVarEnv) is now threaded through type productions (`typeProd`/`atomType`), the
  same way `Γ` (TypeEnv) is threaded through term productions. `atomType` checks `Δ` **before** the
  registry, so a bound type variable resolves to a `TypeVar` carrying its declared bound. The type
  checker uses a combined `TypeCheckCtx` bundling `Γ` and `Δ`. The bound `σ` in `^A <: σ. t` is
  parsed under the outer `Δ` (the variable is not in scope in its own bound). `TypeVar.bound` now
  carries the declared bound (not always `Any`). Binder validation rejects built-in type names
  (`Any`, `Nothing`, `Token`) and registered type names — binding such a name would shadow a real
  type, which is misleading even with lexical scoping. The term is rejected (empty parse forest)
  instead.
- **Files:** `src/core/grammar.ts`, `src/core/typing_grammar.ts`, `src/core/eval_grammar.ts`,
  `test/polymorphism.test.ts`
- **Depends on:** #42 (type-variable reference must work before scoping can be fixed).

#### PBI #20: T-Sub (subsumption) — decide explicit vs implicit and implement

- **Status:** Complete
- **Assignee:** @mlhaufe
- **Goal:** Decide whether T-Sub needs an explicit grammar production or whether the current
  implicit subsumption (via `isSubtype` in `@requires` at each use site) is sufficient. If explicit,
  implement; if implicit, document the decision and add tests.
- **Decision:** **Implicit subsumption.** No standalone T-Sub production. Each consumer site
  enforces `isSubtype` in its own premise — `app`, `variantCon`, `obs`, `fold`, `unfold`, `cofold`,
  `typeApp`, and now `let_`. This is consistent with TAPL `fullfsub`, where subsumption is folded
  into each rule's premise check rather than being a separate rule the programmer invokes.
- **Result:** The T-Let premise 1 (`Γ ⊢ t : σ  ∧  σ <: τ`) was **completely unenforced** — `let_`
  ignored its `_type` and `_def` arguments, so `let x:Nat = \y:Any. y in x` was accepted as `Nat`
  even though `Any → Any` is not `<: Nat`. Fixed by overriding `letProd` in `LCTypeCheck`: after
  parsing the def and getting its type σ, check `isSubtype(σ, τ)` (the declared type). If the check
  fails, return `empty<Type>()` (ill-typed). If it passes, the body is parsed under `Γ + x:τ` (the
  declared type, widened via subsumption). The `@requires` decorator on `let_` is declarative
  metadata for the rule model (same lesson as #39 — `@requires` is not a runtime check). 11 new
  subsumption tests in `test/typing.test.ts` (105 total): S-Refl, S-Top, S-Bot at let-bindings;
  rejection of FunType/Bool/Any bound to a Nat declaration; nested let subsumption.
- **Files:** `src/core/typing_grammar.ts`, `test/typing.test.ts`, `test/metadata.test.ts`
- **Depends on:** #19 (Nothing propagation should land first so subsumption tests cover the bottom
  case).

#### PBI #21: Strengthen `@ensures` contracts to encode Progress theorem

- **Status:** Complete (subsumed by #31)
- **Assignee:** @mlhaufe
- **Goal:** Make `@ensures` contracts strong enough that a successful parse _is_ a Progress proof
  for the parsed term. The `@requires`/`@ensures` split mirrors the premise/conclusion structure of
  the inference rule; Progress is a consequence of the premises, not a separate postcondition.
- **Result:** `@ensures` contracts on all typing rules encode Progress cases. The verification
  (contract composition + Progress proof test) is mechanized by #31 —
  `checkProgress(LCEval.rules,
  LCEval)` reports `holds: true` with no gaps. The
  `@ensures`-strengthening work was the _encoding_; #31 provided the _checking_ via the lang-forma
  metatheory engine.
- **Files:** `src/core/typing_grammar.ts`, `src/core/eval_grammar.ts`, `test/metatheory.test.ts`
- **Depends on:** #19, #20 (Nothing and subsumption should be settled so Progress covers all cases).
- **Subsumed by:** #31 (metatheory verification — `checkProgress` replaces hand-verified contract
  composition).

#### PBI #31: Metatheory verification — mechanize Progress + Preservation via `lang-forma`

- **Status:** Complete
- **Assignee:** @mlhaufe
- **Goal:** Use `lang-forma`'s metatheory engine (`verifyMetatheory`, `checkProgress`,
  `checkPreservation`) to _verify_ Progress and Preservation over the LC grammar's dynamic-semantics
  rules, instead of arguing them by hand. Subsumes the "add a Progress proof test" task in #21 and
  adds Preservation (which #21 does not cover).
- **What was done:**
  1. Added `@requires`/`@ensures` + `rule`/`formula`/`role`/`type` metadata to all 9 `LCEval`
     semantic action methods (E-Lam, E-App, E-Let, E-Fold, E-Unfold, E-Obs, E-Cofold, E-TAbs,
     E-TApp). Value-rules (E-Lam, E-Unfold, E-TAbs) have no premises; step-rules (E-App, E-Let,
     E-Fold, E-Obs, E-Cofold, E-TApp) have one premise each.
  2. Added `@rule({ rule: "E-...", production: "...Prod" })` metadata to the 7 overridden production
     methods in `LCEval` (lambdaProd, appProd, letProd, foldProd, unfoldProd, obsProd, cofoldProd)
     for constructor-coverage linkage. E-TAbs and E-TApp use `production` in their `@ensures`
     metadata instead (their productions are not overridden in LCEval).
  3. Added `type: "τ"` to all premise/conclusion metadata so the Preservation check can verify type
     consistency (the `clauseTypeTokens` extractor checks `meta.type` first).
  4. Created `test/metatheory.test.ts` (12 tests): rule collection, classification, Progress,
     Preservation (static + unification), combined `verifyMetatheory`, rule formatting.
  5. Exported metatheory API (`checkProgress`, `checkPreservation`, `verifyMetatheory`, types) from
     `src/core/index.ts`.
- **Result:** `verifyMetatheory(LCEval, LCTypeCheck)` → `holds: true` (Progress: no gaps;
  Preservation: all 6 step-rules preserve type τ; unification: τ unifies with τ).
- **Files:** `src/core/eval_grammar.ts`, `src/core/index.ts`, `test/metatheory.test.ts`
- **Depends on:** #30 (library rule shape), #19, #20 (core must be sound first). Subsumes the
  verification half of #21.

#### PBI #32: Generative counterexample search — dynamically test Progress + Preservation

- **Status:** Complete
- **Assignee:** @mlhaufe
- **Goal:** Use `lang-forma`'s `findCounterexamples(evalGrammar, typeCheckGrammar, options)` to
  _generate_ well-formed terms and check Progress/Preservation dynamically — the dynamic complement
  to the static metatheory in #31. Catches soundness bugs the static analysis misses (e.g., an
  underspecified `@requires` premise).
- **What was done:**
  1. Created `test/counterexamples.test.ts` with 5 tests: Progress + Preservation (100 runs),
     different seed (200 runs), eval-only Progress (no type checker), reproducibility (same seed →
     same result), and a larger 500-run search. All pass with 0 counterexamples.
  2. Tuned `GeneratorOptions` for the LC grammar: `branchStrategy: "random"` is required (the
     grammar's 7-branch `exprProd` with 6 recursive alternatives causes the default depth-first
     strategy to exhaust the step budget before reaching terminal `atomProd` → `ident`).
     `maxDepth: 5, maxRecursion: 2, maxBacktracks: 500, maxSteps: 15000` produce ~95% generation
     success rate with a good mix of lambdas, variant calls, and variable references.
  3. Exported `findCounterexamples` +
     `Counterexample`/`CounterexampleOptions`/`CounterexampleResult` types from `src/core/index.ts`.
- **Key insight:** The LC grammar's wide `or(...)` fan-out in `exprProd` (7 alternatives, 6
  recursive) makes the default `depth-first` branch strategy impractical — it always tries recursive
  branches first and never reaches the terminal base case within budget. `branchStrategy: "random"`
  gives each branch a fair chance, letting the generator find paths through `obsProd` → `appProd` →
  `typeAppProd` → `atomProd` → `ident` (the only terminal path).
- **Files:** `test/counterexamples.test.ts` (new), `src/core/index.ts` (exports)
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
  2. Generate `lc.md` inference rules from `LCTypeCheck.rules` / `formatRule()` — the formal
     specification and implementation generated from the same source.
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
  #19 (Nothing propagation)      ← complete
  #39 (T-TApp premise enforced)  ← complete (bug found during #19 review; independent of #19)
  #42 (type-var binder/reference) ← complete (bug found during #39 fix; unblocks #20 tests)
  #44 (type-var lexical scoping)  ← complete (bug found during #42 review; depends on #42)
      ↓
  #20 (T-Sub subsumption)        ← complete (implicit subsumption; T-Let premise enforced)
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
- [x] `LCTypeCheck.rules` generates rules matching `lc.md` §5
- [x] `DerivationTree` + `SemanticPass` validated on LC grammar
- [x] Migrated to `@lapis-lang/lang-forma@1.1.0` (compatible superset of `zipper-grammar`)
- [x] Adopt `Grammar.rules()` / `collectRules()` — replace hand-rolled `toInference()` (#30)
- [x] `Nothing` propagation in grammar-based checker (#19)
- [x] T-TApp premises enforced in production path — no `undefined` in the parse forest (#39)
- [x] Type variables can be referenced in type annotations — binder uses `typeName` (#42)
- [x] Type variables resolve to `TypeVar` with declared bound — Δ threaded through type productions;
      reserved binder names rejected (#44)
- [x] T-Sub subsumption decided and implemented/documented (#20)
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
