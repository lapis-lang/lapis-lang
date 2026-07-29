# LC Core Implementation Plan — zipper-grammar v4.1.0

> **Status:** Active plan. zipper-grammar v4.1.0 is installed and all 62 existing tests pass. This
> plan incorporates the new library capabilities: `parseToFixpoint` (circular attribute flow),
> `Symbol.metadata` (contract metadata), `DerivationTree` + `SemanticPass` (tree-consuming passes),
> and `parseSegment` / `composeSegmentsL` (segment composition).
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

### What Works (54 tests passing, v4.0.0)

| Component                                    | Status                                                            | Files               |
| -------------------------------------------- | ----------------------------------------------------------------- | ------------------- |
| Types                                        | ✅ Complete                                                       | `types.ts`          |
| Terms                                        | ✅ Complete                                                       | `terms.ts`          |
| Values (incl. `SpanClosure`)                 | ✅ Complete                                                       | `values.ts`         |
| Subtyping (S-Refl through S-And-Elim)        | ✅ Complete                                                       | `subtyping.ts`      |
| `join` / `meet` lattice operations           | ✅ Complete                                                       | `subtyping.ts`      |
| Concrete syntax grammar (AbstractLC + LCAST) | ✅ Complete                                                       | `grammar.ts`        |
| TypeRegistry with reverse lookups            | ✅ Complete                                                       | `grammar.ts`        |
| Type-checking grammar (LCTypeCheck)          | ✅ T-Var, T-Abs, T-App, T-Let, T-Variant, T-Obs, T-Fold, T-Unfold | `typing_grammar.ts` |
| Evaluation grammar (LCEval)                  | ✅ E-App, E-Let, E-Fold, E-Unfold, E-Obs via `_forward`           | `eval_grammar.ts`   |
| Tree-walking type checker                    | ✅ Complete (all rules)                                           | `typing.ts`         |
| Tree-walking evaluator                       | ✅ Complete (all rules)                                           | `eval.ts`           |
| Soundness checks                             | ✅ Progress + Preservation                                        | `soundness.ts`      |

### What's Missing or Incomplete

| Component                    | Status             | Notes                                                         |
| ---------------------------- | ------------------ | ------------------------------------------------------------- |
| T-TAbs (type abstraction)    | ❌ Not implemented | `Λα <: σ. t` — bounded polymorphism                           |
| T-TApp (type application)    | ❌ Not implemented | `t [τ]` — type application                                    |
| T-Sub (subsumption)          | ❌ Not implemented | `Γ ⊢ t : σ ∧ σ <: τ ⟹ Γ ⊢ t : τ`                              |
| T-Cofold                     | ❌ Not implemented | `cofold [T] e {oⱼ(xⱼ) → t}` — codata elimination              |
| T-FoldMatch                  | ❌ Not implemented | `fold [T] e {pᵢ → tᵢ}` — pattern-matched fold                 |
| T-Pattern                    | ❌ Not implemented | `match(pₖ)` — pattern-matched construction                    |
| E-Cofold                     | ❌ Not implemented | Cofold evaluation                                             |
| E-TApp                       | ❌ Not implemented | Type application evaluation (type erasure)                    |
| Fold recursive field binding | ⚠️ Workaround      | Uses `Any` placeholder; `parseToFixpoint` now available       |
| Grammar ambiguity            | ⚠️ Bug             | 64 parse trees for simple fold; needs grammar restructuring   |
| `@ensures` contracts         | ⚠️ Weak            | Check `result !== undefined`, not full Progress/Preservation  |
| Contract metadata            | ❌ Not yet used    | `Symbol.metadata` + `ContractMeta` available in v4.0.0        |
| Inference rule generation    | ❌ Not yet built   | `Grammar.metadata` available; `toInference()` to build        |
| `Nothing` propagation        | ⚠️ Partial         | Only in tree-walking `checkApp`; not in grammar-based checker |

### New v4.0.0 Capabilities Available

| Feature                 | API                                                                             | Relevance                                                    |
| ----------------------- | ------------------------------------------------------------------------------- | ------------------------------------------------------------ |
| Circular attribute flow | `parseToFixpoint(sigma, parseBodies, join, eq?)`                                | Replaces `Any`-placeholder for fold σ                        |
| Contract metadata       | `@requires(pred, meta)`, `@ensures(pred, meta)`, `@rule(meta)`                  | Declarative rule formulas co-located with predicates         |
| Metadata reflection     | `Grammar.metadata` (static), `collectMetadata()`, `chainMetadata()`             | Generate inference rules, docs, cross-reference with `lc.md` |
| Derivation trees        | `parseToTree(input)` → `{ forest, trees }`                                      | Materialize parse structure as first-class trees             |
| Semantic passes         | `SemanticPass<S>` — subclass and override methods named after production labels | Tree-consuming passes (elaboration, law checking)            |
| Segment parsing         | `parseSegment()`, `checkpointAt()`, `composeSegmentsL()`                        | Parallel/incremental parsing                                 |
| Incremental re-parsing  | `reparseIncremental()`                                                          | IDE/tooling scenarios                                        |
| `@rule(meta)` factory   | `@rule({ production: "expr", description: "..." })`                             | Production-level metadata                                    |

## Plan

### Phase 1: Grammar Restructuring (no library dependency)

**Goal:** Eliminate grammar ambiguity. Every valid input should produce exactly one parse tree.

**Tasks:**

1. **Restructure `obsProd` and `appProd`** to use proper precedence levels instead of overlapping
   left-recursive alternatives. The current structure produces intermediate results during
   left-recursion growth.

2. **Verify single-parse-tree property** with a test that asserts `result.size === 1` for
   unambiguous inputs.

3. **Update all tests** to assert `result.size === 1` instead of `result.size >= 1`.

   > **Done (v4.0.2).** All tests now assert `result.size === 1`. The last duplicate (`fold` eval on
   > a 0-arg variant) was a redundant `.opt()` on `sepBy` in `foldHandler`/`spanFoldHandler` —
   > `sepBy` already matches empty, so `.opt()` added a second empty path. Removed in both
   > `grammar.ts` and `eval_grammar.ts`. See zipper-grammar #32 for the full investigation.

**Files:** `src/core/grammar.ts`, all test files

### Phase 2: Circular Attribute Flow via `parseToFixpoint`

**Goal:** Replace the `Any`-placeholder workaround for fold recursive field bindings with proper
fixpoint iteration using `parseToFixpoint`.

**v4.0.0 API:**

```typescript
parseToFixpoint<S>(
    sigma: S,                                    // initial σ₀ (Any)
    parseBodies: (sigma: S) => readonly S[],       // parse handler bodies under σ
    join: (a: S, b: S) => S,                     // lattice join (our join())
    eq?: (a: S, b: S) => boolean,                 // fixpoint detection
    maxIterations?: number,                      // safety cap
): S
```

**Tasks:**

1. **Override `foldProd` in `LCTypeCheck`** to use `parseToFixpoint`:
   - Start with σ₀ = `Any`
   - Parse all handler bodies under σ₀ (recursive fields bound to σ₀)
   - Compute σ₁ = `join` of all body results
   - Iterate until σₙ₊₁ = σₙ (fixpoint reached)
   - Monotonicity is checked automatically by the library

2. **Remove `foldFieldType` workaround** — no longer needed once `parseToFixpoint` provides the
   correct σ.

3. **Apply same pattern to `unfoldProd`** — the `self` binding should reference the seed type Σ,
   resolved via fixpoint if needed.

4. **Add tests** verifying handler bodies are type-checked under correct σ:
   - A fold where `rest` is used as `Stack` (not `Any`) should type-check
   - A fold where handler bodies disagree should fail (empty forest)

**Files:** `src/core/typing_grammar.ts`, test files

### Phase 3: Contract Metadata + Inference Rule Generation

**Goal:** Add declarative metadata to all contracts and enable `toInference()` for generating formal
rules from the grammar.

**v4.0.0 API:**

```typescript
// Add metadata to contracts:

// Access metadata:
const meta = LCTypeCheck.metadata // ContractMetadataReport
// meta.methods.app.requires[0].meta → { rule: "T-App", formula: "..." }
```

**Tasks:**

1. **Add `ContractMeta` to every `@requires`/`@ensures`** in `typing_grammar.ts` and
   `eval_grammar.ts`:
   - `rule`: the inference rule name (e.g., `"T-App"`)
   - `role`: `"premise"` or `"conclusion"`
   - `formula`: the logical formula as a string
   - `description`: human-readable explanation

2. **Add `@rule(meta)` to productions** with production-level metadata:
   ```typescript
   @rule({ production: "exprProd", description: "main expression production" })
   exprProd(ctx: unknown): Parser<S["expr"]> { ... }
   ```

3. **Build `toInference()` helper** that walks `Grammar.metadata` and produces structured
   `InferenceRule[]`:
   ```typescript
   interface InferenceRule {
       name: string // "T-App"
       premises: string[] // ["fn : σ → τ", "arg <: σ"]
       conclusion: string // "result : τ"
       production: string // "app" (method name)
   }
   ```

4. **Add cross-referencing test** that checks every rule in `lc.md` §5 has a corresponding grammar
   production with metadata.

5. **Generate `lc.md` inference rules** from the grammar (or verify they match).

**Files:** `src/core/typing_grammar.ts`, `src/core/eval_grammar.ts`, `src/core/index.ts`, test files

### Phase 4: Strengthen `@ensures` for Progress

**Goal:** Make `@ensures` contracts strong enough that a successful parse _is_ a Progress proof for
the parsed term. The `@requires`/`@ensures` split mirrors the premise/conclusion structure of the
inference rule; Progress is a consequence of the premises, not a separate postcondition.

**Tasks:**

1. **Define Progress invariants per production.** Each production's `@ensures` should encode the
   Progress case for its term form, leveraging the `@requires` premises:
   - `lam`: "a lambda is always a value" → `result instanceof FunType`
   - `app`: "an application can always step" — follows from `@requires` (fn has function type) +
     grammar structure
   - `let`: "a let can always step" — follows from structure
   - `variantCon`: "a variant with value args is a value" — follows from eager evaluation
   - `fold`: "a fold can step" — follows from `@requires` (scrutinee : T)
   - `unfold`: "an unfold is always a value (codata value)"
   - `obs`: "an observation can step" — follows from `@requires`

2. **Verify contract composition** — sub-term Progress implies super-term Progress across the
   grammar hierarchy.

3. **Add Progress proof test** — parse a term, verify `@ensures` contracts were checked (via
   metadata), verify Progress holds.

**Files:** `src/core/typing_grammar.ts`, `src/core/eval_grammar.ts`, test files

### Phase 5: Complete Missing Typing Rules

**Goal:** Implement all typing rules from `lc.md` §5.

**Tasks:**

1. **T-Sub (subsumption).** May be implicit in `@requires` checks (if `arg <: param`, not just
   `arg = param`). Evaluate whether explicit T-Sub is needed or if subsumption is built into each
   rule's `@requires`.

2. **T-TAbs (type abstraction).** Add `Λα <: σ. t` to the grammar. Extends Δ (type variable context)
   with `α <: σ`. Result type is `∀α <: σ. τ`. Requires threading Δ through the grammar alongside Γ.

3. **T-TApp (type application).** Add `t [τ]` to the grammar. Checks `∀α <: σ. τ` type, verifies
   `τ₂ <: σ`, returns `τ[α := τ₂]`. Requires type substitution.

4. **T-Cofold.** Add `cofold [T] e {oⱼ(xⱼ) → t}` — codata elimination. Handler receives all
   observation results and produces σ.

5. **T-FoldMatch.** Add `fold [T] e {pᵢ → tᵢ}` for pattern-matched data. Each handler binds `match`
   (the Token) and produces σ.

6. **T-Pattern.** Add `match(pₖ)` construction (introduced by lexer).

7. **`Nothing` propagation in grammar-based checker.** Add `Nothing` checks to `variantCon`, `obs`,
   `fold`, `unfold` in `typing_grammar.ts`.

**Files:** `src/core/grammar.ts`, `src/core/typing_grammar.ts`, `src/core/typing.ts`, test files

### Phase 6: Complete Missing Evaluation Rules

**Goal:** Implement all evaluation rules from `lc.md` §3.

**Tasks:**

1. **E-Cofold.** Add `cofold` to `LCEval`. Observe all generators, bind results to handler bindings,
   re-evaluate handler body via `_forward`.

2. **E-TApp.** Add type application to `LCEval`. Type erasure: evaluate the body directly (types
   erased at runtime).

3. **E-FoldMatch.** Add pattern-matched fold to `LCEval`. Scrutinee is `MatchVal`, handler binds
   `match` to the token.

4. **Add productions + semantic actions** for cofold, typeApp, patternFold in the grammar (AST
   builder, type checker, evaluator).

**Files:** `src/core/grammar.ts`, `src/core/eval_grammar.ts`, `src/core/eval.ts`, test files

### Phase 7: Derivation Trees + SemanticPass for Surface Language

**Goal:** Use v4.0.0's `DerivationTree` + `SemanticPass` for the surface language elaboration
pipeline. The LC core keeps the one-pass grammar approach; the surface language uses parse-to-tree +
tree-consuming passes.

**v4.0.0 API:**

```typescript
// Parse to tree (structural phase):
const { forest, trees } = grammar.parseToTree(input);
// trees[0] is a DerivationTree with labeled nodes, spans, children

// Tree-consuming pass (attribute phase):
class ElaboratorPass extends SemanticPass<{ expr: LCTerm }> {
    exprProd(node: DerivationNode, children: LCTerm[]): LCTerm { ... }
    lambdaProd(node: DerivationNode, children: LCTerm[]): LCTerm { ... }
    // ... override methods named after production labels
}
const result = new ElaboratorPass().evaluate(trees[0]);
```

**Tasks:**

1. **Evaluate `parseToTree` on LC grammar** — verify it produces useful `DerivationTree`s with
   correct labels and spans.

2. **Prototype a `SemanticPass`** for a simple tree-consuming type check over the LC grammar, to
   validate the two-phase approach works for our calculus.

3. **Design the surface language pipeline:**
   - Surface grammar parses to `DerivationTree` (structural)
   - `NameResolverPass extends SemanticPass` resolves names (tree-consuming)
   - `ElaboratorPass extends SemanticPass` elaborates to LC terms (tree-consuming)
   - LC terms are then type-checked/evaluated via the one-pass grammar

4. **Document the hybrid architecture** — one-pass for LC core, two-phase for surface language.

**Files:** New `src/core/derivation.ts` (if needed), `_docs/theory/`, test files

### Phase 8: Cleanup and Consolidation

**Goal:** Remove redundant code and consolidate.

**Tasks:**

1. **Evaluate removing tree-walking files.** Once grammar-based `LCTypeCheck` and `LCEval` cover all
   rules, `typing.ts` and `eval.ts` may be unnecessary. Keep only if they serve a purpose the
   grammar-based versions don't (e.g., type-checking pre-built AST terms).

2. **Consolidate `soundness.ts`.** If `@ensures` contracts encode Progress (Phase 4),
   `checkProgress` may be redundant. `checkSoundness` simplifies to: parse with `LCTypeCheck`
   (proves well-typedness + Progress), parse with `LCEval` (proves Preservation via `@ensures`).

3. **Generate `lc.md` inference rules** from `toInference()`. The formal specification and
   implementation generated from the same source.

4. **Update `index.ts` exports** to reflect the final API surface.

**Files:** All `src/core/` files, `_docs/theory/lc.md`

## Dependency Graph

```
Phase 1 (grammar restructuring)      ← no dependency, do first
    ↓
Phase 2 (parseToFixpoint)            ← v4.0.0 available now
Phase 3 (contract metadata)          ← v4.0.0 available now
    ↓ (can run in parallel)
Phase 4 (strengthen @ensures)        ← requires Phase 3
    ↓
Phase 5 (complete typing rules)     ← requires Phase 2 (for fold σ)
Phase 6 (complete eval rules)        ← requires Phase 2 (for fold σ)
    ↓
Phase 7 (derivation trees)           ← independent, can start anytime
    ↓
Phase 8 (cleanup)                    ← requires Phases 5 & 6
```

## Success Criteria

- [ ] Every valid LC input produces exactly one parse tree (Phase 1)
- [ ] Fold handler bodies type-checked under correct σ via `parseToFixpoint` (Phase 2)
- [ ] Every contract has `ContractMeta` with rule name + formula (Phase 3)
- [ ] `toInference()` generates rules matching `lc.md` §5 (Phase 3)
- [ ] A successful parse proves Progress for the parsed term (Phase 4)
- [ ] All typing rules from `lc.md` §5 implemented (Phase 5)
- [ ] All evaluation rules from `lc.md` §3 implemented (Phase 6)
- [ ] `DerivationTree` + `SemanticPass` validated for surface language (Phase 7)
- [ ] Tree-walking files removed or justified (Phase 8)
- [ ] `lc.md` inference rules generated from the grammar (Phase 8)
- [ ] All tests pass, lint clean, format clean
