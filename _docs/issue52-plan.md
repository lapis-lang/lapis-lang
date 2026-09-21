# PBI #52 — CostPass: static cost/depth algebra — Implementation Plan

> **Status:** Implemented — 432 tests green (`deno check` / `test` / `lint` / `fmt` clean).
> Implements the acceptance items of
> [issue #52](https://github.com/lapis-lang/lapis-lang/issues/52): the cost/depth algebra over LC
> terms (`src/core/cost.ts`, new), `CostPass extends SemanticPass` consuming the type checker's
> `DerivationTree`s, certified bounds for the stratified fragment, and **flags** (diagnostics, never
> errors) on value-size feedback without a static bound — the busy-beaver candidates. Design source:
> [`semantics.md`](./theory/semantics.md) §5.5 (The Cost Algebra) and
> [`design-decisions.md`](./design-decisions.md) (Laws — cycles × growth, cost algebra).
> **Dependency #49 is closed**: Ω is acyclic by construction (declaration-order stratification,
> `ops.ts`), which closes the criterion's cycles axis and gives the feedback edges their names — an
> edge references the _named_ operation whose result feeds back, the identity-survival property #49
> was built for. Companion PBIs: #63/#65 — the same certified/flagged philosophy applied to cost
> instead of law truth.

## 1. Summary

Totality guarantees termination, not feasibility. The cage makes cost analysis unusually tractable:
a fold's recursion tree is **isomorphic to its input structure** (container-shaped recursion — the
invocation count is the input's node count, independent of handler bodies), so a **cost/depth
algebra** over terms is mechanically computable, and a decidable criterion separates the certified
fragment from the flagged residual:

| Fragment                                                        | Verdict                                                          |
| --------------------------------------------------------------- | ---------------------------------------------------------------- |
| First-order folds, non-nested                                   | linear — **certified**                                           |
| Stratified folds (re-entry only through bounded-size results)   | primitive-recursive, computed by recurrence — **certified**      |
| Affine-constructor size-preserving feedback (e.g. `map` → fold) | bounded — **certifiable** (Hofmann LFPL shape)                   |
| Higher-order result-size feedback (the Ackermann shape)         | hyper-growth candidate — **flagged**; runtime profiling observes |

What lands:

- **`CostExpr`** — a symbolic size/cost/depth expression algebra (polynomial-form bounds over named
  size variables, saturating arithmetic, an _opaque_ marker for function-typed values).
- **`CostEngine`** — a grammar subclass (the evaluator's architecture: a denotation environment
  threaded through the productions) that computes a term's symbolic summaries in one pass.
- **Op summaries** — memoized per `OpRegistry`, computed in Ω declaration order (the stratification
  order makes the analysis well-founded: an op's summary depends only on earlier ops' summaries).
- **`CostPass extends SemanticPass`** — the `DerivationTree`-consuming entry (the pipeline
  integration the issue mandates): walks a type-checker derivation tree, threads denotation
  environments through deferred summaries, and composes the memoized op summaries.
- **The classifier** — per report: `certified` (every feedback edge's producer has a closed size
  bound) vs `flagged` (an edge whose producer's size is opaque — a function-typed value feeding a
  size-sensitive position). Flags carry the edge payload, the missing bound, and a suggested runtime
  profile. Flags are diagnostics: nothing throws.

## 2. Current state

| Piece                          | Where                                | Note                                                                                                                                                |
| ------------------------------ | ------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------- |
| Ω-acyclicity (the cycles axis) | `ops.ts` (`OpRegistry.declare`)      | Declaration-order stratification; `all()` yields the stratification order — **implemented (#49)**                                                   |
| Op identity                    | `OpSig` / `opProd` / E-Op            | The named form survives substitution; `parseToTree` retains `opProd` nodes — **implemented (#49)**                                                  |
| Symbolic term reader           | `derivation.ts` (`DerivationReader`) | Reads LC source to a symbolic AST; rejects non-fragment shapes — **the cost engine needs a superset** (let/obs/unfold are _analyzed_, not rejected) |
| Size measure                   | `valueSize` (`values.ts`)            | Node count (variant = 1 + Σ fields; token = text length) — the measure the size variables use                                                       |
| Size-class counts              | `coefficients` (`type_algebra.ts`)   | The truncated-fixpoint discipline the recurrence solver mirrors                                                                                     |
| Derivation trees               | `parseToTree` (lang-forma)           | `@rule`-labeled nodes with spans + source; `SemanticPass` dispatches by label, bottom-up                                                            |
| Environment-threaded pass      | `LCEval`                             | The `extendCtx`/production-threaded `ρ` pattern — the capture-safety architecture the engine reuses                                                 |
| Cost analysis                  | —                                    | **Does not exist** — the gap this PBI closes                                                                                                        |

**The gap this PBI closes.** `semantics.md` §5.5 states the algebra and the criterion; nothing
computes them. The recursion skeleton is known (`DefShape`'s handler structure, the carrier's
variants), the size measure exists (`valueSize`), the stratification order exists
(`OpRegistry.all()`), and the DerivationTree pipeline exists — the algebra itself is unimplemented.

## 3. Design decisions

### D1 — Module placement: `src/core/cost.ts` (new)

One module, three layers, in dependency order: the summary algebra (`CostExpr` — pure), the engine +
op summaries (the symbolic analysis), and the pass (the tree entry). Exports via
`src/core/index.ts`. No evaluator and no type-checker import — the analysis is independent of both
(see D7); it shares only the `Type` AST and the registries. Tests in `test/cost.test.ts` (new).

### D2 — Two vehicles, one algebra: the engine (grammar subclass) and the pass (SemanticPass)

The cost pass needs **inherited attributes**: a handler body's cost depends on what its bindings
denote (a recursive binding is the _recursion result_ at the subterm — a symbolic quantity
satisfying the fold's own recurrence; a non-recursive binding is the raw field value). A purely
bottom-up name-based pass is capture-unsafe (a shadowing binder would silently mis-bind a denotation
and the report would claim a wrong bound as certified). The design therefore splits the issue's
"CostPass extends SemanticPass" into two vehicles over the same algebra:

- **`CostEngine extends AbstractLC<CostShape>`** — the grammar-subclass engine, the evaluator's
  architecture verbatim: productions thread a **denotation environment** (`CostEnv`: name ↦ { type,
  provenance, size, depth }), `extendCtx` extends it at binders, and each production's semantic
  action builds the sub-summary. Capture safety by construction — the same reason `LCEval` threads
  `ρ`. This is the vehicle for **op definitions** (Ω entries are LC source strings with no
  derivation tree) and for direct term analysis (`analyzeTerm`).
- **`CostPass extends SemanticPass<CostPassShape>`** — the `DerivationTree`-consuming entry the
  issue mandates. The tree supplies structure (labels + spans + source); the pass's per-production
  methods return **deferred summaries** — thunks over `CostEnv` — so the parent, which knows the
  bindings, builds the handler environments and _applies_ the child thunks under them. This is
  inherited-attribute flow through deferred application: bottom-up evaluation with the environment
  threaded where it is constructed, no re-parsing, no capture unsafety. `foldProd` recovers the
  carrier (the `typeProd` child's span → registry), the scrutinee, the per-handler binding names
  (the `ident` children's spans) and bodies; `opProd` reuses the **memoized op summary** (never
  re-reads a definition — the identity-survival payoff: the tree's `opProd` nodes name the op, the
  summary comes from Ω once).

The two vehicles share the summary algebra and the fold recurrence; they differ only in how
structure arrives (a parse vs a tree walk). This is exactly `semantics.md` §5.6's guidance: the
grammar-subclass shape where one environment flows down, the tree-consuming pass where the pipeline
already has the tree.

### D3 — The summary algebra: `CostExpr`

A term's summary is the triple (cost, depth, result-size), each a symbolic expression:

- **Size/cost expressions** — polynomial form: $\sum_k c_k \cdot \prod_v v^{e_v}$ over named size
  variables (one per parameter/binding: $|x|$ = the value's `valueSize` node count), with
  non-negative integer coefficients, saturating at `COST_CEILING = 2**53` (the `MAX_PATTERN_COUNT`
  discipline). An `opaque` marker: the expression does not exist — the value is **function-typed**
  (a closure, a function-typed parameter or result); function values have no size algebra.
  Constructors: $\text{cost}(C_i(t_j)) = 1 + \sum_j \text{cost}(t_j)$, size $1 + \sum_j |t_j|$ (O(1)
  per node — the issue's rule). Op application: the callee's memoized summary instantiated at the
  argument size expressions. Application of a known closure: the body's cost at the argument's size.
  Application of a function-typed _variable_: an unresolved cost atom (recorded, never flagged by
  itself — see D5).
- **Depth expressions** — max-form: $d(\text{con}) = 1 + \max_j d(t_j)$;
  $d(\text{fold}) = h(s) + \max_i d(\text{body}_i)$ where $h(s)$ is the scrutinee's height variable
  (bounded by $|s|$ — the report substitutes the size bound, the conservative but sound pairing).
- **Growth classes** — `linear` / `polynomial(d)` /
  `exponential (primitive-recursive; recurrence
  stated)` / `unbounded` — derived from the closed
  expression's degree, or the coarse class when the recurrence does not close to a polynomial (D4).
- **Provenance on every summary** —
  `{ kind: "param" | "op" | "fold" | "constructor" | "closure",
  name }`: what produced the value,
  so a feedback edge names both of its ends.

The fold decomposition (the container-shaped core of the algebra):

$$\text{cost}(\text{fold } [T]\; s\; \{\l_brack C_i(x_j) \to t_i\r_brack\}) \;=\; \sum_{\text{nodes of } s} \text{cost}(t_i \text{ at that node})$$

Statically the per-variant node counts of $s$ are unknown, so the algebra computes:

- **Exact, when the scrutinee is a constructor literal** — the structure is known: per-variant
  counts and exact subtree sizes come from the literal itself.
- **Conservative, otherwise** — $\text{invocations} = |s|$ (the node count — the recursion tree IS
  the input), and the per-node work is $\sum_i \text{cost}(t_i)$ with each recursive binding's size
  $|p|$ substituted by $R(|s| - 1)$ (no subtree exceeds the scrutinee minus its own root). The sum
  is a safe over-approximation of the exact $\Sigma_{\text{nodes}}$ decomposition (only one handler
  runs per node, so the sum charges every handler at every node — a handler-count-factor loosening
  for non-uniform handlers); for uniform handlers the sum IS the max, so the pairing stays within a
  constant factor. `SizeExpr` has no max operator — the sum is what the recurrence solver consumes
  directly.

### D4 — The recurrence discipline: affine closed forms, coarse classes beyond

The result-size recurrence per variant: $R(C_i(f_j)) = |t_i|$

with each recursive field's size $|p_a| \mapsto R(\text{subtree}_a)$. The solver mirrors
`coefficients`' truncated-fixpoint discipline (no general equation solving — the same "differentiate
the equation directly, never solve it" rule #64/#65 established):

1. **Affine chain/branch closure (the Hofmann shape).** When the body's size expression is
   non-size-increasing per recursive field — each $R(\text{subtree}_a)$ appears at exponent ≤ 1 with
   coefficient ≤ 1, and the non-recursive contributions are bounded expressions — the recurrence
   closes: $R = |{\rm input}| + (\text{bounded extras})$. This is the LFPL non-size-increasing
   criterion realized on the summary expressions; it is what certifies `map` → fold.
2. **Chain growth.** Single recursive field, coefficient 1: $R(n) = R(n{-}1) + g$ closes to
   $R(0) + n \cdot g$ — symbolic summation of the polynomial $g$. This certifies `add` (linear),
   `mul` (cost quadratic via $|x| \cdot |y|$), and `addZero` (quadratic).
3. **Beyond affine** (geometric structural self-growth — e.g. a chain handler body of size
   $2|p| + 1$): the bound does not close to a polynomial. The verdict stays **certified** (the
   growth is primitive-recursive and the recurrence is mechanically computed) but the certificate
   states the _recurrence_ and the coarse class (`exponential (primitive-recursive)`), not an
   expanded closed form. Honest coarseness, flagged nowhere — the busy-beaver criterion is about
   _feedback_, not structural growth (semantics.md §5.5's table).
4. **Codata dual** — `latency(e.o_k)` = the generator body's cost on the seed (`self` bound to the
   seed's summary), reported per observation.

The cost recurrence uses the same machinery over the per-node work; the depth recurrence the same
over max-forms.

### D5 — The feedback criterion: the flag (and only the flag)

**Size-sensitive positions** — where a value's size drives cost:

1. a fold's scrutinee (the invocation count is the input's node count),
2. an op application's argument positions (the callee's cost expression is driven by its parameters'
   sizes; the **axis** position is the recursion driver),
3. an application's fn position (the applied function's body cost is consumed per application),
4. an observation's generator (the codata dual — the latency).

**The feedback edge** records (producer, consumer, position, bound): producer = the summary's
provenance (which op/fold produced the value), consumer = the size-sensitive site, bound = the
producer's result-size expression when closed.

**The flag fires iff the producer's result-size is opaque** — a function-typed value flowing into a
size-sensitive position. That is the issue's criterion, made decidable: first-order data always
admits a closed size expression (the algebra closes every data-valued term), so _every_ first-order
feedback edge certifies — `map` (with a closed mapped function) → fold certifies with no flag —
while a fold whose recursion threads functions (the Ackermann shape: a fold over `Nat` producing
`Nat → Nat`, whose handler applies the recursion result) has an opaque producer at the application's
fn position → flagged, with the payload:

- `edge` — which fold's result feeds which position (the named form, per #49),
- `missingBound` — the size relationship that cannot be stated (the result is a function value; its
  per-application cost has no static algebra),
- `suggestedProfile` — the runtime observation to attach: sample the application arguments' sizes
  and the fold's invocation counts at the flagged site, accumulate against the flag, alert when the
  observed profile exceeds the certified programs' envelope (withdrawal-style, mirroring law
  observation — semantics.md §7.4).

**Flags are diagnostics, never errors.** Nothing in `cost.ts` throws for analysis outcomes — the
report carries them. (Contrast `LawDeclarationError`: a false law must not enter `E`; a flagged cost
is a fact about the program, made honest by visibility.) Unresolvable _cost_ contributions (applying
a function-typed parameter, e.g. `map`'s `f h`) are recorded as named unresolved atoms in the report
— they bound nothing, flag nothing, and are listed so the certificate states exactly what closed and
what did not.

### D6 — Op summaries: memoized, stratified, identity-bearing

`analyzeOp(op, registry, omega)` computes an op's summary once per `OpRegistry` (a memo keyed on the
registry identity, like the law checker's pattern-hook wiring). The computation walks Ω in
**declaration order** (`OpRegistry.all()`): an op's definition references only earlier ops
(acyclicity, #49), so their summaries are already computed — the analysis is well-founded by the
same stratification that guarantees termination. The feedback edges and the report's flags reference
operations **by name** — the named form is what makes an edge statement meaningful (`addZero`'s
result feeds `add`'s axis argument) and is the concrete payoff of #49's identity-survival for cost
analysis.

Definitions outside the fold fragment are analyzed, not rejected (the derivation engine's
`DefinitionShapeError` discipline is deliberately _not_ imported): `let` (def + body under the
binding), observations (latency), unfolds (the codata value; its generators' costs surface at
observation sites), type abstractions (erasure — passthrough), matched tokens (a named size variable
— the runtime text is statically unknown). A definition the engine cannot read parses to an empty
forest → the summary is reported as `unanalyzed` with the reason (an honest residual, not a crash) —
the cost pass never blocks a program.

### D7 — Typing inside the analysis: lightweight and independent

The engine needs only enough typing to classify _function-typed_ values (the opacity rule): Ω's
declared signatures, the registry's variant fields, lambda annotations in the source, and the fold's
result type inferred from its own handler bodies (an all-lambda fold is function-resulted; its
recursive bindings are opaque). It does **not** consume `LCTypeCheck`'s per-node types.

This independence is load-bearing: the type checker's `T-Fold` fixpoint seeds σ₀ at the _carrier_
(`evalFoldFixpoint`), which is correct for carrier-result folds but **rejects function-result
folds** — the Ackermann shape cannot enter Ω today (the handler body `p(Succ(y))` fails T-App while
`p` is bound at a non-function σ). The cost analysis therefore exercises the Ackermann shape at the
**term level** (`analyzeTerm` / the `CostPass` over a tree), where the engine's own structural
typing applies. Widening `T-Fold`'s seeding to admit function-result folds is a separate PBI (see
§7) — out of scope here, and not required by the issue's acceptance tests.

### D8 — Scope boundaries (first cut, stated)

- **Runtime profiling is a design note, not code.** The flag payload's `suggestedProfile` names the
  observation channel; the channel itself (live-image mode, withdrawal-style alerting) does not
  exist yet — the issue scopes it out explicitly.
- **No surface syntax.** The analysis consumes LC source and derivation trees; surface declarations
  elaborate later (#25's pipeline) and the pass integrates there.
- **`relation`/`closure` (the Datalog cell) excluded.** Semi-naive evaluation over the finite
  span-projection space is its own engine (elaboration §3.4); the cost algebra's table entry for it
  is "termination and PTIME by construction" — nothing to compute per program.
- **Codomain**: data folds + codata observation latency. `cofold`'s handler cost composes like a
  fold's (one handler); its productivity/cost split follows the same algebra.

## 4. Implementation steps

1. **`src/core/cost.ts` (new)** — in dependency order, each committing with the suite green:
   1. `CostExpr`: the polynomial-form size/cost expressions (monomials, saturating arithmetic,
      `opaque`), the max-form depth expressions, the growth classes, rendering (for reports and test
      assertions).
   2. The summary algebra's combinators: constructor/application/op-instantiation/closure
      composition, the unresolved-atom records, provenance threading.
   3. `CostEngine extends AbstractLC<CostShape>` — the denotation environment, per-production
      actions, the fold handler envs (recursive ↔ non-recursive denotations from the variant's
      fields), the fold recurrence (exact-literal / conservative branches), observation latency.
   4. The recurrence solver (D4): affine closure, chain summation, the coarse-class fallback.
   5. `analyzeOp` + the per-registry memo; `analyzeTerm`.
   6. The classifier and the report/flag types (`CostReport`, `CostEdge`, `CostFlag`,
      `LatencyReport`).
   7. `CostPass extends SemanticPass<CostPassShape>` — the deferred-summary tree walk (D2), the
      `DerivationTree` entry.
2. **`src/core/index.ts`** — export the public surface: `analyzeOp`, `analyzeTerm`, `CostPass`,
   `CostReport`, `CostFlag`, `CostEdge`, `CostExpr`, `GrowthClass`, `LatencyReport` (the algebra
   internals stay module-private).
3. **`test/cost.test.ts` (new)** — the suite (§5).
4. **Docs** — `semantics.md` §5.5 gains an implementation-status note (what computes, what stays
   coarse); `design-decisions.md`'s cost-algebra bullet gains the implemented-module pointer;
   `_docs/lc-core-implementation-plan.md` gains the PBI #52 entry (v0.3.0 — Laws); this document's
   status header.

## 5. Tests

**The algebra (`test/cost.test.ts`):**

- `CostExpr` unit tests: construction, saturation at the ceiling, substitution, rendering; `opaque`
  propagation (any opaque operand → opaque).
- Constructor/app/op composition on hand-computable terms: `Zero()` costs 1, size 1;
  `Succ(Succ(Zero()))` costs 3, size 3; an op application instantiates the callee's summary at the
  argument sizes.

**Certified bounds (the issue's acceptance items):**

- **Linear (first-order, non-nested).** `add` (the #49 fixtures): cost $= |x|$ (the axis parameter's
  size — one O(1) handler invocation per node), depth $= |x| + c$, result size $= |x| + |y|$ —
  assert each against the known recurrence, and the verdict `certified` with an empty flag list.
- **Stratified (re-entry through bounded-size results).** `mul` (fixtures): per-node work
  $\le |y| + c$, invocations $= |x|$ ⇒ cost $= O(|x|{\cdot}|y|)$ — assert the polynomial form;
  `addZero` (a new fixture, the derivation engine's canonical second op): recursion result
  $R(n) = 1 + R(n{-}1) + |b|$ ⇒ $n{\cdot}|b| + 1$; per-node work $|p| \le R(|x|{-}1)$ ⇒ cost
  quadratic in $|x|$ with coefficient $|b|$ — assert the closed forms match the hand recurrences.
- **Exact-literal scrutinee.** A fold over a literal (`fold [Nat] Succ(Succ(Zero())) {...}`): the
  per-variant node counts are known ⇒ the exact invocation count (the literal's node count — 3, for
  the 3 nodes of `Succ(Succ(Zero()))`) with the handlers' summed per-node work (2), tighter than the
  conservative `|s|`-driven form.
- **No flag on `map`-then-`fold` (affine constructors).** A `List` fixture and a `map` op whose
  mapped function is a _closed_ op (e.g. `succ`): the producer's result size closes ($\le$ a linear
  expression in $|l|$ — the affine shape, D4.1), the consumer fold's edge certifies — assert no
  flags, verdict `certified`.

**The flag (the issue's acceptance item):**

- **The Ackermann shape.** `analyzeTerm` on
  `fold [Nat] m { Zero() -> \y:Nat. Succ(y), Succ(p) -> \y:Nat. p(Succ(y)) }` — the recursion result
  (a function) is applied: the edge (this fold's result → the application's fn position) has an
  opaque producer ⇒ verdict `flagged`, exactly one flag, the payload names the fold and the
  application site, `missingBound` states the function-value shape, `suggestedProfile` names the
  samples. (A term, not an op — see D7 for why the checker cannot declare it today.)
- **The negative control is already above**: the `map` → fold edge — same position kinds, closed
  producer — no flag. The flag is the _opacity_, not the edge.

**Codata latency (the issue's acceptance item):**

- An unfold whose `head` generator folds over a `Nat` (expensive) and whose `tail` is `self`:
  `latency(.head)` $= $ the fold's cost expression at the seed's size; `latency(.tail)` $= O(1)$
  (the generator returns `self`). Assert both, and that the report's codata section separates
  latency from call cost.

**Op summaries and the pass:**

- Memoization: two analyses of the same registry produce one summary per op (identity, not
  re-computation); a fresh registry recomputes.
- Stratification: a three-op chain (c references b references a) — summaries compute in declaration
  order; no summary references a later op.
- `CostPass` over a `parseToTree` tree of an op-application term: the report composes the memoized
  op summary with the argument analyses (the identity-survival integration — the tree's `opProd`
  node names the op; the summary comes from Ω).
- Unanalyzable definition (a definition the engine cannot parse): `unanalyzed` with the reason — no
  throw.

## 6. Acceptance mapping (issue #52)

| Acceptance item                                                                                                  | Covered by             |
| ---------------------------------------------------------------------------------------------------------------- | ---------------------- |
| `src/core/cost.ts` — the cost algebra (constructor O(1); app = fn + arg + body; fold = Σ per node; latency dual) | Steps 1.1–1.3 (D3)     |
| `CostPass extends SemanticPass` over `DerivationTree`s; flags as diagnostics, not errors                         | Steps 1.5–1.7 (D2, D5) |
| Certified bounds for the stratified fragment (recurrence-computed)                                               | Steps 1.4 + §5 (D4)    |
| Flag payload: the feedback edge, the missing bound, the suggested profile                                        | D5 + §5                |
| Runtime profiling hook — design note only                                                                        | D8 (deferred)          |
| Tests: certified linear/stratified; Ackermann flag; no flag on map→fold; codata latency                          | §5                     |
| Scope: `cost.ts` (new), `index.ts` (exports), `cost.test.ts` (new)                                               | Steps 1–3              |

## 7. Deferred items — with reasons

- **Runtime profiling integration.** The live-image mode does not exist; the flag payload's
  `suggestedProfile` is the design note the issue asks for. The observation channel lands with the
  live-image work (the same withdrawal-style alerting law observation uses).
- **T-Fold's function-result seeding.** `evalFoldFixpoint` seeds σ₀ at the carrier, so a fold
  producing a function type is rejected by the type checker — the Ackermann shape cannot be
  _declared_ as an op today. Widening the seeding (and the fixpoint's T-App premise under a
  to-be-refined σ) is a checker PBI with its own soundness argument; the cost analysis handles the
  shape at the term level, which is what the acceptance test needs.
- **Exponential closed forms.** Super-affine structural growth reports the coarse
  `exponential (primitive-recursive)` class with the recurrence stated, rather than expanding
  $a^n$-forms. The certificate stays honest; expanding it adds expression machinery no acceptance
  item needs.
- **Branching-carrier exact recurrences.** The conservative bound (invocations = node count × worst
  per-node work) is within a constant factor for uniform handlers; exact per-variant distribution
  tracking for symbolic branching scrutinees is a refinement (literal scrutinees are already exact).
- **The pure-Hofmann criterion for unknown functions.** `map(f, l)` with `f` a function-typed
  _parameter_ leaves the heads' sizes opaque (the mapped function's summary is unknown) — the edge
  flags, honestly. The LFPL criterion's full resource-annotation discipline (certifying
  non-size-increasing composition through unknown callees) is a later refinement; the first cut
  certifies what has closed summaries.
- **Surface-syntax integration and the elaboration pipeline.** The pass integrates when surface
  declarations elaborate to core terms (#25's pipeline); the core entries are complete now.

## 8. Risks

- **The conservative bound's tightness.** $|s| \times \max_i$ per-node work can overestimate when
  handler costs are wildly uneven; the certificate states the bound's shape (max-form), never an
  exact count, so nothing false is claimed. The literal-scrutinee path covers the exact cases the
  tests assert.
- **Closure summaries through op composition.** A fold returning closures whose bodies reference the
  recursion result is where the flag's detection must not miss a cycle (the wrapped-Ackermann shape:
  the application hides inside an earlier op's body). The first cut detects the direct shape (the
  recursion result applied within the analysis); the wrapped shape needs closure-body cost equations
  parameterized through Ω composition — deferred with the exponential closed forms, and the coarse
  verdict still never claims a bound that does not hold.
- **Capture safety.** The denotation environment is threaded by construction (D2) — the failure mode
  a name-based bottom-up pass would have (silent mis-binding under shadowing) is designed out; a
  test pins the shadowing case (a handler binding shadowing an outer parameter).
- **Analysis cost.** The engine parses each op definition once (memoized); the tree pass re-drives
  spans without re-parsing productions. Budgets mirror the law checker's discipline (`COST_CEILING`
  saturation; no unbounded iteration — the recurrence solver's substitution loop is bounded by the
  expression degree).
- **`ScreenOutcome`-style shape breaks: none.** `cost.ts` is additive; no existing exported type
  changes. The only touched files are the new module, the export list, and the new test file.
