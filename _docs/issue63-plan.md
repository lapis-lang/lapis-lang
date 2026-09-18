# PBI #63 — BMF Derivation Engine: Implementation Plan

> **Status:** Implemented (see the status note at the end of §4 — the engine's moves and the tests'
> canonical outcomes are the record). Implements the full acceptance list of
> [issue #63](https://github.com/lapis-lang/lapis-lang/issues/63) in one PBI — the handler-fragment
> characterization, the skeleton generation, the calculational discharge engine, the `derivable`
> regime arm, and the tests. The issue's "consider splitting into a design PBI + an engine PBI" note
> is **resolved: no split** — the characterization below is stated as the engine's specification
> (the fragment is _defined_ by what the bounded engine closes), so the design and the mechanism
> land together and cannot drift apart. Design sources:
> [`type-algebra.md`](./theory/type-algebra.md) §6, [`semantics.md`](./theory/semantics.md) §5.4
> (the `derivable` regime row), [`design-decisions.md`](./design-decisions.md) (Laws — the
> provenance ladder), [`lc.md`](./theory/lc.md) §7. Companion PBIs: #62 (sub-space sweeps —
> different regime, shares the provenance plumbing), #52 (CostPass — the certified/flagged
> philosophy applied to cost, a follow-up).

## 1. Summary

The `derivable` regime is the third law-discharge mechanism and the **only route to `discharged` for
unbounded μ-carriers** (List/Nat/Tree): structural exhaustion is unavailable (unbounded), pattern
carriers route through the machineFinite sub-space sweeps (#62), and today every unbounded-carrier
claim stays `asserted` forever. This PBI makes the derivable regime real:

- a **precise, decidable fragment characterization** — a law claim is derivable iff a _bounded,
  search-free derivation_ closes it, where the derivation's moves are exactly: fold-computation
  unfolding (from checked `Ω` definitions), congruence, the induction hypothesis at the recursion
  positions, and one-step axiom instantiation from `E`'s `primitive`/`discharged` laws;
- **skeleton generation** — the induction motive is the law's own schema instance and the case
  structure is read off the carrier's variants (`allVariants()`): the functor fixes the motive, so
  the skeleton is mechanical (type-algebra.md §6's structural fact);
- the **`derivable` arm** in `screeningRegime` and `declareCheckedLaw`: a successful derivation
  installs provenance `discharged` with a derivation certificate; a derivation that does not close
  falls through to the existing residual screen (falsify-only, `asserted`) — routing never loses the
  screen's protection.

The engine is deliberately **not a prover**: no search, no backtracking, no unification. Each schema
case gets a fixed-priority move sequence under a step budget; a claim the budget cannot close is
honestly not derivable and stays screened. Soundness is by construction (every move is either the
language's own fold computation rule, an installed unconditional axiom, or the structural induction
hypothesis); incompleteness is the honest residual the provenance ladder already names.

## 2. Current state

| Piece                | Where                                 | Note                                                                                                                                         |
| -------------------- | ------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- |
| Provenance ladder    | `laws.ts` (`LawProvenance`)           | `primitive \| discharged \| asserted` — implemented; `primitive` is the type only, **nothing installs it today** (see D5)                    |
| Regime routing       | `screeningRegime` (`law_checking.ts`) | Type-shape based: `finite` / `machineFinite` / `residual`; the `derivable` arm is the documented placeholder ("awaits a characterization")   |
| Discharge mechanisms | `exhaustLaw`, `screenLaw`             | Exhaustion → `discharged`; certified screen → `asserted`. The derivable arm joins this dispatch                                              |
| Schema instantiation | `instantiate` (`law_checking.ts`)     | Builds LC **source strings** for axiom instances over sample values — the derivable engine needs the symbolic (term-level) counterpart       |
| Op definitions       | `OpSig.definition` (LC source)        | Fold-built strings (`\a:Nat. fold [Nat] a {...}`); no AST extraction exists — the engine needs a definition reader (D2)                      |
| Op reference scan    | `OpRegistry.referencedOps` (private)  | Regex scan for call-shaped camelCase identifiers; used for Ω acyclicity — the fragment gate reuses it (D7 promotes it to an export)          |
| Evaluation           | `LCEval` (concrete values only)       | Total, but **value-level**: useless for symbolic obligations. The derivation is purely symbolic; evaluation is never consulted by the engine |
| Derivation engine    | —                                     | Does not exist                                                                                                                               |

**The gap this PBI closes.** `type-algebra.md` §6 states the design direction ("the induction motive
is fixed by the functor … the skeleton generates the proof obligation, the primitive law set
discharges it") but leaves the fragment as a working criterion in prose. This PBI fixes the
criterion as a runnable specification, implements it, and wires it into the regime dispatch.

## 3. The design target: a worked derivation

Everything below is shaped by what the engine must do to this canonical example. Fix, over
`Nat = Zero | Succ(pred: Self)`:

```
add     = \a:Nat. \b:Nat. fold [Nat] a { Zero() -> b,        Succ(p) -> Succ(p) }
addZero = \a:Nat. \b:Nat. fold [Nat] a { Zero() -> b,        Succ(p) -> Succ(add(p, b)) }
```

`add : associative` is installed `primitive` (language fiat — in tests, a direct
`LawRegistry.declareLaw` with provenance `primitive`; the test IS the fiat, see D5).

**Claim 1 — `identity: Zero` on `add` (derives from the fold schema alone, zero axiom steps).** Two
instances (`lc.md` §7.2):

- `add(Zero, a) ≡ a`: unfold at the constructor scrutinee (`Zero` handler returns the second
  parameter) → `a ≡ a` — closed by reflexivity.
- `add(a, Zero) ≡ a`: induction on `a` (the fold's scrutinee parameter — the recursion axis).
  - Base `a = Zero()`: both sides unfold to `Zero()` — closed.
  - Step `a = Succ(p)`: LHS unfolds `add(Succ(p), Zero)` → `Succ(add(p, Zero))`; RHS is `Succ(p)`;
    congruence on `Succ` leaves `add(p, Zero) ≡ p` — exactly the claim at the recursion variable `p`
    — closed by the IH.

**Claim 2 — `identity: Zero` on `addZero` (derives from `add`'s primitive law — the acceptance
test's "deriving from primitive laws").**

- `addZero(Zero, a) ≡ a`: unfold → `a ≡ a` — closed.
- `addZero(a, Zero) ≡ a`: step case unfolds `addZero(Succ(p), Zero)` → `Succ(add(p, Zero))`;
  congruence leaves `add(p, Zero) ≡ p`. No IH applies (`add` is a _different_ op — its recursion
  variable is internal). The **axiom move** instantiates `add`'s installed `identity: Zero` law's
  right direction (`add(x, e) ↝ x` with `x := p`, `e := Zero`): one step, closed.

**Claim 3 — `commutative` on `add` (NOT derivable — the honest residual).** The base case for
`a = Zero()` unfolds the left side to `b` but the right side is `add(b, a')` with a **variable**
scrutinee — no unfold applies, no IH applies (`b` is not a recursion variable of the case), no axiom
is shaped to close it. The closure needs a nested double induction — outside the fragment. The claim
is still TRUE; the engine returns _not-derivable_ (not falsified), the dispatch falls through to the
certified screen, and the law installs `asserted`. The ladder stays honest: derivation proves, the
screen only disbelieves.

This example pins all three outcomes the acceptance list names: a fold-schema-only derivation, an
axiom-consuming derivation, and a non-derivable handler staying residual.

## 4. The derivable fragment — characterization (the decidable test)

The fragment is characterized **operationally**: a claim is derivable iff the bounded derivation
below closes every case. Stated as a test on the fold's definition and the claim:

1. **Definition shape** — `def(op)` parses as a lambda chain whose body is a `fold [T]` whose
   scrutinee is one of the lambda's parameters (the **recursion axis**). Definitions containing
   `unfold`, `cofold`, `let`, or a fold whose scrutinee is a compound term are outside the fragment
   (loud shape-rejection with the offending construct named).
2. **Case structure** — one case per variant of the axis carrier (`DataType.allVariants()`); a
   case's recursive fields carry the IH; non-Self data-typed fields do not (the #64 boundary: the IH
   reaches direct recursion only).
3. **Closure** — every schema instance (both directions for argument-taking kinds, mirroring
   `instantiate`) closes within the move set and the step budget (D4).

The characterization's soundness/completeness profile is stated in the docs exactly as the engine
behaves: **sound** (every closed derivation is a real proof — each move is the fold computation
rule, an unconditional axiom, the IH, or congruence) and **deliberately incomplete**
(budget-bounded, syntactic axiom matching, single-axis induction). Non-closing claims are not
rejected — they route to the residual screen, which keeps its falsification power. "Handlers call
only primitive or already-discharged operations in semantically essential ways" is realized _a
posteriori_ by closure: the derivation consumes an op's law only where an obligation actually needs
it, so a lawless call blocks closure exactly when it is semantically essential (see D5 for the
provenance filter and the dead-call boundary).

## 4. Design decisions

### D1 — Module placement: `src/core/derivation.ts` (new)

One module, exported from `src/core/index.ts`, mirroring the one-mechanism-per-module pattern
(`type_algebra.ts`, `pattern_lang.ts`):

- **`derivation.ts`** — the definition reader (`defShape`), the symbolic schema instantiation, the
  skeleton generator, the bounded discharger, the fragment gate (`derivableFragment`), the
  derivation entry (`deriveLaw`), and the certificate type. Purely symbolic: **no evaluator, no
  value enumeration, no sampling** — the derivable regime enumerates nothing (unlike
  exhaustion/screen, its evidence is the derivation itself, and its only budgets bound the
  derivation's work).
- **`law_checking.ts`** — the regime arm and dispatch wiring only.

Naming note: the word "derivation" already names lang-forma's _parse_ derivation trees
(`test/derivation.test.ts`, `DerivationTree`). The module's artifacts are deliberately suffixed to
stay disjoint (`DerivationProof`, `DerivationCertificate`); the test file is
`test/derivable.test.ts` to keep the two worlds from colliding in test listings.

### D2 — The definition reader: `defShape` (a small term AST)

`OpSig.definition` is LC source; the grammars' parse actions build `Type`/`Value`s directly, and
lang-forma's `parseToTree` couples the engine to parse-forest internals. The engine instead carries
a **small structural reader** (~250 lines) over the LC concrete syntax, producing:

```ts
interface DefShape {
    params: { name: string; type: Type }[]
    /** The outermost fold's scrutinee parameter (the recursion axis). */
    axis: number
    carrier: DataType
    handlers: { variantName: string; fieldVars: { name: string; isRecursive: boolean }[]; body: Term }[]
}

/** The term forms the fragment admits. */
type Term =
    | { k: "var"; name: string }
    | { k: "lam"; param: string; body: Term }
    | { k: "app"; fn: Term; arg: Term }
    | { k: "op"; name: string; args: Term[] }
    | { k: "con"; variant: string; args: Term[] }
    | { k: "fold"; axis: Term; carrier: string; handlers: … }
```

Reader discipline (mirroring `pattern_lang.ts`'s precedent): term forms the fragment does not admit
(`let`, type abstraction, unfold/cofold) are _recognized and rejected with the construct named_ —
never silently mis-parsed. The reader is unit-tested against the exact LC concrete syntax the
grammar defines; a syntax evolution that the reader does not know fails loud (shape-rejection),
which routes the claim to the residual screen — the failure mode is incompleteness, never
unsoundness.

The **fold-computation rule** the engine's unfold move implements is E-Fold at the symbolic level:
`f(Cᵢ(vⱼ…))` unfolds to handler body `tᵢ` with field variables bound to `vⱼ` and each
recursive-field variable bound to `f` applied to the corresponding subterm — the same substitution
E-Fold performs on concrete values, so the engine's rewriting and the evaluator agree by
construction (this agreement is what the belt-and-braces screen of D6 double-checks on concrete
samples).

### D3 — Skeleton generation: the motive is the schema, the cases are the variants

For claim `L` on op `f` (post `validateLaw`: arity and schema typing are already established):

- **Motive**: the law's axiom schema instantiated _symbolically_ — the same per-kind shapes
  `instantiate` builds as source strings (`associative: f(f(a,b),c) ≡ f(a,f(b,c))` etc., both
  directions for `identity`/`absorbing`), as `Term`s over free schema variables, with `e`/`z`
  substituted by the parsed argument term. The two representations (this module's symbolic shapes,
  `law_checking.ts`'s source strings) are kept in sync by a shared per-kind table moved to `laws.ts`
  next to `SCHEMA_ARITY` — one source of truth, rendered to `Term`s here and to source there.
- **Cases**: the axis carrier's variants. Case `Cᵢ(xⱼ…)`: substitute the case pattern `Cᵢ(xⱼ…)` for
  the axis parameter in the motive; the IH is the motive re-instantiated at each recursive field
  variable (only `isRecursive` fields — the direct-recursion boundary of #64 D5).
- **Per case, per obligation side**: the unfold fixpoint — repeatedly unfold every op application
  (and every fold term) whose scrutinee is a constructor application, innermost-first, until none
  applies (bounded by `MAX_UNFOLDS_PER_CASE`).

The functor-fixes-the-motive fact is what makes this mechanical: the induction's case tree _is_ the
carrier's variant tree; nothing is invented.

### D4 — The bounded discharger (search-free, budgeted)

Each case's residual obligation list is processed with a fixed-priority move sequence, no
backtracking, under `MAX_STEPS_PER_CASE` (axiom + IH applications) — defaults
`MAX_UNFOLDS_PER_CASE = 64`, `MAX_STEPS_PER_CASE = 8` (tuning knobs, documented in the module):

1. **Reflexivity** — syntactic term equality (alpha-renaming-free: the reader canonicalizes
   bound-variable names).
2. **Congruence decomposition** — same constructor head on both sides: recurse into arguments.
3. **IH application** — the claim re-instantiated at _this case's recursion variables only_; a
   syntactic match of one side's shape rewrites it to the other's. (Enforcing the IH's variable
   discipline is the engine's key soundness invariant — see the misuse-guard test in §6.)
4. **Axiom application** — for each op referenced in the claim's handler bodies, for each of its
   `E`-laws with provenance `primitive` or `discharged`, instantiate the axiom schema at the
   obligation's subterms (syntactic schema-shape match, one step, fixed direction: the direction
   whose left side matches the found subterm). At most one axiom step per obligation pass; the
   obligation re-enters the sequence at (1).
5. **Exhaustion** — budget reached with an open obligation → the case is open → `notDerivable` for
   the whole claim.

All five moves are sound by construction (language computation rule, structural equality, structural
induction, installed unconditional axioms, and structural decomposition). The budget is the
fragment's decidability: a claim closing within it is in the fragment; one that needs more is out.

**Relation to the BMF calculus (the acceptance item's "at minimum fold-fusion").** The move set
realizes the first-cut fusion proofs directly: a fold-composition obligation unfolds both folds (the
fusion proof's first move), and the per-handler residual closes by the called op's laws — which is
fusion's side-condition at this granularity. An explicit named fusion rule adds nothing at this
scale; the mapping is documented in `type-algebra.md` §6 rather than implemented as a separate move.

### D5 — The axiom base: `primitive`/`discharged` only — no laundering

Derivation consumes **only** laws with provenance `primitive` or `discharged`. An `asserted` law is
_never_ an axiom step: using one would launder declaration risk into `discharged` (the derived law's
soundness is relative to its axioms; the ladder's whole point is that `primitive`/`discharged` are
established unconditionally, `design-decisions.md` Laws). The derivation certificate records every
axiom it used with its provenance — the visible trust chain, in the same spirit as `subSpaceSweep`'s
visible extent.

**The `primitive` tier is realized as it stands.** Today nothing installs `primitive`; the language
definition's builtin-op pinning (a surface-level concern, v0.4.0-adjacent) is _not_ part of this
PBI. Tests seed primitive laws via a direct `LawRegistry.declareLaw(…, "primitive")` — exactly the
authority the tier claims (language fiat; the test plays the language definition's role). The engine
is provenance-consumer only; seeding is out of scope and needs no engine changes when it arrives.

**The "semantically essential" boundary (first cut).** A handler call to a lawless op makes the
claim derivable iff the closure never needs that op's laws (the call may be eliminated by unfolding,
or the obligation may close without touching its shape). A conservative refinement — proving a call
is _dead_ (its result does not flow into the returned spine) to excuse its lawlessness — is deferred
(§10): the first cut treats any closure-blocking lawless call as disqualifying, which is sound and
honest.

### D6 — Routing: the `derivable` arm, with an honest fallback

- `ScreeningRegime` gains `"derivable"`. `screeningRegime(law, op)` keeps its existing type-shape
  checks verbatim; a claim routed `residual` runs the cheap syntactic gate (D-§4 item 1 — definition
  shape + axis, no `E` consulted, no evaluation): shape-pass ⇒ `"derivable"`, else `"residual"`.
  Existing call sites and tests are untouched (the union is additive; a claim that routed `residual`
  by type shape either stays there or upgrades to `derivable`).
- `declareCheckedLaw` dispatch: `derivable` → `deriveLaw`:
  - **Closes** → install **`discharged`**, with the `DerivationCertificate` in the returned record
    (additive field `derivation`), after the belt-and-braces screen (D7).
  - **Does not close** → fall through to the existing residual path (`screenLaw`), install
    `asserted` on a passing screen — and report the regime that _produced the outcome_
    (`"residual"`), so the returned regime always names the mechanism that established the
    provenance. Not-derivable is a _decline_, not a falsification: the claim proceeds to screening
    exactly as it did before this PBI.
- The regime table's row (semantics.md §5.4) is updated to the implemented reading: `derivable` is
  the residual regime's proof-shaped arm, entered by handler shape, exiting either `discharged`
  (derivation) or the screen's `asserted` (residual as before).

### D7 — The screen never sleeps (belt-and-braces)

A successful derivation is **additionally screened** before installation: the certified prefix sweep
runs exactly as for the residual (the claim is over an unbounded carrier, so this is cheap and
bounded). A falsifying sample throws `LawError` — nothing installs — which converts any engine bug
that fabricates a bogus proof into a loud rejection on concrete instances (the screen and the engine
disagreeing is an engine bug, and the screen wins). A _declining_ screen (no sample vocabulary)
skips the guard: decline is not falsification. The screen's outcome is recorded on the certificate
(`screenChecked: number`) so the discharged declaration shows both evidences.

### D8 — The certificate

```ts
interface DerivationCertificate {
    /** Per schema instance: the cases (variants) and how each closed. */
    instances: {
        direction: "left" | "right" // argument-taking kinds only
        cases: { variant: string; closedBy: "reflexivity" | "IH" | "axiom"; steps: number }[]
    }[]
    /** Every axiom consumed, with its provenance (all primitive|discharged). */
    axiomsUsed: { op: string; kind: LawKind; provenance: LawProvenance }[]
    /** The belt-and-braces screen's instance count (undefined if it declined). */
    screened?: number
}
```

Additive on `declareCheckedLaw`'s return (`derivation?`), like `coverage`/`subSpaceSweep`. The
certificate is _visible provenance_ — the consumer of a `derivable`-discharged law sees which axioms
the proof stood on, matching the trust-boundary framing of the ladder.

### D9 — Scope boundaries (first cut, stated in the module doc)

- **Intrinsic kinds only**: `associative`, `commutative`, `identity`, `idempotent`, `involutory`,
  `absorbing`. `distributive` is a stretch (a two-op schema doubles the skeleton's axiom surface) —
  deferred (§10); a `distributive` claim routes to the residual path exactly as today.
- **Pattern carriers**: outside the fragment (no variant cases to skeletonize; their honest route is
  machineFinite sub-space sweeps or the screen). The shape gate rejects them with the reason named.
- **Multi-axis motives**: one induction axis (the outermost fold's scrutinee parameter). Claims
  needing a nested/double induction (the canonical example: `commutative` on `add`) stay
  not-derivable — this is the fragment's honest edge, and the exact shape a future extension (nested
  skeletons) would admit without redesign.
- **Higher-order positions**: `screenableDomain` already bars them from every regime's check path;
  the derivable arm inherits the same bar.

### D10 — The Fiore–Leinster caution, enforced by omission

The engine's move set contains **no type-level rewrites at all** — no isomorphism steps, no
generating-function manipulation, nothing that could smuggle a `from`/`to`-less type-iso rewrite
into `↝`. Every move is term-level and individually sound (D4). The §6 caution is therefore honored
structurally, not by a check: the raw-algebraic manipulations the caution warns about
(subtraction/division tricks, seven-trees-in-one) have no representation in the engine. The doc
restates the caution with this note.

## 5. Implementation steps

1. **`src/core/derivation.ts`** (new) — the term AST + `defShape` reader (D2); symbolic schema
   instantiation (the per-kind table shared with `law_checking.ts`, D3); the skeleton generator; the
   bounded discharger with the budgets (D4); `derivableFragment` (the cheap gate); `deriveLaw`
   returning `DerivationCertificate | { derivable: false; openCase: … }`. Imports: `types.ts`,
   `ops.ts`, `laws.ts`, `values.ts` (rendering only). No evaluator dependency — the engine is
   symbolic end to end.
2. **`src/core/ops.ts`** — promote the private `referencedOps` scan to an exported
   `scanOpReferences(source: string)` (the acyclicity check and the fragment gate share one scanner;
   behavior unchanged).
3. **`src/core/law_checking.ts`** — `ScreeningRegime` gains `"derivable"` (doc comment updated: the
   "awaits a characterization" note is replaced by the characterization's pointer);
   `screeningRegime`'s residual exit runs the cheap gate (D6); `declareCheckedLaw` dispatches
   `derivable` → `deriveLaw` → `discharged` + certificate, with the notDerivable fallback; the
   belt-and-braces screen in the closing path (D7).
4. **`src/core/index.ts`** — export `derivableFragment`, `deriveLaw`, `DefShape`,
   `DerivationCertificate`.
5. **`test/derivable.test.ts`** (new) — engine unit tests + end-to-end routing tests (§6). Existing
   suites untouched except: `test/discharge.test.ts` gains the routing-boundary tests (a claim that
   upgrades to `derivable`, a claim that must keep routing `residual`).
6. **Docs** — `type-algebra.md` §6 (design → characterized: the fragment statement, the move set,
   the fusion mapping, the caution note) + §7 status table; `semantics.md` §5.4 (the regime table's
   `derivable` row → implemented, the honest-fallback note, the implementation-status paragraph);
   `design-decisions.md` Laws (the derivation mechanism's one-line status under the provenance
   ladder); `lc.md` §2.4 (one clause: derivation is implemented, the move set is the machine-checked
   skeleton); `lc-core-implementation-plan.md` (PBI #63 pointer; fix stale statuses while there);
   this document's status header.

## 6. Tests (`test/derivable.test.ts`, plus routing in `discharge.test.ts`)

**Definition reader (`defShape`):**

- `add`'s definition: axis = param 0, carrier = Nat, two handlers, `Succ`'s `pred` field marked
  recursive.
- `double = \n:Nat. fold [Nat] n { Zero() -> Zero(), Succ(p) -> Succ(Succ(p)) }` (nested
  constructors, no op calls) parses.
- Loud rejections, each naming the construct: an `unfold`-containing definition; a `cofold`; a
  `let`; a fold whose scrutinee is a compound term (`fold [Nat] add(x, y) {…}`).
- Reader/evaluator agreement: for each fixture op, unfolding `f(Cᵢ(concrete…))` via
  `defShape`+E-Fold semantics equals the evaluator's value (a property test over the fixtures' ops —
  the D2 agreement pin).

**Engine unit (symbolic, no evaluator):**

- **Claim 1** (`identity: Zero` on `add`): closes; zero axioms used; the certificate's cases are
  `{Zero: reflexivity} / {Zero: reflexivity,
  Succ: IH}`.
- **Claim 2** (`identity: Zero` on `addZero`, `add : identity:Zero` installed `primitive`): closes;
  `axiomsUsed` records exactly `add/identity/primitive`; the Succ case's `closedBy` is `axiom`.
- **`associative` on `add`** (primitive axiom, for the fusion-shape test): closes with the Succ case
  closing by IH; the base case by congruence + reflexivity.
- **`commutative` on `add`**: `notDerivable` with the open base case named (`b` vs `add(b, …)` — no
  move applies). The honest edge, pinned.
- **IH misuse guard**: `constB = \a:Nat. \b:Nat. fold [Nat] a { Zero() ->
  b, Succ(p) -> Zero() }`,
  claim `identity: Zero` — the left instance closes, the right instance's Succ case
  (`Zero() ≡ Succ(p)`) stays open, and the certificate must NOT record an IH application there (the
  IH at `p` does not match a constructor head). `notDerivable` overall.
- **Budget**: a handler whose Succ case needs more than `MAX_STEPS_PER_CASE` axiom applications (a
  chain of composed wrappers) exhausts the budget → `notDerivable` with the budget named. (The
  discharger accepts an override for this test.)
- **Axiom eligibility (no laundering)**: `g` with an _`asserted`_ associative law; `f`'s handlers
  call `g`; claim `associative` on `f` — the derivation declines (the only candidate axiom is
  ineligible) → `notDerivable`; the same claim with `g`'s law re-installed `primitive` (fresh
  registry) closes.
- **Absorbing/involutory shapes**: a unary `involutory` op over Nat
  (`succInv = \n. fold [Nat] n { Zero() -> Zero(), Succ(p) -> p }` — hmm, not involutive; use
  `doubleNeg`-shaped over a Bool-carried Nat — picked from fixtures; closes by unfold×2 +
  reflexivity) and an `absorbing` claim with a constructor-shaped argument term; a non-constructor
  argument term (e.g. `add(x, y)`) → shape-rejection at `deriveLaw` entry.

**Routing (end-to-end through `declareCheckedLaw`):**

- `screeningRegime({identity, Zero}, addOp)` → `"derivable"` (axis is a param, definition
  fold-built); without the derivable arm's gate passing (e.g. an unfold-containing definition) →
  `"residual"`.
- `identity: Zero` on `add` end-to-end: installs **`discharged`**, regime `"derivable"`,
  `derivation` certificate present, and the belt-and-braces screen's count recorded.
- **The fallback**: `commutative` on `add` → engine declines → the residual screen runs → installs
  **`asserted`**, reported regime `"residual"` — pre-existing behavior preserved, now with the
  attempted derivation visible in the certificate-less return.
- **The falsified residual**: `identity: Zero` on `constB` (which does NOT satisfy it) → screen
  falsifies → `LawError`, nothing installed.
- **Non-derivable handler staying residual** (the acceptance test): a Nat op whose handler calls a
  lawless op; claim `identity` → `notDerivable` → screen → `asserted`.
- Existing exact counts unchanged: exhaustion 8/4, pattern screen 1/2, `declareCheckedLaw` return
  shape additive only.

## 7. Acceptance mapping (issue #63)

| Acceptance item                                                                                             | Covered by                           |
| ----------------------------------------------------------------------------------------------------------- | ------------------------------------ |
| The handler-fragment characterization, decided and documented                                               | §4, D5, step 6 (type-algebra.md §6)  |
| Skeleton generation from the fold functor (the motive is mechanical)                                        | D3                                   |
| The calculational rules (at minimum fold-fusion) as the discharge engine                                    | D4 (+ the fusion mapping note)       |
| `screeningRegime` gains the `derivable` arm; `discharged` on a successful derivation                        | D6, step 3                           |
| Tests: a fold-composition law on Nat deriving from primitive laws; a non-derivable handler staying residual | §6 (Claims 2 and the residual tests) |
| Fiore–Leinster caution honored: no type-iso rewrite enters `↝` from raw algebraic manipulation              | D10                                  |

## 8. Risks

- **Reader/grammar drift.** `defShape` reads the LC concrete syntax independently of the grammar; a
  syntax revision the reader doesn't know fails loud (shape-rejection with the construct named) —
  routed residual, never mis-proved. The reader/evaluator agreement test (§6) pins drift.
- **Symbolic divergence.** Unfold grows terms (`Succ(add(p, b))` re-embeds ops); the budgets
  (`MAX_UNFOLDS_PER_CASE`, `MAX_STEPS_PER_CASE`) bound every case absolutely — the engine terminates
  on all inputs by construction, and budget exhaustion is an _incompleteness_ (residual), never a
  hang.
- **The optimistic arm.** `derivable` routing runs the (cheap) derivation attempt on every
  shape-passing residual claim; claims that decline pay one failed derivation before screening. The
  gate is syntactic and budget-free; the cost is bounded and the fallback is the untouched residual
  path.
- **Fabricated proofs.** The engine's IH is the only move that could fabricate soundness if
  mis-scoped (D4's guard: recursion variables of the current case only). The misuse-guard test pins
  the behavior; the belt-and-braces screen (D7) gives concrete-instance redundancy on every
  discharged claim.
- **`distributive` expectations.** Deferring it leaves relational laws on unbounded carriers
  residual (as today). The deferral is stated in §10 with the design surface it will need (a two-op
  skeleton), not silently dropped.

## 9. Deferred items — with reasons

- **`distributive` derivation.** Needs a two-operation skeleton and cross-op axiom matching; the
  single-op engine lands first and the extension is additive (a second motive family). Routes
  residual until then — unchanged behavior.
- **Nested/double induction skeletons** (the `commutative`-on-`add` shape). The fragment's honest
  edge; documented as the natural extension, not a redesign.
- **Dead-call analysis** (excusing lawless calls in semantically dead positions). Requires a
  liveness analysis over handler bodies; the first cut's conservative reading (any closure-blocking
  lawless call disqualifies) is sound and decidable.
- **AC-matching in axiom steps.** Axiom application is syntactic schema-shape matching;
  commutativity-modulo-AC matching would broaden the fragment but adds search-shaped machinery —
  explicitly against this engine's design (no search, no unification).
- **Builtin-op pinning (seeding real `primitive` laws).** A surface/ language-definition concern
  (which builtins exist, their pinned law sets); the engine consumes the ladder as it stands (D5)
  and needs no change when pinning arrives.
- **Live-observation re-derivation.** The runtime observation channel (design-decisions.md) is a
  separate mechanism; a withdrawn axiom invalidates derivations that consumed it — a re-derivation
  policy rides with the live-image mode, not this PBI.

## 10. Effort and sequencing

**Effort: Large.** The reader (~250 lines) and the discharger (~400 lines) are the substance; the
routing is thin. Sequence: steps 1–2 (reader + scan export, unit-tested) → 3 (routing) → 5 (tests,
continuously green) → 6 (docs). The suite stays green throughout; the derivable arm is additive —
every pre-existing routing outcome is preserved verbatim when the gate declines.

## 11. Implementation record (2026-09)

Steps 1–5 are complete: `src/core/derivation.ts` (the term AST, the `DerivationReader` grammar
subclass, `readDefShape`, the symbolic schema instantiation, `proveCase`, `deriveLaw`,
`derivableFragment`), `scanOpReferences` exported from `ops.ts`, the `derivable` arm wired through
`declareCheckedLaw` (with the belt-and-braces screen), the barrel exports, and
`test/derivable.test.ts` — 18 tests covering the reader, the gate, the three canonical claims, the
IH misuse guard, the budget, the no-laundering rule, the argument-shape rejection, and the routing
boundaries.

Two engine details settled during implementation, beyond the plan's sketch:

- **The E-Op operand rule at the symbolic level.** An op application is a symbolic value (its
  operands are values at evaluation time), while a fold term is NOT a value shape (its value depends
  on the scrutinee's future value). The unfold therefore fires first and the operands stay symbolic;
  the E-Fold scrutinee rule normalizes the scrutinee before firing. This keeps normalization
  symmetric — the mirrored side of an obligation unfolds the same way.
- **The discharger's progress guard.** The fixed-priority move sequence never backtracks, so a
  rewrite that re-produces a configuration already processed this case (the mirror ping-pong) is
  recorded as a failed move and the next move is tried on the current pair — the move sequence does
  not restart on a rewrite that made no progress.

The routing tests live in `test/derivable.test.ts` (the registry-free caller, the falsified
residual, the lawless-axiom-base decline, the derivable installation) — `discharge.test.ts` was left
untouched; the boundaries the plan assigned it are pinned by the derivable suite's routing tests.

Step 6 (the theory docs' status updates) remains open.
