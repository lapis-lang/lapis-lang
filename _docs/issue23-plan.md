# PBI #23 — T-FoldMatch + E-FoldMatch: pattern-matched fold (elimination)

> **Status:** Planning. Implements [issue #23](https://github.com/lapis-lang/lapis-lang/issues/23) —
> the elimination form for pattern-matched data types (`PatternDataType`), the grammar-as-semantics
> counterpart of the introduction side (#24, merged via PR #79). Branch: `mlhaufe/issue23` (created;
> baseline `3658503`, check/test/lint/fmt green).

## 1. Summary

`fold [T] e {pᵢ → tᵢ}` is the elimination form over a pattern-matched data type `T = μ α. Σᵢ pᵢ`:
each handler takes one declared pattern, the scrutinee is a matched token, and the handler receives
the token bound to `match`. Two rules implement it — **T-FoldMatch** (typing, lc.md §5.2b) and
**E-FoldMatch** (lc.md §3.1) — plus a base-grammar production `patternFoldProd` shared by all
`AbstractLC` subclasses.

The shape is deliberately the "easy fold": a `PatternDataType` has **no fields and no `Family`
positions** — the fold is depth-1. There is no recursive-field substitution walk, no σ fixpoint, no
`Family` handling: T-FoldMatch is fixpoint-free (each handler body types once under `match : Token`,
and the fold's σ is the bodies' COMMON result type — see D2 below), and E-FoldMatch is a single-step
extraction. The novelty here is not the control flow; it is that `data`'s declaration _is_ a grammar
production and this fold is its semantic action — the third consumer of the `PatternDataType`
machinery after the token gate (#24) and the law-checking sample vocabulary.

## 2. Formal rules (authoritative source: `_docs/theory/lc.md`)

```
T = μ α. Σᵢ pᵢ
Γ ⊢ e : T
Γ ⊢ tᵢ : Token → σ   (for each pattern pᵢ)
────────────────────────────────────────────────────────────────  (T-FoldMatch)
Γ ⊢ fold [T] e {pᵢ → tᵢ} : σ
```

```
fold [T] (match(pₖ)) {pᵢ → tᵢ}
  → [match ↦ tok] tₖ                                  (E-FoldMatch)
  where tok is the matched Token for pattern pₖ
```

Progress/Preservation sketches already cover the rule (lc.md §6.1 "Fold" and §6.2 "E-FoldMatch") —
**no `lc.md` changes needed**. The doc already writes the `match ↦ tok` binding; it does not yet
spell the _concrete_ handler syntax below — surface-syntax.md is where concrete syntax lives, and it
is silent on this form today.

## 3. Design decisions

### D1 — Concrete syntax: `fold [T] e { match("pᵢ") → tᵢ }` (no binding position)

The abstract notation writes handlers as bare `pᵢ → tᵢ`, but the concrete syntax needs a spelling.
Options:

- **(a) `match("pᵢ") → tᵢ`** — the handler head reuses `patternMatchProd`'s shape (`match` + tight
  paren + quoted pattern). The _gate is the same walk_ (`patternTypeName`): a handler's pattern must
  be **declared on the fold's carrier** — the declared-ness premise T-FoldMatch reads off the
  carrier's `patterns` list, and `match("p")`'s gate already proves exactly that (anchored,
  resolvable, declared). Exhaustiveness = every declared `pᵢ` of the carrier has a handler; dispatch
  compares canonical sources.
- (b) bare quoted pattern `"pᵢ" → tᵢ` — a NEW lexeme class inside `{…}`, a string-literal position
  the grammar otherwise never has; introduces a second spelling for "a pattern as a constructor"
  that the introduction form does not use.
- (c) bare `ident → tᵢ` — collides with the variant-fold handler head and with variable references.

**(a) is chosen.** The handler head is the constructor (`T-Pattern`'s premise: "input matches pₖ ∈
{pᵢ}") — spelling the constructor the same way in both introduction and elimination makes the two
routes lexically one form, and the canonicalization story (two spellings of one AST introduce equal
tokens) carries over to dispatch unchanged. No new lexemes, no new gates.

**No binding position.** E-FoldMatch substitutes `[match ↦ tok]` — a fixed binding name, like the
`match` keyword's own shape. A `C(x)`-style binding list would suggest field extraction, which does
not exist (a pattern has no fields). The handler body simply references `match`:

```
fold [NatPat] tok { match("[0-9]+") → toNumber(match) }
```

`match` binds at type `Token` (lc.md §5.2b: `tᵢ : Token → σ`). Reserved-name check: `match` is
already reserved from Ω (`BUILTIN_CALL_FORMS`, `ops.ts`), and a user `λmatch:…` would shadow
lexically — acceptable and consistent with every other binder; the binding is installed _under_ the
existing Γ/ρ extension machinery, so shadowing follows the usual last-binding-wins rule (see D5 for
the shadowing interplay with the pattern gate's `nameBound`).

### D2 — Typing: one pass, no fixpoint

T-Fold is a fixpoint because recursive (`Family`) fields rebind to the σ being computed. A
`PatternDataType` has **no fields at all** — every handler body is a closed judgment `Γ ⊢ tᵢ : σ`
with `match : Token` in Γ. There is nothing to iterate: σᵢ is just each body's type. But the rule's
conclusion demands **one** σ for the whole fold.

Options:

- **(a) Require all bodies to share one type via join** — `σ = ⨆ᵢ type(tᵢ)`. Matches T-Fold's shape
  (σ exists independently of the scrutinee).
- **(b) Require all bodies to be equal** (S-Refl per body against the first) — stricter, no lattice
  dependence.

**(b) is chosen** — lc.md §5.2b's formal rule demands every handler body types as `Token → σ` for
the SAME σ (the shared conclusion its preservation argument reads), so a body diverging from the
first body's type rejects the fold (an empty forest — the branch-reject shape, never a laundered
`Any`). The join of unrelated types would admit a fold whose fired branch is unknowable — a
semantics change the authoritative rule does not license.

So T-FoldMatch typing is: parse handlers (capturing spans + extended contexts, exactly T-Fold's
`spanFoldHandler` shape), check each body ONCE (no re-parse — there is no σ to refine; `match`'s
type is statically `Token`), require every body to equal the first body's type (`typeEquals` — one
common σ), and emit that σ. **No `parseToFixpoint` involvement.** The σ slot in the base `fold()`
action signature is filled with that common type (for the AST builder's shape; see D4).

**Premises, checked in this order** (a failure at any step rejects the branch — `empty<Type>()`,
never a throw; the established production-path shape):

1. The annotation `ty` is a `PatternDataType` (`fold [Stream] …` on codata rejects, like the base
   fold's `DataType` gate).
2. Scrutinee types at all and `isSubtype(scrutineeType, T)`.
3. **Exhaustiveness: every declared pattern of `T` has a handler** — the dual of T-Fold's
   every-variant check, keyed on canonical pattern source (`patternToString`), the same key the
   registry's reverse index uses.
4. `scrutineeType` is not `NothingType` → result `Nothing` (principle of explosion, checked after
   the structural premises exactly as T-Fold does).
5. Each handler body types under `Γ, match: Token` — a failed body rejects the branch (loud parse
   rejection; the body's type feeds the common-σ check).

**Result:** `σ = join(type(t₁), …, type(tₙ))`, well-formedness guaranteed by `join`'s own contract.

Note on `Token`: `TokenType`/`Token` already exists (`types.ts`), subtyping handles it
(`S-Refl`/`S-Top` only — subtyping.ts line ~180), and `Any`/`Nothing` absorb it normally. Binding
`match : Token` needs no lattice work.

### D3 — Evaluation: span-captured handlers + `_forward`, token dispatch

E-FoldMatch mirrors `evalFold`'s architecture with the token shortcut:

1. **Production override** (`@rule({ rule: "E-FoldMatch", production:
   "patternFoldProd" })`) —
   capture each handler body's span (the `_forward` discipline E-Fold uses so a handler body
   re-evaluates under the fold's ambient scope), the same `spanFoldHandlers` pattern with pattern
   heads instead of variant heads.
2. **Dispatch:** the scrutinee is a value (the fold is eager — same premise discipline as E-Fold's
   `scrutinee instanceof VariantVal`). It must be a `TokenVal` whose `dataTypeName` names the fold's
   carrier. No match → `EVAL_ERROR("fold scrutinee is not a TokenVal")` (the E-Fold message
   convention).
3. **Handler lookup by canonical pattern source:** compare the scrutinee `TokenVal.text` against the
   handler's canonical pattern source. The token's text IS the canonical source on the `match("p")`
   route and the type name on the bare-atom route. **The bare atom's text will not equal any
   declared pattern source** — the dispatcher must consult the route: a `route ===
   "token"`
   scrutinee carries the type name, not a pattern, so it matches by position only when the carrier
   declares a pattern whose canonical source equals the type name (a pathological coincidence). The
   honest reading: the bare-atom token does not name a pattern, so E-FoldMatch dispatch on it is a
   **miss → `EVAL_ERROR`** unless the carrier genuinely declares that name-shaped pattern. Document
   the asymmetry in `eval_grammar.ts`'s handler doc rather than special-casing (the bare atom
   remains the _value_ of the type; the _fold_ keys on declared patterns — a bare-atom token
   introduced under a type whose declared patterns do not include its own name-lexed form simply has
   no handler it can reach, which is the same "no handler for variant" failure shape E-Fold
   reports).
4. **The step:** `handlerEnv = ambientEnv.extend("match", scrutinee)` — the token value itself, NOT
   re-evaluated (it is already a value; E-FoldMatch is a single step, `[match ↦ tok] tₖ`). Then
   `_forward` the body span under that environment (the E-Fold body-replay machinery, offset
   save/restore included).
5. **No recursion:** no fields, no `Family` — no `evalFold`-style recursive call. If the body
   mentions the fold again (e.g. `fold [T] tok { … fold [T]
   match … }`), that inner fold
   evaluates through the same path on its own scrutinee — the termination story is the _term's_
   structure, not the fold's.

**Zero-pattern carriers** (`patterns.length === 0`): exhaustiveness is vacuous (no declared patterns
→ no handlers required), but the fold is then unreachable — the carrier has no tokens (the token
gate still accepts a bare atom for a zero-pattern type today, `patternTokenProd` checks only
`instanceof PatternDataType`; a fold over such a token errors at dispatch — "no handler for pattern"
— which is the honest dead end, matching E-Fold's behavior for a zero-variant type).

### D4 — Grammar surface: `patternFoldProd` + abstract action

In `grammar.ts` (base `AbstractLC`):

```ts
// fold [T] e { match("pᵢ") → tᵢ, ... }
@rule
protected patternFoldProd(ctx: unknown): Parser<S["expr"]> {
    // kw("fold") + [T] gate on PatternDataType (branch REJECTED on wrong kind,
    // like foldProd's DataType gate — the two branches are lexically
    // IDENTICAL up to the type gate, so ORDER MATTERS: patternFoldProd is
    // tried BEFORE foldProd, or foldProd's `assert(ty instanceof DataType)`
    // throws out of the parse on a pattern carrier).
}
```

**Ordering is the one sharp edge.** `foldProd` currently `assert`s its annotation kind; a
pattern-typed annotation would crash the parse rather than reject the branch. Two shapes fix this:

- **Chosen: `patternFoldProd` ordered FIRST in `exprProd`'s `or(...)`, and it rejects the branch
  (`empty`) when `ty` is not a `PatternDataType`.** The base `foldProd` keeps its assert — it is now
  only reached with a non-pattern annotation, so the assert is a caller-bug guard again (same shape
  `matchedToken`'s assert took in #24). Actually safer still: **change both folds to branch-reject
  on wrong kind** (`empty`), keeping the assert only in the checker/evaluator subclasses where the
  premise is _formally_ owned. The base grammar never throws on a user program; wrong-kind
  annotations are failed parses.
- Alternative rejected: a shared production parameterized on kind — more coupling than the 15
  duplicated lines are worth.

**New abstract action** (the `fold()` mirror):

```ts
protected abstract patternFold(
    dataType: PatternDataType,
    scrutinee: S["expr"],
    handlers: { patternSource: string; body: S["expr"] }[],
    resultType: Type,
): S["expr"]
```

`resultType` slot matches `fold()`'s signature shape (the checker's σ — `Any` at the base grammar,
as `foldProd` passes today). Handlers carry the **canonical** pattern source (the `patternTypeName`
gate returns it) — dispatch and exhaustiveness key on canonical form everywhere.

**Handler production** `patternFoldHandler(dataType, ctx)`: `kw("match")` + tight paren +
`patternString` + tight close, `ws`, `arrow`, `ws`, body — the body parsed under
`extendCtx(ctx, "match", Token)` (checker) / `extendCtx(ctx, "match", ...)` — wait, the base
grammar's `extendCtx` is the context-extension hook both subclasses override, so the base production
passes `this.extendCtx(ctx, "match", Token)` exactly as `foldHandler` extends with field types. The
base grammar does NOT need to know the carrier for this — `match : Token` is kind-independent.

**Gate:** the handler head runs `patternTypeName(source)` (the existing `patternMatchProd` walk) and
additionally checks the resolved type's name equals the fold carrier's name. A pattern declared on a
DIFFERENT registered type rejects the handler branch (it would be unmatchable and would corrupt the
exhaustiveness accounting).

**`DerivationReader` (derivation.ts):** the fold-skeleton fragment is a variant-carrier language.
The reader's `patternFold` action (new abstract action → new required override) throws
`DefinitionShapeError` naming the construct, and `REJECTED_CONSTRUCTS` gains no entry — `fold` is
already rejected at the pre-scan level _only_ when the reader cannot skeletonize it; actually the
pre-scan rejects by lexeme, and `fold` is NOT in `REJECTED_CONSTRUCTS` (variant-carrier folds are
legal). So: the reader's `patternFold` override throws loudly (same shape as `matchedPattern`'s
throw — the fragment is variant-only today; extending the skeleton to pattern carriers is future
work for the derivation engine, NOT this PBI). The reader-side seam is one throw with a good
diagnostic.

### D5 — Naming/`match` binding interactions

- `nameBound("match", ctx)` inside a fold handler: the handler's context extension shadows any outer
  `match` binding for the body — standard lexical behavior, no special casing.
- The `patternMatchProd` introduction gate is **context-unaware** (T-Pattern has no Γ premise) — but
  a user binding `match` as a variable inside a pattern-fold body
  (`fold [T] e { match("p") → let match:Any = … }`) shadows for the body only. No interaction with
  the fold's own `match ↦ tok` substitution (the evaluator extends ρ once; the body's own let
  shadows inside its span). Nothing to enforce; a test pins it.
- The base `patternFoldProd` is gated on the registry only through the carrier's existence (the
  annotation `ty` IS the carrier — a resolved `PatternDataType` by definition). No registry gate
  beyond the annotation lookup the type grammar already performs.

### D6 — Rule-model contracts (metadata.test.ts)

The @requires/@ensures contracts feed `collectRules`; `metadata.test.ts` pins the full rule list —
the new rules MUST be added to `expectedTyping`/ `expectedEval` or the metadata tests fail.

- **T-FoldMatch** (on the checker's action, `production: "patternFoldProd"`): premises `e : T`
  (scrutinee subtype) + `tᵢ : Token → σ` (each handler body's type under `match:Token`); conclusion
  `result : σ` (well-formed type).
- **E-FoldMatch** (on the evaluator's action): premise `scrutinee : TokenVal of
  T` (scrutinee
  instanceof TokenVal + carrier match — the `@requires` predicate); conclusion `result : w` (the
  handler body's value).
- The contracts' `formula` strings should quote lc.md's shapes (the established style:
  `rule: "T-FoldMatch", role: "premise", formula: "e : T ∧ T = μ α. Σᵢ pᵢ"`).

### D7 — Cost pass: honest fallback, no new algebra this PBI

`CostPass` (`cost.ts`) reads folds through `foldProd`'s tree records (`spanFoldHandler` records,
`foldSummaryFrom`). A pattern-fold tree today produces: no `spanFoldHandler` records (the new
handler production has a different name) and a carrier that is not a `DataType` → the existing
`foldSummaryFrom` path returns the scrutinee's summary (the `childFlow`/scrutinee fallback at the
top of `foldProd`). That is the WRONG cost shape silently (it under-counts the handler body's work),
and `foldSummaryFrom` is typed on `DataType`.

Decision: **`CostPass` overrides `patternFoldProd` with an explicit conservative summary** — the
fold costs the join (max) of handler bodies' costs plus the scrutinee's cost (no recursion
substitution — there are no recursive positions; `#foldRec` never appears). Records come from a new
`spanPatternFoldHandler` record read the same way. This is a SMALL delta: one override + one
record-reading branch + a `patternFoldSummaryFrom` helper mirroring `foldSummaryFrom` minus the
Family machinery. Alternative (reject pattern folds in the cost fragment) was rejected: the pass
already handles every other expression form, and a silent `scrutinee-only` fallback is the kind of
laundering the repo's review findings flag. (The `CostEngine` — the denotation side — needs only the
`patternFold` abstract action override; its token sizing (`token(T:<p>)`) already exists.)

### D8 — Non-goals (from the PBI + this review)

- **Derivation skeleton support** — the symbolic `Term` gains no `"patternFold"` form; the reader
  throws. (The derivable-regime engine's move set is variant-carrier folds only; pattern-fold laws
  are a separate research question, related to #50's respect-claims.)
- **`cofold`-style multi-pattern simultaneous observation** — patterns are a sum; one handler fires.
- **Real matched text** — E-FoldMatch binds the token the introduction produced (canonical source,
  per #24's value shape). A revision introducing lexer-produced matched text extends the form, not
  this rule.
- **Cross-type folds** — the fold's carrier gates the handlers (D4's gate); a fold over `NatPat`
  cannot match a `DigitPat` token (its scrutinee would fail premise 2's `isSubtype` before dispatch
  anyway).
- **`lc.md` changes** — the formal rules exist (§5.2b, §3.1, §6). Only surface-syntax.md gains a
  short entry (see D10).

## 4. File-by-file deltas

| File                             | Delta                                                                                                                                                                                                                                                                                                                                                                                                |
| -------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `src/core/grammar.ts`            | `patternFoldProd` (base, ordered before `foldProd` in `exprProd`); `patternFoldHandler` (head gate via `patternTypeName` + carrier-name check, body under `extendCtx(…, "match", Token)`); abstract `patternFold` action; header comment's production list updated. `foldProd`'s `assert` → branch-reject (`empty`) on wrong-kind annotation (asserts stay in subclasses).                           |
| `src/core/typing_grammar.ts`     | Override `patternFoldProd` (`@rule`): span-capture handlers under `match:Token` contexts; `evalPatternFold`-style action: premises 1–5 (§3 D2), common-σ check, `@requires`/`@ensures` T-FoldMatch contracts. Exhaustiveness via canonical-source set difference. Nothing-propagation arm (D2.4).                                                                                                    |
| `src/core/eval_grammar.ts`       | Override `patternFoldProd` (`@rule({rule:"E-FoldMatch", production:"patternFoldProd"})`): `spanPatternFoldHandlers` (body spans), `evalPatternFold`: TokenVal dispatch + carrier check + canonical-source handler lookup + `extend("match", scrutinee)` + `_forward` body; `@requires`/`@ensures` E-FoldMatch contracts; `patternFold` action override (unreachable-throw shape like `LCEval.fold`). |
| `src/core/cost.ts`               | `CostPass.patternFoldProd` override (record-reading assembly, §3 D7); `spanPatternFoldHandler` passthrough; `patternFoldSummaryFrom` (no-`Family` mirror of `foldSummaryFrom`); `CostEngine.patternFold` denotation override (reject/throw shape — the engine is the reader for `evaluateReport`, and pattern-fold denotations ride the same re-read fallback).                                      |
| `src/core/derivation.ts`         | `DerivationReader.patternFold` → `DefinitionShapeError` (loud, fragment boundary); no symbolic `Term` form.                                                                                                                                                                                                                                                                                          |
| `src/core/index.ts`              | No new exports (the form is exercised through the grammars; no standalone API).                                                                                                                                                                                                                                                                                                                      |
| `_docs/theory/surface-syntax.md` | Short entry: the `fold [T] e { match("pᵢ") → tᵢ }` concrete form, the `match:Token` binding, the carrier-gated handler head.                                                                                                                                                                                                                                                                         |
| `test/pattern_fold.test.ts`      | New file (§5).                                                                                                                                                                                                                                                                                                                                                                                       |
| `test/metadata.test.ts`          | Add T-FoldMatch to `expectedTyping`, E-FoldMatch to `expectedEval`.                                                                                                                                                                                                                                                                                                                                  |

## 5. Test plan (`test/pattern_fold.test.ts`)

Fixture: reuse `pattern_match.test.ts`'s harness shape (`patternHarness` with `createPatternType`
from `fixtures.ts`) — extract the shared harness or duplicate the 30-line helper (duplication
preferred unless a second consumer appears; #14's fixture module is the long-term home).

**T-FoldMatch:**

1. `fold [NatPat] match("[0-9]+") { match("[0-9]+") → 42 }` types as `Int` (single handler; body
   references `match` at `Token`).
2. Multi-pattern join: bodies of types `Int` and `Nat` (subtypes) join to `Int`; unrelated joins to
   their supertype (or the honest `Any`/rejection shape `join` yields — assert what `join` actually
   returns).
3. **Exhaustiveness:** `NatPat = [0-9]+ , [0-9]*[02468]` (two declared patterns) with one handler →
   `undefined` (empty forest).
4. Undeclared pattern in a handler head (`match("[a-z]+")` over `NatPat`) → `undefined`.
5. Pattern declared on a DIFFERENT registered type in a handler head → `undefined`.
6. Wrong-kind annotation `fold [Nat] … {…}` → `undefined` (branch-reject, not a crash — the ordering
   pin, D4).
7. Scrutinee of the wrong type (`fold [NatPat] <variant-of-Bool> {…}`) → `undefined`.
8. Scrutinee `Nothing`-typed → `Nothing` (principle of explosion arm).
9. `match` shadowing: a λ-bound `match` in scope; the handler body's `match` refers to the token
   (the fold's binding wins inside the body — extendCtx shadows).
10. Canonical equivalence: handler head `match("0123456789")` matches a scrutinee `match("[0-9]")`
    when both normalize to one canonical source (registry-declared either way — one of the two
    spellings must be the registered one; assert dispatch succeeds through canonicalization).

**E-FoldMatch:**

11. `fold [NatPat] match("[0-9]+") { match("[0-9]+") → 42 }` evaluates to `42` (the token steps into
    the body's `match` reference — a body using `match` renders/compares it: e.g. an op identity
    `size(match)`-style check or an `equals` against the token).
12. Multi-pattern: each declared pattern's token routes to its own handler.
13. Non-token scrutinee (a variant) → `EvalErrorValue` ("not a TokenVal").
14. Token of a different type than the carrier → `EvalErrorValue` (no handler).
15. Bare-atom scrutinee (`NatPat` as a term) over a fold whose handlers key patterns →
    `EvalErrorValue` per D3's asymmetry (the token's text is the name, not a pattern source).
16. Missing handler for the matched pattern (non-exhaustive caught at typing; eval-side miss via
    direct `evalPatternFold` if reachable, else skip — typing gates first).
17. `_forward` body span re-evaluation: the body's free variables resolve in the fold's ambient
    scope (an op call or λ in the ambient env used inside the handler body).

**Cost:**

18. Pattern-fold cost report: handler body's cost appears; scrutinee edge present; no `#foldRec`
    variable (no recursion).
19. Opaque scrutinee → conservative summary (no crash).

**Derivation boundary:**

20. `readDefShape` of a definition containing a pattern fold → `DefinitionShapeError` naming the
    construct (the reader's loud rejection).

**Metadata:**

21. `metadata.test.ts`'s two rule-list tests include T-FoldMatch/E-FoldMatch (shape match, premise
    count 2/1, `production` key present for both).

**Round-trip of the form itself** (grammar sanity): the new production's spans — a nested
pattern-fold inside a handler body re-parses (the span-capture machinery under offset arithmetic;
the E-Fold `_forward` offset dance is the risky bit — test a fold-in-fold).

## 6. Boundary conditions

- `deno check src/index.ts` / `deno test` / `deno lint` / `deno fmt` green.
- All 456+ existing tests pass unchanged EXCEPT `metadata.test.ts`'s two rule-list assertions
  (mechanical additions).
- The bare-token gate (`patternTokenProd`), `match("p")` introduction, and E-Pattern/T-Pattern
  behavior are UNCHANGED (no production reordering beyond `exprProd`'s list, which is additive at
  the head).
- No `lc.md` drift: §5.2b/§3.1 already specify the rules; the implementation adds NO rule the doc
  lacks and implements NONE of the doc's rules differently (the `match ↦ tok` substitution is the
  body's binding, not a term rewrite).
- Cross-module first: `deno check src/index.ts` catches grammar-shape breaks (every `AbstractLC`
  subclass must implement the new abstract action — the compiler enumerates them: `LCTypeCheck`,
  `LCEval`, `DerivationReader`, `CostEngine` — all four, no drift).

## 7. Risks / gotchas (from repo memory + this review)

- **Branch ordering in `exprProd`** — the two `fold` forms are lexically identical up to the type
  gate. Get the order wrong and pattern folds crash (`assert`) or ordinary folds reject. Mitigate
  with test 6 AND test 1 side by side.
- **`deno fmt` re-sorts import blocks** — re-read files after fmt before further edits (repo
  gotcha).
- **`Object.freeze` + mutable-typed field needs a cast** — irrelevant here (no new frozen arrays),
  but `patternTypeName`'s returned object is shared — treat as readonly.
- **`IntersectionType` has no `name`** — error messages must not interpolate `type.name` for
  arbitrary types; the fold's carrier is always a `PatternDataType` on verified paths, so messages
  are safe, but scrutinee-mismatch messages should quote the CARRIER name only.
- **Sentinel/error-message pinning**: tests assert message PREFIXES (`EVAL_ERROR` messages flow into
  `EvalErrorValue.message`); keep messages single-line (multi-line template literals break test
  matching — repo gotcha).
- **The bare-atom route's text** (`= name`) vs pattern-source route: D3's asymmetry is a
  documentation + test item, not a bug — do NOT "fix" it by making the bare atom's text a pattern
  source (that would change `TokenVal.equals` and the cost algebra's variable naming, breaking #24's
  pinned behavior).
- **Exhaustiveness keying**: canonical sources ONLY (`patternToString` normalization). Raw-spelling
  keys would let `match("0123456789")` satisfy a `[0-9]` handler only by luck of registry spelling —
  canonical keys make it deterministic regardless of which spelling was registered.

## 8. Effort & sequencing

**Effort:** Medium (as the PBI estimates). The typing side is the largest piece (premise ordering +
join semantics); the evaluator is a small mirror of `evalFold` without the recursion; cost is a
conservative summary; derivation is one throw. Estimated ~600–900 lines including tests.

**Sequencing within the milestone:** unblocks #25 (surface language elaboration, whose dependency
set #22/#23/#24/#20 completes with this PBI). #34 (unparse round-trip) and #50 (quotient research)
remain independent.
