# PBI #62 — Pattern-Carrier Discharge: Language Equations + Sub-Space Specs

> Plan for [issue #62](https://github.com/lapis-lang/lapis-lang/issues/62) (rescoped 2026-09-18: the
> original body's _encoding-family declarations on data types_ are dropped — they contradict the
> token-value architecture; see the issue body's rescope rationale). Design sources:
> [`type-algebra.md`](./theory/type-algebra.md) §2.3/§3/§5, [`semantics.md`](./theory/semantics.md)
> §5.4, [`surface-syntax.md`](./theory/surface-syntax.md) §1.3, issue #65 D6 (the deferred
> language-equation reading).

## 1. Summary

Pattern carriers (`Nat`, `Int`, `String`, user-declared pattern types like `Rational`, `Complex`,
Bra–ket) are permanently barred from structural exhaustion: §2.3 (Chomsky–Schützenberger) — their
generating functions are rational, never polynomial, so `screeningRegime` routes them `residual`
today. This PBI closes the gap with two mechanisms:

1. **The pattern language-equation reading** — `coefficients` computes exact size-class counts for
   pattern types from the pattern's language equation (concatenation multiplies, alternation sums,
   Kleene star inverts $(1-P)$), replacing the #65-declared singleton fallback (issue #65 D6). The
   certificate becomes _derived_, not asserted: it cannot disagree with the pattern the user wrote.
2. **Sub-space specifications on law declarations** — a law scopes its claim ("all Ints with
   $|x| \le 2^{31}$"), so bounded enumeration **certifies the checked sub-space**: `discharged` for
   the sweep ∩ sub-space, `asserted` beyond it — visible provenance, the claim is the certification.
   This is the only honest discharge route for pattern carriers, and totality makes it necessary:
   full-coverage certification (the `exhaustLaw` contract) requires sweeping the complete sample
   space, so a sweep that skips out-of-sub-space instances would silently break the certificate. The
   sub-space scope belongs on the law declaration, not the type.

Also decided here (one line, no mechanism): the character universe for `.` and character classes is
a single language-definition fiat (recorded in `surface-syntax.md`), not a per-type declaration
form. Bounded-length string enumeration rides on sized types (the existing termination decision).

## 2. Current state

| Piece                                                     | Location                                                   | Status                                                          |
| --------------------------------------------------------- | ---------------------------------------------------------- | --------------------------------------------------------------- |
| `PatternDataType` (sum of regexes, token sole inhabitant) | `src/core/types.ts`                                        | implemented — patterns are `string[]` (source form), **no AST** |
| T-Token (token types as its pattern type)                 | `src/core/typing_grammar.ts` `matchedToken`                | implemented                                                     |
| Token value (raw text IS the value)                       | `src/core/values.ts` `TokenVal`                            | implemented                                                     |
| Token sampling (the singleton name-token)                 | `src/core/law_checking.ts` `patternSamples`                | implemented — the #65 fallback                                  |
| Coefficient fallback (c₁ = 1)                             | `src/core/type_algebra.ts` `coefficients`                  | implemented — the declared fallback, line ~431                  |
| Enumeration fallback                                      | `src/core/law_checking.ts` `inhabitantsUpToSize`           | implemented — the same fallback                                 |
| Regime routing (`finite` / `residual`)                    | `src/core/law_checking.ts` `screeningRegime`               | implemented — pattern carriers always `residual` (sweep = ∞)    |
| Exhaustion (`discharged` on full coverage)                | `src/core/law_checking.ts` `exhaustLaw`                    | implemented — never routes for pattern carriers                 |
| Certified screen (size-≤ kᵢ prefix, theorem-checked)      | `src/core/law_checking.ts` `screenLaw` + `certifyCoverage` | implemented (#65)                                               |
| Law declaration surface                                   | `src/core/laws.ts` `LawDecl`                               | `kind` / `target` / `argument` — **no scope field**             |
| Provenance ladder                                         | `src/core/laws.ts` `LawProvenance`                         | `primitive \| discharged \| asserted` — unchanged by this PBI   |

## 3. Design decisions

### D1 — The language-equation reading: a pattern AST is the prerequisite

`PatternDataType.patterns` is `string[]` — raw source. The language-equation reading needs
structure: each pattern becomes an AST node whose language equation is read mechanically.

- **Module: `src/core/pattern_lang.ts` (new).** The pattern grammar is _already_ specified in
  `surface-syntax.md` §1.3 (restricted regular fragment: char literals, `.`, classes, negated
  classes, `+ * ?`, type references `<T>`, escapes; excluded: alternation `|`, groups `()`, anchors,
  backreferences). The AST is: `Concat(parts)`, `Alt(parts)` (only via multi-variant declaration),
  `Star(p)`, `Plus(p)`, `Opt(p)`, `Class(chars, negated)`, `Any`, `Char(c)`, `TypeRef(name)`.
- **Parsing**: a small hand-rolled recursive-descent parser (lang-forma already powers the surface;
  the pattern grammar is tiny and self-contained — a dedicated parser avoids a grammar-in-grammar
  cycle). Rejection of excluded constructs (`|`, `()`, `^` anchors, backrefs) happens here, loudly.
- # **The equation (the counting semantics)**: for a pattern node $P$, its language's per-length counting $c_n$ satisfies — char/class/`. → $c_1 = 1$; concatenation $PQ$ → convolution
  ($c_n = \sum_i c^P_i c^Q_{n-i}$); star $P^*$ → $c_0 = 1$, then convolution with the prefix sum
  (the geometric reading of $L = 1 + P·L$; for`Nat
  [0-9]+`: $L = P·L^?$ gives $c_n = 10^n$);
  plus/opt → prefix of the inner reading; type reference`<T>`→ the referenced type's coefficients
  (recursion through registered types, memoized — cycles reject loudly: a`<T>` cycle makes the
  language equation ill-founded).
- **Where it lands**: `coefficients`'s `PatternDataType` arm switches from the fallback to
  `patternCoefficients(pattern, k)`; `inhabitantsUpToSize`'s `PatternDataType` arm enumerates the
  true size-≤ k token set (all matched strings of length ≤ k over the equation's alphabet) instead
  of the singleton. The **certification stays exact**: `certifyPosition` asserts enumerated count ==
  coefficients count — for pattern types this is now a real theorem (e.g. `Nat`, k = 2: enumerate
  `0, 1, …, 99, …` → 110 tokens of size ≤ 2; coefficients say $10^0+10^1+10^2 = 111$… see D2 for the
  size convention fix this forces).
- **Budgets stay**: `PREFIX_BUDGET` caps any prefix sweep; a pattern type whose size-≤ k class
  exceeds the budget declines loudly (the certificate never guesses).

### D2 — Token size: text length is the size measure

`valueSize` counts constructor nodes; a token is one node (size 1) today — that is why the fallback
certificate is c₁ = 1. With the language-equation reading the honest measure for tokens is **text
length** (the language equation counts per-length; `Nat`'s $c_n = 10^n$ counts strings of exactly
length n). Decision: a `TokenVal`'s size is `text.length` (a nonempty token; the empty string
matches `[^"]*`-style patterns — size 0, honest). `valueSize` gains the token arm; the singleton
fallback (a size-1 name-token) and the equation reading (length-based) then agree that c₁ counts
single-character tokens. Migration: the fallback c₁ = 1 remains true only for pattern types whose
language has exactly one length-1 string — the tests' `NatPat = [0-9]+` has c₁ = 10, and
`inhabitantsUpToSize(NatPat, 1)` returns 10 tokens. The #65 tests asserting the singleton fallback
are updated (the fallback is _replaced_, per issue #65 D6's own note).

### D3 — Sub-space specs live on `LawDecl`, not the type

A law declaration gains an optional scope:

```ts
interface SubSpaceSpec {
    /** The operand position the spec restricts (schema variable index). */
    readonly position: number
    /** The restriction, as an LC predicate over the bound (LC source). */
    readonly where: string
}
// LawDecl gains: readonly subSpace?: readonly SubSpaceSpec[]
```

- **Why on the law**: the claim "commutativity holds for all $|x| \le 2^{31}$" is a claim about the
  _law_, not the type. The type stays the pure lexeme space (the token architecture); the
  interpretation (what `|x|` means) is the fold layer's business — the predicate is evaluated by the
  same `eval_` machinery every check already uses.
- **Surface**: an extension of the properties/spec-record surface
  (`properties: (commutative where: [x | |x| <= 2147483647])` shape — final spelling lands with the
  surface PBI; the core accepts the structured `SubSpaceSpec`). The predicate is type-checked
  against the operand's carrier (a `LawTypeChecker` premise, same as argument terms).
- **Certification arithmetic**: for a position with sub-space spec S, the certified sweep is
  $\prod_i |T_i|^{v_i} \times \prod_{i \in S} \text{density}(S_i)$… no — simpler and honest: the
  enumeration filters each position's space by the predicate; the certificate counts **exactly the
  swept sub-space**: "checked all inhabitants of size ≤ kᵢ satisfying Sᵢ — exactly N, verified".
  `coefficients` on a pattern carrier provides the denominator only when the sub-space's size is
  itself computable; otherwise the certificate states the swept count and the filter predicate (the
  claim is scoped, so the count IS the claim's domain — the same sweep arithmetic `screeningRegime`
  runs, restricted).

### D4 — Discharge: the `machineFinite` arm routes to sub-space exhaustion

- `screeningRegime` gains the `machineFinite` outcome: a carrier that is a `PatternDataType` (or a
  record/finite over pattern-typed fields) WITH a total sub-space spec whose restricted sweep fits
  `MAX_EXHAUSTION_INSTANCES` routes `machineFinite`; everything else stays `finite`/`residual`
  (unchanged).
- The routed check is `exhaustLaw` with per-position filtering: the lazy per-position spaces are
  filtered by the sub-space predicate _before_ the product — the full-coverage contract (a
  non-evaluating instance rejects) carries over untouched, now over the sub-space.
- Provenance: a passing sub-space exhaustion installs `discharged`, and the law's declaration
  carries the scope — the visible provenance is `discharged` **scoped to the declared range**
  (`asserted` beyond it is the honest reading: the tag's meaning is per-claim, and the claim was
  scoped). No new provenance tag.
- An unscoped law over a pattern carrier: no discharge route (§2.3 bars full-domain exhaustion) →
  stays `residual`/`asserted` via the certified screen — now with exact coefficients (D1).

### D5 — Provenance is UNCHANGED (the ladder holds)

`LawProvenance` keeps three tiers. The scope lives on the declaration (like `argument` does for
argument-taking kinds); the ladder's meaning is per-declaration. Nothing in `≡`/`↝` consults
provenance today; nothing consults the scope either — both are recorded authority metadata. The
"asserted beyond the range" honesty is documentation + the declaration's visible scope, not a
runtime guard (a rewrite consuming a scoped `discharged` law outside its scope is a v0.4.0+
exploitation-phase question, deferred with the rest of exploitation).

### D6 — What stays out (the dropped mechanism, restated)

No encoding-family declarations on `data` (the rescope). No `|T|` constants, no `encoding` keyword,
no per-type alphabet declarations. Machine numerics (`Float` et al.) are prelude pattern types +
primitive operations with pinned laws when they land — the `primitive` tier is their trust story,
not a declaration on the type. The character universe is a one-line fiat in `surface-syntax.md`
(recorded here as the decision: the universe is **ASCII** (code points 0–127) for now — `.` and
classes range over ASCII only; widening to Unicode is a later, separate language-definition change,
and until then a Unicode lexeme has no pattern variant and no token can carry it).

## 4. Implementation steps

1. **`src/core/pattern_lang.ts` (new)** — the pattern AST, the recursive-descent parser (source →
   AST, rejecting excluded constructs loudly), and `patternCoefficients(ast, k, env)` (the
   language-equation reading: convolution-based counting, memoized across type references). Pure; no
   imports beyond `types.ts` (for the registered-type environment interface).
2. **`src/core/types.ts`** — `PatternDataType.patterns` becomes `PatternAST[]` (parsed at
   declaration); a `parse` failure is a declaration error, loud. (If keeping `string[]` source is
   preferred for rendering, the AST is stored alongside: `patterns: string[]` stays, +
   `patternAsts: PatternAST[]` — decided at implementation: AST-only, rendering back to source is a
   `toString` on the AST.)
3. **`src/core/type_algebra.ts`** — `coefficients`'s `PatternDataType` arm → the language-equation
   reading (D1). Remove the fallback comment; the fallback is gone (replaced).
4. **`src/core/values.ts`** — `valueSize`'s token arm: text length (D2).
5. **`src/core/law_checking.ts`** — `inhabitantsUpToSize`'s pattern arm: enumerate all matched
   strings of size ≤ k (from the AST, via the same lazy-product discipline; deduped; budget-capped);
   `LawDecl.subSpace` filtering in `exhaustLaw` (the machineFinite arm) and `screenLaw` (scoped
   certificates state the filter); `screeningRegime`'s `machineFinite` arm (D4); `declareCheckedLaw`
   plumbs the scope into the installed `LawDecl`.
6. **`src/core/laws.ts`** — `LawDecl.subSpace` + validation (the predicate type-checks against the
   operand carrier; positions are in range; the predicate mentions exactly one schema variable;
   `LawTypeChecker` integration in `validateLaw`).
7. **`src/core/index.ts`** — export the new surface (`SubSpaceSpec`, `patternCoefficients`, the AST
   types).
8. **`test/pattern_lang.test.ts` (new)** — parser round-trips, equation counts, rejection cases.
9. **`test/type_algebra.test.ts`** — pattern-type coefficient tests (§5); update the fallback tests.
10. **`test/discharge.test.ts`** — sub-space discharge tests (§5); update the fallback-dependent
    assertions.
11. **Docs** — `type-algebra.md` §2.3 (the language-equation reading is implemented; §5 rewritten:
    sub-space specs + the dropped mechanism recorded as a rejected design with rationale) + §7
    status table; `semantics.md` §5.4 (machineFinite design note → implemented-status, minus
    encoding families); `surface-syntax.md` §1.3 (the character-universe fiat; the sub-space surface
    form when the surface PBI lands); `issue65-plan.md` D6 (pointer: replaced by #62);
    `_docs/lc-core-implementation-plan.md` (PBI #62 entry updated).

## 5. Tests

**Pattern language equations (`test/pattern_lang.test.ts`, `test/type_algebra.test.ts`):**

- `Nat = [0-9]+`: $c_n = 10^n$ — coefficients `[0, 10, 100, 1000]` at k = 3.
- `Int = -?[0-9]+`: $c_1 = 11$ (`-` … digits — `-?` contributes the length-1 `-`), $c_2 = 110$.
- Multi-variant alternation (two patterns): the counts SUM per length.
- `String = "<Char>*"` via the type reference: $c_n = |\Sigma|^n$ with `Char = .` — the universe
  fiat's consequence, asserted explicitly ($|\Sigma| = 128$ under the ASCII fiat).
- Concatenation: a two-pattern-concat shape counts as the convolution.
- Type-reference cycle (`A = <B>`, `B = <A>`): loud rejection.
- Excluded constructs (`|`, `()`, backrefs, bare `.*`): parse rejection with reason.
- Enumeration == coefficients: `inhabitantsUpToSize(NatPat, 2)` has exactly 110 members and the
  certificate asserts the match (size ≤ 2 strings over 10 digits).

**Sub-space discharge (`test/discharge.test.ts`):**

- A `machineFinite`-routed law over a pattern carrier with a sub-space spec discharges
  (`discharged`, scope visible on the installed declaration; instance count == the filtered sweep).
- The same law unscoped stays `residual` → `asserted` via the certified screen.
- The scope predicate is type-checked: a predicate naming an unbound/ill-typed variable rejects
  (`LawDeclarationError`).
- An out-of-range position index rejects.
- A sub-space sweep past `MAX_EXHAUSTION_INSTANCES` declines loudly (residual, not a silent
  oversized sweep).
- The filtered space is genuinely filtered: an operation's law that fails outside the sub-space
  still discharges inside it (and a counterexample inside the sub-space rejects the declaration).

## 6. Acceptance mapping (issue #62, rescoped)

| Issue item                                                                                  | Plan                                                                                            |
| ------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------- |
| Language-equation reading; exact counts; undecidable fragment states the limitation         | D1/D2, steps 1–3, 8–9                                                                           |
| Surface syntax for sub-space specs                                                          | D3 (core: structured field; surface form lands with the pattern-surface PBI — noted in step 11) |
| `screeningRegime` routes machineFinite with certified-range provenance                      | D4, step 5                                                                                      |
| Scoped `discharged` / `asserted` beyond, visible                                            | D4/D5, steps 5–6                                                                                |
| Tests: scoped discharges; unscoped stays residual; exact coefficients match enumeration     | §5                                                                                              |
| Doc updates (semantics §5.4, type-algebra, plan) — encoding families dropped with rationale | Step 11                                                                                         |

## 7. Risks

- **The size-convention change (D2)** touches #65's certificate arithmetic — the fallback tests were
  written under c₁ = 1. Mitigation: the change is confined to token carriers; the updated tests
  re-assert the _theorem_ (enumeration == coefficients) rather than the old constant.
- **Pattern-AST density**: `Nat` at k = 3 already means enumerating 1110 strings for the certificate
  cross-check. Budgets (`PREFIX_BUDGET`, `SWEEP_BUDGET`) apply as-is; larger-k pattern certificates
  decline loudly (consistent with #65's strictness decisions).
- **Type-reference cycles** through `<T>` need a registered-type environment at parse/analyze time —
  the same registry the evaluator already consults; cycle detection is memoized reach analysis (loud
  on a cycle).
- **The sub-space predicate is user code** — it is evaluated by the same total evaluator (no
  divergence risk), but a predicate erroring on an instance is an evaluation hole: the same
  `exhaustLaw` contract applies (reject, don't under-cover).

## 8. Resolved decisions (user-ratified, 2026-09-18)

- **Pattern representation**: AST-only (`patterns: string[]` → parsed `PatternAST[]`); rendering
  back to source is the AST's `toString` (step 2's "decided at implementation" note is resolved:
  AST-only).
- **Sub-space surface form**: core accepts the structured `SubSpaceSpec` now; the surface spelling
  lands with the v0.4.0 pattern-surface PBIs (D3's deferral stands).
- **Character universe**: **ASCII** (code points 0–127) for now. `.` and character classes range
  over ASCII only; a Unicode lexeme has no pattern variant and no token can carry it until a later,
  separate language-definition change widens the universe. Consequence asserted in tests: `String`'s
  counting under `Char = .` has $|\Sigma| = 128$.
