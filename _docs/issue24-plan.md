# PBI #24 — T-Pattern: pattern-matched construction (implementation plan)

> **Status:** Implemented (2026-09-22). Implements
> [issue #24](https://github.com/lapis-lang/lapis-lang/issues/24) — the `match("p")` introduction
> form for pattern-matched data types (T-Pattern), on branch `mlhaufe/issue24`. Gate verified after
> implementation (`deno fmt` / `deno lint` / `deno check src/index.ts` clean; 487 tests green — 29
> in `test/pattern_match.test.ts`).
>
> Out of scope (deliberate): T-FoldMatch + E-FoldMatch — pattern-matched fold (elimination) is #23,
> the next PBI on this branch's critical path. Introduction lands alone; it is independently
> testable (T-Pattern typing + E-Token evaluation + the token's interactions), and #23 consumes it
> as-is.

## 1. Summary

Give `PatternDataType` its introduction form. Today a pattern type's sole representable term is the
**token atom** — a bare PascalCase `Ident` gated on the registry (`patternTokenProd`, lc.md §2.3
"matched token"), which the lexer-side reading already treats as "the token for the pattern the
registry names". The introduction rule the spec commits to (lc.md §5.1 T-Pattern) is broader:
`T = μ α.
Σᵢ pᵢ`, `input matches pₖ ∈ {pᵢ}`, `tok : Token` ⟹ `Γ ⊢ tok : T` — the constructor is the
_pattern itself_, and the premise is **the input matches one of the type's declared patterns**.

The missing piece that makes T-Pattern a real rule (not just the token gate restated): a
concrete-syntax form that carries an explicit pattern and is accepted **iff the pattern is declared
on the named type**. This PBI adds:

- **`patternMatchProd`** in `grammar.ts`: the term `match("p") : T` — the call-shaped form `match(`,
  a quoted pattern source, `)`, gated on the type registry (`T` is a registered `PatternDataType`)
  and on the pattern check (the parsed pattern is declared on `T`). It reuses the
  `BUILTIN_CALL_FORMS` reservation `match` already has in `ops.ts` — the name is reserved from
  operations and excluded from the acyclicity scan precisely so this form can exist without
  shadowing (the #30 review fix anticipated it: "an op named `match` in Ω would make the `opProd`
  gate treat every `match(...)` as an op application, shadowing T-Pattern when #24 lands").
- **T-Pattern** in `typing_grammar.ts`: `match(pₖ)` types as the registered `PatternDataType` the
  declared pattern belongs to. Premise (declared, anchored, matching) enforced on the production
  path.
- **E-Pattern** in `eval_grammar.ts`: `match(pₖ)` evaluates to the matched token — a
  `TokenVal(T, text)`, the same axiom E-Token already produces. The token is an axiom of the
  operational semantics (lc.md §1: "no evaluation rule produces it; it is an axiom"); E-Pattern _is_
  the lexer-side introduction made explicit — the value IS the matched text, and the pattern check
  at eval time re-verifies what T-Pattern's premise declared.
- Tests for typing, evaluation, the pattern constraints, and the interaction surface (op-gate
  shadowing, reserved name, registry gate).

## 2. Review of the PBI against the current tree

### 2.1 Verified claims

| PBI claim                                                                | Current tree (verified)                                                                                                                                                                                                                                                                                                             |
| ------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| "`PatternMatch` and `PatternDataType` types exist in `types.ts`"         | `PatternDataType` exists (`types.ts` ~569 — `name` + frozen `PatternAST[]`, `dispatch`/`map` complete). A `PatternMatch` _type_ class does **not** exist on the tree — the issue body names a stale shape from the pre-#74 type model. What actually needs to land is the _term form_ (`patternMatchProd`), not another type class. |
| "no grammar production for `match(pₖ)` construction (T-Pattern)"         | Confirmed — no `patternMatchProd`/`T-Pattern`/`E-Pattern` anywhere in `src/`. The only pattern-construction path is `patternTokenProd` (the bare-`Ident` token atom) with its actions `matchedToken` (base, `typing_grammar.ts` ~1345 = the T-Token reading, `eval_grammar.ts` ~1231 = E-Token → `TokenVal`).                       |
| "`PatternDataType` is a type with no inhabitants" (in the term language) | Confirmed — a pattern type has no variant constructors and no term form that carries a chosen text. The law checker constructs `TokenVal`s directly (`law_checking.ts` `patternSamples`/`patternSpaceOf`) — that is library-internal value construction, not a term.                                                                |
| "`match` reserved from operations; excluded from the acyclicity scan"    | Confirmed — `BUILTIN_CALL_FORMS = ["match"]` (`ops.ts` ~114), `declare` check 1b rejects an op named `match`, `scanOpReferences` skips it. `test/ops.test.ts` pins both. The gate is ready; the language form it reserved the name for is exactly this PBI's.                                                                       |
| "Depends on: #19 (Nothing propagation) for soundness"                    | Complete — #19 landed; propagation through `variantCon`/`obs`/`fold`/`unfold`/`cofold`/`opApp` is in place with tests. T-Pattern itself has no sub-terms (its premise is on the pattern, not a Γ judgment), so it inherits nothing new from #19; the dependency is discharged.                                                      |
| Subtyping already reflexive-only for pattern types                       | `isSubtype`: `PatternDataType <: PatternDataType` iff same name (S-Refl path). Nothing to change — T-Pattern's conclusion types the term at the named type; subsumption at use sites needs no new rule.                                                                                                                             |

### 2.2 What the review adds

1. **The concrete syntax question decides the shape of everything else.** lc.md §2.2 writes the form
   as `match(pₖ)` — "pattern-matched construction (introduction via lexer match)" — and §1 says
   `match(pₖ)` "is a value introduced by the lexer (external to the calculus)". In a _real_ lexer
   integration, T-Pattern has no syntax at all: the lexer matches `[0-9]+` against input and hands
   the checker a `TokenVal`. LC is grammar-based, and the grammar-as-semantics architecture realizes
   the lexer's job as a **parse-time gate**: the branch is taken iff the text is in the pattern
   type's language. Two candidate spellings were weighed:
   - _Bare text lexing_ (`42` lexes as a `Nat` token): how elaboration.md §2.1 describes the
     **surface** language (`42 ↦ match("42") : Nat`). Wrong layer for LC — the LC concrete syntax is
     explicitly "NOT the Lapis surface syntax" (`grammar.ts` module doc), it has no literals, and
     bare-text lexing inside a _parse_ would make every identifier boundary a pattern-match point
     (an ambiguity surface the one-pass grammar cannot afford; derivation-path dedup already fights
     fan-out).
   - _Explicit form_ `match("<pattern-source>")` (a quoted pattern string inside the call-shaped
     form): matches the existing test fixtures' pattern-source convention
     (`createPatternType(name, patternSources)` takes _sources_, parsed through `parsePattern` —
     "the same surface form the `data` declaration carries"), and `test/ops.test.ts` already uses
     exactly this spelling (`new OpSig("usesMatch", [nat], nat, 'match("[0-9]+")')`) as a definition
     source that must declare cleanly. Decision: **explicit form** — `match("p")` parses a pattern
     source through `parsePattern`, gates on the registry + the declared-pattern check, and
     introduces the token. Elaboration (#25) will rewrite surface literals (`42`) to `match("42")` —
     the table in elaboration.md §2.1 is literally this shape, so the core form is the elaboration
     target, not the surface syntax.
2. **`match` stays a reserved name; the op gate is ordered first.** `opProd` (Ω-gated, tight paren)
   precedes `patternMatchProd` in `atomProd`; since Ω can never hold `match` (declare rejects it),
   the op branch declines and the pattern branch owns the form. This ordering is already forced by
   `atomProd`'s shape (`opProd` before variant/token branches) — no reorder needed. The pattern
   branch is placed AFTER `patternTokenProd` in the reader's file layout but the `or` order is
   explicit: `match(...)` (call-shaped, lowercase head) and `Ident` (PascalCase token) are lexically
   disjoint (camelCase-then-`(` vs PascalCase-then-anything), so neither shadows the other; ordering
   there is for documentation, not correctness.
3. **E-Pattern is E-Token's sibling, not a new value kind.** The value layer already has the right
   shape: `TokenVal(dataTypeName, text)` with type+text identity, `size() = text.length`, display
   `Type("text")`. The evaluator's `matchedToken` returns exactly this. E-Pattern reuses it: the
   production parses the pattern source, checks it against the type's declared patterns, and emits
   `matchedToken(T.name, text)`. **The distinction from the bare token atom is the premise**, not
   the value: T-Token types a name the registry holds (any text the name lexes to); T-Pattern
   additionally proves the explicit pattern string is _declared_ on the type (and anchored). Both
   are "the token is an axiom" — the operational semantics gains no new value form. The
   `renderSource` contract extends: a `TokenVal` whose text equals its type name renders as the bare
   name (the token-atom reading, unchanged); a token _introduced by_ `match("…")` renders as
   `match("<pattern>")` exactly when the token was introduced by the match form — the value carries
   its introduction ROUTE (`TokenVal.route`: "token" | "pattern"; E-Pattern stamps "pattern", every
   other construction defaults to "token"). The route, not the text, decides: a direct-constructed
   token with arbitrary text (the law checker's enumerated matched texts are TEXTS, not pattern
   sources) declines — `match("<text>")` would not re-evaluate, and the round-trip judgment
   ("renderSource = the LC source that re-evaluates to this value") never emits a partial render.
4. **Where does the "input" live?** T-Pattern's formal premise reads `input
   matches pₖ ∈ {pᵢ}`.
   In the grammar-based realization the "input" of the pseudo-lexer is the **pattern source written
   in the term** — i.e. the check is `parsePattern(source) is declared on T` (structural equality
   against the declared pattern ASTs, via `patternToString` normalization). A _match-simulation_
   reading (enumerate the type's language, check the text is a member) is the law checker's sweep
   (`patternSpaceOf`), not a parse-time judgment — the parse cannot know a runtime text that isn't
   written. What T-Pattern proves at parse time: the pattern is one of the type's declared
   constructor patterns, and it is anchored (surface-syntax.md §1.3). What it does NOT claim: any
   particular text. The text is chosen at eval time (E-Pattern) — in this grammar-based lexer the
   "matched text" of a parse-time introduction is the token atom's convention (text = the name) —
   see decision 5.
5. **The text of an E-Pattern token.** The bare token atom fixes `text = name` (the grammar-based
   lexer's identity: "the token's source IS its content" — `matchedToken(name, name)`). `match("p")`
   has an explicit pattern, not a text. The honest grammar-based reading: the token's text is the
   **canonical source of the matched pattern** (`patternToString(ast)`) — the same identity the
   token atom has (source = content), lifted one level: the _pattern_ is the source, and the token
   carries it. This keeps `TokenVal.text` the round-trippable content, keeps `size()` = the
   pattern's source length (the length-class reading the certificates use — `patternCounts` counts
   strings, and the pattern's own source is the canonical representative the display form shows),
   and makes `match("[0-9]+")` evaluate to a token whose display (`Nat("[0-9]+")`) names exactly
   which constructor was chosen. The alternative (a fresh, arbitrary text sample) would make
   E-Pattern non-deterministic — an evaluator parse yielding different tokens per parse is an
   ambiguity the determinism policy (E-Op's "exactly one result") forbids in internal windows;
   canonical text keeps one parse = one value.
6. **Anchoring check is cheap and owed.** surface-syntax.md §1.3: "patterns must start with a
   specific literal character or character class (not `.*` or `*` or `?`)". The pattern _parser_
   does not enforce anchoring (a leading `.` or `*`… parses; bare `*`/`?` don't — they need a
   preceding atom). The declaration machinery that would enforce it belongs to #25's surface `data`
   declarations; `createPatternType` fixtures bypass it. T-Pattern's gate checks anchoring on the
   explicit pattern by its FIRST ATOM — the first leaf, descending through the postfix wrappers —
   which must be a literal char, a class, or a type reference; a leading `.` (any) rejects. The
   first-leaf reading is what makes the canonical carriers anchorable: `Nat = [0-9]+` is a PLUS
   wrapping a class — its first leaf IS a class — so it anchors (the top-node reading would wrongly
   reject the bootstrapping example, design-decisions.md). A concatenation anchors at its first part
   (the first atom decides where the match must start), and `".*"` anchors at its leading quote
   literal while bare `.*` does not. A typeref `<T>` is trusted as anchored (it resolves to another
   declared pattern whose own anchoring the declaration machinery checked — #25's obligation; the
   gate cannot re-litigate it without unfolding the registry). A bare token atom skips this check
   (its premise is registry membership only) — unchanged.
7. **Duplicate-pattern equality is structural.** Declared-vs-explicit comparison runs over
   `patternToString` of each declared AST vs the explicit parse (the same normalization the
   round-trip test uses — `[0-9]` renders as `[0-9]`, so source-level and AST-level equality agree).
   A source string that parses to the same AST as a declared pattern is declared —
   `match("0123456789")` is NOT accepted for `[0-9]` (different AST: concat of ten chars vs a
   class), while `match("[0123456789]")` IS (same class AST, same canonical source).
8. **JSR slow-types / no-explicit-any discipline** carries over: the new production's parse-tree
   type is `S["atom"]` (shape-polymorphic, like the sibling branches); the checker's override
   produces `Type`, the evaluator's `Value`. No new exported types. The only new export surface is
   the semantic action name (`patternMatch`), private to the grammar hierarchy — nothing leaves
   `src/core`.

## 3. Design

### 3.1 Concrete syntax

```
match("⟨pattern-source⟩")          — introduced by patternMatchProd (this PBI)
Ident                              — matched token (existing patternTokenProd)
Ident(args)                        — variant construction (existing variantProd)
ident(args)                        — op application (existing opProd, Ω-gated)
```

The form is call-shaped like `opProd` but lexically disjoint from it: `match` is camelCase (an
`opIdent` head), but Ω can never hold it (`BUILTIN_CALL_FORMS` reservation), so the call shape is
unambiguous. The pattern source is a quoted string — LC concrete syntax has no other string
literals, and this is the ONE deliberate exception: the payload is a _pattern_ (the constructor),
not a term.

Whitespace discipline mirrors `opProd`'s tight paren: `match (` (space before paren) must NOT parse
as the pattern form — it is a variable `match` applied (or an error if unbound). The tight-paren
rule keeps the form positionally disjoint from variable application, exactly the op form's
disambiguation.

### 3.2 Grammar (`grammar.ts`)

- New abstract action:
  ```ts
  protected abstract matchedPattern(dataTypeName: string, patternSource: string): S["atom"]
  ```
  (sibling of `matchedToken`).
- New production, referenced from `atomProd` after `patternTokenProd`:
  ```ts
  protected patternMatchProd(ctx: unknown): Parser<S["atom"]> {
      return seq(
          this.kw("match"),
          char("("),                              // tight paren — no ws
          this.patternString,
          char(")"),
      ).bind(([, , source]) => {
          const resolved = this.registry.lookup("match")  // never a PatternDataType —
          void resolved                                    // `match` is not a type name
          const typeName = this.matchTypeName(source)      // registry-wide: the ONE
                                                           // registered type declaring it
          if (typeName === undefined) return empty<S["atom"]>()
          return epsilon(this.matchedPattern(typeName, source))
      })
  }
  ```
  **Registry-wide pattern lookup (decision point):** the form `match("[0-9]+")` names a pattern, not
  a type — which `PatternDataType` owns it? The registry must resolve pattern-source → type.
  Options: a. **First-declared-wins scan over registered pattern types** (simple, order- dependent,
  matches the lexer's "declaration order breaks ties" rule). b. Annotate the form with the type:
  `match("[0-9]+") : Nat` requires an expected type flowing down — bidirectional checking, which
  grammar-as-semantics explicitly rejects ("Why Lapis doesn't need it", §4). Decision: **(a)** —
  scan the registry's pattern types for one whose declared patterns contain the parsed source;
  longest/first match is unnecessary here because the comparison is _equality against a declared
  pattern_, not a lex of the input. Two registered types declaring the same pattern is an ambiguity
  the declaration machinery (surface `data`, #25) must reject; at the core layer, the scan takes the
  first and the ambiguity note documents it. `TypeRegistry` grows a
  `lookupPatternSource(source: string): PatternDataType | undefined` (a pattern index, sibling of
  `variantIndex`/`observerIndex`).

  The **pattern-string lexeme**: a double-quoted string of pattern source. The content grammar is
  _pattern-safe by construction_: metacharacters (`+ * ? [ ] \ . < >`) are allowed raw (they are the
  pattern language's syntax); the string terminates at the first unescaped `"`; a `"` inside the
  pattern must be escaped as `\"` (patterns containing quotes — e.g. `"<Char>*"` — write
  `match("\"<Char>*\"")` … note the pattern source itself uses `[^"]`-style classes for strings; the
  escape is the string-literal escape, not a pattern escape). The lexeme is a small dedicated
  parser, not `pred`-greedy: `"` → scan to unescaped `"` → unescape.
- `matchedToken` doc extended to name its sibling.

### 3.3 Type checker (`typing_grammar.ts`) — T-Pattern

```
T = μ α. Σᵢ pᵢ (registered PatternDataType)
pₖ ∈ declared(T) ∧ pₖ is anchored
────────────────────────────────  (T-Pattern)
Γ ⊢ match(pₖ) : T
```

- `matchedPattern(dataTypeName, patternSource): Type` — the action returns the registered
  `PatternDataType` (loud `assert` on the premise, mirroring `matchedToken`'s: a violation is a
  caller bug, never `Any`).
- `patternMatchProd` override: parse the string, parse the pattern (`parsePattern` — a malformed
  pattern is a _rejection_, not a throw: the parse error is caught and the branch returns
  `empty<Type>()`; a term that never parses is ill-typed, not a crash), check declared-on-T
  (registry lookup by pattern source), check anchored, then `epsilon(resolved)`. The `@ensures`
  contract on the action:
  ```ts
  @ensures(
      (_self, _args, _old, result) => isWellFormedType(result),
      { rule: "T-Pattern", role: "conclusion", formula: "result : T" },
  )
  ```
  No premises — the premise is enforced on the production path (the established #56 pattern:
  `@requires` is metadata, the override rejects).
- Nothing-propagation: N/A — the term has no sub-terms; T-Pattern is a value-rule (like T-Token,
  which has no contract either — the token atom carries none; see 3.5).

### 3.4 Evaluator (`eval_grammar.ts`) — E-Pattern

- `matchedPattern(dataTypeName, patternSource): Value` → `new TokenVal(dataTypeName, patternSource)`
  — the token's text is the pattern source (decision 5: source = content, lifted one level).
- `patternMatchProd` override: same gate shape as the checker (registry lookup by pattern source;
  the parse+check happens once here, and a violation is `empty<Value>()` — eval errors are
  forest-empty, never thrown). `@rule({ rule: "E-Pattern", production: "patternMatchProd" })`
  metadata for the rule model (the `E-Token` axiom currently has NO rule-model entry —
  `matchedToken` carries no `@requires`/`@ensures` in either grammar. E-Pattern gets a value-rule
  entry: no premises, conclusion `result : TokenVal`).
- `TokenVal` identity is `(dataTypeName, text)`; two `match("…")` of the same pattern on the same
  type are equal values — consistent with `TokenVal.equals`.

### 3.5 Rule model / metadata

- `T-Pattern` joins `LCTypeCheck.rules` (`matchedPattern` method, no premises, conclusion
  `result : T`) → `test/metadata.test.ts` inventory row.
- `E-Pattern` joins `LCEval.rules` (value-rule; production `patternMatchProd`) → metadata
  inventory + `metatheory.test.ts` value-rule list (`["E-Lam", "E-TAbs", "E-Unfold"]` → +
  `"E-Pattern"`). Step-rules unchanged (7). Progress/Preservation unaffected (a value-rule adds no
  step).
- The derivation fragment (`derivation.ts`) _rejects_ pattern-matched construction (`matchedToken`
  throws `DefinitionShapeError`); `matchedPattern` mirrors that (the derivation engine's
  fold-skeleton fragment admits no tokens — axioms over pattern carriers route through the pattern
  sweep instead). Same for `cost.ts`'s `matchedToken` — `matchedPattern` returns the same token-cost
  summary shape (`SizeExpr.variable("token(T)")`) — a pattern's source length is a static size
  variable exactly as the token atom's is.

### 3.6 What does NOT change

- `patternTokenProd` (the bare token atom) — stays exactly as is; T-Token is the registry-gated
  form, T-Pattern the pattern-carrying form. Both type as the pattern type; both evaluate to
  `TokenVal`s (the bare atom's text = the name; `match("…")`'s text = the pattern source).
- `PatternDataType` — no new fields (the declared patterns array is the premise's data; the
  comparison is a lookup, not a mutation).
- `ops.ts` — `BUILTIN_CALL_FORMS` already contains `match`; the reservation is now _load-bearing_
  rather than anticipatory (its doc comment says "when #24 lands" — the comment's future-tense note
  is updated to present tense).
- Subtyping — pattern types stay reflexive-only.
- `derivation.ts` — the fragment rejects both token forms; unchanged shape.

## 4. Tasks

Dependency-ordered; each lands with the full suite green.

1. **`src/core/grammar.ts`**: `TypeRegistry.lookupPatternSource(patternSource)` + the pattern index
   (built in `register`, reading each registered `PatternDataType`'s patterns through
   `patternToString`); the pattern-string lexeme; `patternMatchProd` (registry+declared+anchored
   gate, tight paren); abstract `matchedPattern` action; `atomProd` gains the branch (after
   `patternTokenProd`); header grammar-sketch update.
2. **`src/core/typing_grammar.ts`**: T-Pattern — `matchedPattern` override (returns the registered
   type; loud premise assert) + `@ensures` contract; `patternMatchProd` override
   (parse+declared+anchored premises on the production path, `empty<Type>()` on failure).
3. **`src/core/eval_grammar.ts`**: E-Pattern — `matchedPattern` → `TokenVal`; `patternMatchProd`
   override (same gate, `empty<Value>()` on failure);
   `@rule({ rule: "E-Pattern", production: "patternMatchProd" })` linkage.
4. **`src/core/derivation.ts`** + **`src/core/cost.ts`**: `matchedPattern` overrides (fragment
   rejection / token-cost summary) so the abstract action is implemented by every `AbstractLC`
   subclass.
5. **`src/core/values.ts`**: extend `TokenVal.renderSource` — a token whose text equals a declared
   pattern of its type renders as `match("<pattern>")` when the bare-name form would be wrong (text
   ≠ typeName) and the text IS the pattern source; falls back to the existing contract otherwise.
   (This is what makes law-counterexample rendering round-trip for `match`-introduced tokens.)
6. **`src/core/ops.ts`**: present-tense doc fix on `BUILTIN_CALL_FORMS` (the shadowing hazard is now
   realized as the form it reserved).
7. **`test/fixtures.ts`**: `createPatternFixtures()` — a registry with `NatPat` (`[0-9]+`),
   `EvenPat` (`"[0-9]*[02468]"` … anchored class+star — anchoredness of `+`-patterns comes from
   their inner atom), `StringPat` (`"<Char>*"` needs the escape form), plus `typeCheck/eval` helpers
   bound to it.
8. **`test/pattern_match.test.ts`** (new): the tests in §5.
9. **`test/metadata.test.ts`** + **`test/metatheory.test.ts`**: T-Pattern row in the typing
   inventory; E-Pattern in the value-rule list; Preservation step-rule list unchanged.
10. **`_docs/theory/lc.md`**: T-Pattern already specified (§5.1) — add the concrete-syntax note
    (`match("p")` in LC, quoted pattern source) to §2.2 and the E-Pattern axiom to §3.1's rule list
    (E-Token is currently implicit in §2.3's values; E-Pattern names the explicit form).
11. **`_docs/lc-core-implementation-plan.md`**: PBI #24 → Complete (with the match-vs-token split
    noted); the status table row flips.
12. `deno fmt` → `deno lint` → `deno check src/index.ts` → `deno test`.

## 5. Tests (`test/pattern_match.test.ts`)

- **T-Pattern well-typed:** `match("[0-9]+")` with `NatPat = [0-9]+` registered → forest =
  `{NatPat}`.
- **T-Pattern premise — undeclared pattern:** `match("[a-z]+")` (registered type declares only
  `[0-9]+`) → empty forest.
- **T-Pattern premise — unregistered type:** no pattern type declares the source → empty forest (the
  registry gate).
- **T-Pattern premise — anchoredness:** a leading `.` (any) rejects — the unanchored shape the spec
  names; the postfix wrappers are TRANSPARENT (the first-leaf reading): `match("[0-9]*")`,
  `match("[0-9]?")`, `match("[0-9]+")` all anchor at their class first-leaf (the canonical carrier
  `Nat = [0-9]+` is a plus of a class), while the bare token atom for an unanchored-but-declared
  type still works (T-Token's premise is registry membership only).
- **Malformed pattern source:** `match("[0-9")` (unterminated class) → empty forest (the parse error
  is caught, branch rejected — not a thrown error out of the checker).
- **Escaped quote in the source:** `match("\"<Char>*\"")` parses (the string-literal escape), the
  pattern source round-trips.
- **E-Pattern evaluates to TokenVal:** `match("[0-9]+")` → `TokenVal("NatPat",
  "[0-9]+")`;
  identity: two parses equal; `size()` = source length.
- **E-Pattern registry gate:** unknown pattern source → empty forest (no silent error value on the
  unregistered path — the branch rejects like the checker).
- **Value round-trip:** a match-introduced token's `renderSource` is the `match("…")` form;
  re-evaluating the rendered source yields an equal `TokenVal` (the round-trip judgment). A
  direct-constructed token with arbitrary text declines (route-qualified — the route, not the text,
  decides).
- **Token atom unchanged:** the bare `NatPat` atom still types/evaluates as before (regression guard
  for the sibling branch).
- **`match` is not an op:** with an op registry, `match("[0-9]+")` never consults Ω (an op named
  `match` cannot exist — pinned by ops tests; here: the term parses as the pattern form even when Ω
  is populated).
- **Shadowing precedence:** `match(` with a space (`match ("[0-9]+")`) does not parse as the pattern
  form (tight paren); a variable named `match` bound in Γ/ρ is a variable (the nameBound gate — the
  call shape's first lexeme is `match` but the pattern branch never consults variables… note:
  `match` as a _variable name_ is unreachable via `ident`? No — `match` is camelCase, a legal
  `ident`; `opIdent` accepts it but Ω rejects it. A λ-bound `match` variable is legal: the pattern
  branch is registry-gated on the pattern, not the name, so `match` the variable still applies by
  whitespace. Test: `\match:Nat. match` types (the variable reference) — the pattern form needs the
  tight paren).
- **Nothing-interaction:** N/A (no sub-terms) — but a `match("…")` in an operand position that fails
  its own premise still rejects the enclosing term (e.g. `let x:NatPat = match("[a-z]+") in x` →
  empty).
- **Op-definition integration:** an op whose definition uses `match("[0-9]+")` declares and
  evaluates through E-Op (the definition window opens; the pattern branch parses inside it) — the
  `usesMatch` fixture in `test/ops.test.ts` becomes actually type-checkable with `opWellFormedness`
  once the checker knows the form (its `permissive` stub currently bypasses the check; the real
  checker must accept the definition — cross-file integration test here, not a change to ops.test).
- **Derivation fragment rejection:** `matchedPattern` throws `DefinitionShapeError` naming the form
  (mirror of the `matchedToken` throw).
- **Metadata:** T-Pattern in `LCTypeCheck.rules`; E-Pattern classified value-rule; Preservation
  step-rule list unchanged (7).

## 6. Risks / open questions

- **Ambiguity fan-out:** `patternMatchProd` adds an atom branch. Its first lexeme (`match` + tight
  paren) is disjoint from every other atom branch (`(`-exprs, PascalCase variants, PascalCase
  tokens, bare idents, Ω-gated ops) — no new two-parse terms are introduced. The
  `derivation-path dedup` work should confirm: `match("[0-9]+")` must yield exactly one parse.
- **The generator** (`findCounterexamples`) generates terms by walking the grammar; the new branch
  is terminal (no recursive sub-terms), so it only widens the atom surface — generation succeeds,
  and the checker rejects `match("…")` unless a registered pattern type declares the source. With
  the counterexample fixtures' registries (no pattern types), the branch is inert — `empty` parse,
  same shape as the op gate with an empty Ω. Generation statistics may shift slightly (a branch
  tried and declined); the tests pin "0 counterexamples" not exact generation paths, so no
  expected-value churn.
- **`TypeRegistry` scan cost:** `lookupPatternSource` is O(#registered pattern types × #patterns)
  with memoizable structure — the registry is tiny (≤ tens); the law checker's existing per-type
  sweeps are far larger. A pattern index keyed by canonical source string keeps it O(1) after
  registration.
- **The token's text = pattern source** is a _representation choice_, not a semantic claim: no
  runtime "matching" is being simulated. #23's E-FoldMatch is where matched text becomes runtime
  data (the handler binds `match ↦ tok`); until then the token carries the canonical pattern source.
  If a later revision wants real matched text at introduction, the form extends to
  `match("p", "text")` — out of scope here (nothing consumes it yet; the law sweeps construct their
  own tokens directly).
- **`deno.json` lint rules:** no `any`, no explicit types needed beyond the hierarchy's existing
  shapes. The pattern-string parser is a private helper in `grammar.ts` — no new public surface.
