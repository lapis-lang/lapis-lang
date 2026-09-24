# PBI #80 — Mixed data carriers + unified fold elimination: Implementation Plan

> **Status:** Planned. Plans [issue #80](https://github.com/lapis-lang/lapis-lang/issues/80) — a
> `data` declaration mixes named variants and pattern constructors; `fold` becomes ONE form with two
> handler schemas (T-FoldMatch/E-FoldMatch retire into T-Fold/E-Fold); counted repetition (`{n}`,
> `{n,}`, `{n,m}`) lands in `pattern_lang.ts`. Gate at plan time: branch `mlhaufe/issue80` (even
> with `master` at 10d512e — PR #81 merged) — `deno check src/index.ts` green, **529 passed / 0
> failed / 2 ignored**, lint/fmt clean. Dependencies verified CLOSED (merged): #23
> (T-FoldMatch/E-FoldMatch), #24 (T-Pattern/T-Token), #74 (`FamilyType`/`foldType`). #25 (surface
> elaboration) is OPEN and an explicit non-goal — the surface `data` grammar's mixed-declaration
> spelling (including the tentative `#[A-F0-9]{6}` lexing syntax) stays #25's scope.

## 1. Summary

Three moves, in dependency order:

1. **One carrier.** `DataType` gains a second member list — `patterns` — alongside `variants`; the
   builder gains `addPattern`; `allPatterns`/ `findPattern` mirror `allVariants`/`findVariant` (comb
   inheritance included). `PatternDataType` is **absorbed**: the class is deleted, the `patternData`
   arm retires from the `TypeCases` protocol, and the registry's pattern index retargets `DataType`.
   A carrier's _kind_ stops being a class distinction and becomes a member-shape fact (variants only
   / patterns only / mixed).
2. **One elimination.** The paired fold productions (`patternFoldProd` ordered before `foldProd` —
   lexically identical up to the annotation gate) merge into one production whose handler list
   interleaves both arm spellings: `Cᵢ(xⱼ) → tᵢ` (fields bound at their types; `Family` arms at σ)
   and `match("pᵢ") → tᵢ` (`match : Token` bound, single-step). Typing (kind-dispatched premises
   inside the existing `parseToFixpoint` walk), evaluation (scrutinee-kind dispatch), and cost
   (per-arm composition) merge; the `foldMatch` provenance kind retires. `DerivationReader` stays
   variant-carrier: a pattern arm in a derivable-regime fold rejects loudly.
3. **Counted repetition.** `pattern_lang.ts` parses `{n}`, `{n,}`, `{n,m}` (desugaring the
   star/plus/opt/identity shapes at parse time), with the counting and enumeration read off the set
   closure — the exact route this tree's counting already runs.

## 2. Review of the PBI against the current tree

### 2.1 Verified claims

| PBI claim                                                | Current tree (verified)                                                                                                                                                                                                                                                                                                                              |
| -------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Two disjoint μ-forms in the type grammar                 | `lc.md` §2.1 (lines 37–38): `μ α. Σᵢ Cᵢ(σᵢ)` vs `μ α. Σᵢ pᵢ`; the notation table (lines 142–143) carries both rows. §2.2's term grammar (line 41) spells only the variant-arm fold `fold [T] t {Cᵢ(xⱼ) → tᵢ}`.                                                                                                                                       |
| `DataType`/`PatternDataType` disjoint `Type` subclasses  | `types.ts` — `DataType` (line 392, persistent builder, `variants`, `parent`) and `PatternDataType` (line 578, direct immutable constructor, `patterns`). Both `equals` are name-only WITHIN the class (`463`, `589`) — two same-named carriers of different kinds are unequal today.                                                                 |
| Subtyping name-reflexive per kind                        | `subtyping.ts` — S-Data-Width/Depth for `DataType` pairs (line 165 → `isDataTypeSubtype` ~205); `PatternDataType` pairs: reflexive only (line 170).                                                                                                                                                                                                  |
| Two fold rule pairs                                      | `grammar.ts`: abstract actions `fold` (303) and `patternFold` (339); productions `patternFoldProd` (714) ordered BEFORE `foldProd` (814) — the ordering, not lexical shape, decides ownership (the header comment at 706–713 says exactly this). Checker overrides at `typing_grammar.ts` 626/806; evaluator overrides at `eval_grammar.ts` 389/560. |
| Value-kind-exclusive dispatch                            | `eval_grammar.ts` — `evalFold` rejects non-`VariantVal` scrutinees (492–493), `evalPatternFold` rejects non-`TokenVal` (678–679).                                                                                                                                                                                                                    |
| Measured surface: 54 instanceof sites / 11 files         | Verified ≈50 line-hits across 11 src files (grep counts lines; some lines carry two). Full table in §3. 27 `allVariants` sites (8 files), 14 `findVariant` sites (6 files).                                                                                                                                                                          |
| `TypeCases` carries separate `data`/`patternData` arms   | `types.ts` 1023 — yes; both arms already exist in every table (`cost.ts` 885, `subtyping.ts` 71, `type_algebra.ts` 358/495/660/823 are the dispatch-table consumers).                                                                                                                                                                                |
| Composition only at the FIELD level                      | `law_checking.ts` 173–176 dispatches a field's sample vocabulary per kind (`samplesFor` vs `patternSamples`); `type_algebra.ts` coefficients counts a pattern-typed field as the singleton-token fallback `x` (the comment at ~600). No constructor-level mixing exists.                                                                             |
| §1.3's disambiguation rule is untestable                 | `surface-syntax.md` line 77 — "Named constructors take precedence over patterns when both could match" — untestable while a declaration carries one member kind. The core-side analogue is the branch order `variantProd` → `patternTokenProd` → `patternMatchProd` (`grammar.ts` ~1031–1040).                                                       |
| No counted repetition                                    | `pattern_lang.ts` — the AST (118–130) has `char/any/class/concat/star/plus/opt/typeref`; `parseRepeat` (284) handles postfix `* + ?` only. Confirmed: no `{…}` construct anywhere (src or tests).                                                                                                                                                    |
| `DerivationReader` fold-skeleton is variant-carrier-only | `derivation.ts` — the `patternFold` action throws `DefinitionShapeError` (415–424); `readDefShape`'s axis gate rejects non-`DataType` carriers with the "pattern carriers have no variant cases to skeletonize" diagnostic (~701); `unfoldOne` requires a `con` scrutinee (~940).                                                                    |

### 2.2 What the review corrects or adds

1. **The PBI's counting premise is outdated for this tree.** It says the language-equation side
   "convolves counts" and bounded repetition "needs its own convolution". This tree's
   `patternCounts` is deliberately **set-based** (`pattern_lang.ts` 502, doc comment 480–501): the
   classic convolution recurrences count SPLITS and double-count closed sublanguages; the
   enumerated-string-set arithmetic is the only exact route and agrees with enumeration by
   construction. So `{n,m}` needs **no new convolution**: its counts are the per-length sizes of
   `⋃_{i∈[n..m]} Pⁱ` — a union of powers of the inner's enumerated set, the same closure machinery
   `starStringsOf` runs. The truncated-geometric closed form the PBI mentions is a property the set
   reading exhibits, not machinery to build.
2. **Absorption, not member-shape.** The PBI leaves `PatternDataType`'s fate open. The tree decides
   it: both classes' `equals` are name-only, so name reflexivity over a combined member set is
   already the equality story; the `patternData` arm's only content is "be a second kind"; and most
   of the 50 instanceof sites are kind GATES that die outright under absorption rather than
   converting to table walks. Keeping the class as a "member-shape carrier" would keep two
   vocabularies alive for zero semantic difference. Decision: **absorb** (D2).
3. **The PBI's "§7's open-question entry" is a section slip.** The open question is
   `surface-syntax.md` **§9 item 7** (line 727 — pattern constructors with captures), the same item
   the non-goals defer. The doc delta is a resolution note on that item (captures stay deferred; the
   mixed carrier's arm schemas are now the thing a capture would have to collapse), not a §7 edit.
4. **The strict common-σ premise must survive the merger as a per-arm-group premise.** T-FoldMatch's
   ONE-common-σ rule (`typing_grammar.ts` 740–760, pinned by `pattern_fold.test.ts` "multi-handler
   fold requires ONE common result type") is load-bearing. The unified rule keeps it for the
   pattern-arm group (D5) — without it, two pattern arms at divergent types would silently join,
   changing pinned behavior.
5. **The bare-atom asymmetry and `token(T)` vs `token(T:<p>)` naming are contract, not incident.**
   `eval_grammar.ts` 660–670 documents the dispatch asymmetry (the bare atom's text names the type,
   not a pattern source); `cost.ts` 1762–1790 pins the two introduction routes' distinct size
   variables. The merger carries both verbatim (D7).
6. **Mixed-carrier coefficients must COMPOSE, not branch.** Today `coefficients` branches per kind
   (`type_algebra.ts` 633: pattern arm → `typeUnionCountsWith`; otherwise the semiring fixpoint). A
   mixed carrier needs the sum of the two readings (D8) — sound because the two value universes are
   kind-disjoint (`VariantVal` vs `TokenVal`, `values.ts` 186/275), so no string is counted twice.
7. **Comb inheritance extends to patterns.** Variants inherit down the parent chain (`allVariants`,
   `types.ts` 480) and the registry indexes the walk (`grammar.ts` 204–208). Patterns must mirror:
   `allPatterns`/`findPattern`, indexed the same way, first-declaration tie-break unchanged.
8. **`lc.md` §2.2's term-grammar line needs the merger too** (the PBI names only §2.1/§5.2b/§3.1) —
   the unified fold's production line gains the pattern-arm spelling.

## 3. Current state (the audit baseline)

`instanceof DataType | instanceof PatternDataType` line-hits by file (grep; ≈50 across 11 files —
the PBI's 54 counts occurrences):

| File                | Hits | Stage-2 fate                                                                                                                                                        |
| ------------------- | ---- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `types.ts`          | 5    | 3 die (builder-slot checks are kind-blind already in spirit; 2 are `equals` — deleted with the class), 2 stay (construction internals)                              |
| `grammar.ts`        | 6    | registry indexing (204/222) merges into one member-shape walk; fold gates (729/833) merge in Stage 3; token gate + anchoring walk (1071/1220) widen to member-shape |
| `law_checking.ts`   | 12   | field-sample dispatch (173) becomes the composed sampler (Stage 5); regime routing (1468/1482/1846/1894) and width tests (1056–1082) become member-shape dispatch   |
| `law_testing.ts`    | 4    | stay — the ∂T machinery is variant-carrier by design                                                                                                                |
| `laws.ts`           | 4    | `screenableDomain` (460) and `paramTypeCompatible` (598–613) collapse under absorption                                                                              |
| `subtyping.ts`      | 2    | merge into one S-Data branch (Stage 5)                                                                                                                              |
| `typing_grammar.ts` | 4    | fold gates merge (Stage 3); intro asserts (1597/1631) widen to member-shape (Stage 2)                                                                               |
| `eval_grammar.ts`   | 2    | fold gates merge (Stage 3)                                                                                                                                          |
| `cost.ts`           | 4    | tree-assembly gates merge (Stage 3); `dataTypeNameOfType` (3128) simplifies                                                                                         |
| `derivation.ts`     | 3    | carrier gates become member-shape (variants required); diagnostics unchanged                                                                                        |
| `type_algebra.ts`   | 4    | coefficients/count/collect become member-shape dispatch (Stage 5)                                                                                                   |

## 4. Design decisions

### D1 — One carrier: `DataType` gains `patterns`

- `DataType` gains `readonly patterns: readonly PatternAST[]` (frozen in the constructor, exactly
  `PatternDataType`'s discipline — the constructor copies into a frozen array so the registry's
  reverse index cannot drift).
- `DataTypeBuilder` gains `addPattern(...patterns: PatternAST[])` returning a NEW builder
  (persistent, like `addVariant`); the builder carries both member lists; `build()`/`buildAll`
  freeze both.
- `allPatterns(): PatternAST[]` / `findPattern(canonicalSource: string)` walk the parent chain,
  mirroring `allVariants`/`findVariant`.
- Member-shape predicates (derived, not stored): `hasVariants` / `hasPatterns` — every former kind
  gate reads these.

### D2 — `PatternDataType` is absorbed

- The class is deleted; every `PatternDataType` reference migrates to `DataType` (≈128 line-hits
  across 13 src files + fixtures/tests).
- The `TypeCases` protocol's `patternData` arm is deleted; `RequiredCases` forces every case table
  to drop the arm (compile-forced sweep — the same mechanical migration #74/#77 ran).
- `TypeRegistry`: the `types` map widens its element type (`DataType | CodataType`), the pattern
  index retypes to `Map<string, DataType>`, and `register` indexes BOTH member kinds in one walk
  (variants by name via `allVariants`; patterns by canonical source via `allPatterns` —
  first-declaration tie-break unchanged, now uniform across both indexes).
- `PatternDataType`'s module doc's immutability contract moves onto `DataType`'s patterns slot.

### D3 — One fold production, discriminated handler records

- The base grammar's `patternFoldProd` (714) and `foldProd` (814) merge into ONE `foldProd`: the
  annotation gate accepts `DataType` (any member shape); the handler list is `sepBy(handler)` where
  handler parses EITHER `Cᵢ(xⱼ) → tᵢ` OR `match("pᵢ") → tᵢ` — the two head lexemes are disjoint
  (PascalCase-then-`(` vs camelCase-`match`-then-`(`), so the ordered choice is unambiguous. Branch
  order inside the handler alternation: variant head first, then the `match` head (mirroring
  `atomProd`'s ordering discipline).
- The handler record becomes a discriminated union:
  `{ kind: "variant"; variantName: string; bindings: string[]; body } |
   { kind: "pattern"; patternSource: string; body }`
  (canonical source for pattern arms, as today).
- The abstract actions `fold` (303) and `patternFold` (339) merge into one
  `fold(dataType, scrutinee, handlers, resultType)`; the `patternFoldBinding` hook survives for
  pattern arms (the `match : Token` binding).
- Exhaustiveness covers the COMBINED member set: every variant AND every declared pattern has a
  handler (keyed by name / canonical source respectively).

### D4 — Evaluation: one dispatch on scrutinee kind

- `evalFold` gains the token arm: a `TokenVal` scrutinee of the carrier takes #23's route verbatim —
  type-name check, handler lookup by `patternSource === scrutinee.text` (canonical dispatch),
  `match ↦ tok` binding, span replay; the bare-atom miss (text = the carrier's name) and the "no
  handler" failure shape are unchanged. A `VariantVal` scrutinee takes the existing route. Anything
  else: the merged diagnostic names BOTH kinds ("fold scrutinee is neither a VariantVal nor a
  TokenVal of the carrier") — an `EVAL_ERROR`, never a crash, like today.
- A token scrutinee contributes NO recursion (single step); a variant scrutinee recurses through
  `Family` fields exactly as today. The two routes never mix within one step.

### D5 — Typing: kind-dispatched premises inside one rule

- One `foldProd` override in the checker; the handler parser produces the discriminated records
  (variant arms' bodies parse under the field bindings with `Family` at the carrier placeholder —
  the existing `spanFoldHandler` context walk; pattern arms' bodies under `match : Token` — the
  existing `spanPatternFoldHandler` extension).
- The premises, in order: scrutinee : T; exhaustiveness over the combined member set; Nothing
  propagation; then the fixpoint:
  - variant arms participate in `parseToFixpoint` as today (Family bindings rebound to the current σ
    each iteration; bodies re-parsed);
  - pattern arms are CONSTANT across iterations (their context never mentions σ) — their body types
    enter the join every round at no cost;
  - the pattern-arm GROUP keeps the strict common-σ premise: all pattern arms' body types are
    `typeEquals` (the pinned T-FoldMatch behavior); the group's common type joins with the variant
    arms' fixpoint result;
  - a patterns-only carrier degenerates to today's T-FoldMatch exactly (no variant arms → the join
    is the pattern group's σ — byte-identical results); a variants-only carrier degenerates to
    today's T-Fold.
- `T-FoldMatch`'s rule/metadata entries retire into T-Fold's (`metadata.test.ts` row 22 and its
  `production` linkage note update).

### D6 — Evaluation metadata and rule model

- `E-FoldMatch`'s contracts (`@requires`/`@ensures` on the unreachable `patternFold` action,
  `eval_grammar.ts` 1394–1422) retire; the merged `fold` action's metadata gains the token-arm
  premise (`scrutinee : Cₖ(vⱼ) ∨ match(pₖ)`). `metatheory.test.ts`'s rule lists update (the
  step-rule set loses `E-FoldMatch`; the Preservation "8 step-rules" count drops to 7).

### D7 — Cost: one composition, per arm

- `CostEngine.fold` (1371) and `CostEngine.patternFold` (1590) merge: the handler list is walked per
  arm — variant arms run the existing recursion-substitution walk (`#foldRec` substitution, chain
  recurrence, invocation count over the scrutinee's node count); pattern arms run #23's single-step
  charge (dispatch by the `token(T:<p>)` size variable, exact-when-fired / conservative-otherwise,
  no `#foldRec`).
- The provenance kind `foldMatch` **retires** (the PBI's first option): one kind `fold` for the
  unified elimination; the scrutinee edge's `position` string distinguishes the arm shape ("fold
  scrutinee" / "pattern fold scrutinee" as today). The retired kind's consumers (`provenanceName`,
  report renderers, `pattern_fold.test.ts`'s edge assertion) update with it.
- `patternFoldSummaryFrom` folds into `foldSummaryFrom` (one composition, per-arm); the
  tree-assembly overrides (`CostPass.patternFoldProd` 2627 / `foldProd` 2705) merge into one reader
  of the discriminated `SpanFoldRecord` union (`cost.ts` 2820/2827 merge).
- The per-pattern token variable naming (`token(T:<p>)` vs the bare atom's `token(T)`) survives
  untouched — `patternFoldBinding`'s override and `tokenDenotation` are unchanged.

### D8 — Type algebra: mixed coefficients compose

- `coefficients` (553): a carrier with BOTH member kinds returns the per-length SUM of (the
  variant-system fixpoint) + (`typeUnionCountsWith(patterns)`). Soundness: variant inhabitants are
  `VariantVal`s (size = constructor-node count), pattern inhabitants are tokens (size = text length)
  — kind-disjoint universes, so the sequences add without double-counting.
- The field GF taxonomy gains nothing: a pattern-typed FIELD stays the singleton-token fallback `x`
  (unchanged — the declared-encoding machinery remains a follow-up); the carrier's OWN pattern
  members are the new contribution.
- `finiteInhabitants`/`count` (477): a carrier with pattern members is unbounded (infinite token
  language) unless every pattern member is a finite language AND the variant side is finite — the
  member-shape dispatch replaces today's `patternData → undefined` arm (which made any pattern
  presence unbounded; a finite-language pattern member — e.g. `ab` — is finitely inhabitable and the
  finite regime should route it; the `typeUnionCounts` sum bounded by the exhaustion ceiling
  decides).

### D9 — Subtyping and the law machinery

- `isSubtype`: the S-Data branch absorbs the pattern branch (one branch; `equals` is name-based on
  the unified class, so S-Refl already equates same-named carriers). `isDataTypeSubtype`
  generalizes: width requires every super variant present in sub (unchanged) AND every super pattern
  declared in sub by canonical source (a pattern member's width contribution is its declared
  constructor identity; depth does not apply — patterns bind no fields).
- `laws.ts`: `screenableDomain` and `paramTypeCompatible` simplify (the kind-split is gone;
  compatibility is name equality on the unified carrier).
- `law_checking.ts`: the sampler composes — a mixed carrier's sample vocabulary is the variant walk
  (`samplesFor`) UNION the token walk (`patternSamples`), deduped by value identity; the
  machineFinite regime routes a mixed position to the composed space; `patternSpaceOf` and `spaceOf`
  stay as the pure-kind helpers the composition calls.
- `law_testing.ts`'s ∂T machinery stays variant-carrier (a mixed carrier's derivative skeletonizes
  its variants; token holes are not punchable — unchanged).

### D10 — Counted repetition in `pattern_lang.ts`

- New AST node:
  `| { kind: "repeat"; readonly inner: PatternAST; readonly min: number; readonly max: number | undefined }`
  (`undefined` = unbounded).
- **Desugar at parse** (`parseRepeat`): `{0,}` → `star`, `{1,}` → `plus`, `{0,1}` → `opt`, `{1}` →
  the inner itself — the residual shapes (`{n}` and `{n,}` for n ≥ 2, `{n,m}` beyond the sugar)
  become `repeat` nodes. This keeps one new AST kind instead of four, and every downstream consumer
  (counts, enumeration, rendering, anchoring) handles exactly one new case.
- **Semantics — the set reading**: `patternCounts`' repeat arm unions `P^i` for `i ∈ [min..max]`
  over the inner's enumerated string set (the `starStringsOf` machinery iterated to the bound;
  budget `MAX_STAR_COUNT_BUDGET` applies — decline loudly, like star/plus). `enumerateNode` mirrors
  it. Exactness is by construction (the set reading — §2.2 item 1); the counts and the enumeration
  share the walk, so the certificate's two derivations agree for `{n,m}` exactly as they do for
  star.
- **Rendering** (`patternToString`): `inner{min}`, `inner{min,}`, `inner{min,max}` — canonical,
  round-trip-stable (desugared shapes render as their sugar, so existing canonical sources are
  byte-identical).
- **Anchoring** (`isResolvableAndAnchored`): transparent through `repeat`'s inner (the same rule
  star/plus/opt run — the first atom decides), including `min = 0` (a zero-minimum pattern's first
  atom is still its anchor — the grammar never produces an empty `repeat` because the inner must
  parse).
- Parse errors: a malformed `{…}` group (non-numeric, inverted `n > m`, unterminated) rejects with
  `PatternParseError` naming the construct; `{}` is never a literal brace — braces are new
  metacharacters (a literal brace escapes: `\{`). The `surface-syntax.md` metacharacter list gains
  `{ }`.

### D11 — Docs

- `lc.md`: §2.1's two μ-forms unify into one row with a mixed member list (`mᵢ ::= Cᵢ(σᵢ) | pᵢ`,
  homogeneous lists = the pure carriers); §2.2's fold production line gains the pattern-arm
  spelling; §3.1's E-FoldMatch folds into E-Fold (kind-dispatched); §5.2b folds into §5.2 (T-Fold
  with two handler schemas; the strict common-σ premise stated per pattern-arm group); the §2.5
  notation rows merge; §6's progress/preservation sketches update to the single rule.
- `surface-syntax.md`: §1.3's pattern table gains the `{n}`/`{n,}`/`{n,m}` rows and the
  metacharacter note; the elimination paragraph (§1.3's fold example) rewrites to the unified form;
  §9 item 7 gets its resolution note (captures stay deferred; the mixed fold's two schemas are the
  boundary a capture would collapse — the item cites the plan, docs may carry PBI references).
- No issue-tracker IDs in code comments (repo rule); docs are fine.

## 5. Implementation plan (stages, file-level deltas)

Order keeps `deno check src/index.ts` green through Stage 1; Stage 2 is the one big-bang sweep
(absorption cannot land incrementally); Stages 3+ are independently green again. (Repo memory: check
catches cross-module errors first via `src/index.ts`; `deno fmt` re-sorts import blocks — re-read
after fmt before further import edits.)

### Stage 1 — additive: `DataType` gains patterns (green throughout)

- `types.ts`: D1's field, builder method, `allPatterns`/`findPattern`, member-shape predicates;
  module doc's patterns-slot contract.
- `grammar.ts`: `TypeRegistry.register` indexes a `DataType`'s patterns alongside its variants
  (additive — `PatternDataType` indexing stays until Stage 2; the DataType walk reads
  `allPatterns()` so a comb child whose parent declared the pattern indexes under its registrar,
  mirroring the variant walk's `allVariants()`); `lookupPatternSource` return type widens to
  `DataType | PatternDataType | undefined` during the coexistence window (both shapes occupy the
  index until Stage 2 absorbs the union).
- `grammar.ts` intro gates widen: `patternTokenProd` (1071) and the anchoring walk's typeref arm
  (1220) accept a carrier with patterns (`resolved.patterns.length > 0`); `patternTypeName`'s
  registry read follows.
- `typing_grammar.ts`/`eval_grammar.ts`/`cost.ts`: the `matchedToken`/`matchedPattern` premise
  asserts widen from `instanceof PatternDataType` to the member-shape check (a carrier with pattern
  members can introduce tokens).
- New fixture: `createMixedType(name, variants, patternSources)` in `test/fixtures.ts`;
  `createPatternType` keeps its signature (Stage 2 re-points it at the builder).

### Stage 2 — absorption sweep (one phase: src + tests together)

- `types.ts`: delete `PatternDataType`; the `TypeCases` interface drops `patternData`; every case
  table in src drops the arm (compile-forced): `cost.ts` 885, `subtyping.ts` 71, `type_algebra.ts`
  358/495/660/823.
- `grammar.ts`: registry element types; `register`'s single member-shape walk; the
  fold/token/pattern gates re-point at `DataType` + member shape.
- `subtyping.ts`: the `PatternDataType` branch (170) deletes; S-Data covers all carriers.
- `type_algebra.ts`: the `coefficients` pattern arm (633) becomes the member-shape dispatch (Stage 5
  completes the composition; the interim arm keeps `typeUnionCountsWith` for patterns-only carriers
  via `type.patterns.length > 0 && type.variants.length === 0` routing).
- `law_checking.ts`/`laws.ts`/`law_testing.ts`/`derivation.ts`/`cost.ts`: mechanical reference
  migration (the §3 table's Stage-2 column).
- `test/fixtures.ts`: `createPatternType` → `DataType.define(name).addPattern(...).build()`.
- Grep-zero checklist: `PatternDataType`, `patternData:` outside the protocol history,
  `createPatternType`'s old body.

### Stage 3 — the rule merger

- `grammar.ts`: one `foldProd` + one `foldHandlers`/`foldHandler` producing the discriminated
  records; the abstract action pair merges; the branch-ordering comment (706–713) rewrites to the
  handler-alternation story.
- `typing_grammar.ts`: one `foldProd` + one `spanFoldHandler` (D5); the fixpoint gains the
  pattern-arm constants; `typePatternFold`'s logic folds into `evalFoldFixpoint`; the `T-FoldMatch`
  contract metadata merges into T-Fold's.
- `eval_grammar.ts`: one `foldProd` + `spanFoldHandler`; `evalPatternFold` folds into `evalFold` as
  the token arm (D4).
- `cost.ts`: `CostEngine.fold` absorbs `patternFold`; `foldSummaryFrom` absorbs
  `patternFoldSummaryFrom`; the `CostPass` assemblies merge; the `SpanFoldRecord` union replaces the
  two records; `foldMatch` retires from `Provenance` and its consumers.
- `derivation.ts`: the `patternFold` action's rejection moves INTO the merged `fold` action (a
  pattern arm in the handler list throws the same diagnostic); `readDefShape`'s carrier gate becomes
  member-shape (variants required); `readRejectedConstruct`'s `patternFold` seam keeps its
  diagnostic (the exposed method re-points at the merged action's arm check).
- `test/metadata.test.ts`: the `T-FoldMatch`/`E-FoldMatch` rows retire; T-Fold's premise list gains
  the token arm.
- `test/metatheory.test.ts`: the rule-name lists, the value/step classification, and the
  Preservation "8 step-rules" count update.
- `test/pattern_fold.test.ts`: rewritten as the mixed-fold suite — the
  premises/dispatch/conservative-charge tests migrate onto mixed and patterns-only carriers; the
  two-forms-side-by-side test (line ~440) becomes the one-form test; the `foldMatch`-edge assertion
  updates to `fold`.

### Stage 4 — counted repetition

- `pattern_lang.ts`: the `repeat` node; `parseRepeat`'s `{…}` postfix + desugar; `patternToString`'s
  rendering; `patternCounts`/`enumerateNode`'s set-closure arms; `isResolvableAndAnchored`'s
  transparent arm.
- Tests (`pattern_lang.test.ts`): parse/round-trip per shape; count/enumerate agreement for `{n}`,
  `{n,}`, `{n,m}` (including a nested `{2,3}` over a class and a `{2,}` over a typeref); the desugar
  equivalences (`a{0,}` ≡ `a*` canonically); budget-decline loudness for a large `{n,}` over `.`;
  anchoring through `{0,}`.
- `#[A-F0-9]{6}`-shaped acceptance: a `Color`-shaped carrier's pattern `#[A-F0-9]{6}` counts exactly
  one length-7 string class — the coefficients/ enumeration agreement test drives the spelling.
  (Until Stage 4 lands, the mixed-carrier tests spell the same LANGUAGE as an explicit six-fold
  class concat — `#[A-F0-9][A-F0-9]…` — because `{6}` is not in the supported fragment: `{` is a
  literal there. The gate tests pin parse/dispatch routes, which are spelling-agnostic; the
  counted-repetition semantics is Stage 4's own acceptance.)

### Stage 5 — subtyping + law machinery for mixed carriers

- `subtyping.ts`: `isDataTypeSubtype`'s width gains the pattern-member clause; `subtyping.test.ts`
  gains the mixed width/depth cases (a mixed sub over a variants-only super with the super's
  patterns present; a patterns-only super rejected when a pattern is missing).
- `type_algebra.ts`: the mixed-coefficient composition (D8) + `finiteInhabitants`' member-shape
  dispatch; `type_algebra{,_class}.test.ts` gain the mixed cases (the sum reading; a finite-language
  pattern member keeping the carrier finite).
- `law_checking.ts`: the composed sampler (D9); the machineFinite routing dispatches on member
  shape; `law_checking.test.ts`/`laws.test.ts` gain a mixed-carrier law screen (identity over a
  mixed carrier with both arm kinds in the sample vocabulary).

### Stage 6 — docs (D11)

### Stage 7 — gate

`deno check src/index.ts` && `deno test` && `deno lint` && `deno fmt`; the §3 audit re-run: zero
`instanceof PatternDataType` anywhere, and every surviving kind-deciding read routes through the
member-shape predicates or a case table.

## 6. Acceptance mapping (PBI checkboxes → plan)

| PBI acceptance item                                                                                 | Where                                                                                                              |
| --------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| Mixed `data` declaration end-to-end (token + `match("…")` routes)                                   | Stage 1 (gates) + Stage 3 (fold) + new mixed tests                                                                 |
| ONE fold production, both arm kinds, per-arm premises/eval/cost                                     | Stage 3 (D3–D7)                                                                                                    |
| T-FoldMatch/E-FoldMatch retire (rules + metadata lists)                                             | Stage 3 + `metadata.test.ts`/`metatheory.test.ts` deltas                                                           |
| `isSubtype` handles the mixed carrier                                                               | Stage 5 (D9)                                                                                                       |
| Counted repetition with exact counts + certificate agreement                                        | Stage 4 (D10 — set closure; §2.2 item 1 corrects the PBI's convolution premise)                                    |
| `TypeCases`-driven dispatch replaces the paired walks                                               | Stage 2 (absorption collapses the split) + Stage 7's audit re-run                                                  |
| Docs: `lc.md` grammar/rules; §1.3 real (ordering test); open-question entry                         | Stage 6 (D11) + a grammar branch-order test pinning variant-head precedence over the pattern head in `foldHandler` |
| Gates green; pinned behaviors unchanged (#24 identity, bare-atom asymmetry, #23 canonical dispatch) | Stage 7 + the pin-survival assertions in `pattern_fold.test.ts`'s migration                                        |

## 7. Risks

- **The absorption sweep is broad** (≈128 references, 13 src files + tests). Mitigation:
  compile-forced (the deleted class and the retired case arm turn every site into an error); the
  sweep is one phase with a grep-zero checklist, the same discipline #77 ran.
- **The fixpoint + pattern-arm interaction.** Pattern arms are σ-independent; a naive integration
  re-parses them per iteration (wasted work) or lets them poison convergence. The plan hoists their
  (constant) body types into the join without re-binding — verified by the degenerate-case tests
  (patterns-only and variants-only carriers reproduce today's outputs byte-for-byte).
- **`{n,m}` counting budget.** A large `{n,}` over a wide class explodes the set closure;
  `MAX_STAR_COUNT_BUDGET` declines loudly (the honest bound, the same discipline star runs). The
  certificate never guesses.
- **The `foldMatch` provenance retirement ripples** into report renderers and cost tests.
  Mitigation: grep-driven sweep of `foldMatch` after Stage 3; `provenanceName`'s update is part of
  the phase.
- **Mixed coefficients sum-soundness** rests on the value-kind disjointness — pinned by a direct
  test (a mixed carrier whose variant count and token count are independently verified against
  enumeration, then the sum).
- **Brace metacharacters** change the pattern lexer's literal set: a previously-legal literal `{`
  pattern (e.g. a carrier declaring `{`) now needs `\{`. The plan treats this as a deliberate,
  documented widening (surface-syntax.md's metacharacter list), with a round-trip test for the
  escaped form.
- **`deno fmt` import re-sorting** between stages — re-read before further import edits (repo
  memory).
