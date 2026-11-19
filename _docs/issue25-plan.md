# PBI #25 — Surface language elaboration pipeline (implementation plan)

> **Status:** Planning (2026-11-18). Implements
> [issue #25](https://github.com/lapis-lang/lapis-lang/issues/25) on branch `mlhaufe/issue25`.
>
> **This plan deviates from the issue text in one place, and the deviation is grounded in verified
> behaviour rather than preference.** See §2.

## 1. Summary

Build `src/surface/`: the surface language's structural grammar, a name-resolution step, and an
elaborator that produces LC core source. The core keeps its one-pass executable grammar; the surface
gets parse-to-structure plus two tree-consuming passes.

The boundary with #97 is recorded on
[#97's thread](https://github.com/lapis-lang/lapis-lang/issues/97#issuecomment-6993789699): **#25
owns the pipeline and its architecture; #97 owns the `data` declaration's full production set.** #25
validates the pipeline on the smallest slice that is _demonstrable_ — one `data` declaration with
`fold` — and #97 extends the same productions with patterns, captures, inheritance, `unfold` in
data, and contracts.

## 2. What verification changed about the design

Four facts were established by probing the real dependency and the real core, not by reading the
spec. Two of them contradict #25's literal plan.

### 2.1 Layout is expressible — the issue's silent risk is not a risk

The surface grammar is indentation-sensitive (§7, L1/L2), and `lang-forma`'s whitespace primitives
(`ws`, `ws1`, `wsChar`) are newline-inclusive, so they cannot express "4 spaces, no more". But the
README's documented answer for context-sensitive grammars applies directly: **`@rule` methods may
take parameters, memoised per `(instance, method, args)`**, and the worked `IndentLang` example is
exactly block-depth threading.

Verified by spike: a `@rule item(column: number)` production built from `literal(" ".repeat(n))`
parses

```
data Stack
    Empty
    Push
```

into `{ name: "Stack", items: ["Empty", "Push"] }` on the first attempt. So §7's "P4P-style
column-parameterised productions … `spaces(n)` matches exactly `n` spaces" is implementable as
written. **No pre-pass, no token rewriting, no line-splitting lexer.**

### 2.2 `parseToTree` produces a token tree, not a structural tree — this changes the pass design

`DerivationNode` carries `.label` (the `@rule` name), `.span`, `.children`, and `.value` (the
semantic action's result). Three probes established its shape:

| Grammar construct              | Resulting tree                              |
| ------------------------------ | ------------------------------------------- |
| `seq(char("a"), char("b"))`    | `[pair "ab"]` — one node, no children       |
| nested `@rule`s, no repetition | `[outer] → [inner]` — clean, structural     |
| `many()` over a `@rule`        | `[as "aaa"] → [as "aa"] → [as "a"] → [one]` |

So a repeated production yields **nested same-label nodes carrying partial values**, and a `seq` of
fixed arity yields **one node, no children** — the tree records _where a `@rule` matched_, not the
shape of the production. Verified consequence on a real surface production:

```
[dataDecl {name:"Stack"}]
  [dataDecl {name:"Stac"}]
    [dataDecl {name:"Sta"}]
      [dataDecl {name:"St"}]
        [dataDecl {name:"S"}]
          [ident "S"]
        [ident "St"]
      [ident "Sta"]
    [ident "Stac"]
  [ident "Stack"]
```

A `SemanticPass` dispatching on `dataDecl` therefore fires **five times for one declaration**, and a
naive bottom-up `defaultHandler` composes the partial results into nonsense.

`CostPass` already documents this hazard in the core — "the checker's left-recursive productions
duplicate the same term across multiple derivation depths, so a raw bottom-up walk would
multiply-count shared work" — and works around it by re-parsing with the engine. That workaround is
available here only because the core's semantics are re-derivable from source; the surface has no
such second engine.

**Conclusion:** `NameResolverPass`/`ElaboratorPass` should consume a **surface AST**, not the
`DerivationTree`. The two-phase shape #25 wants is preserved; only the retained artifact changes.

### 2.3 The core represents terms as source text, so "elaborate to core" means "emit LC source"

`OpSig.definition` is _"the operation's defining LC term, as concrete-syntax source text"_, and
`LCEval.evalOp` parses and applies it. `LCTypeCheck.parseWith` / `LCEval` consume strings. There is
no shared core AST to construct (`derivation.ts`'s `Term` is the derivation engine's own narrowed
form, not a general core AST).

So `ElaboratorPass` emits **LC concrete syntax**, which is then fed to the existing one-pass
grammar. This is a simplification, not a compromise: it is the same contract `Ω` already honours for
every operation definition. The LC grammar's `arrow` production accepts both `→` and `->`, and fold
handlers are comma-separated, so emitted text is straightforward.

### 2.4 `Family` already resolves at construction

`typing_grammar.ts` calls `field.type.resolveFamily(dataType)` in both `variantCon` and
`variantPremisesHold`, so `Cons(Nil(), Nil())` types against a `Family`-recursive carrier today.
Whatever #25 emits for recursive fields works without new subtyping work — the lattice gap is #102's
scope, and it does not block elaboration.

## 3. Design

### 3.1 Pipeline shape

```
surface source
   │
   ├─ SurfaceParse  (one-pass executable grammar → surface AST)
   │                 `parseToTree` also available; feeds #34's unparser and diagnostics
   │
   ├─ NameResolverPass   (AST → resolved AST + declaration table)
   │
   ├─ ElaboratorPass     (resolved AST → LC core source text)
   │
   └─ LCTypeCheck / LCEval  (existing one-pass grammar, unchanged)
```

The `SemanticPass` base class is still used — for the **AST**-consuming passes, via a small adapter
that walks the AST generically. That keeps #25's OOP-native pass composition (subclass one method,
inherit the rest) without inheriting the token tree's repetition problem. `parseToTree` stays wired
for diagnostics and #34.

### 3.2 Files

| File                             | Contents                                                                                                                                                                            |
| -------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `src/surface/ast.ts`             | Surface AST types: `SurfaceProgram`, `DataDecl`, `VariantDecl`, `FoldDecl`, `CaseArm`, `SpecRecord`, `Expr` (`Call`, `BinOp`, `Ref`, `VariantRef`, `Construct`, `Paren`, `Literal`) |
| `src/surface/layout.ts`          | `spaces(n)`, `newline`, `hws`, `indented(n, p)`, `blankOrComment` — the §7 primitives, in one place so every block production shares them                                           |
| `src/surface/grammar.ts`         | `AbstractSurface<S extends SurfaceShape>` + `SurfaceParse` (AST-producing). Declarations first (`data`), then expressions                                                           |
| `src/surface/resolve.ts`         | `NameResolverPass`, the declaration table (`TypeRegistry` population), reserved-word gates                                                                                          |
| `src/surface/elaborate.ts`       | `ElaboratorPass` — AST → LC source; the μ-type as a `DataType` via `DataType.define`, each `fold` as an `Ω` declaration                                                             |
| `src/surface/index.ts`           | Public surface exports                                                                                                                                                              |
| `src/index.ts`                   | Re-export `./surface/index.ts`                                                                                                                                                      |
| `test/surface_grammar.test.ts`   | Layout, declaration shapes, rejection cases                                                                                                                                         |
| `test/surface_elaborate.test.ts` | End-to-end: surface source → core types/values; AST equals `DataTypeBuilder` equivalent                                                                                             |

### 3.3 Scope of this PBI (deliberately narrow)

**In:** `data` with named variants; variant construction (`Variant x: 1 y: 2`, bare and qualified
per #84); an in-body `fold` with case arms; the expression primaries needed to write an arm body
(`literal`, `ident` refs, parens, binary/unary calls, keyword calls); elaboration to `DataType` +
`fold_T`; end-to-end type check and evaluation through the existing core.

**Out:** patterns and captures (#85, #100), comb inheritance (#86), `unfold` in data,
`behavior`/`protocol`/`relation`/`query`/`io`, contracts (#110), `merge`/`scan`, integer literals
and arithmetic (#119). Each is a #97 or later PBI's production set, plugged into this same pipeline.

**Why this slice:** the surface has no top-level expression form (overview §12.6 — a program is
`declaration*`), so a pipeline validated on expressions alone would have nothing to parse. One
declaration plus its fold is the smallest _complete program_.

### 3.4 Reserved-word and rejection policy

Rejections return `empty()` from the production (branch pruning), per the library's own contract
guidance: _"a failed `@requires` does not reject the branch … rejecting the branch is the production
path's job."_ `@requires` is used for the rule model and metatheory, not for rejection.

`Family`/`Self` reservation (#101) is enforced at the registry population point in `resolve.ts`, not
in the grammar — the declaration name is syntactically a `pascalIdent` either way; the rejection
belongs where the name is _declared_.

## 4. Tasks

1. `src/surface/layout.ts` — the §7 primitives, with a test proving 4-space exactness (a 3-space or
   5-space body must reject).
2. `src/surface/ast.ts` — the AST types, plus a `walk` helper for generic passes.
3. `src/surface/grammar.ts` — `dataDecl`/`dataBody`/`variantDecl` at column 4; `foldDecl` at column
   4 with `foldBody` at column 8 and indented arm bodies at column 12; arm heads with bindings;
   `specRecord`.
4. `src/surface/grammar.ts` — expression productions at the three precedence levels of §3.1,
   `primary` including parens and construction.
5. `src/surface/resolve.ts` — build the declaration table; resolve variant/field/operation
   references; apply the `Family`/`Self` gate.
6. `src/surface/elaborate.ts` — `data` → `DataType` via `DataType.define(...).addVariant(...)` with
   `Family` for recursive fields; `fold` → an `OpSig` whose `definition` is LC source.
7. `src/surface/index.ts` + `src/index.ts` exports.
8. Tests (§5).
9. `_docs/theory/language-design.md` — the hybrid-architecture note, and `surface-grammar.md` §9's
   status table updated from "Not implemented" to the implemented per-production list.

## 5. Tests

**`test/surface_grammar.test.ts`**

- Layout exactness: a body at 3 and at 5 spaces rejects; 4 parses.
- Blank lines and comments between body items are consumed.
- `data Stack` with `Empty` / `Push value: Any rest: Family` → the expected AST.
- `fold size <out: Int>` with two arms → the expected AST, including indented arm bodies.
- Arm bodies at column 12 parse; at column 8 they reject.
- A declaration at column 4 rejects (declarations are top-level only).

**`test/surface_elaborate.test.ts`**

- `data Stack …` elaborates to a `DataType` structurally equal to the `DataTypeBuilder`-built
  fixture (the #97 acceptance criterion, proven here first).
- The registry is populated; `LCTypeCheck` type-checks `Push(Zero(), Empty())` against it.
- A `fold size` declaration produces an `OpSig` whose `definition` type-checks against its declared
  `paramTypes → resultType` (the `Ω` seal already enforces this — reuse `checkDefinition`).
- Evaluation: the elaborated fold applied to a constructed stack yields the expected value.
- Round-trip: `parseToTree` → `unparse` reproduces the source (de-risks #34).

## 6. Risks

| Risk                                                                                                        | Mitigation                                                                                            |
| ----------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| `many()`/`sepBy` produce nested same-label nodes, so trees are unusable as ASTs                             | Consume the AST, not the tree (§2.2). Keep `parseToTree` for spans/diagnostics only                   |
| Left-recursive expressions (`binaryExpr ::= binaryExpr op unaryExpr`) may duplicate derivations in the tree | The AST path is unaffected (inline `.map`); verify only the `parseToTree` test                        |
| Ambiguity between construction (`Variant x: 1`) and keyword call (`key: expr`)                              | §3.3's greedy rule; test both spellings and a deliberately ambiguous case                             |
| Layout errors reported as bare "empty forest"                                                               | Defer message design to #99; this PBI only ensures rejection is _total_ and a fixture exists per case |
| `deno.json`'s `build` task references a non-existent `src/cli.ts`                                           | Out of scope (#98). Do not "fix" it here                                                              |

## 7. Open questions carried, not decided

1. **Where `in:` binds in a fold arm** — §5.1's decided rule binds beyond-field-count bindings at
   the arm (`Cons head rest v -> …`). Implemented as decided; if #97 finds the seed binding belongs
   elsewhere, it changes `resolve.ts` only.
2. **Contract clauses in a fold body** — #110 owns the bindable-name set. Clause _parsing_ can land
   here (they are `foldItem`s); clause _semantics_ waits for #110.
3. **`satisfiesClause`** — parsed and preserved in the AST, not elaborated (needs protocols).
