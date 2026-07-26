# Session Handoff — 2026-07-25

> This document captures the state of the Lapis language project at the end of
> this session, so the next session (in the devcontainer) can pick up where we
> left off. Delete or archive once consumed.

## What we accomplished this session

### 1. Design documents created (all in `_docs/`)

| Document | Purpose | Status |
|---|---|---|
| `index.md` | Index/routing for all docs, organized by audience | Done |
| `rationale.md` | Narrative for prospective users (Hutton → totality → laws → calculating vs scheming (Wadler) → Datalog/Prolog → contracts) | Done |
| `why-lapis.md` | Defense via Atanassow's 5 questions | Done |
| `lapis-vs-coal.md` | Comparison with Coal (closest existing language) | Done |
| `language-design.md` | Master doc: decisions, document map, 7-stage implementation plan | Done |
| `core-calculus.md` | Formal calculus: F<: + μ/ν + fold/unfold, typing rules, subtyping, soundness sketch | Done |
| `semantics.md` | Denotational (fold) / operational (unfold) / bialgebraic (Turi-Plotkin) semantics, evaluation strategy, contracts, equality | Done |
| `elaboration.md` | Surface → core desugaring for all constructs | Done |
| `surface-syntax.md` | Lexical structure, precedence ladder, railroad diagrams, declaration forms, indentation strategy | Done |
| `syntax-design.md` | Original surface syntax design (pre-existing, preserved) | Pre-existing |

### 2. Source code created (all in `src/`)

| File | Purpose | Status |
|---|---|---|
| `ast.ts` | Class-based AST hierarchy (pre-existing, renamed from .mts) | Done |
| `grammar.ts` | Base grammar: characters → AST (pre-existing, renamed, imports updated) | Done |
| `types.ts` | Semantic types: LapisType hierarchy, subtyping, TypeEnv, NameEnv | Done (skeleton) |
| `nameresolver.ts` | Name resolution pass: two-pass (collect declarations, then resolve references) | Done (skeleton) |
| `typechecker.ts` | Type checking pass: implements T-Fold, T-Unfold, T-Cofold, T-Obs, exhaustiveness checking | Done (skeleton) |
| `index.ts` | Public exports | Done |

### 3. Deno migration completed

- All `.mts` files renamed to `.ts`
- All imports updated: `.mjs` → `.ts` (relative), `@lapis-lang/derivative-parser` → `jsr:@lapis-lang/zipper-grammar`
- `package.json` and `tsconfig.json` removed
- `deno.json` created (tasks, import map, compiler options, fmt/lint config)
- `.devcontainer/devcontainer.json` created (Ubuntu 24.04 + Deno feature + VS Code Deno extension)
- `deno check src/index.ts` passes clean
- Parser library renamed and published to JSR as `@lapis-lang/zipper-grammar@2.1.0` (user did this separately)

### 4. Key design decisions pinned (in repo memory + docs)

See `_docs/design-decisions.md` for the full list (copied from repo memory so it survives container rebuilds). Highlights:
- Core calculus: F<: + μ/ν + fold/unfold (NOT Fω — subtyping subsumes generics)
- Eager data, lazy codata (invisible to user, fixed by declaration kind)
- No general recursion (totality by construction)
- Contracts not effects (core is effect-free, rescue → Result)
- Static where possible, dynamic when needed (type soundness vs law soundness as separate theorems)
- Boolean as data, no primitive `if`
- Grammar-as-semantics: use zipper-grammar's subclassing + `super` + `chain` for semantic passes

## Where we left off / what's next

### Immediate next steps

1. **`_docs/grammar-as-semantics.md`** — planned but not yet written. Should document:
   - The `super`-based multi-pass model (base grammar → name resolver → type checker → law checker → evaluator)
   - How `chain` (monadic bind) enables one-pass judgment-as-production (L-attributed)
   - How Lapis's enforced structure means the hard type-theory cases (polymorphic recursion, let-generalization) don't arise
   - The zipper-grammar v2.1.0 grammar-native contracts (`@requires`, `@ensures`, `@invariant`, `@rescue`) as inference-rule encoding
   - Concrete examples: T-Fold as a `@rule` production with `@requires`/`@ensures`

2. **Refactor semantic passes to use zipper-grammar's new features** — the current `nameresolver.ts` and `typechecker.ts` are tree-walking implementations. They should be refactored to use the grammar-subclass pattern with `chain` for one-pass type checking where possible. The zipper-grammar v2.1.0 now supports this directly (see its `stlc.ts` example for Simply Typed Lambda Calculus with one-pass type checking).

3. **Stage 1 implementation** (from `language-design.md` §5):
   - Core calculus: μ-types, ν-types, fold, unfold, observation, lambda, application
   - Type checker: typing rules for the above, subtyping (reflexive, transitive, top, bottom, function, μ/ν width+depth)
   - Tree-walking evaluator: eager data, lazy codata
   - Elaboration: surface `data`/`fold` → core μ/fold; surface `behavior`/`unfold` → core ν/unfold
   - Test: Stack (data + fold), Stream (behavior + unfold + observation)

### Open questions still unresolved

1. **Fold dispatch model** — dynamic (method on prototype, comb chain) vs static (match on tag)? Prototype uses dynamic; core calculus written static. Reconcile in elaboration.
2. **Equality** — structural for μ, bisimulation for ν. Formalize `=` and `≈`.
3. **Strictness** — `Lazy τ` explicit wrapper recommended but not decided.
4. **Multi-sorted** — simultaneous μ-bindings for mutual recursion.
5. **Intersection types** — first-class vs elaboration-time constraints? "Static where possible" suggests constraints by default, first-class in live-image mode.
6. **Record elaboration** — records not in the core calculus yet. Need to decide: add to core or elaborate to ad-hoc data types.
7. **Operator resolution** — binary operators elaborate to folds, but which fold? Need a standard library of operator-to-fold mappings.

### Resources the user was gathering

The user mentioned gathering "other resources for you to review for an upcoming addition we'll pursue." This was mentioned before the Deno migration discussion. The user should be asked what those resources are when the session resumes.

## File structure after migration

```
lapis-lang/
  deno.json                    — Deno config (tasks, imports, fmt, lint)
  .devcontainer/
    devcontainer.json          — Ubuntu 24.04 + Deno feature + VS Code extension
  _docs/
    index.md                   — doc index
    rationale.md               — narrative for users
    why-lapis.md               — defense (Atanassow)
    lapis-vs-coal.md           — comparison with Coal
    language-design.md         — master doc + implementation plan
    core-calculus.md           — formal calculus
    semantics.md               — denotational/operational/bialgebraic
    elaboration.md             — surface → core desugaring
    surface-syntax.md          — syntax spec with railroad diagrams
    syntax-design.md           — original design (pre-existing)
  src/
    ast.ts                     — AST node classes
    grammar.ts                 — base grammar (characters → AST)
    types.ts                   — semantic types (LapisType hierarchy, subtyping)
    nameresolver.ts            — name resolution pass
    typechecker.ts             — type checking pass
    index.ts                   — public exports
```

## Key external references

- Parser library: `jsr:@lapis-lang/zipper-grammar@2.1.0` (renamed from derivative-parser, published to JSR)
  - Now has `chain` (monadic bind) for L-attributed one-pass parsing
  - Now has grammar-native contracts: `@requires`, `@ensures`, `@invariant`, `@rescue`
  - See `examples/stlc.ts` for the headline example (STLC with 4 interpretations over one grammar)
- Prototype: `lapis-js` on GitHub (the semantic prototype, npm package)
- Coal language: `coal-lang.org` (closest existing language, comparison in lapis-vs-coal.md)