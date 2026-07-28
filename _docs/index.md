# Lapis Language Documentation

> Lapis is a bialgebraic programming language where fold and unfold are the only recursion forms.
> Data types are initial algebras (μF); behavior types are final coalgebras (νF). Programs are built
> by composing folds and unfolds — the Bird-Meertens Formalism made into a user-facing language.

The documentation is organized into two tracks, each written for a different audience. Pick the one
that matches what you're here for.

## For the Curious Programmer — `users/`

> You write programs. You've used `map` and `filter`, maybe `fold`, maybe touched Haskell or Scala.
> You don't need category theory to follow along — the formal vocabulary is earned, not assumed.

| Document                                     | What it covers                                                                                                                                                                                                                                                                  |
| -------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [`users/why-lapis.md`](./users/why-lapis.md) | The hook: one thing you can't do in any language you're using — declare a law, the compiler verifies it and applies Horner's rule for you. Short, concrete, honest about the tradeoff                                                                                           |
| [`users/rationale.md`](./users/rationale.md) | The narrative journey: Hutton's universality of fold → the dual unfold → totality by construction → law-driven optimization → calculating programs (Wadler, Bird) → a tutorial → data/codata duality → Datalog from relations → Prolog from queries → contracts without effects |

_(A Stack/Stream tutorial with worked calculational examples is planned — see the open items
below.)_

## For Language Designers & Contributors — `theory/`

> You know PLT. You want the formal calculus, the typing rules, the soundness argument, the
> implementation plan, and the honest comparison with prior work.

| Document                                                             | What it covers                                                                                                                                                                                                                                                                                                                                 |
| -------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [`theory/why-lapis.md`](./theory/why-lapis.md)                       | The defense: what problem Lapis solves, how the prototype proves it, why no existing language does, what's essential, and the honest risks                                                                                                                                                                                                     |
| [`theory/lapis-vs-coal.md`](./theory/lapis-vs-coal.md)               | Point-by-point comparison with Coal: shared ground (enforced fold/unfold, bialgebraic duality), the critical difference (law exploitation), and what each language can learn from the other                                                                                                                                                    |
| [`theory/language-design.md`](./theory/language-design.md)           | Master document: key design decisions (subtyping not generics, eager data/lazy codata, no general recursion, contracts not effects, static-where-possible, Boolean-as-data), document map, and the 7-stage iterative implementation plan                                                                                                       |
| [`theory/lc.md`](./theory/lc.md)                                     | LC in TAPL style: syntax, evaluation rules, typing rules, subtyping rules, soundness — the formal specification the implementation checks against                                                                                                                                                                                              |
| [`theory/semantics.md`](./theory/semantics.md)                       | Denotational semantics (fold = meaning), operational semantics (unfold = dynamics), bialgebraic laws (Turi-Plotkin), eager-data/lazy-codata strategy with Church–Rosser justification, attribute-grammar equations for static analysis, contract semantics, equality (structural for μ, bisimulation for ν)                                    |
| [`theory/elaboration.md`](./theory/elaboration.md)                   | Surface → core desugaring: every construct mapped to its core term. Expression elaboration, declaration elaboration (data/behavior/protocol/relation/query/io), recursion-scheme elaboration (para/histo/zygo/map/merge/scan), contract elaboration (demands/ensures/rescue/invariant → Result), properties elaboration, subtyping elaboration |
| [`theory/surface-syntax.md`](./theory/surface-syntax.md)             | Lexical structure, pattern-matched data types (no base types), uniform binary precedence (Smalltalk model), message-send model, composite expressions (blocks, arrays, records, specs), all six declaration forms with railroad diagrams, fold/unfold/map/merge syntax, and the P4P indentation strategy                                       |
| [`theory/grammar-as-semantics.md`](./theory/grammar-as-semantics.md) | Implementation architecture: grammar subclassing as compiler pipeline, `chain` for one-pass L-attributed type checking, grammar-native contracts (`@requires`/`@ensures`/`@invariant`/`@rescue`) as inference-rule encoding, why Lapis's structure eliminates polymorphic recursion and let-generalization, T-Fold as a contracted production  |
| [`theory/syntax-design.md`](./theory/syntax-design.md)               | The original surface syntax design document — the Self/Smalltalk-influenced syntax with all declaration forms, spec keys, contract clauses, and worked examples                                                                                                                                                                                |

## Cross-Cutting Notes (root)

These aren't audience-specific docs — they're working notes that inform both tracks.

| Document                                       | What it covers                                                                                              |
| ---------------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| [`design-decisions.md`](./design-decisions.md) | Pinned design decisions (core calculus, evaluation, effects, laws) — the authoritative cache of repo memory |
| [`user-preferences.md`](./user-preferences.md) | Working preferences for the design process                                                                  |

## Document Relationships

```
users/                          theory/
─────                           ─────
rationale.md  ─────refs──────►  why-lapis.md
                                lapis-vs-coal.md
                                language-design.md
                                     │
                        ┌────────────┼────────────┬────────────┐
                        ▼            ▼            ▼            ▼
                  lc.md  semantics  elaboration  surface-syntax
```

- **`users/rationale.md`** is the entry point for new readers. It references the formal docs in
  `theory/` for those who want to go deeper.
- **`theory/why-lapis.md`** is the defense — it answers "why does this deserve to exist?" and
  references the prototype and the comparison.
- **`theory/language-design.md`** is the master implementation document — it indexes the formal
  specs and defines the staging plan.
- **`theory/lc.md`**, **`theory/semantics.md`**, **`theory/elaboration.md`**, and
  **`theory/surface-syntax.md`** are the formal specifications that the implementation checks
  against.
- **`theory/syntax-design.md`** is the original design sketch, preserved for reference.

## Open Items

- **`users/` tutorial** — Stack and Stream worked examples in the calculational style (problem →
  law-cited derivation → result). The document that makes someone want to use Lapis.

## Status

All documents are **Draft v0.1** — living documents, refined through implementation. The semantic
prototype ([`lapis-js`](https://github.com/lapis-lang/lapis-js)) demonstrates every claim; the
native language (this repository) is early. See `theory/language-design.md` §5 for the
implementation plan and staging.
