# Lapis

> A programming language where **fold and unfold are the only recursion** — and where algebraic
> laws, once declared and verified, are structure the compiler exploits.

This is the outline for the landing page, in the style of the
[Flix homepage](https://flix.dev): a hero with one self-contained code panel, then a feature tour —
alternating prose/code columns, one claim per section, each panel showing its result as a trailing
`"=> ..."` comment. Escalate from familiar to distinctive; the tour ends on laws, the hero feature.

Status: **outline**. Sections marked ✱ have example programs already specified in the internal
drafts and can be written immediately; the rest need example programs authored first.

---

## Hero

- Headline: Lapis — a total, algebraic programming language.
- Sub: fold and unfold are the only recursion forms. Programs terminate by construction, and every
  operation has a known algebraic shape — which is what lets the compiler verify and exploit the
  laws you declare.
- Code panel: the NumList `sum` / `scaleEach` / `merge scaledSum` program from
  `users/why-lapis.md` — three constructs, two passes fused into one, result as a comment.

## Feature tour (in presentation order)

1. **Algebraic Data Types and Pattern Matching** ✱
   `data` declarations with variants and case tables; `->` arms, uniform access.
   Example: `Color` with `fold toHex` — `Color Red toHex  "=> '#FF0000'"`.

2. **Pattern-Matched Data Types — No Base Types** ✱
   Even `Nat` is `data` with lexical patterns (`Nat = [0-9]+`); the lexer is driven by `data`
   declarations. Show the built-ins table and one user-defined pattern type.

3. **Structural Dispatch Replaces Conditionals** ✱
   `fold` over variants is the only branching: exhaustive case tables, compiler-checked
   coverage. `Empty -> 0` / `Push value rest -> 1 + rest`.

4. **Streams and Codata** ✱
   `behavior` declarations, observers, `Self` continuations, memoized observations.
   Example: `nats = Stream From: 0`, `nats take: 5  "=> [0, 1, 2, 3, 4]"`.

5. **Recursion Schemes as Language Constructs** ✱
   `<para>`, `<histo>`, `<aux: #f>` are declared, not library-encoded: `old`, `prev`, `aux`.
   Example: `fold fib <histo, out: Number>`.

6. **Map and Merge — Fusion by Construction** ✱
   `map` transforms fields; `merge` composes two folds into one traversal (deforestation).
   Example: `merge doubleSum <#double, #sum>`.

7. **Protocols and Subtyping** ✱
   `protocol` with default bodies, `satisfies:`, structural conformance; ADT extension via
   `data ExtendedColor <: Color`.

8. **Relations, Queries, and IO** ✱
   `relation` (spans, transitive closure), `query` (cospan search, `explore:`), `io`
   (Mealy machines). One short panel each; link out for detail.

9. **Design by Contract** ✱
   `demands:` / `ensures:` / `rescue:` clauses on folds. *(Reconcile clause placement in the
   spec first — see `docs/README.md`.)*

10. **Declared Laws, Verified and Exploited** — the climax
    `properties: (commutative, associative, identity: ..., distributive: #sum)`. Declare → the
    compiler screens it against samples → the optimizer may fuse, short-circuit, cancel.
    Reprise the hero's Horner example with the derivation made explicit.

## Nav (top bar, mirroring the site structure)

`Home` · `Why Lapis` · `Tutorial` · `Syntax` · `Semantics` — mapping to the pages listed in
[`README.md`](./README.md). `Get Started` is the Tutorial once it exists.

## Layout notes (Flix-style)

- Alternating two-column rows: prose left / code right, then flipped; full-bleed section
  separators between major groups.
- Dark code panels; comments and `"=> ..."` results visually distinct from code.
- Code panels are static (no playground) for v0; each panel's program must be one that the
  current grammar actually accepts — copy examples from the spec docs, do not invent syntax.