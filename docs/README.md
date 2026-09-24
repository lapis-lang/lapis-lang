# docs/ — User-Facing Documentation

This folder is the **published** documentation for the Lapis language website (GitHub Pages).
[`_docs/`](../_docs/) remains the **working draft** home for design rationale, theory, and planning
documents. The flow is one-directional: material is drafted and argued in `_docs/`, then distilled
into `docs/` for the site.

| Folder   | Audience     | Contents                              | Published |
| -------- | ------------ | ------------------------------------- | --------- |
| `docs/`  | Lapis users  | curated, example-driven, stable pages | yes       |
| `_docs/` | contributors | drafts, theory, plans, working notes  | no        |

See [`index.md`](./index.md) for the landing-page outline (the Flix-style feature tour).

## Rules of thumb

- **Match the spec, not aspiration.** Every published claim must be backed by the current
  specification documents (`_docs/theory/surface-syntax.md`, `_docs/theory/lc.md`,
  `_docs/theory/semantics.md`). When those change, the pages here follow.
- **Examples are self-contained.** Every code panel shows its result as a trailing comment
  (`"=> ..."`) in the Smalltalk comment style. A reader should never need prior sections to read
  one panel.
- **One claim per section** on the landing page; depth lives in the linked pages.
- **Link only within `docs/`.** The internal drafts are not part of the site; if a page needs the
  full formal treatment, that content gets copied and adapted here, not linked.

## Page map

| Page                 | Purpose                                                        | Source material                                        |
| -------------------- | -------------------------------------------------------------- | ------------------------------------------------------ |
| `index.md`           | Landing page outline: hero + Flix-style feature tour           | `users/why-lapis.md`, `theory/syntax-design.md`        |
| `why-lapis.md`       | The essay: the hook, why it works, the tradeoff, stated honestly | `users/why-lapis.md`, `theory/why-lapis.md`          |
| `tutorial.md`        | Guided tour: Stack → Stream → law-verified NumList → relation  | to be authored (calculational style)                   |
| `syntax.md`          | Language reference: lexical, expressions, declarations, folds  | `theory/surface-syntax.md` (user-facing rewrite)       |
| `semantics.md`       | What the language means: μ/ν, fold/unfold, laws, totality      | `theory/lc.md`, `theory/semantics.md` (digestible form) |

## Publishing (when ready)

GitHub Pages supports this layout natively: **Settings → Pages → Deploy from a branch →
`main` → `/docs`**. Two decisions to make at that point (deferred until content exists):

1. **Rendering.** Recommended: [Lume](https://lume.land) (Deno-native SSG) for templates, nav, and
   syntax highlighting once the site has more than the landing page. Zero-build alternative:
   `.nojekyll` + hand-rolled HTML/CSS, which gives full control of the Flix-style two-column
   layout at the cost of markdown convenience.
2. **Syntax highlighting.** No highlighter ships a `lapis` lexer. Start with dark code panels and
   no coloring (acceptable for v0); later, a small custom highlighter (keywords, comments,
   strings, `->` arrows) covers the whole surface language.

## Example debts to settle before publishing

Found while mapping examples to sections — pin these in the spec docs first:

- **`distributive` spelling.** `users/why-lapis.md` writes `properties: (distributive: sum)`;
  `theory/syntax-design.md` writes `distributiveOver: #add` and `distributive: #sum`;
  `theory/surface-syntax.md` §3.4 says relational laws are `distributive: #opName`. The `#`
  symbol-reference form appears to be the spec'd one; the landing-page hero must use it.
- **Contract clause position.** `surface-syntax.md` §5.1 puts contract clauses inside the fold
  (before case arms); the `syntax-design.md` contracts sketch places `invariant:` among variant
  fields. Reconcile before the contracts section can be published.
- **User-declared pattern carriers.** The pattern language and the built-in pattern types
  (`Nat`, `String`, …) are specified (`surface-syntax.md` §1.3), but the surface declaration
  syntax for a user-defined pattern carrier is not yet pinned. The "No base types" section's
  example uses only built-ins until it is.