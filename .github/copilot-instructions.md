# GitHub Copilot Instructions

- never use eslint-disable-next-line complexity or similar. resolve the complexity issues.
- never auto-publish a branch, nor push it to the remote repository without review. Don't stage or
  commit changes without user approval.
- Don't reference the backlog or any external issue tracking IDs in our code comments. We also don't
  need a history lesson in the comments; focus on explaining the code itself.
- don't use inline import statements. Instead, import statements should be placed at the top of the
  file

## Language work

This repository is a programming language, not an application. The rules below follow from that.

- **The specification is normative, and it lives in `_docs/theory/`.** `lc.md` is the core calculus,
  `surface-grammar.md` the surface grammar (normative on _shape_; `surface-syntax.md` is its
  narrative counterpart and wins on what tokens _mean_), `elaboration.md` the translation,
  `semantics.md` cost and evaluation, `prelude.md` the built-in types. A change that contradicts one
  of them is wrong even when it is self-consistent. If the spec is silent, say so rather than
  inventing a rule.
- **A decision is not real until it is written down.** Decisions belong in `_docs/overview.md` §12
  (numbered) or `_docs/design-decisions.md`. A decision recorded only in a pull-request body or a
  commit message is not recorded — later code cannot cite it.
- **A green test suite is evidence about the implementation, not about the language.** Tests
  exercise the terms the implementation happens to accept. When you claim a semantic property holds,
  say which assertion would fail if it did not, and check it against the spec rather than against
  the code.
- **Verify a claimed failing case before fixing it.** An issue's premise can expire: #102's reported
  failure (`Cons(Nil())` rejected by the variant premise) had already stopped reproducing, and the
  surviving defect was narrower. Re-run the case first.
- **A name the corpus teaches must be declared, or the checker accepts it silently.** `atomType`
  mints a `TypeVar` for any unknown name, so `Number`, `Boolean`, and `Object` were taught for
  months while nothing declared them. Where the surface has no type variables — which is permanently
  the case — an unknown name is an error at its annotation, never an opaque variable.
- **Layout is grammar.** A block at the wrong column must be rejected, not tolerated. Column
  threading is a `@rule` method parameter; the engine's `ws` family is newline-inclusive and cannot
  express it.
- **`DerivationTree` is not an AST.** `parseToTree` records _where a `@rule` matched_, not the shape
  of a production: repeated productions nest as same-label nodes carrying partial values, and a
  fixed-arity `seq` yields one childless node. Semantics belongs on a surface AST; the tree is for
  spans, diagnostics, and unparsing.
- **The core represents terms as concrete syntax.** `OpSig.definition` is LC source text, so
  elaboration emits text the core re-parses. The core's fold handlers separate _bindings with
  spaces_ and _handlers with commas_, and a zero-field variant must be emitted as `Empty()` — a bare
  `Empty` is a variable reference there.
- **Ambiguity is a defect even when the results agree.** Two derivations that yield structurally
  identical objects still double every enclosing forest. Check `forest.size`, not just the value.

## Review

Use the `spec-review` skill (`.github/skills/spec-review/`) when reviewing language changes. Its
`references/rubric.md` records the nine defect classes this repository actually produces, drawn from
the 33 findings in `_docs/overview.md` §12 — use them as the checklist rather than a generic review.
