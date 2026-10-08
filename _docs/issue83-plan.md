# PBI #83 — Comments & result annotations: syntax decision

> **Status:** Decided (2026-10-02). Resolves
> [issue #83](https://github.com/lapis-lang/lapis-lang/issues/83) — the syntax for source comments
> and the `"..."` annotation convention used in every example. The decision summary is posted on the
> issue; this document is the spec-side record: the survey, the rules, the deltas, and the follow-up
> work.

## 1. The decision

| Form              | Spelling                             | Rules                                                                                                                     |
| ----------------- | ------------------------------------ | ------------------------------------------------------------------------------------------------------------------------- |
| Comment           | `/* ... */`                          | Block form, **nesting** (delimiters balance by counting). No escapes inside; a comment cannot contain an unbalanced `*/`. |
| String value      | `"foo"`                              | As specified — `String = μ α. "<Char>*"`, no repair. `\"` escapes a quote (the `match("p")` convention, lc.md §2.2).      |
| Char value        | `'a'`                                | Single-quoted, exactly one character (`Char = μ α. .`); `\'` escapes a quote.                                             |
| Result annotation | trailing comment after an expression | A comment's **position is its grade**: trailing = a record of that expression's result; no prefix punctuation.            |
| Prose comment     | own line                             | Associates **forward** — describes the next declaration/body line at greater-or-equal indent.                             |

```lapis
/* A Color declaration — the pattern's spelling is its constructor. */
data Color
    Red
    Green
    Blue
    #[0-9A-F]{6}

Color Red toHex            /* "#FF0000" */
```

## 2. The metasyntax/metadata axis

The survey's organizing question. A language with a meta-channel must decide what _grade_ each
form's content occupies:

- **Metasyntax** — a channel the semantics never sees. Consumed at fixed points, in no production's
  AST, invisible to typing, cost, and law checking. Whitespace is the degenerate case; comments are
  the rich case.
- **Metadata** — data the language carries. Survives into declarations, participates in checking,
  spelled in the object language itself. Lapis already owns this grade: `properties:` in spec
  records, `demands:`/`ensures:`/`invariant:`/`rescue:` contracts, `satisfies:`.

The settled division of labor:

| Claim kind                           | Where         | Form                               | Checked by                                      |
| ------------------------------------ | ------------- | ---------------------------------- | ----------------------------------------------- |
| "this body produces X"               | inside a body | `ensures:`/`invariant:`/`demands:` | the compiler (declaration-time)                 |
| "this expression yields X"           | doc fragments | trailing annotation comment        | future doc-example harness (never the language) |
| "this construct is for Y"            | anywhere      | prose comment                      | nothing — by design                             |
| "this declaration means Y"           | declarations  | `doc:` spec key                    | follow-up work (own PBI)                        |
| "attach Y to this node, dynamically" | the image     | MOP/image-time association         | Stage-7 metaprogramming lane                    |

## 3. The option survey (closed)

1. **Quoted-string comments (`"..."`) — the original assumption, retired.** §1.4 pinned them by
   assumption (following the Smalltalk-flavored message-send syntax); no explicit decision was ever
   made. Retired because strings _stay_ double-quoted: a shared delimiter reintroduces exactly the
   comment-vs-value ambiguity this PBI flags — `Color Red  "the Red singleton"` would be
   indistinguishable from a string value. The block form restores the disjointness on the _comment_
   side instead.
2. **C-family block comments (`/* ... */`) — chosen, with nesting.** The flat-form objections
   (attachment heuristics, corner cases) were about _placement freedom_; the own-line/trailing
   position discipline (below) resolves association deterministically, and nesting answers the
   multi-line question with one form (no delimiter runs). One rule to teach: prose cannot contain an
   unbalanced `*/`.
3. **Line comments (`//`) — not considered further.** Subsumed by the block form; adds a second pair
   where one suffices.
4. **A `comment ...` keyword (in-AST comments; the old Lisp route) — closed.** It multiplies
   alternations across every body-item production (declaration bodies, case-arm tables, module
   bodies, io steps, contract stacks) and freezes descriptions into source text — the wrong channel
   for a Language System / Live-Programming roadmap, where descriptions must be _re-settable without
   re-parse_ (the Smalltalk `Class comment:` precedent).
5. **Metadata-as-data (Zod-style `.meta()` attachment; no comment syntax at all) — absorbed.** Lapis
   already implements the structured grades of the
   [annotation continuum](http://lambda-the-ultimate.org/node/2908#comment-64894) (properties,
   contracts); what is missing is only the _least structured_ grade — prose — and prose must not
   count in token budgets, cost algebra, or law checking
   ([LtU 3295](http://lambda-the-ultimate.org/node/3295): prose must be checkable or must not
   participate). The metadata grade grows out of declarations: see §5's follow-up work.
6. **The `=>` result-annotation prefix — dropped.** Position is the language-grade marker (trailing
   comment = result record); a prefix duplicated what placement already says. The mechanical rewrite
   over the doc corpus, per site: (a) a trailing/own-line DQ comment becomes a block comment —
   `"payload"` → `/* payload */` (nested upgrades where the prose quoted quotes); (b) an annotation
   payload drops the `=>` prefix — `"=> 3"` → `/* 3 */`; (c) string values convert single→double
   quotes — `'foo'` → `"foo"` (delimiter escapes flip: a literal `'` inside a string needs no escape
   under DQ; a literal `"` inside spells `\"`); (d) single-character sites stay single-quoted — they
   are now Char values (`'a'`), not strings; (e) payload _text_ beyond the prefix is otherwise
   unchanged — the migration is lexical, never re-wording claims.

## 4. The reservation rules

Two rules keep the forms unambiguous, both extensions of implemented machinery:

1. **Reserved pattern heads.** A user-declared pattern's **leftmost-matchable set — computed from
   its AST, not its source** — must exclude `'` and `"` (reserved for the char and string value
   forms), AND its **reserved two-character prefix language** must exclude the comment pair: a
   pattern whose matchable strings can begin with `/*` is rejected (reserved for the comment form).
   The `/*` shape is a PREFIX check — the first character's matchable set alone cannot exclude a
   two-character delimiter while leaving other slash-led patterns legal: the computation walks the
   AST's per-position first-sets (position one: `/`; position two: `*`), so `/[0-9]` stays legal
   while `/*` and `[^0][*]`-led shapes reject. This generalizes the pinned letter-leading rule
   (`overview.md` §12.11): letter-initial matches are reserved for identifiers and named
   construction; the reserved spellings and prefixes belong to the literal and comment forms. The
   check reuses the same walk `isResolvableAndAnchored` runs (`src/core/grammar.ts`), rejected
   loudly at declaration. Built-ins are exempt — their patterns _define_ the reserved spellings (the
   same built-in/user asymmetry as keywords).
2. **No comment-shaped operation names.** A declared symbolic operation name may not contain `/*` or
   `*/`. The comment scanner runs at every boundary position before lexical phases (the precedence
   whitespace already has), so a `/*`-containing name after a `/` is unreachable; the
   operation-registry shape check rejects it.

## 5. Follow-up work (named lanes, not owned here)

1. **`doc:` declaration metadata (own PBI).** A spec-record key carrying a declaration's description
   — first-class, elaborated with the declaration, and _re-settable at image time without re-parse_
   (the Live-Programming requirement; Smalltalk's `Class comment`/`comment:` is the precedent).
   Value is a `String` initially; the endgame is the rich documentation value (prose plus checkable
   examples).
2. **Doc-example harness (Stage-5-adjacent).** The annotation channel's checker: evaluate a doc
   fragment, compare each trailing comment's record against the observed value. A `docs/`-CI job —
   never a surface-grammar feature, since top-level source has no expression statements (§6 below):
   only fragments contain the positions the harness needs.
3. **Metaprogramming/MOP lane (`language-design.md` Stage 7).** Image-time association of
   descriptions with program entities — the registry's first-class metalevel objects
   (`DataType`/`CodataType`/`OpSig`/`LawDecl`) are the hooks; the named hard problem is stable node
   identity under incremental re-editing (spans shift; anchors must reestablish).

## 6. The recorded realization: annotations are a fragment convention

While drafting, this survey surfaced a realization worth carrying into the overview's findings:
**top-level source has no expression statements.** A program's top level is declarations (`data`,
`behavior`, `protocol`, …); expressions exist inside bodies — where the language's checked answer to
"what does this produce?" is already contracts. Every trailing-annotation site in the corpus
(`xs sum /* 3 */`, `s size /* 2 */`, …) is a **documentation-fragment** convention — REPL, print-it,
doctest lineage — not a source-level pairing. That is why the annotation grade belongs to position
and to the future harness, and why in-source result claims route to contracts.

## 7. Spec deltas (this change)

- [`theory/surface-syntax.md`](./theory/surface-syntax.md) §1.4 — rewritten for the block-comment
  form (nesting, consumption, position grades); §1.3 — reserved-head rule added to the pattern
  constraints; §8 complete example updated.
- [`overview.md`](./overview.md) — §2's teaching text introduces `/* ... */` at first use; the
  built-ins discussion (§2.3) confirms strings stay `"..."`; annotation examples reformatted
  (payload preserved, no prefix); §12 gains the finding (top-level expressions don't exist).
- [`design-decisions.md`](./design-decisions.md) — the pinned decision entry (comment form +
  reservation rules + the grade table).
- [`lc.md`](./theory/lc.md) — one-line note: the surface comment form has no core presence; the LC
  core's one quoted form stays `match("p")` (machine-facing).
- `docs/README.md`, `docs/index.md` — published-copy wording ("trailing `/* ... */` records") and
  the layout style rules.
