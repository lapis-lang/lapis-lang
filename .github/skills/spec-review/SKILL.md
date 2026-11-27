---
name: spec-review
# No slash command of its own. Review is one workflow with one entry point; a
# second name for the same skill is two surfaces to remember. Auto-loading by
# description still applies, so the model reaches for this when the description
# matches.
user-invocable: false
description: "Review pending changes in a programming-language implementation as a PL theorist and a language designer would. USE FOR: reviewing a branch, PR, or working-tree diff before committing; auditing a diff against the *specification* rather than against itself; whether a typing, evaluation, or subtyping rule is sound and complete for its stated form; whether an elaboration is type-preserving and semantics-preserving; whether a grammar production accepts the corpus it claims; whether an AST vs. DerivationTree distinction is respected; whether a test proves a semantic property or merely exercises a code path; whether an inference-rule contract or metatheory claim is real; finding a rule implemented in one place but stated in two; finding a name the docs teach that nothing declares; checking canonicalization consistency on both sides of a comparison. DO NOT USE FOR: fixing the findings, pure style or formatting (lint owns that), or application code in a non-language repository."
argument-hint: "Optionally name a base branch, an issue/PBI number, or a file or spec section to focus on"
---

# Programming-Language Specification Review

Produce the review a **PL theorist** and a **language designer** would leave, not a summary of the
diff. The diff is evidence. The subject is **the language the diff claims to define**.

Language work fails differently from application work, and that difference is the whole reason this
skill exists. In an application, a wrong branch produces a wrong answer that a test can catch. In a
language, a wrong rule produces a language nobody has described, and the test suite keeps passing
because it only exercises the terms the implementation happens to accept. **A green suite is
evidence about the implementation. It is not evidence about the language.**

## The two lenses

| Lens                  | Question                                                                                     | Passes |
| --------------------- | -------------------------------------------------------------------------------------------- | ------ |
| **PL theorist**       | Is the rule sound? Is the reduction total? Does the type system say what the semantics does? | A–C, D |
| **Language designer** | Is this the language we said we were building, and will the docs still be true?              | E–G    |

Keep them apart. A soundness finding and a design finding have different remedies, and conflating
them produces a finding that is wrong in its own frame.

## Ground rules

1. **Never report what lint, typecheck, or the compiler already report.** Unused imports,
   formatting, and naming are not findings. But note the inverse: this repository's rules are
   **structural**, and lint cannot see that a production accepts input the spec forbids, that two
   rules disagree, or that a docblock states a false rationale. Those are what this review exists
   for.

2. **Audit against the spec, never against the diff.** The specification is `_docs/theory/` —
   `lc.md` for the core, `surface-grammar.md` for the surface, `elaboration.md` for the translation,
   `semantics.md` for cost and evaluation. A change that is self-consistent but contradicts `lc.md`
   is a finding _against the change_, and the finding names the section. When the spec is silent,
   that silence is the finding — say which section should have decided it.

3. **The author's plan is not the spec.** A `_docs/issueNN-plan.md` is a claim to check. A plan
   asserting "criterion met → symbol X" is the thing to verify. Its _numbers_ are claims too: a plan
   reporting "43 tests" or "5 parses" is evidence only if you can trace each number to an artifact
   you ran or opened.

4. **Every finding must be verified.** Run the probe, open the production, count the forest. If you
   cannot verify it, phrase it as a question after the findings, not as a claim. An unverified claim
   is worse than silence.

5. **Say nothing positive.** The author can read their own diff.

6. **One finding per defect.** If a defect recurs at several sites, say it once and list the sites.

7. **A clean review is an allowed outcome.** Do not invent findings.

8. **A conformance finding names the rule it breaks.** Quote the grammar production, the inference
   rule, or the recorded decision, so the author can appeal to the rule rather than to your taste.

9. **Evidence must be able to distinguish the defect from the design.** A test that passes, and a
   test that would also pass if the implementation were wrong, are the same observation. If the
   evidence is equally consistent with both, saying so is the finding.

10. **A comment justifying a deviation is the thing to check, not the license to accept it.** A
    docblock arguing in specification language for a behaviour that the spec forbids reads as a
    considered decision and will survive a review that trusts it. Verify _why_ the code diverges.
    Likewise, documentation lowers a finding's severity; it never removes the finding.

## The defect classes this repository actually has

`_docs/overview.md` §12.1 lists the nine classes of defect this language produces. They cluster.
Check these deliberately, because a generic reviewer misses every one of them.

Their shape is always the same: **the language says one thing in one place and something else
everywhere else, and nothing detects the disagreement.**

| Class                                  | The question                                                               | Recorded cases                                                              |
| -------------------------------------- | -------------------------------------------------------------------------- | --------------------------------------------------------------------------- |
| **Undeclared name taught by the docs** | Does every type name in the corpus resolve to a built-in or a declaration? | `Number` (§12.18), `Boolean` (§12.31), `Object` (§12.29)                    |
| **Unspellable construct**              | Is every form the spec _teaches_ actually a production?                    | `Block<σ,τ>` (§12.27a), `typeParam:` (§12.29), `data` declarations (§12.15) |
| **Two spellings for one concept**      | Does one reference form have one spelling?                                 | `aux d` vs `aux #d` (§12.26)                                                |
| **Same spelling, two meanings**        | Does one token resolve one way?                                            | `Family` open vs. closed recursion (§12.12)                                 |
| **Rule stated, never enforced**        | Is a decided rule enforced at its site, or only recorded in prose?         | `Family` reserved, unenforced (§12.16)                                      |
| **Grammar vs. corpus drift**           | Do the productions match their own examples?                               | `protocolItem` had no signature form (#113)                                 |
| **Missing arm in a relation**          | Does every constructor of a judgment have a rule?                          | `isSubtype` had no `FamilyType` arm (§12.14)                                |
| **Silent permissiveness**              | Does the checker accept what it should reject?                             | unknown type names minted a `TypeVar` (§12.29, #116)                        |
| **Stale evidence**                     | Does the issue's claimed failing case still fail?                          | `Cons(Nil())` became legal; #102's premise expired                          |

**The last row is the one that bites.** Verify the failing case before reporting it. An issue whose
premise has silently expired is itself a finding — against the tracker, not the code.

## Procedure

### 1. Establish the change set

The review runs on **pending work**, before a PR exists. Do not create one and do not push. Collect
the change set:

```bash
git status --short
git diff --stat && git diff          # unstaged
git diff --cached --stat             # staged, if any
git --no-pager log --oneline @{u}..  # committed, if the branch is tracked
```

For a large change set, read the stat first and then each file's diff in pieces. Never review a diff
you have only skimmed the summary of.

**Also read what is _not_ in the diff.** A language change has three parts, and a diff can contain
one:

1. the productions / rules / types (**the implementation**),
2. the spec sections they correspond to (**the description**),
3. the tests that claim to bind the two (**the evidence**).

A change carrying only (1) is the most common defect in this repository — the `data` productions
shipped as a plan while `surface-grammar.md` still said "not implemented". Report which of the three
are present.

### 2. Identify the spec sections in scope

| The diff touches                               | The normative section                                             |
| ---------------------------------------------- | ----------------------------------------------------------------- |
| `src/core/types.ts`, subtyping                 | `lc.md` §2.1, §4                                                  |
| `src/core/grammar.ts` productions              | `lc.md` §2.2 (terms), §2.1 (types)                                |
| `src/core/typing_grammar.ts`                   | `lc.md` §5 (all typing rules)                                     |
| `src/core/eval_grammar.ts`                     | `lc.md` §3.1 (evaluation rules)                                   |
| `src/core/patterns*`, `pattern_lang.ts`        | `lc.md` §5.1, `surface-syntax.md` §1.3                            |
| `src/surface/**`                               | `surface-grammar.md` (normative), `surface-syntax.md` (narrative) |
| Elaboration anywhere                           | `elaboration.md` §1–§3                                            |
| `src/core/cost.ts`, `laws.ts`, `derivation.ts` | `semantics.md` §5.5, `type-algebra.md` §6                         |
| Any decision recorded in `overview.md` §12     | the finding it closes                                             |

`surface-grammar.md` wins over `surface-syntax.md` on **shape** (its own header says so);
`surface-syntax.md` wins on **what the tokens mean**. Reviewing a surface change against the wrong
one produces a finding the author can correctly reject.

### 3. Pass A — mechanical and verifiable

Facts, not judgments. These are the cheapest findings and the most convincing.

- **Run the gates, and read what they mean.** `deno check src/index.ts`, `deno lint`,
  `deno fmt --check`, `deno test --allow-run`. A green result is the _baseline_ for everything
  below, never a finding itself. `deno.json`'s `build` task references a `src/cli.ts` that does not
  exist — that is #98's known gap, not this diff's defect; do not re-report it.
- **Count the tests added and name the property each asserts.** "43 passed" says nothing. The
  question is whether each `Deno.test` would fail under a mutation that breaks the rule it names. A
  test whose name says "rejects" must assert an empty forest; a test asserting `size > 0` where the
  claim is rejection proves nothing.
- **Check every new production against its own examples.** Take the EBNF from the spec, take the
  corpus examples beneath it, and parse them. A production that rejects its own documentation is the
  #113 defect.
- **Check every new inference rule names its premises.** This codebase records rules as
  `@requires`/`@ensures` with `{ rule, formula, role }` metadata. `collectRules`/`formatRule` read
  it. A rule action with no metadata is a rule the metatheory engine cannot see, and
  `verifyMetatheory` will silently cover less.
- **Check arity and order at every changed call site** where a judgment is destructured — the
  tuple-index errors are silent when the wrong slot happens to be a compatible type.

### 4. Pass A′ — the structural probes

Run the drift probe over the repository:

```bash
deno run --allow-read .github/skills/spec-review/scripts/check-spec-drift.ts
```

It reports the two shapes this repository produces most and that nothing else detects:

1. **Type names taught but never declared.** Every PascalCase name in a _type_ position inside a
   `` ```lapis `` fence, checked against the built-ins, the `data` declarations the corpus makes,
   the variants those declarations introduce, and the types the fixtures register. This is the
   `Number`/`Boolean`/`Object` leak class (§12.18, §12.29, §12.31) — found by reading, three times,
   because `atomType` accepts every name it does not recognize (#116).
2. **`data` bodies at a column L1 does not admit.** A body must be exactly one indent unit (4
   spaces) deeper than its header; the probe checks every `data` line inside a code fence against
   the next line's indentation.

On the tree as it stands the probe reports ten candidates, several of which are meta-notation rather
than Lapis (`Type`, `T`, `Type1`, `ParamType` in `surface-syntax.md`'s production tables) — and at
least two that are real: `Float`, which the prelude defers (§5.3), and `Ordered`, a protocol member
used in `data
Num`'s `satisfies:`. **Treat the output as candidates to verify, never as findings.**
The probe is textual: it cannot resolve a name declared in another file, cannot read EBNF, and
cannot tell a protocol from a type. Its value is that it is exhaustive where reading is not.

### 5. Pass B — soundness and totality

For each changed rule, ask: **is there a term this rule now admits that has no next step?**

- **Totality of the reduction.** Every new evaluation rule must either be a value rule or have a
  successor for every input it accepts. An accepted term with no rule is a stuck term, and Progress
  fails.
- **Preservation.** The new conclusion's type must be the premise's type. For a fold, `fold_T e {…}`
  types as the handler result; check the rule states it.
- **Every constructor of a judgment has an arm.** This is the #102 class. When a new type kind
  enters the lattice (a new `Type` subclass), `isSubtype`, `dispatch`'s `RequiredCases`, and `map`'s
  `TypeCases` each need their arm — and `RequiredCases` is the only one the compiler enforces. Check
  the others by hand.
- **Reflexivity is not a rule.** A branch that only satisfies `σ <: σ` where the spec demands a real
  relation is a rule that looks present and is absent. Verify by _probing the asymmetric case_, not
  the same-type case.
- **Rigid vs. permissive failure.** A minted `TypeVar` for an unknown name is rigid, so it fails
  late and far from the cause (#116). Late failure is a soundness-_presentation_ defect: the term
  that should have been rejected at its annotation is rejected, misleadingly, somewhere else.

### 6. Pass C — the elaboration contract

Any change touching `src/surface/**` or `elaboration.md` must satisfy two properties, and each is
checked separately.

- **Type-preserving.** If `Γ ⊢ s : σ` in the surface then `Γ ⊢ ℰ(s) : σ` in the core. Concretely:
  elaborate a fixture, then feed the emitted LC text to `LCTypeCheck` and assert the type is the
  source's declared type. Asserting only that the emission is a string is not this property.
- **Semantics-preserving.** The value the surface denotes is the value the core computes. Elaborate,
  then `LCEval.parseWith` the definition — note `parseToTree` is **not** the evaluator's entry
  point, and using it returns an `EvalErrorValue` that a `size > 0` assertion happily accepts.

**Check the emitted syntax against the core grammar, not against intuition.** The core's fold
handlers separate _bindings with spaces_ and _handlers with commas_, and a zero-field variant must
be emitted as `Empty()` because a bare `Empty` is a variable in core syntax. Both mistakes
parse-fail silently, which is why the only adequate test is a round-trip through the real checker.

### 7. Pass D — the representation question

This repository has a specific, load-bearing distinction, and a diff that ignores it will look
correct and be wrong.

- **`DerivationTree` is not an AST.** `parseToTree` records _where a `@rule` matched_, not the shape
  of a production: a repeated production yields nested same-label nodes carrying partial values, and
  a fixed-arity `seq` yields one node with no children. A `SemanticPass` that dispatches on those
  labels fires once per repetition. A change that walks a tree as though it were structured is a
  High finding — `CostPass` documents this hazard and works around it by re-parsing.
- **A surface AST is the retained form; the tree is for spans.** Diagnostics, unparsing (#34), and
  error spans are what the tree is for. Semantics is not.
- **Source text is a legitimate IR here.** `OpSig.definition` is concrete syntax by design, so
  "elaborate" means "emit LC source". A finding that demands a core AST is wrong for this codebase;
  a finding that emits text the core grammar rejects is right.

### 8. Pass E — grammar and layout conformance

- **Layout is grammar, not whitespace.** A block at the wrong column must be _rejected_, not
  tolerated. Check that a changed block production takes its column as a parameter and that the
  tests assert rejection at column ±1.
- **Ambiguity is a defect even when the results agree.** Two derivations of the same input that
  yield structurally identical but distinct objects double every enclosing forest. `Any`/`Nothing`
  matching both a built-in arm and `pascalIdent` did exactly this; `nil` parsing as both a literal
  and an operation reference did too.
- **A zero-width separator inside a repetition makes segmentation ambiguous.** Three names separated
  by optional whitespace have hundreds of derivations. The separator between _items_ must require at
  least one character (`hws1`, not `hws`).
- **A keyword is not a name, except where it is.** `ident` excludes keywords (§2.2), but
  contract-clause bindings are literally `self`, `old`, `result`, `ensures` — all keywords. A
  production that admits keywords where the grammar spells one, and only there, is correct; a
  blanket `ident` everywhere is not.

### 9. Pass F — the documentation obligation

A language change is not finished until the description matches. Check, and report each absence:

- **The grammar document.** `surface-grammar.md` §9's per-production status table and its front
  matter both state what is implemented. A new production with a stale status line is a finding
  (Low, but it is the `data`-declarations defect repeating).
- **The elaboration document.** A new surface form with no `elaboration.md` section is a rule with
  no translation rule.
- **The finding ledger.** A decision made in the diff belongs in `_docs/overview.md` §12 with a
  number, or in `design-decisions.md`. A decision recorded only in a PR body is not recorded — this
  repository's whole methodology is that decisions are written down so later code can cite them.
- **The comment's rationale.** A docblock explaining _why_ code diverges from the spec must be true.
  Verify it against the spec; a false rationale is worse than no comment, because it reads as
  authority (ground rule 10).

### 10. Pass G — the backlog and the premise

This is the pass a generic reviewer never runs, and here it is not optional.

- **Does the change close an issue, and does it meet the issue's acceptance criteria?** Not the
  plan's restatement — the issue body's checkboxes.
- **Is the issue's own premise still true?** #102's claimed failing case (`Cons(Nil())` failing the
  variant premise) had stopped failing; the surviving defect was narrower. A diff that implements a
  premise nobody re-verified is a diff against a ghost. Re-run the claimed failure before accepting
  the fix.
- **Does the change introduce a new PBI-shaped gap?** A deliberate deferral is fine, and belongs on
  the record. Say so and name it.
- **Are the dependency edges still true?** `gh issue edit N --add-blocked-by M` is how ordering
  lives here, not milestone numbers.

## Reporting

Write findings as a list, each with **severity**, **location**, **the rule it breaks**, and **what
you verified**. Then questions. Then nothing else.

```
**High** — `src/core/subtyping.ts:isSubtype`
`FamilyType` has no arm, so a recursive field compared against any other type
falls through to `false`. `lc.md` §4.2's S-Data-Depth requires the field's type
resolve against its carrier first. Verified: `isSubtype(closedList, openList)`
is `false` although the fields are otherwise identical.
```

Severity is the consequence of shipping as written, not your confidence:

| Severity   | Test                                                                                                                                                                                                    | Examples                                                                                                                                      |
| ---------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- |
| **High**   | The language is wrong on a path a program will reach: a term type-checks but evaluates to a stuck state, a rule is unsound, elaboration changes meaning, a decided rule is unenforced where it matters. | Missing subtyping arm; an elaboration that emits text the core rejects; a production accepting input the spec forbids                         |
| **Medium** | The language is right but the description is not, or the failure needs an unusual term.                                                                                                                 | Doc teaches an undeclared name; status table stale; two derivations of one input                                                              |
| **Low**    | The cost is confusion or maintenance.                                                                                                                                                                   | A comment contradicting the spec; a test name that overstates what it asserts; a missing `elaboration.md` section for a form nothing uses yet |

**Escalate** when the failure is silent — a wrong type that still parses, an elaboration that loses
meaning, a rule that only exists in the diff's imagination. **De-escalate** when the author recorded
the trade-off and the deferral is on the record — but keep the finding.

The rubric, the per-class probes, and the worked examples are in
[`./references/rubric.md`](./references/rubric.md).

## What this skill is not

- Not a bug hunt in the application sense. There is no production traffic, no tenant scoping, no
  migrations.
- Not a code-style review. `deno fmt` and `deno lint` own that.
- Not a rewrite proposal. A structural concern is a decision; the architect's job is to ensure it
  was made **deliberately and on the record**, not to demand a different architecture.
