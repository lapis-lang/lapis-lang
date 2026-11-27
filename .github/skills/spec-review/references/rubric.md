# Spec Review Rubric

The per-class probes behind the passes in `SKILL.md`. Each entry gives the question, the probe that
answers it, and the case that motivated it.

## 1. Undeclared names

**Question.** Does every type name in the corpus resolve to a built-in or a declaration?

**Probe.** Run `scripts/check-spec-drift.mjs`. Then, for each candidate, ask: is it in
`BUILTIN_TYPE_NAMES` (`Any`, `Nothing`, `Family`, `Self`), in the prelude (`Char`, `String`, `Bool`,
`Int`, `Nat`, `List`), declared by a `data` form anywhere in the corpus, or a _variant_ rather than
a type?

**The trap.** `Int` is a declared pattern type, `Bool` a declared variant type, and both spell
PascalCase — so a name being capitalized proves nothing. `Number` and `Boolean` were both
capitalized, taught for months, and declared nowhere (§12.18, §12.31). `Object` was a third
(§12.29).

**The enforcement gap this exposes.** `atomType`'s final fallback mints `new TypeVar(name, Any)`, so
the checker _accepts_ every one of these. That is why reading found them and the compiler did not
(#116). A change that adds a type name to the corpus without declaring it will pass every gate.
Check it by hand.

## 2. Unspellable constructs

**Question.** Is every form the spec teaches a production?

**Probe.** For each construct in the changed docs, find the EBNF production that admits it. If there
is none, that is the finding.

**Cases.**

| Construct                            | Status                                                                                       |
| ------------------------------------ | -------------------------------------------------------------------------------------------- |
| `Block<σ,τ> = ν α. Π value: (σ → τ)` | Retracted — a type constructor at kind `*→*→*`, which §2.1 forbids, and uninhabited (§12.27) |
| `typeParam:` spec key                | Removed — a second spelling for what the arm binding already carries (§12.29)                |
| `data List<a>`                       | Forbidden permanently — no declaration takes a parameter list (§12.29)                       |
| `protocol equals: <in: Self, …>`     | Was unspellable — `protocolItem` had no signature form (#113)                                |

**Distinguish two failures.** A construct with _no production_ is a spec defect. A construct with a
production that _rejects its own example_ is a grammar defect. They have different remedies and
different severities.

## 3. Two spellings, or two meanings

**Question.** Does one concept have one spelling, and does one spelling have one meaning?

**Probes.**

- _Two spellings:_ grep the corpus for the reference forms. `aux` was written `aux #depth` at the
  declaration site and `aux depth` at every read site (§12.26). Neither was marked provisional.
- _Two meanings:_ find a token whose resolution depends on ambient declarations. `Family` meant open
  recursion in a program without a user type of that name, and closed recursion in a program with
  one (§12.12). The recursion discipline flipped silently, decided by what else was in scope
  (§12.16).

**Why this class matters more than it looks.** A language whose surface has two readings per token
cannot be documented, because any sentence is true in one reading and false in the other.

## 4. Rules stated but never enforced

**Question.** Is a decided rule enforced at its site, or only recorded?

**Probe.** For each "Decided" / "Open" block in the changed docs, find the code that enforces it.
`grep` for the check. If the only occurrence of the rule is its prose, the rule does not exist.

**Cases.** `Family` reserved in type position was decided (§12.16) and enforced nowhere —
`data Family { … }` parsed, published, and registered. `Family`/`Self` reservation now lives in
`resolve.ts`, which is a _whole-program_ pass; a production-level check could not see the
declaration.

**Where the check belongs.** Not always the grammar. A name is syntactically a `pascalIdent` whether
it is reserved or not, so the rejection belongs where the name is _declared_ — resolution, not
parsing. A finding that demands the check in the lexer is likely wrong.

## 5. Grammar vs. corpus drift

**Question.** Do the productions match their own examples?

**Probe.** Extract the examples under a production and parse them. Automate it if the production is
stable.

**Case.** `protocolItem ::= foldDecl | unfoldDecl | mapDecl | mergeDecl | scanDecl` — yet every
protocol member in the corpus was written without the keyword (`equals: <in: Self, out: Boolean>`).
The production matched none of its own examples, and abstract members cannot be a `foldDecl` at all,
since they have no body (#113).

## 6. A missing arm in a relation

**Question.** Does every constructor of a judgment have a rule?

**Probe.** Enumerate the type constructors (`Type` subclasses). For each relation (`isSubtype`,
`join`, `meet`, `equals`, `map`, `dispatch`), check each constructor has an arm. The compiler
enforces exactly one of these — `RequiredCases` on `dispatch`. The rest are by hand.

**Case.** `isSubtype` dispatched on type kind with no `FamilyType` case, so a recursive field fell
through every branch to `return false` (§12.14, #102). `resolveFamily` existed on the type and was
never called from the relation.

**Verify with the asymmetric case.** `isSubtype(T, T)` is `true` via S-Refl whether or not the
missing arm exists. The rule's presence proves nothing; its _absence_ shows only when the two sides
differ.

**Stale-premise warning.** #102's original evidence was that `Cons(Nil())` failed the variant
premise. By the time it was picked up, `variantCon` and `variantPremisesHold` both called
`resolveFamily`, so that case passed. The surviving defect was narrower — the lattice arm — and only
#86 consumed it. **Re-run the claimed failure first.**

## 7. Silent permissiveness

**Question.** Does the checker accept what it should reject?

**Probe.** For each accepting fallback, ask what input reaches it unintentionally.

**Case.** `atomType`'s last line was `return new TypeVar(name, Any)`, so `\x:Natt. x`,
`\x:Number. x`, and `\x:Object. x` all parsed and type-checked (#116). The minted variable is
_rigid_, not permissive, so the failure is not unsoundness — it is a **late, confusing** error,
surfacing wherever the two variables fail to relate, naming a type the author never wrote.

**The rule.** Where the surface has no type variables (permanently, §12.29), an unknown name can
have no legitimate meaning, so acceptance is always the defect. The fix is a hook: default to the
core's permissive behaviour, override to reject in the surface.

## 8. Elaboration properties

**Two properties, checked separately.**

**Type preservation.** `Γ ⊢ s : σ` implies `Γ ⊢ ℰ(s) : σ`.

```ts
const { operations } = elaborateProgram(ast, table)
const forest = [
    ...new LCTypeCheck().setRegistry(registry)
        .parseWith(operations[0].definition, new TypeEnv()),
]
assertEquals(forest.map(String), ["(Stack → Stack)"])
```

Asserting the definition is a non-empty string proves nothing.

**Semantics preservation.** The surface's value is the core's value.

```ts
const value = [
    ...new LCEval().setRegistry(registry)
        .parseWith(`(${op.definition}) Push(Empty(), Empty())`, new ValueEnv()),
][0]
```

**`parseToTree` is not the evaluator's entry point.** It returns a tree whose values are
`EvalErrorValue` when the term does not evaluate, and a `size > 0` assertion accepts that happily.
Use `parseWith`.

**Emit the core's syntax exactly.** Verified against the core grammar, not intuition:

| Wrong              | Right          | Symptom                                                                                     |
| ------------------ | -------------- | ------------------------------------------------------------------------------------------- |
| `Push(x, rest)`    | `Push(x rest)` | parse fails silently; bindings are space-separated, handlers comma-separated                |
| `Empty`            | `Empty()`      | a bare PascalCase name is a _variable_ in core syntax; the nullary constructor needs parens |
| `\e:Stack. fold …` | same           | correct — `\\` in a JS string literal is one backslash                                      |

**A one-element fold handler list is not enough.** `{ Empty() -> Empty() }` failed where
`{ Empty() -> Empty(), Push(…) -> … }` passed, because exhaustiveness is per-carrier.

## 9. The representation question

**Question.** Is the retained form the right one for the pass that consumes it?

**Probe.** Walk a tree from `parseToTree` and inspect labels. A repeated production shows nested
same-label nodes with partial values; a fixed `seq` shows one node with no children.

**Case.** The surface `dataDecl` production produced **five** nested `dataDecl` nodes for one
declaration, each carrying a prefix of the name (`"S"`, `"St"`, `"Sta"`, `"Stac"`, `"Stack"`). A
`SemanticPass` dispatching on that label fires five times and cannot distinguish a partial value
from a complete one.

**`CostPass` is the precedent.** It documents the hazard and works around it by re-parsing with its
engine — available there because the core's semantics are re-derivable from source. The surface has
no such second engine, so it retains an **AST** built by the productions' own `.map`/`chain`
actions, which see each production exactly once.

**What the tree is still for.** Spans, diagnostics, and unparsing (#34). Do not report a change for
keeping `parseToTree` wired; report one for _dispatching semantics_ off its labels.

## 10. Layout

**Question.** Is indentation grammar or whitespace?

**Probes.**

- A block one space short or long must be **rejected**. Assert both.
- A tab must be rejected: the indent unit is four spaces.
- A blank or comment-only line between items must not consume the _next_ item's indentation, or the
  block after a blank line vanishes.
- Column threading is a `@rule` **method** parameter, memoized per `(instance, method, args)`. A
  parameterless block production cannot implement L1 at all.

**Why the engine's primitives do not work here.** `ws`/`ws1` are newline-inclusive, so a line can
swallow the newline that terminates it — collapsing exactly the structure the column parameter
exists to enforce. Newline-excluding primitives (`hws`, `hws1`, `lineEnd`) are required.

## 11. Ambiguity

**Question.** Does the input have one derivation?

**Probes.** Parse the input and check `forest.size`. Two structurally identical _objects_ do not
collapse in a `Set` (only identical primitives do), so a "harmless" ambiguity doubles every
enclosing forest.

**Cases found by probing, all four real:**

| Input                        | Parses | Cause                                                                              |
| ---------------------------- | ------ | ---------------------------------------------------------------------------------- |
| `Any` in type position       | 2      | matched both the built-in arm and `pascalIdent` (`Any`/`Nothing` are not keywords) |
| `nil` in expression position | 2      | matched both `specialValue` and `ident`→`opRef`                                    |
| `Push value: nil`            | 2      | a construction (§3.4) and a keyword send (§3.3) have the same shape                |
| `self old result`            | 1024   | a zero-width separator inside a repetition                                         |

**The rules that remove them.**

- Exclude built-in names from the `pascalIdent` arm in `atomType`.
- Exclude §2.5's special values from the operation-reference arm.
- §3.3's greedy collection: a keyword part's value is a `binaryExpr`, a PascalCase receiver takes
  **no** keyword parts, and a unary message stops before a `key:` pair.
- A separator between items requires at least one character.

## 12. Metadata and the metatheory engine

**Question.** Is a rule visible to the machinery that verifies it?

**Probe.** `collectRules(LCTypeCheck)` and check the changed rule appears with its premises. A rule
action with no `@requires`/`@ensures` metadata is invisible to `verifyMetatheory`, which then simply
covers less — it does not report a gap.

**The convention.** `@requires(pred, { rule: "T-App", role: "premise", formula })`,
`@ensures(pred, { rule, role: "conclusion", formula })`. `formatRule` renders these as proof trees,
so a missing `formula` is a rule that cannot be documented from its own source.

**Also check the rejection path.** A failed `@requires` yields `undefined` in the forest, which is
_not_ a rejection. Branch pruning is the production's job (`empty()`). A change that relies on
`@requires` for rejection accepts the term.

## 13. Documentation obligations

A language change is not done until the description matches. Report each absence, Low severity, but
report it.

| Where                                       | What must agree                                            |
| ------------------------------------------- | ---------------------------------------------------------- |
| `surface-grammar.md` front matter           | what is implemented today                                  |
| `surface-grammar.md` §9                     | per-production status table                                |
| `elaboration.md`                            | a translation rule per surface form                        |
| `overview.md` §12.2 / `design-decisions.md` | the finding's index row, and the decision where it has one |
| `_docs/theory/lc.md`                        | the inference rule, if the core changed                    |
| `examples/README.md`                        | blockers, if a fixture became runnable                     |

**The `data`-declarations precedent.** The surface productions shipped while `surface-grammar.md`
still said "**Not implemented**". The docs taught a language the compiler could not read — for
months, through several doc sweeps. The status block is not cosmetic; it is the only place a reader
learns what is real.

## 14. Backlog and premise hygiene

**Probes.**

- Does the change meet the **issue body's** acceptance criteria, not the plan's restatement of them?
- Is the issue's premise still true? Re-run the failing case it reports.
- Does the change defer something? Name it and put it on the record.
- Are the dependency edges still accurate?

**How ordering lives here.** Not milestone numbers — those are themes, and a lower number does not
gate a higher one. `gh issue edit N --add-blocked-by M` is the ordering. A review that says "#97
blocks #98" must have the edge, not a reading of the milestone titles.

**The #25/#97 case.** Two issues each claiming to own "the surface grammar", under two different
architectures, neither mentioning the other. The finding was not that either was wrong — it was that
the ownership boundary was unstated, so implementing either first would have duplicated the other.

## Severity calibration

| Situation                                                 | Severity                       |
| --------------------------------------------------------- | ------------------------------ |
| A term type-checks and then gets stuck                    | High                           |
| Elaboration emits text the core rejects                   | High                           |
| A subtyping arm missing, reachable from a real program    | High                           |
| A decided rule unenforced where user code can exercise it | High                           |
| A production accepts input the spec forbids               | High                           |
| The docs teach a name nothing declares                    | Medium                         |
| The status table or `elaboration.md` is stale             | Medium                         |
| Two derivations of one input                              | Medium                         |
| A comment states a false rationale                        | Medium — it reads as authority |
| A test name overstates what its assertion proves          | Low                            |
| A deferral not on the record                              | Low                            |

**Documentation lowers severity; it never lowers the finding.** Ask: _if this comment were deleted,
would this be a finding?_ If yes, it is a finding now.
