# Lapis Language Design Decisions

> **Source:** Copilot repo memory (`/memories/repo/lapis-design-decisions.md`). Copied here on
> 2026-07-25 because repo memories don't survive devcontainer rebuilds. This file is the
> authoritative copy; the memory file is a convenience cache. Update both when decisions change, or
> just this file and re-import.

Pinned in `_docs/theory/language-design.md`, `_docs/theory/lc.md`, and `_docs/theory/why-lapis.md`.

## Original motivation (rediscovered, see why-lapis.md)

- The Bird-Meertens Formalism (Squiggol) should be a programming language, not a theory.
- The unique property: enforced structural recursion (fold/unfold only) COMBINED with first-class,
  verifiable, AND exploitable algebraic laws.
- Enforcement without exploitation = Charity (a cage). Exploitation without enforcement =
  Haskell+rewrite rules (a library, unreliable). Lapis = both together.
- The three ESSENTIALS (irreducible): (1) fold/unfold as only recursion, (2) first-class exploitable
  law declarations (properties), (3) μ/ν bialgebraic duality.
- NOT essential (could be library/sugar): surface syntax, relation/query/io sugar, contracts, module
  system, subtyping. These make the cage habitable but aren't why the language exists.
- Enforcement is a language-level decision — cannot be a library. This is the answer to "why a
  language, not a library."
- Asymptotic argument: algebraic correctness goes from O(program size) global composition analysis
  to O(1) local law declarations. Enforcement reduces compiler's reasoning from "analyze arbitrary
  recursion" to "trust the structure" — same complexity reduction types provide.

## Core calculus

- **F<: + μ/ν + guarded fold/unfold + qualified types.** NOT Fω — no higher-kinded polymorphism.
- Subtyping subsumes generics (Meyer OOSC, Bracha). Comb inheritance + field narrowing is the
  mechanism.
- Cost: loss of parametricity. Recovered _by declaration_ via `properties` annotations (associative,
  idempotent, etc.). Reframe `properties` as the price paid for subtyping-over-generics.
- No general fixpoint. Recursion only via fold (terminating, data finite) and unfold (productive,
  guarded). Sized-types story specialized to bialgebraic setting.
- **Iso-recursive, not equi-recursive.** `fold_T`/`unfold_T` are explicit core terms, not silent
  coercions. Rationale: in Lapis, fold and unfold are not type coercions (as in TAPL) but the
  primary computational constructs — the catamorphism and anamorphism. They carry semantic weight:
  `properties` (algebraic laws), `@requires`/`@ensures` (contracts), `<para>`/`<histo>`/`<aux>`
  (recursion scheme modifiers), and `<in:`/`<out:` (type specs) are all declared _on the fold_.
  Making fold/unfold implicit (equi-recursive) would destroy the declaration surface where the user
  tells the compiler the algebraic structure of their operation — which is the whole point of the
  language. The hybrid: iso-recursive core + elaboration, equi-recursive surface for pattern
  matching inside fold handlers (the user pattern-matches directly; the fold machinery manages the
  recursive boundary). Subtyping rules (S-Data-Width, S-Data-Depth) use the guarded assumption
  (`α <: T'` in the premise) — the standard iso-recursive treatment (Amadio-Cardelli).

### Design rationale narrative

The calculus is shaped by three deliberate choices, each with a cost that is paid back by a design
feature:

1. **F<:, not Fω.** No higher-kinded polymorphism. Subtyping (with bounded quantification) subsumes
   generics (Meyer, Bracha). Protocols are predicates over the subtyping lattice, not
   type-constructors. The cost — loss of parametricity — is recovered _by declaration_ via
   `properties`.

2. **μ/ν, not general fix.** Data is μ (initial algebra); codata is ν (final coalgebra). No `fix` or
   `Y`. Termination of folds and productivity of unfolds follow from the F-structure being the
   measure — no separate termination checker. This is the soundness lever.

3. **Iso-recursive, not equi-recursive.** (See bullet above.) The cost — explicit fold/unfold in the
   core — is paid back by the declaration surface for laws, contracts, and recursion scheme
   modifiers.

4. **Effect-free.** No effect type. Contracts elaborate to `Result`; IO is a Mealy data value. The
   core is sound for pure fold/unfold + contracts-as-results.

**Position vs. Verse (Epic Games).** The most credible recent contrast — full comparison in
`_docs/theory/lapis-vs-verse.md`, summary in `why-lapis.md` §3. Verse's two-decade lineage (Ontic's
committed choice → λℵ's set-theoretic single-term language → the untyped Verse calculus)
converges with Lapis on rejecting the primitive conditional, but the foundations are incompatible:
**types-as-predicates (sets) vs types-as-shapes (μF/νG)** — a set has no recursion structure, so a
terms-only foundation deletes fold/unfold, the bialgebra, and the law machinery Lapis exists to
build (λℵ's own undecidability wall is the cautionary precedent). Verse makes logic, failure, and
time ambient in one unified calculus with a fixed closed effect vocabulary and per-effect totality
(`converges` sublanguage); Lapis stratifies — failure is data, logic is a fixpoint fragment, time is
external (Mealy driver) — with unconditional totality. The compatible residue: the *phase
distinction* (types-as-shapes govern elaboration; types-as-predicates — contracts, law screens,
`instanceof` — govern the live runtime), already Lapis's implicit practice, now stated explicitly.
Verse has no algebraic-law story; the exploitation tier is unoccupied there too.

## Evaluation model

- Eager data (μ), lazy codata (ν). Fixed by declaration kind — NOT a user knob.
- Church–Rosser invoked to justify compiler rewrites _within_ each strategy (confluence for
  terminating reductions).
- Strictness of data fields is part of the type. Lazy field = explicit `Lazy τ` (trivial codata
  wrapper) or behavior-typed field.
- Codata contracts (demands/rescue) are observation-gated — fire at observation time, not
  construction. State as feature.

## Effects

- Core is effect-FREE. Contracts (DbC) not effect systems (per lapis-js#113 analysis).
- rescue/retry elaborate to `Result`-typed core terms (sum of success/failure + retry counter).
- IO is a Mealy machine — pure data value `{init, request, respond}` interpreted by runtime. IO is
  data, not an effect.
- 20% gap (deferred exec, multi-shot continuations, nondeterminism) parked in `query`/future `Amb`.

## Laws: static where possible, dynamic when needed

- Type soundness (Progress/Preservation) is static + total — proved for fold/unfold typing,
  independent of law truth.
- Law soundness is a SEPARATE theorem, best-effort: compiler discharges statically what it can,
  runtime sample-checking (LawError) for rest.
- **Law authority is the provenance ladder (resolved 2026-09-12).** No third-party certification:
  Model B (external Coq/Agda/Lean certificates) is **rejected** — the trust anchors are the
  language definition and the programmer's own declarations, exactly the trust already extended
  by using the language. Every law in `E` is an axiom carrying a **provenance tag**:

  - **`primitive`** — the language definition pins builtin operations with fixed law sets
    (e.g. `Nat.+ : associative, commutative, identity:Zero`). Authority: language fiat; the TCB
    is the language implementation, the same trust already granted for totality/evaluation.
    The primitive tier is also the **axiom base** for derivations: composite laws over folds
    built from primitives are derivable via BMF calculational rules (fold-fusion etc.).
  - **`discharged`** — the compiler establishes the law itself, via three mechanisms:
    1. *Finite-domain exhaustion*: for genuinely finite types (Bool, enums, records of
       finites) the entire input space is checked — a **proof, not a screen**.
    2. *Bounded-domain exhaustion for machine-finite types*: `Float`/`Int`/`Char` are
       pattern-matched data over fixed alphabets and fixed encodings (binary64 has exactly 2⁶⁴
       inhabitants, including `Inf`/`NaN` as in-domain values). Full-domain enumeration is
       possible in principle; sub-space enumeration **certifies the checked space**.
    3. *Derivation*: law schemas proved from primitive laws + fold-induction skeletons
       (the BMF calculus as the discharge engine).
  - **`asserted`** — programmer declaration, screened (falsifies, never establishes). The honest
    residual: laws on unbounded-depth types (List/Tree-shaped μ-types) whose handler bodies
    call non-primitive, non-discharged operations in semantically essential ways.

  Soundness of `↝` is **relative to E**, and the trust boundary corresponds to a theorem: laws in
  the `discharged`/`primitive` tiers are established unconditionally (by the discharge
  mechanism); only `asserted` laws carry declaration risk. A rare false `asserted` law (e.g. a
  fold that collapses at a hidden threshold — expressible despite totality, since the cage
  constrains recursion shape, not handler-body semantics) corrupts rewrites silently, which is
  why the residual carries visible provenance plus the observation channel below.
- **Rice-style undecidability bounds the discharge fragment; it does not erase it.** Totality
  does NOT make extensional properties decidable in general (equivalence of total programs is
  still undecidable for expressive total calculi). But the correct question is *which* extensional
  properties of this particular calculus are decidable — and the cage carves out the non-empty
  fragments above (exhaustion, derivation) that no general-purpose language possesses.
- **Laws are environments, not terms.** The core acquires an operation signature environment `Ω`
  and an equational theory environment `E` (peers of `Γ`/`Δ`), plus a named operation application
  form `op(t₁, ..., tₙ)` — definitional sugar whose definition `Ω` carries. Laws live in `E`,
  attached to the operation _name_, never in the term grammar. Laws generate an equational theory
  (`≡`), never evaluation steps: AC-laws as reduction rules would immediately nonterminate
  (oscillation). The optimizer uses directed consequences (`↝`) of `≡` — the direction is a
  compiler strategy, not semantics. See `_docs/theory/lc.md` §7. (`Σ` stays reserved for the
  unfold seed type per lc.md §2.5.)
- **Operation identity must survive elaboration.** Surface operator use elaborates to
  `op(t₁, ..., tₙ)`, not to an anonymous lambda — otherwise `let`-inlining erases the very identity
  an optimizer needs to recognize two applications of the same algebraic operation. This is the
  one core-syntax concession laws require; it is sugar over ordinary application, so the core
  stays computation-minimal.
- **Closed law vocabulary.** Users declare membership in a fixed catalog (associative,
  commutative, identity, idempotent, involutory, distributive, absorbing) — never arbitrary
  equations. Arbitrary user equations would import the full equational-theory problem space
  (matching modulo AC, critical pairs, undecidable equality) into the compiler.
- **Intrinsic vs. relational laws.** One-operation laws (associative, ...) vs. two-operation
  relations (distributive:g) are distinct in the core representation — different axiom schemas,
  different screening arities.
- Core carries law _declarations_ as constraints, not proofs. Checking strategy is per-law,
  per-mode. The verification ladder is `asserted` (screening, the floor) → `discharged`
  (exhaustion + derivation — algorithmic because the induction motive is fixed by the fold
  schema) → `primitive` (language fiat). Provenance upgrades evidence; it never gates declaration.
  Lapis does not compete with proof assistants on arbitrary theorems (unstatable without
  dependent types, excluded by F<:); it substitutes for them on catalog claims — see
  `_docs/theory/lapis-vs-provers.md`.
- **Runtime observation as the fourth channel (live-image mode).** No finite evidence
  establishes a universal law, but a live system accumulates it: the property harness
  continuously re-screens declared laws against actual usage, building per-operation evidence
  profiles; an observed counterexample **withdraws** the axiom from `E` at runtime (checked mode),
  making bad library laws self-limiting rather than silently corrupting. For `asserted` laws on
  unbounded-depth types this is the only additional evidence channel that exists — something
  neither Coq nor Haskell can do, possible only because Lapis is a live system with an executable
  theory. Package-boundary trust policy (which tiers a build may exploit from dependencies) is a
  follow-up decision, not v0.3.0.
- Leaves room for Lapis as a Programming Language System (Smalltalk/DBMS family): live-image mode
  with runtime checking.
- **Parser associativity ≠ algebraic associativity.** The parser groups binary operators
  left-associatively (a syntactic convention); `associative` declares a semantic equivalence
  between the two groupings. Documented explicitly to prevent confusion — see lc.md §7.3.
- **`Ω` is acyclic by construction (cycles × growth).** Named operations reintroduce a call
  graph; unguarded cyclic op references would reintroduce general recursion through `Ω` with no
  syntactic witness of a decreasing measure — the Charity-style per-program semantic checker this
  language deliberately does not have. Rule: **an operation may only reference operations
  declared earlier in `Ω`** — a decidable dependency-graph condition checked once per
  declaration, the same stratification family as Datalog's negation stratification. The framing:
  unsafe recursion = **cycles × value growth**. Datalog forbids growth, keeps cycles (finite
  active domain ⇒ finite lattice ⇒ monotone ascent to lfp — termination and PTIME by
  construction). Lapis requires growth (constructors are the point; μ-types are initial
  algebras) and so forbids cycles. The two moves are dual. Lapis already runs the Datalog
  argument where it applies: `relation`/`closure` is a fixpoint engine over the finite
  span-projection space, cycles included.
- **Cost is analyzable: certified vs. flagged (the cost algebra).** Totality guarantees
  termination, not feasibility — but container-shaped recursion (a fold's recursion tree
  isomorphic to its input structure, independent of handler bodies) makes a **cost/depth
  algebra** mechanically computable over terms. The stratified fragment (no value-size feedback)
  is **certified** — its primitive-recursive/polynomial bounds close by recurrence; affine
  constructor use extends certification (Hofmann LFPL). The residual — higher-order
  result-size feedback, the Ackermann shape — is undecidable in general (the correctly-stated
  Rice wall) and is **flagged** statically, then observed at runtime (profiling — the same
  certified/flagged split as law provenance). See `_docs/theory/semantics.md` §5.5.

### Quotient types (open — deferred)

- **The gap.** Data equality is structural; codata equality is bisimulation (already a coinductive
  quotient); terms have `≡`. Missing: **quotient μ-types** `T // ≈` — data types whose elements
  are equivalence classes of a user-declared relation (Nuprl, Hofmann). Without them, laws are
  optimizer-visible but never runtime-observable (`equals(Bag(1,2,3), Bag(3,1,2))` is false
  without hand-written canonicalization), and law-bearing folds lack their natural denotation:
  the initial (Ω,E)-algebra — the term algebra quotiented by declared laws.
- **Position (tentative, not v0.3.0).** Lapis's enforcement already makes quotients _definable_
  (the relation `≈` is a fold; the canonicalizer is a fold); the missing piece is _declaring_
  them. Two candidate mechanisms reuse machinery already on the books:
  1. **Well-definedness as a screened algebraic claim (Model A).** Eliminating from `T // ≈`
     requires proving `x ≈ y ⟹ f(x) = f(y)` in Nuprl/Coq-style systems. Lapis would make
     "this fold respects `≈`" a law-vocabulary claim (`respect: #equalsOp`), screened by
     sampling, trusted as an axiom in `E` — the same authority model as every other law, no
     proof obligations. This is the distinctive option; no mainstream language has it.
  2. **Canonical forms as computational content.** The directed rewrites (`↝`) normalize to
     representative terms, so `T // ≈` has decidable equality and efficient hashing/dedup —
     avoiding the setoid tax (relations threaded through every signature, no canonical
     representation).
- **Open sub-questions** (see `semantics.md` §9.9): cross-theory congruence for elimination into
  another quotient; interaction of `≈` with `equals`-as-a-fold, hashing, memoization; quotient
  subtyping (`T // ≈` vs `T // ≈'`) — no standard treatment exists; coinductively-defined `≈`.

## No primitive conditional

- Boolean is a data type: `Bool = μ α. (True | False)`.
- `ifTrue:ifFalse:` is a fold over Bool. No primitive `if` in core. "No conditional" claim literally
  true.

## No base types — everything is μ or ν (pattern-matched data)

- Base types (`ι` in the calculus: `Int`, `String`, `Bool`, ...) are **eliminated**. All types are
  `μ` (data) or `ν` (codata).
- `Bool` = `data Bool (True | False)` — named constructors, zero fields.
- `Nat`, `Int`, `String`, `Complex`, `Rational`, etc. = `data` types with **pattern-matched
  constructors** (a compact specification of an infinite constructor set).
- **Pattern language**: restricted regular fragment with type references — character literals,
  character classes `[...]`, negated classes `[^...]`, any character `.`, quantifiers `+ * ?`,
  escape `\`, type reference `<TypeName>` (pattern interpolation — match the pattern of another data
  type here). NO alternation `|` (use multiple variants), NO groups `()`, NO anchors, NO
  backreferences. Compiles to a DFA for flat patterns; type references make it context-free (handled
  by the zipper-grammar engine's lazy recursion). Longest match wins; declaration order breaks ties.
- **Pattern constraints**: patterns match contiguous characters. A pattern may consume whitespace if
  its structure includes it (via `.`, `[^...]`, character classes containing space, or delimited
  regions). Whitespace that no pattern consumes is a token boundary (fallback). Patterns must be
  **anchored** — must start with a specific literal character or character class (not `.*` or `*` or
  `?`); a pattern starting with `.` is allowed only if preceded by a literal delimiter (e.g., `".*"`
  is fine; bare `.*` is rejected). This is how lexers work: undelimited patterns (like `[0-9]+`)
  naturally exclude space; delimited patterns (like `"<Char>*"`) naturally include it.
- **Metacharacters** (must be escaped with `\` when meant literally): `+ * ? [ ] \ . < >`. `.` = any
  single character. `<TypeName>` = type reference (non-terminal). `\<` and `\>` = literal angle
  brackets.
- **Bootstrapping order**: alphabet (primitive — input domain, not a type) → `Token` (primitive: raw
  matched text, the one non-μ type) → `Char` (`.` — any single character) → `String` (`"<Char>*"` —
  quoted sequence of Chars) → `Nat` (`[0-9]+`) → `Int` (`-[0-9]+` and `[0-9]+`) → `Bool` (named) →
  operators on `Nat`/`Int` → everything else.
- **Pattern-matched folds are flat**: no `Family` fields, no recursion. The fold is a single-step
  extraction: the handler receives the matched token (implicit `match` field) and transforms it.
  Recursion depth 1.
- **Mixed constructors**: a `data` type can have both pattern constructors (terminals/leaves) and
  named constructors (non-terminals/recursive). The `data` declaration _is_ a grammar production;
  the `fold` is the semantic action. This is grammar-as-semantics at the language level.
- **Lexer priority**: patterns > operators > identifiers. Within each phase, longest match wins;
  ties broken by declaration order. Named constructors take precedence over patterns when both could
  match (more specific).

## Symbolic operation names and uniform binary precedence

- Operation names (fold names) can be **symbolic**: `+`, `-`, `*`, `<`, `<=`, `==`, etc. Following
  the Smalltalk binary selector convention. Multi-character, longest match among declared operators.
- **Position discriminates data from operations**: prefix (contiguous, start of token) =
  pattern-matched constructor (data introduction). Infix (between whitespace-delimited tokens,
  message-send position) = symbolic operation (fold/elimination). The lexer alternates between
  "expecting a token" (prefix — try patterns > identifiers > named constructors) and "expecting an
  operator" (infix — try operators > identifiers for named sends). Whitespace is consumed between
  tokens in both modes.
- **Operation name rules**: symbolic (`+`, `<=`, `<+>`, `<>`, `==`) or named (`add`, `lessThan`). No
  spaces — an operation name is a contiguous sequence of non-whitespace characters. Can include
  grouping characters (`<`, `>`, `(`, `)`, `[`, `]`, `{`, `}`) as part of the name. Recognized in
  infix position only. Longest match among declared operators. **Can never be patterns** — they're
  in a different lexical context (expression level, not pattern level). Character set for symbolic
  operators: any non-whitespace, non-alphanumeric character; multi-character operators are sequences
  of these.
- **Naming convention**: PascalCase prefix = named constructor. Symbolic prefix (no whitespace) =
  pattern-matched constructor. camelCase infix = named operation. Symbolic infix = symbolic
  operation.
- **Uniform binary precedence** (Smalltalk model): ALL binary messages have the same precedence.
  Evaluated strictly left-to-right. `1 + 2 * 3` parses as `(1 + 2) * 3 = 9`. Explicit parentheses
  required for mathematical grouping: `1 + (2 * 3) = 7`. NO configurable or hierarchical operator
  precedence. Precedence between message _types_ (unary > binary > keyword) is retained.
- **Escaping in patterns**: special characters (`+ * ? [ ] \`) are escaped with `\` when meant
  literally. E.g., `[0-9]+\+[0-9]+j` for complex numbers — the `\+` is a literal `+` inside the
  token, while the unescaped `+` after `[0-9]` is the quantifier.

## Attribute grammars + zipper-grammar (renamed from derivative-parser)

- Parser library now published to JSR as `@lapis-lang/zipper-grammar@4.1.0`.
- v2.1.0 adds: `chain` (monadic bind) for L-attributed one-pass parsing, grammar-native contracts
  (`@requires`, `@ensures`, `@invariant`, `@rescue`), `diagnostic()` for failure reporting.
- v2.2.0 adds: `_forward` (higher-order attributes — one-pass evaluation via re-parsing substrings
  under extended context), `TreeExp`/`flattenTree`/`parseTree` (tree-consuming grammars for passes
  over already-built ASTs), standalone combinators (`sseq`, `plus`, `sepBy`, `between`, `trim`,
  `keyword`), lexeme helpers (`ws`, `ws1`, `digit`, `digits`, `ident`). The 2.2.0 API is a breaking
  change from 2.1.0 (combinators are standalone functions, not Grammar methods).
- v3.0.0 adds: typed contract predicates — `@requires`/`@ensures`/`@rescue` now infer
  `Parameters<F>` and `ReturnType<F>` from the decorated method, and `old` is typed as
  `OldSnapshot<This>` (data-only snapshot, excluding function-valued keys). Full type safety on
  arguments and results in contract predicates.
- Two patterns for semantics: (1) multi-pass via `super` (subclass calls super.expr.map(evalFn)),
  (2) one-pass judgments-as-productions via `@rule expr(Γ): Parser<Type>` with `chain` for
  left-sibling synthesized → right-sibling inherited flow. With 2.2.0's `_forward`, evaluation is
  also one-pass (closures re-parse body via `_forward`); tree-consuming grammars handle passes over
  ASTs.
- Grammar-class subtyping = natural layering for semantic passes: base grammar (syntax) → subclass
  (name resolution) → subclass (type check) → subclass (law check) → subclass (evaluation). Each
  pass inherits productions it doesn't override.
- Lapis's enforced structure means hard type-theory cases DON'T ARISE: no polymorphic recursion (no
  general recursion, declared result types), no let-generalization (subtyping not generics), `super`
  gives complete AST node (no bidirectional flow needed).
- See zipper-grammar `examples/stlc.ts` for headline example: STLC with 4 interpretations (AST, type
  checker, evaluator, proof-bearing) over one abstract grammar.

## Deno migration (completed 2026-07-25)

- Project converted from Node/TypeScript (.mts + package.json + tsconfig.json) to Deno (.ts +
  deno.json).
- All imports: `.mjs` → `.ts` (relative), `@lapis-lang/derivative-parser` →
  `jsr:@lapis-lang/zipper-grammar`.
- `deno check src/index.ts` passes clean.
- Devcontainer: `.devcontainer/devcontainer.json` (Ubuntu 24.04 + Deno feature + VS Code Deno
  extension).
- `deno.json` has tasks: check, test, build (deno compile → exe), fmt, lint.
- `minimumDependencyAge: "0"` in deno.json (zipper-grammar was freshly published).

## Implementation staging (see language-design.md §5)

- Stage 0: resolve foundational Qs (doc-only) — core calculus typing rules + soundness sketch
- Stage 1: minimal core (data+fold, behavior+unfold) parse→typecheck→eval, tree-walker
- Stage 2: subtyping + protocols
- Stage 3: recursion schemes (map/merge/scan/para/histo/zygo) as elaborations
- Stage 4: relation/query/io as sugar
- Stage 5: contracts + laws
- Stage 6: graph-reduction backend + GC
- Stage 7: modules + language-system mode

## Open questions (core)

1. Fold dispatch: dynamic (method on prototype, comb chain) vs static (match on tag)? Prototype
   dynamic; LC written static. Reconcile in elaboration.
2. Equality: structural for μ, bisimulation for ν. Formalize = and ≈.
3. Strictness: Lazy τ explicit wrapper recommended.
4. Multi-sorted: simultaneous μ-bindings for mutual recursion.
5. Intersection types: first-class vs elaboration-time constraints? "Static where possible" suggests
   constraints by default, first-class in live-image mode.
6. **Pattern constructors with captures (tentative).** A pattern constructor could have named
   captures (`<name: TypeName>`) that extract sub-matches as typed fields, paralleling named
   constructor fields. E.g., `Rect <real: Nat>\+<imag: Nat>j` for `Complex`. The captures would be
   the fields, bound in fold handlers by the constructor name. This is conceptually sound (the
   pattern is a parser, captures are semantic values) but the syntax and handler-dispatch mechanics
   need validation against a real implementation. Deferred until Stage 1.
7. **Blame in the calculus?** Contracts currently elaborate to folds over `Bool` and `Result` —
   blame is a runtime concern, not a calculus concern. Wadler's blame calculus ("Well-typed programs
   can't be blamed", 2009) makes blame labels first-class core entities, enabling the blame theorem
   to be proved at the calculus level. Lapis's contracts are richer (DbC with `rescue`, LSP
   subcontracting tied to the subtyping lattice), and the interaction of subtyping + contracts +
   blame may require calculus-level support. Deferred to Stage 5 (contracts + laws).
