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
- **No generics, no type parameters — permanently.** Subtyping is the _sole_ abstraction mechanism,
  not a substitute waiting to be swapped back (Meyer OOSC, Bracha). Comb inheritance + field
  narrowing is the mechanism, and the surface has **no type-variable production and no parameter
  list on any declaration** (`src/surface/grammar.ts`). There is no `data List<a>`, no `t[τ]` in
  type position, and no `typeParam:` spec key. This is a closed decision: the calculus stays F<:,
  and no future proposal reopens it. Where a generic type would appear, one of three existing forms
  does the work instead — a **subtype** with narrowed fields, the declaring type itself (`Self`), or
  the lattice top **`Any`**.
- Cost: loss of parametricity. Recovered _by declaration_ via `properties` annotations (associative,
  idempotent, etc.). `properties` is the price paid for subtyping-over-generics.
- No general fixpoint. Recursion only via fold (terminating, data finite) and unfold (productive,
  guarded). Sized-types story specialized to bialgebraic setting.
- **Data folds are bottom-up; codata unfolds are top-down.** A variant arm runs _after_ its
  recursive children have been folded, so a `Family` binding holds the **already-computed result**
  of the subterm, never the subterm itself — `Succ pred: Family` is bound to a value of the fold's
  result type σ (`lc.md` §5.2, `tᵢ : Fᵢ(σ)[α := σ] → σ`). `unfold` is the dual: a generator runs at
  the observation that demands it, so a recursive observer position is the seed's own type. The
  consequence that matters for source shape is that **recursion needs no self-reference**: the
  fold's induction _is_ the recursion, so `add` on `Nat` is `Succ pred -> Succ pred: pred` and a
  `size` on `List` is `Cons head rest -> Succ pred: rest`. The prototype's std reads the same way
  (`List.length` is `Cons({ tail }) { return 1 + tail; }`), and it is what makes `Ω`'s acyclicity
  rule (`lc.md` §2.5) sound rather than restrictive: a fold body never names its own operation.
  Reading one orientation into the other is the defect this records — a top-down reading of data
  makes recursive fields subterms (so `Succ(pred)` would rebuild a list), and a bottom-up reading of
  codata makes a generator's `self` an already-observed value rather than the seed.
- **An implementation's capture scan binds a `Family` field to `⊥`, never to the carrier.** Before
  `σ` is known the body's type is not available to decide anything, so whatever an arm's scan binds
  a recursive field to is a placeholder for `σₙ` and not a premise. `⊥` is the only admissible
  placeholder: `S-Bot` puts it below every type, so every premise the converged `σₙ` could satisfy
  is satisfiable during the scan, while the carrier (an upper bound on the field, which rejects
  `Succ(rest)` before the fixpoint runs) and `Any` (the wrong direction, since a `Nat` premise
  cannot accept it) both decide the fold early. Acceptance and rejection stay the fixpoint's — a
  body that cannot type under the converged `σ` is still rejected (`lc.md` §5.2).
- **A fold's result type is declared or inferred; it is never defaulted to `Any`.** `T-Fold`'s `σ`
  is the fixpoint `⨆ᵢ type of tᵢ` seeded at `⊥` (`lc.md` §5.2) — the join's identity, so the arms'
  common type is the result. The limit is the **join**, so arms with no common supertype below `Any`
  make the fold `Any`; that is the typing rule and it does not change. What changes at the surface
  is that an omitted `out:` is **inferred** as that LUB, and an inference landing on `Any` from
  _disagreement_ is **reported**, not admitted. The reason is the direction of subtyping: `Any` is
  the top, so an entry typed `Nat → Any` is substitutable into no narrower position and its declared
  result says nothing about its arms — a caller cannot use the value where the arms' type is wanted.
  Writing `out: Any` makes that an explicit decision. An arm that is itself `Any`-typed is the
  honest case and is accepted, since `join` collapses the two into `Any` and only the arms can tell
  them apart. A **declared** `out:` is a premise on every arm, checked case by case so the
  diagnostic names the arm and its type rather than the join's `Any`. `elaboration.md` §1.3 states
  both rules; `T-Fold` is unchanged.
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

1. **F<:, not Fω.** No higher-kinded polymorphism, and **no generics at any kind**. Subtyping is the
   sole abstraction mechanism (Meyer, Bracha); protocols are predicates over the subtyping lattice,
   not type-constructors. The cost — loss of parametricity — is recovered _by declaration_ via
   `properties`. Permanent: no surface type-variable or type-parameter production exists or will.

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
committed choice → λℵ's set-theoretic single-term language → the untyped Verse calculus) converges
with Lapis on rejecting the primitive conditional, but the foundations are incompatible:
**types-as-predicates (sets) vs types-as-shapes (μF/νG)** — a set has no recursion structure, so a
terms-only foundation deletes fold/unfold, the bialgebra, and the law machinery Lapis exists to
build (λℵ's own undecidability wall is the cautionary precedent). Verse makes logic, failure, and
time ambient in one unified calculus with a fixed closed effect vocabulary and per-effect totality
(`converges` sublanguage); Lapis stratifies — failure is data, logic is a fixpoint fragment, time is
external (Mealy driver) — with unconditional totality. The compatible residue: the _phase
distinction_ (types-as-shapes govern elaboration; types-as-predicates — contracts, law screens,
`instanceof` — govern the live runtime), already Lapis's implicit practice, now stated explicitly.
Verse has no algebraic-law story; the exploitation tier is unoccupied there too.

## Evaluation model

- Eager data (μ), lazy codata (ν). Fixed by declaration kind — NOT a user knob.
- Church–Rosser invoked to justify compiler rewrites _within_ each strategy (confluence for
  terminating reductions).
- Strictness of data fields is part of the type. Lazy field = explicit `Lazy τ` (trivial codata
  wrapper) or behavior-typed field.
- **Application is call-by-value.** The eager/lazy split above is a _field and generator_ strategy;
  it does not change the application rule. Totality removes call-by-name's classical motive (a
  well-typed argument cannot diverge), and the two surviving pressures both favour CBV: the cost
  algebra is stated over evaluated arguments (`cost.ts`), and contract firing order must be statable
  — `demands:` on an unused argument fires at the call site. See §"Function values".
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
  Model B (external Coq/Agda/Lean certificates) is **rejected** — the trust anchors are the language
  definition and the programmer's own declarations, exactly the trust already extended by using the
  language. Every law in `E` is an axiom carrying a **provenance tag**:

  - **`primitive`** — the language definition pins builtin operations with fixed law sets (e.g.
    `Int.+ : associative, commutative, identity: 0`). Authority: language fiat; the TCB is the
    language implementation, the same trust already granted for totality/evaluation. The primitive
    tier is also the **axiom base** for derivations: composite laws over folds built from primitives
    are derivable via BMF calculational rules (fold-fusion etc.).
  - **`discharged`** — the compiler establishes the law itself, via three mechanisms:
    1. _Finite-domain exhaustion_: for genuinely finite types (Bool, enums, records of finites) the
       entire input space is checked — a **proof, not a screen**.
    2. _Bounded-domain exhaustion for machine-finite types_: `Float`/`Int`/`Char` are
       pattern-matched data over fixed alphabets and fixed encodings (binary64 has exactly 2⁶⁴
       inhabitants, including `Inf`/`NaN` as in-domain values). Full-domain enumeration is possible
       in principle; sub-space enumeration **certifies the checked space**.
    3. _Derivation_: law schemas proved from primitive laws + fold-induction skeletons (the BMF
       calculus as the discharge engine). **Implemented** — `src/core/derivation.ts`: the bounded,
       search-free discharger; the derivable fragment is defined by what the engine closes (the
       characterization), and an `asserted` law is never an axiom step (no laundering).
  - **`asserted`** — programmer declaration, screened (falsifies, never establishes). The honest
    residual: laws on unbounded-depth types (List/Tree-shaped μ-types) whose handler bodies call
    non-primitive, non-discharged operations in semantically essential ways.

  Soundness of `↝` is **relative to E**, and the trust boundary corresponds to a theorem: laws in
  the `discharged`/`primitive` tiers are established unconditionally (by the discharge mechanism);
  only `asserted` laws carry declaration risk. A rare false `asserted` law (e.g. a fold that
  collapses at a hidden threshold — expressible despite totality, since the cage constrains
  recursion shape, not handler-body semantics) corrupts rewrites silently, which is why the residual
  carries visible provenance plus the observation channel below.
- **Rice-style undecidability bounds the discharge fragment; it does not erase it.** Totality does
  NOT make extensional properties decidable in general (equivalence of total programs is still
  undecidable for expressive total calculi). But the correct question is _which_ extensional
  properties of this particular calculus are decidable — and the cage carves out the non-empty
  fragments above (exhaustion, derivation) that no general-purpose language possesses.
- **Laws are environments, not terms.** The core acquires an operation signature environment `Ω` and
  an equational theory environment `E` (peers of `Γ`/`Δ`), plus a named operation application form
  `op(t₁, ..., tₙ)` — definitional sugar whose definition `Ω` carries. Laws live in `E`, attached to
  the operation _name_, never in the term grammar. Laws generate an equational theory (`≡`), never
  evaluation steps: AC-laws as reduction rules would immediately nonterminate (oscillation). The
  optimizer uses directed consequences (`↝`) of `≡` — the direction is a compiler strategy, not
  semantics. See `_docs/theory/lc.md` §7. (`Σ` stays reserved for the unfold seed type per lc.md
  §2.5.)
- **Operation identity must survive elaboration.** Surface operator use elaborates to
  `op(t₁, ..., tₙ)`, not to an anonymous lambda — otherwise `let`-inlining erases the very identity
  an optimizer needs to recognize two applications of the same algebraic operation. This is the one
  core-syntax concession laws require; it is sugar over ordinary application, so the core stays
  computation-minimal.
- **Closed law vocabulary.** Users declare membership in a fixed catalog (associative, commutative,
  identity, idempotent, involutory, distributive, absorbing) — never arbitrary equations. Arbitrary
  user equations would import the full equational-theory problem space (matching modulo AC, critical
  pairs, undecidable equality) into the compiler.
- **Intrinsic vs. relational laws.** One-operation laws (associative, ...) vs. two-operation
  relations (distributive:g) are distinct in the core representation — different axiom schemas,
  different screening arities.
- Core carries law _declarations_ as constraints, not proofs. Checking strategy is per-law,
  per-mode. The verification ladder is `asserted` (screening, the floor) → `discharged`
  (exhaustion + derivation — algorithmic because the induction motive is fixed by the fold schema) →
  `primitive` (language fiat). Provenance upgrades evidence; it never gates declaration. Lapis does
  not compete with proof assistants on arbitrary theorems (unstatable without dependent types,
  excluded by F<:); it substitutes for them on catalog claims — see
  `_docs/theory/lapis-vs-provers.md`.
- **Runtime observation as the fourth channel (live-image mode).** No finite evidence establishes a
  universal law, but a live system accumulates it: the property harness continuously re-screens
  declared laws against actual usage, building per-operation evidence profiles; an observed
  counterexample **withdraws** the axiom from `E` at runtime (checked mode), making bad library laws
  self-limiting rather than silently corrupting. For `asserted` laws on unbounded-depth types this
  is the only additional evidence channel that exists — something neither Coq nor Haskell can do,
  possible only because Lapis is a live system with an executable theory. Package-boundary trust
  policy (which tiers a build may exploit from dependencies) is a follow-up decision, not v0.3.0.
- Leaves room for Lapis as a Programming Language System (Smalltalk/DBMS family): live-image mode
  with runtime checking.
- **Parser associativity ≠ algebraic associativity.** The parser groups binary operators
  left-associatively (a syntactic convention); `associative` declares a semantic equivalence between
  the two groupings. Documented explicitly to prevent confusion — see lc.md §7.3.
- **`Ω` is acyclic by construction (cycles × growth).** Named operations reintroduce a call graph;
  unguarded cyclic op references would reintroduce general recursion through `Ω` with no syntactic
  witness of a decreasing measure — the Charity-style per-program semantic checker this language
  deliberately does not have. Rule: **an operation may only reference operations declared earlier in
  `Ω`** — a decidable dependency-graph condition checked once per declaration, the same
  stratification family as Datalog's negation stratification. The framing: unsafe recursion =
  **cycles × value growth**. Datalog forbids growth, keeps cycles (finite active domain ⇒ finite
  lattice ⇒ monotone ascent to lfp — termination and PTIME by construction). Lapis requires growth
  (constructors are the point; μ-types are initial algebras) and so forbids cycles. The two moves
  are dual. Lapis already runs the Datalog argument where it applies: `relation`/`closure` is a
  fixpoint engine over the finite span-projection space, cycles included.
- **Cost is analyzable: certified vs. flagged (the cost algebra).** Totality guarantees termination,
  not feasibility — but container-shaped recursion (a fold's recursion tree isomorphic to its input
  structure, independent of handler bodies) makes a **cost/depth algebra** mechanically computable
  over terms. The stratified fragment (no value-size feedback) is **certified** — its
  primitive-recursive/polynomial bounds close by recurrence; affine constructor use extends
  certification (Hofmann LFPL). The residual — higher-order result-size feedback, the Ackermann
  shape — is undecidable in general (the correctly-stated Rice wall) and is **flagged** statically,
  then observed at runtime (profiling — the same certified/flagged split as law provenance). See
  `_docs/theory/semantics.md` §5.5. **Implemented in `src/core/cost.ts`**: the polynomial-form
  expression algebra, the recurrence solver (the recursion variable must appear BARE in the step — a
  symbolic factor riding it is multiplicative feedback, which does NOT close: the certificate states
  the recurrence coarsely rather than a false linear bound), the memoized op summaries, `CostEngine`
  (the grammar-subclass vehicle) and `CostPass extends SemanticPass` (the derivation-tree entry),
  with the flag's payload (the feedback edge, the missing bound, the suggested runtime profile) in
  `test/cost.test.ts`.

### Quotient types (open — deferred)

- **The gap.** Data equality is structural; codata equality is bisimulation (already a coinductive
  quotient); terms have `≡`. Missing: **quotient μ-types** `T // ≈` — data types whose elements are
  equivalence classes of a user-declared relation (Nuprl, Hofmann). Without them, laws are
  optimizer-visible but never runtime-observable (`equals(Bag(1,2,3), Bag(3,1,2))` is false without
  hand-written canonicalization), and law-bearing folds lack their natural denotation: the initial
  (Ω,E)-algebra — the term algebra quotiented by declared laws.
- **Position (tentative, not v0.3.0).** Lapis's enforcement already makes quotients _definable_ (the
  relation `≈` is a fold; the canonicalizer is a fold); the missing piece is _declaring_ them. Two
  candidate mechanisms reuse machinery already on the books:
  1. **Well-definedness as a screened algebraic claim (Model A).** Eliminating from `T // ≈`
     requires proving `x ≈ y ⟹ f(x) = f(y)` in Nuprl/Coq-style systems. Lapis would make "this fold
     respects `≈`" a law-vocabulary claim (`respect: #equalsOp`), screened by sampling, trusted as
     an axiom in `E` — the same authority model as every other law, no proof obligations. This is
     the distinctive option; no mainstream language has it.
  2. **Canonical forms as computational content.** The directed rewrites (`↝`) normalize to
     representative terms, so `T // ≈` has decidable equality and efficient hashing/dedup — avoiding
     the setoid tax (relations threaded through every signature, no canonical representation).
- **Open sub-questions** (see `semantics.md` §9.9): cross-theory congruence for elimination into
  another quotient; interaction of `≈` with `equals`-as-a-fold, hashing, memoization; quotient
  subtyping (`T // ≈` vs `T // ≈'`) — no standard treatment exists; coinductively-defined `≈`.

## No conditional — branching is structural dispatch

- `Bool` is a data type: `Bool = μ α. (True | False)`, and it appears in **result position only**. A
  predicate eliminates a meaningful type and produces a verdict (`fold isWarm <out: Bool>`); `Bool`
  is never a declaration site.
- **There is no named eliminator for `Bool`** and no sugar for one. An operation declared on `Bool`
  that returns its two outcomes takes them as parameters — it discards its eliminated structure and
  has nothing to dispatch on, inverting the rule that every operation is declared inside the type it
  eliminates.
- **Branching takes two forms, both structural.** Fold arms dispatch on a variant, so the arm keying
  is the decision. Unfold arms decide on a seed — `guard | payload`, first match wins.
- **A decision with no discriminating variants is a decision on a seed**, so it belongs in an unfold
  over a declared seed type, never in a fold arm's body (`syntax-design.md` §"Behavior").
- **Fold arms stay order-free.** Guards on fold arms were considered and rejected: no corpus arm
  needs one, and they would make arms a first-match chain, spending exhaustiveness checking, the
  per-variant induction skeleton (`derivation.ts`), and variant-keyed inheritance (#86). `unfold`
  escapes this because generators are first-match by construction.

## No base types — everything is μ or ν (pattern-matched data)

- Base types (`ι` in the calculus: `Int`, `String`, `Bool`, ...) are **eliminated**. All types are
  `μ` (data) or `ν` (codata).
- `Bool` = `data Bool (True | False)` — named constructors, zero fields.
- **A value spelling is a declared constructor's name.** There is no special-value category: no
  `nil`, no reserved `true`/`false`. A literal is whatever text a declared pattern matched, and
  every other value is written as the constructor that builds it (`True`, `False`, a declared
  `Nil`). The consequence is that an undeclared name denotes nothing rather than being a value the
  language supplies — the same rule that stops an unknown type name from minting a `TypeVar`
  (`overview.md` §12.29, §12.69). A null value specifically has no denotation to give: the calculus
  has no such term (`lc.md` has no `nil`), and `Nothing` is the uninhabited bottom type, so a
  spelling for it could only ever mean "nothing at all".
- `Int`, `String`, `Complex`, `Rational`, etc. = `data` types with **pattern-matched constructors**
  (a compact specification of an infinite constructor set). `Int`'s one pattern is `-?[0-9]+`,
  covering both signs.
- `Nat` = `data Nat (Zero | Succ pred: Family)` — a **named** Peano carrier, not a pattern type. It
  carries the integer story where a definition is required of the _language_ rather than of the
  lexer, and it is what the law suite's `add` is declared over. There is no `Nat <: Int`: pattern
  subtyping requires the subtype to declare every pattern source its super declares, and `Int`'s
  language is not `Nat`'s. See [`theory/prelude.md`](./theory/prelude.md) §2.4–§2.5.
- **Pattern language**: restricted regular fragment with type references — character literals,
  character classes `[...]`, negated classes `[^...]`, any character `.`, quantifiers `+ * ?`,
  escape `\`, type reference `<TypeName>` (pattern interpolation — match the pattern of another data
  type here). NO alternation `|` (use multiple variants), NO groups `()`, NO anchors, NO
  backreferences. Compiles to a DFA for flat patterns; type references make it context-free (handled
  by the lang-forma engine's lazy recursion). Longest match wins; declaration order breaks ties.
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
  matched text, the one non-μ type, core-only and not user-spellable) → `Char` (`'.'` — any quoted
  single character) → `String` (`"<Char>*"` — quoted sequence of Chars) → `Int` (`-?[0-9]+`) →
  `Bool` (named) → operators on `Int` → everything else. `Token` is deliberately absent from the
  _prelude_, which is the user-visible layer: the core needs it to type the `match` binding, and a
  program never names it (`theory/prelude.md` §2.1).
- **Pattern-matched folds are flat**: no `Family` fields, no recursion. The fold is a single-step
  extraction: the handler receives the matched token (implicit `match` field) and transforms it.
  Recursion depth 1.
- **Mixed constructors**: a `data` type can have both pattern constructors (terminals/leaves) and
  named constructors (non-terminals/recursive). The `data` declaration _is_ a grammar production;
  the `fold` is the semantic action. This is grammar-as-semantics at the language level.
- **Lexer priority**: patterns > operators > identifiers. Within each phase, longest match wins;
  ties broken by declaration order. Named constructors take precedence over patterns when both could
  match (more specific).
- **No collection literal.** A container value is a declared constructor, never a bracketed or
  braced spelling: `List`'s empty value is `Nil` and a non-empty one is `Cons …` / the `,` operator.
  There is no `{}` or `{a, b, c}` production, so no array literal, no list literal, and no array
  type to go with one (`prelude.md` §2.6 retires `Array`). The `,` operator is the only
  multi-element spelling, and it is a fold on `List` rather than sugar over one (`overview.md`
  §12.71).

## Comments and result annotations

- **Comments are `/* ... */` — nested block form.** Delimiters balance by counting (a comment may
  contain further `/* ... */` pairs); no escapes inside comments; the one writer rule: prose cannot
  contain an unbalanced `*/`. Consumed at statement boundaries before any token phase (the
  precedence whitespace already has); present in no term of any semantic grammar — comments cost
  nothing.
- **Value spellings reserved:** strings `"foo"` (`String = μ α. "<Char>*"` — `\"` inside, the
  `match("p")` convention), char values `'a'` (exactly one character; `\'` inside).
- **A comment's position is its grade.** Trailing after an expression = a _result annotation_ (a
  record of what it produces — documentation-grade, never checked by the language; the future
  checker is a doc-example harness). Own-line = a _prose comment_ describing the construct beneath
  it (forward association). The realization behind the grade rule: top-level source has no
  expression statements — trailing annotations are a doc-fragment device; the language's checked
  answer for result claims in real code is contracts (`ensures:`/`invariant:`/`demands:`).
- **Reservation rules (generalizing the letter-leading pattern rule):** a user-declared pattern's
  leftmost-matchable set (computed from its AST) must exclude `'` and `"` — reserved for the char
  and string value forms — AND its reserved two-character PREFIX language must exclude `/*`: a
  pattern whose matchable strings can begin with the comment opener is rejected (the prefix check
  walks the AST's per-position first-sets, so `/[0-9]` stays legal while `/*`-spelling shapes
  reject). Built-ins exempt (they define the spellings). Declared symbolic operation names may not
  contain `/*` or `*/` (the comment scanner runs at every boundary before lexical phases).
- **Retired:** the `"..."` comment form (the original §1.4 assumption — died when strings stayed
  double-quoted: a shared delimiter reintroduces the comment-vs-value ambiguity); a `comment ...`
  keyword (freezes descriptions into source — wrong channel for the Language-System roadmap;
  image-time association is the metaprogramming lane's mechanism, `language-design.md` §5 Stage 7).

## Program shape and name introduction

- **A program's top level is declarations only.** `program ::= declaration*` — no expression
  statements, and no definition/binding form. `name = expr` is **not** a production, at any level:
  `=` is an equality _operator_ (a declared fold name, §"Symbolic operation names"), so a definition
  spelling would also reintroduce the uniform-precedence footgun (`x = y + 1` grouping as
  `(x = y) + 1`). Trailing comments in the docs are documentation fragments — a doc-example harness
  device, never source (`surface-syntax.md` §1.4).
- **Names are declared, never bound.** A value name is introduced by a zero-field variant
  (`variantRef`, `src/surface/grammar.ts`). A computation name is introduced by an operation
  declaration — which is what makes it carry a declared type, membership in `Ω`, a law set
  (`properties:`), and a memoized cost summary. Nothing introduces a name by assignment: the core
  has `let` and no store (`lc.md` §3, `E-Let` and no `E-Assign`).
- **There is no arm-level binding form.** No `let … in`, no `name ::= expr` header, no
  initialised-slot block, and no default-valued block parameter used as a binder. Each candidate was
  rejected on its own terms:

  | Candidate                                | Rejected because                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
  | ---------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
  | `let … in`                               | Two keywords for zero new semantics — `T-Let`/`E-Let` is `λ`-application (`E-App`), so the form buys only spelling. `let` is not a declaration former and `in` is not an operation name; exposing both makes `in` a surface keyword for the first time (it is currently reserved only for the core's terminator) and adds a non-declaration grammar former to a language whose pitch is "your declarations are your lexer".                                                                            |
  | `name = expr` at arm level               | Steals `=`, a declared operator (same defect as the top-level form).                                                                                                                                                                                                                                                                                                                                                                                                                                   |
  | `name ::= expr` / `name := expr`         | Would be the only reserved _operator spelling_. `opIdent` is deliberately keyword- and shape-permissive (`grammar.ts`), and `LC_RESERVED_WORDS` is `["in"]` alone because every keyword position is positionally disjoint from operation application. An infix `::=` is not disjoint: `lo ::= x` is simultaneously a declaration line and a well-formed binary expression. It also silently settles the open operator-charset question (whether `:` is an operator character) by carving a hole in it. |
  | Initialised block head, `[x: 40 \| …]`   | Defaults are observable only at a call site, so the block must be _called_ — the surface has no application production (§10 open question 11). Auto-invoking a block in arm position would give one syntax two meanings by position. Worse, a block standing alone in an arm body has no expected type, so its parameter is typed `Any` (`elaboration.md` §2.3) — a regression from the checked type a declared operation carries.                                                                     |
  | `Let` constructor + infix `in` operation | The only candidate that reserves no vocabulary, but a runtime constructor cannot bind a name: binder names resolve at parse/elaboration time (`extendCtx`), so this requires names-as-values and an environment interpreter — contradicting "static where possible" and the ban on ambient scope, and requiring `Symbol` back (retired, `overview.md` §12.23) with its interning/equality and reference-vs-value collision unresolved.                                                                 |

- **An intermediate needed by an arm is a declared sibling operation.** Either a fold consumed by
  another fold, or a companion fused into the same traversal via `<aux: …>`. This is not a
  workaround: the declared form is strictly stronger (declared type, reuse, laws, cost summary,
  identity preserved through elaboration by `E-Op`). The quadratic formula is the canonical case —
  the discriminant is a `fold discriminant <out: Float>` and `roots` is `<aux: #discriminant>`
  (`examples/quadratic.lapis`). The corpus supports the rule: no worked example in `_docs/` needs a
  local except the two-root case, which `aux` already serves.
- **Revisit trigger.** Reifiable binding (a `Let` _value_, programs-as-data) is a Stage-7
  metaprogramming question, not a surface-syntax one. Any such proposal must first answer name
  interning and equality, and the `#name` reference-vs-value spelling collision — exactly the clause
  `overview.md` §12.23 leaves open for `Symbol`.

## Function values: no literal, no wrapper type

- **There is no block literal.** `[params | expr]` is removed from the grammar. It was the surface
  language's last anonymous binder: no top-level definition form, no `let … in`, and no arm-level
  binding remain (see the section above), so retiring it completes that rule rather than departing
  from it.
- **Why remove it at all.** The literal bought nothing the declared form does not: an operation
  reference carries a declared type, a `properties:` law set, membership in `Ω`, and a memoized cost
  summary (`lc.md` §2.2, `E-Op`); an anonymous lambda carries none of them. A block literal was also
  a thunk-by-hand in the one place (contracts) where the elaborator was already going to delay the
  body.
- **A function value is a value of function type.** Its type is the operation's curried signature, a
  `FunType` chain (`ops.ts`'s `OpSig.signature`) — there is no function-value type in the prelude,
  and no wrapper for a lambda to inhabit. An intermediate `Block<σ,τ>` codata type was considered
  and **rejected**: it would have needed type parameters to be writable, which §2.1 rules out, and
  it would have been uninhabited anyway, since an `unfold` cannot produce a `σ → τ` and an operation
  reference already _is_ one.
- **Applying a function value needs no production.** A keyword send already means "eliminate the
  receiver, then apply the arguments" (`elaboration.md` §2.5): `fold` eliminates data, **observation
  eliminates codata**, and **application eliminates a function type**. Application is therefore
  _derived_ rather than _added_ — there is no `expr expr` production and no `value:` suffix. **The
  surface cannot in fact reach it:** a surface type is `atomType` (`src/surface/grammar.ts`), so no
  declaration can state a function type and no expression can acquire a receiver of one. Application
  stays a core rule, reached by elaboration and never written.
- **Parentheses re-open the message chain.** `(f k: x) k: y` is two sends, not one two-part selector
  — the same mechanism that keeps uniform binary precedence unambiguous. The core's application is
  single-argument, so multi-argument function values are curried by nesting, matching the core's
  `Observer` (one type slot). No tuple/product type is introduced.
- **Under-application is an error.** `xs append` where `append` has an `<in: …>` parameter is an
  arity error, never a silently produced function value. The uniform-access getter/method split is
  unchanged. Partial application (a section) is a separate open item — `overview.md` §12.27,
  [#109](https://github.com/lapis-lang/lapis-lang/issues/109).
- **Operation references are the function-value spelling.** An unbound camelCase `ident` in
  `primary` position resolves through `ρ` (an arm binding), then through `Ω`. Since nothing binds a
  name otherwise, an operation is the only thing such a name can denote — no new resolution rule.
  Qualification follows constructor qualification exactly: `Int double`, bare when unique in scope.
  One rule for variants, patterns, and operations.
- **Contract clauses take an indented body, not a block.** `demands:`, `ensures:`, `invariant:`,
  `rescue:` each take an expression at the arm-body column. The clause's body is always forced by
  the fold machinery at its own chosen moment and never held as a value, so a literal added a thunk
  for no reason and a second spelling for "a body at a given column."
- **`map` is declared with a fold body.** Its transform is the operation's own arm form, not a
  literal — which is what it elaborates to (`overview.md` finding 3 records the same collision).
- **Ratified: application is call-by-value.** Totality removes the classical motive for call-by-name
  (no well-typed argument can diverge), and the two surviving pressures both point to CBV: the cost
  algebra is intensional over evaluated arguments (`cost.ts` —
  `cost(app t u) = cost(t) + cost(u) +
  body(u)`; an unforced argument has no cost), and contract
  firing order must be statable (`demands:` on an unused argument fires at the call site under CBV,
  not "whenever"). Eager data / lazy codata is a _field and generator_ strategy fixed by declaration
  kind — it is not a change to the application rule.

## Symbolic operation names and uniform binary precedence

- Operation names (fold names) can be **symbolic**: `+`, `-`, `*`, `<`, `<=`, `==`, etc. Following
  the Smalltalk binary selector convention. Multi-character, longest match among declared operators.
- **Position discriminates data from operations**: prefix (contiguous, start of token) =
  pattern-matched constructor (data introduction). Infix (between whitespace-delimited tokens,
  operation-application position) = symbolic operation (fold/elimination). The lexer alternates
  between "expecting a token" (prefix — try patterns > identifiers > named constructors) and
  "expecting an operator" (infix — try operators > identifiers for named sends). Whitespace is
  consumed between tokens in both modes.
- **Operation name rules**: symbolic (`+`, `<=`, `<+>`, `<>`, `==`) or named (`add`, `lessThan`). No
  spaces — an operation name is a contiguous sequence of non-whitespace characters. Recognized in
  infix position only. Longest match among declared operators. **Can never be patterns** — they're
  in a different lexical context (expression level, not pattern level). **The character set is
  closed**: `+ - * / < > = ! ? & | , .` (`surface-grammar.md` §2.3). It excludes every core
  delimiter — parentheses, brackets, braces, `:`, `\`, whitespace — because a name that could
  contain a delimiter would collide with the syntax around it, and maximal munch would then swallow
  the delimiters (`(+)` would lex as one name). Angle brackets are inside the set, so `<+>` is a
  legal name; round, square and curly brackets are not.
- **Naming convention**: PascalCase prefix = named constructor. Symbolic prefix (no whitespace) =
  pattern-matched constructor. camelCase infix = named operation. Symbolic infix = symbolic
  operation.
- **A symbolic name IS the operation's name — it is not an alias.** Aliasing (one operation, several
  names) has no surface spelling yet (`overview.md` §12.33), so a prelude row pairing `+` with `add`
  describes two _distinct_ names, not one operation with two spellings.
- **Uniform binary precedence** (Smalltalk model): ALL binary messages have the same precedence.
  Evaluated strictly left-to-right. `1 + 2 * 3` parses as `(1 + 2) * 3 = 9`. Explicit parentheses
  required for mathematical grouping: `1 + (2 * 3) = 7`. NO configurable or hierarchical operator
  precedence. Precedence between message _types_ (unary > binary > keyword) is retained.
- **Escaping in patterns**: special characters (`+ * ? [ ] \`) are escaped with `\` when meant
  literally. E.g., `[0-9]+\+[0-9]+j` for complex numbers — the `\+` is a literal `+` inside the
  token, while the unescaped `+` after `[0-9]` is the quantifier.

## Operation applications in core text carry the `#` sigil

- **Every** operation application in core concrete syntax is `#name(args)` — `#add(a, b)`,
  `#+(a, b)`, `#<+>(a, b)`. One rule, no conditionals: a symbolic name is not a special case.
- **Why a spelling of its own at all.** An operation's name is whatever the surface declared, and
  `lc.md` §2.2 says the named form _is_ "the symbolic identity of a fold". A symbolic name has no
  spelling in a grammar whose name lexeme is identifiers, and `add(a, b)` is ambiguous with variable
  application until the registry says otherwise. The sigil settles both at the lexeme.
- **Why `#` and not a bracket form.** The spelling must be one the _surface cannot produce_, so no
  user declaration can capture core-owned vocabulary. No surface operator character set contains
  `#`, so `#+`/`#add` are outside the surface's name grammar. Bracketed forms fail this test: `(+)`
  becomes spellable the moment `(` and `)` join the operator set, and each candidate bracket (`(`
  `)` `[` `]` `{` `}`) is core syntax, so admitting one overlaps the operator alphabet with the
  delimiter alphabet. This is the same reasoning that spells the core-owned raw-text type `@Token`
  (`lc.md` §2.1), which names `#name` as the precedent.
- **Why uniform rather than "sigil only for symbolic names".** A conditional sigil needs an
  `isSymbolic` test at every text boundary — render, parse, the declaration gate, the dependency
  scan, and the law machinery's obligation interpolation — and each test is a place the two sides
  can disagree. Uniform also buys a parse that does not consult `Ω` to identify the form.
- **The surface's `#` already means this.** The surface uses `#` for a spec record's `aux #name`
  entry and for a law argument's keyword-part reference (`identity: #add`). Both denote an
  operation, so they are the _same_ form as an application rather than a third kind of thing. The
  reference-vs-value distinction is `overview.md` §12.6; what this decision fixes is the _spelling_
  of an application, which the surface had none of before.
- **The registry gate stays a prefix, and it is not what identifies the form.** The sigil identifies
  the form syntactically; the gate still runs before the argument list is parsed, because parsing
  arguments the registry will reject is work the backtracking engine repeats at every enclosing
  alternative — a combinatorial blowup on exactly the nested terms law screening generates
  (`#op(#op(a))`).
- **Round-tripping.** `renderOperationName` and `parseOperationName` (`src/core/ops.ts`) are total
  and mutually inverse, so core text carries no side table, no counter, and no compilation-order
  dependence. A numeric tag would have needed all three, and would make two compilation units mint
  colliding names.

## Elaboration has a verdict

Elaboration is not a text emitter that leaves correctness to a later stage. `elaborateProgram`
returns a verdict: `ok`, a per-operation `errors` list, and an `Ω` holding **only** the operations
that passed. The checks are the core's own (`LCTypeCheck.opWellFormedness`, through
`OpRegistry.declare`), so the verdict and the `Ω` entry are one judgement — a second implementation
of "is this well formed" is the defect, not the fix.

- **Per-operation, not per-program.** A declaration that fails is absent from `Ω` and named in
  `errors`; its siblings still elaborate and install. This mirrors resolution's `ok` + `errors`
  shape, and it matters because a program's declarations are independent by design (no ordering
  rule).
- **`not-well-formed` covers everything `declare` rejects.** The signature comes from the spec
  (`in:` value, `out:` result) and the definition from the arms, so an `in:` that names something
  other than what the emitted lambda takes is the same failure as a mismatched result type; one
  reason, because `Ω` requires agreement component-wise. It also covers a recursive body, whose
  self-reference `Ω`'s acyclicity rule forbids. Reporting recursion as an elaboration failure is
  honest — the operation genuinely cannot be installed — but it is not the language's answer for
  recursion; that is a separate decision.
- **A fold's arity is one or two, and `in:` is the second argument.** The carrier is always the
  first parameter (the arms destructure the declaring type's variants), and at most one `in:`
  follows it (`surface-syntax.md` §2.3). The emitter writes one annotated lambda per declared
  parameter, and an arm head's binding beyond the variant's field count _names_ that lambda — it is
  not a handler binding, because the core supplies values for the variant's fields only. The
  resolver enforces the count exactly.
- **A fold arm's head is a pattern, so it spells the fields' names.** Each binding for a variant's
  field must be that field's declared name; `M a b -> …` is the only spelling for `M`'s two fields,
  and `M x y -> …` is an error rather than a rename. This is the construction rule read the other
  way: a construction's keyword sequence equals the declared fields, so a fold arm's binding
  sequence does too. `_` discards a field without naming it. The reason is uniform — a case arm _is_
  a pattern-matching form, and a pattern that renames its subjects is not a destructuring of the
  declared variant but a fresh set of bindings that happens to have the right arity. An **unfold**
  arm is exempt: it binds the seed, which no variant declares, so its name is the author's choice.
- **The one non-field binding is `in`.** A fold's extra argument has no declaration to agree with,
  so the language fixes its name: `in`, matching the spec record's key and the name a protocol
  default body uses — the same word in all three positions. The emitter must translate it when
  writing a core binder, because the core reserves `in` (`LC_RESERVED_WORDS`) for its `let … in`
  delimiter; that half is `overview.md` §12.63 and #142.
- **Parameter types are compared by mutual subtyping.** A parameter _is_ the declared type, not
  merely compatible with it: one-way contravariance would admit `Any → τ` against a declared
  `N → τ`, leaving the signature and the definition describing different operations. A
  function-typed _result_ is legal and is the one case where the definition has more lambdas than
  the declared arity; there the residue must equal the declared result, since that is what callers
  are promised.

## Citing the specification

A section number is not a citation unless it names its document. `_docs/theory/` has **six** `§2.4`
headings — `lc.md`'s _Contexts_, `surface-grammar.md`'s _Literals_, `surface-syntax.md`'s _Railroad
diagram_, `elaboration.md`'s _Binary operators_, `prelude.md`'s _`Int`_, and `semantics.md`'s
_Observation semantics_ — so a bare `§2.4` in a code comment resolves to nothing a reader can act
on. The convention (`CONTRIBUTING.md` §"Citing the specification") is to name the document, and,
where the section's title does not name the content, to cite the named paragraph inside it.

The rule exists because the failure is silent: a wrong citation looks exactly like a right one, and
nothing downstream re-checks it. `E-Op` is in `lc.md` §3.1, not §2.4, though §2.4 is where the
`Ω`-well-formedness paragraph lives; `compare` is not a prelude operation at all, though
`prelude.md` §3.1 declares five orderings that look like it.

**Fix the document, not the citation.** When a citation needs a warning attached to be usable, the
section it points at is malformed. A section whose title names one topic and whose body carries
another makes a correct number read as a wrong section — the remedy is a section per topic, not an
apology at every citation site.

This is the same rule the corpus already applies to names: a name the documents teach must be
declared somewhere a reader can find it (`prelude.md`'s types), and a finding the documents cite
must exist in the ledger. A citation is a claim, and a claim is checked against the text, not
against another citation.

## Attribute grammars + lang-forma

- Parser library published to JSR as `@lapis-lang/lang-forma`.
- `bind`/`chain` (L-attributed binds) for one-pass parsing, grammar-native contracts (`@requires`,
  `@ensures`, `@invariant`, `@rescue`) with typed predicates, `diagnostic()` for failure reporting.
- `_forward` (higher-order attributes — one-pass evaluation via re-parsing substrings under extended
  context), `parseToTree`/`SemanticPass` (retained derivation trees and tree-consuming passes),
  standalone combinators (`sseq`, `plus`, `sepBy`, `between`, `trim`, `keyword`), lexeme helpers
  (`ws`, `ws1`, `digit`, `digits`, `ident`).
- Two patterns for semantics: (1) multi-pass via `super` (subclass calls super.expr.map(evalFn)),
  (2) one-pass judgments-as-productions via `@rule expr(Γ): Parser<Type>` with `bind` for
  left-sibling synthesized → right-sibling inherited flow. With `_forward`, evaluation is also
  one-pass (closures re-parse body via `_forward`); `SemanticPass` handles passes over already-built
  trees.
- Grammar-class subtyping = natural layering for semantic passes: base grammar (syntax) → subclass
  (name resolution) → subclass (type check) → subclass (law check) → subclass (evaluation). Each
  pass inherits productions it doesn't override.
- Lapis's enforced structure means hard type-theory cases DON'T ARISE: no polymorphic recursion (no
  general recursion, declared result types), no let-generalization (subtyping not generics), `super`
  gives complete AST node (no bidirectional flow needed).
- See lang-forma `examples/stlc.ts` for headline example: STLC with 4 interpretations (AST, type
  checker, evaluator, proof-bearing) over one abstract grammar.

## Deno migration (completed 2026-07-25)

- Project converted from Node/TypeScript (.mts + package.json + tsconfig.json) to Deno (.ts +
  deno.json).
- All imports: `.mjs` → `.ts` (relative), `@lapis-lang/derivative-parser` →
  `jsr:@lapis-lang/lang-forma`.
- `deno check src/index.ts` passes clean.
- Devcontainer: `.devcontainer/devcontainer.json` (Ubuntu 24.04 + Deno feature + VS Code Deno
  extension).
- `deno.json` has tasks: check, test, build (deno compile → exe), fmt, lint.
- `minimumDependencyAge: "0"` in deno.json (lang-forma was freshly published).

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
6. **Pattern constructors with captures — DECIDED conceptually, pinning in
   [#85](https://github.com/lapis-lang/lapis-lang/issues/85).** Pattern constructors carry named
   captures (`<name: TypeName>`) that extract sub-matches as typed fields, paralleling named
   constructor fields. E.g., `Rect <real: Int>\+<imag: Int>j` for `Complex`. The captures are the
   fields, bound in fold arms by the capture name. The pattern is a parser, captures are semantic
   values. `_docs/overview.md` §2.2 teaches the form (`Ratio <p: Int>/<q: Int>`,
   `Cartesian <re: Float>+<im: Float>i`). Remaining to pin (the #85 work items):
   capture-vs-type-reference disambiguation (`<T>` vs `<name: T>`), greedy/bounded reading of
   `String`-typed captures in delimited regions, counted-postfix interaction, and the fold
   arm-keying rule — **decided in `overview.md` §12.10**: a pattern arm keys on the declared
   constructor name; single-pattern types may keep the anonymous spelling keying on the type name
   (binding the whole match as `value`). **Adjacent decision — no letter-leading patterns:** a
   pattern's leftmost-matchable set (computed from its AST, not its source) must exclude `[A-Za-z]`;
   letter-initial matches are reserved for identifiers/keywords/variant construction (see
   `overview.md` §12.11, `surface-syntax.md` §1.3 anchoring).
7. **Blame in the calculus?** Contracts currently elaborate to folds over `Bool` and `Result` —
   blame is a runtime concern, not a calculus concern. Wadler's blame calculus ("Well-typed programs
   can't be blamed", 2009) makes blame labels first-class core entities, enabling the blame theorem
   to be proved at the calculus level. Lapis's contracts are richer (DbC with `rescue`, LSP
   subcontracting tied to the subtyping lattice), and the interaction of subtyping + contracts +
   blame may require calculus-level support. Deferred to Stage 5 (contracts + laws).
8. **`Family` in type/declaration position — DECIDED: reserved, not shadowable** (see `overview.md`
   §12.16). The form `data Family { Cons ... rest: Family }` is legal today and not
   compiler-ambiguous — the resolution chain (bound-Δ → built-ins → registry → `TypeVar` fallback)
   decides deterministically, and the `FamilyType` singleton is in none of those slots. The hazard
   is **name capture that flips semantics by scope**: in a program without a user type named
   `Family`, `rest: Family` is the open-recursion reference (the μ-bound α); in a program with one,
   the same spelling resolves to the user's type (closed recursion). Same text, opposite recursion
   discipline, decided silently by context. Fix at the lexeme: `Family` is reserved in
   type/declaration position — the language-defined μ-bound reference; user declarations that want
   the name choose another. Enforcement gap: `LC_RESERVED_WORDS` gates only the lowercase `ident`
   lexeme; `variantName`/`typeName` (PascalCase) never consult it — the gate must extend to those
   two lexemes (or a dedicated check in `atomType`'s registry route). Enforcement scoped in
   [#85](https://github.com/lapis-lang/lapis-lang/issues/85).
