# Lapis Language Design Decisions

> **Source:** Copilot repo memory (`/memories/repo/lapis-design-decisions.md`).
> Copied here on 2026-07-25 because repo memories don't survive devcontainer
> rebuilds. This file is the authoritative copy; the memory file is a convenience
> cache. Update both when decisions change, or just this file and re-import.

Pinned in `_docs/theory/language-design.md`, `_docs/theory/core-calculus.md`, and `_docs/theory/why-lapis.md`.

## Original motivation (rediscovered, see why-lapis.md)
- The Bird-Meertens Formalism (Squiggol) should be a programming language, not a theory.
- The unique property: enforced structural recursion (fold/unfold only) COMBINED with first-class, verifiable, AND exploitable algebraic laws.
- Enforcement without exploitation = Charity (a cage). Exploitation without enforcement = Haskell+rewrite rules (a library, unreliable). Lapis = both together.
- The three ESSENTIALS (irreducible): (1) fold/unfold as only recursion, (2) first-class exploitable law declarations (properties), (3) μ/ν bialgebraic duality.
- NOT essential (could be library/sugar): surface syntax, relation/query/io sugar, contracts, module system, subtyping. These make the cage habitable but aren't why the language exists.
- Enforcement is a language-level decision — cannot be a library. This is the answer to "why a language, not a library."
- Asymptotic argument: algebraic correctness goes from O(program size) global composition analysis to O(1) local law declarations. Enforcement reduces compiler's reasoning from "analyze arbitrary recursion" to "trust the structure" — same complexity reduction types provide.

## Core calculus
- **F<: + μ/ν + guarded fold/unfold + qualified types.** NOT Fω — no higher-kinded polymorphism.
- Subtyping subsumes generics (Meyer OOSC, Bracha). Comb inheritance + field narrowing is the mechanism.
- Cost: loss of parametricity. Recovered *by declaration* via `properties` annotations (associative, idempotent, etc.). Reframe `properties` as the price paid for subtyping-over-generics.
- No general fixpoint. Recursion only via fold (terminating, data finite) and unfold (productive, guarded). Sized-types story specialized to bialgebraic setting.
- **Iso-recursive, not equi-recursive.** `fold_T`/`unfold_T` are explicit core terms, not silent coercions. Rationale: in Lapis, fold and unfold are not type coercions (as in TAPL) but the primary computational constructs — the catamorphism and anamorphism. They carry semantic weight: `properties` (algebraic laws), `@requires`/`@ensures` (contracts), `<para>`/`<histo>`/`<aux>` (recursion scheme modifiers), and `<in:`/`<out:` (type specs) are all declared *on the fold*. Making fold/unfold implicit (equi-recursive) would destroy the declaration surface where the user tells the compiler the algebraic structure of their operation — which is the whole point of the language. The hybrid: iso-recursive core + elaboration, equi-recursive surface for pattern matching inside fold handlers (the user pattern-matches directly; the fold machinery manages the recursive boundary). Subtyping rules (S-Data-Width, S-Data-Depth) use the guarded assumption (`α <: T'` in the premise) — the standard iso-recursive treatment (Amadio-Cardelli).

## Evaluation model
- Eager data (μ), lazy codata (ν). Fixed by declaration kind — NOT a user knob.
- Church–Rosser invoked to justify compiler rewrites *within* each strategy (confluence for terminating reductions).
- Strictness of data fields is part of the type. Lazy field = explicit `Lazy τ` (trivial codata wrapper) or behavior-typed field.
- Codata contracts (demands/rescue) are observation-gated — fire at observation time, not construction. State as feature.

## Effects
- Core is effect-FREE. Contracts (DbC) not effect systems (per lapis-js#113 analysis).
- rescue/retry elaborate to `Result`-typed core terms (sum of success/failure + retry counter).
- IO is a Mealy machine — pure data value `{init, request, respond}` interpreted by runtime. IO is data, not an effect.
- 20% gap (deferred exec, multi-shot continuations, nondeterminism) parked in `query`/future `Amb`.

## Laws: static where possible, dynamic when needed
- Type soundness (Progress/Preservation) is static + total — proved for fold/unfold typing, independent of law truth.
- Law soundness is a SEPARATE theorem, best-effort: compiler discharges statically what it can, runtime sample-checking (LawError) for rest.
- Core carries law *declarations* as constraints, not proofs. Checking strategy is per-law, per-mode.
- Leaves room for Lapis as a Programming Language System (Smalltalk/DBMS family): live-image mode with runtime checking.

## No primitive conditional
- Boolean is a data type: `Bool = μ α. (True | False)`.
- `ifTrue:ifFalse:` is a fold over Bool. No primitive `if` in core. "No conditional" claim literally true.

## No base types — everything is μ or ν (pattern-matched data)
- Base types (`ι` in the calculus: `Int`, `String`, `Bool`, ...) are **eliminated**. All types are `μ` (data) or `ν` (codata).
- `Bool` = `data Bool (True | False)` — named constructors, zero fields.
- `Nat`, `Int`, `String`, `Complex`, `Rational`, etc. = `data` types with **pattern-matched constructors** (a compact specification of an infinite constructor set).
- **Pattern language**: restricted regular fragment with type references — character literals, character classes `[...]`, negated classes `[^...]`, any character `.`, quantifiers `+ * ?`, escape `\`, type reference `<TypeName>` (pattern interpolation — match the pattern of another data type here). NO alternation `|` (use multiple variants), NO groups `()`, NO anchors, NO backreferences. Compiles to a DFA for flat patterns; type references make it context-free (handled by the zipper-grammar engine's lazy recursion). Longest match wins; declaration order breaks ties.
- **Pattern constraints**: patterns match contiguous characters. A pattern may consume whitespace if its structure includes it (via `.`, `[^...]`, character classes containing space, or delimited regions). Whitespace that no pattern consumes is a token boundary (fallback). Patterns must be **anchored** — must start with a specific literal character or character class (not `.*` or `*` or `?`); a pattern starting with `.` is allowed only if preceded by a literal delimiter (e.g., `".*"` is fine; bare `.*` is rejected). This is how lexers work: undelimited patterns (like `[0-9]+`) naturally exclude space; delimited patterns (like `"<Char>*"`) naturally include it.
- **Metacharacters** (must be escaped with `\` when meant literally): `+ * ? [ ] \ . < >`. `.` = any single character. `<TypeName>` = type reference (non-terminal). `\<` and `\>` = literal angle brackets.
- **Bootstrapping order**: alphabet (primitive — input domain, not a type) → `Token` (primitive: raw matched text, the one non-μ type) → `Char` (`.` — any single character) → `String` (`"<Char>*"` — quoted sequence of Chars) → `Nat` (`[0-9]+`) → `Int` (`-[0-9]+` and `[0-9]+`) → `Bool` (named) → operators on `Nat`/`Int` → everything else.
- **Pattern-matched folds are flat**: no `Family` fields, no recursion. The fold is a single-step extraction: the handler receives the matched token (implicit `match` field) and transforms it. Recursion depth 1.
- **Mixed constructors**: a `data` type can have both pattern constructors (terminals/leaves) and named constructors (non-terminals/recursive). The `data` declaration *is* a grammar production; the `fold` is the semantic action. This is grammar-as-semantics at the language level.
- **Lexer priority**: patterns > operators > identifiers. Within each phase, longest match wins; ties broken by declaration order. Named constructors take precedence over patterns when both could match (more specific).

## Symbolic operation names and uniform binary precedence
- Operation names (fold names) can be **symbolic**: `+`, `-`, `*`, `<`, `<=`, `==`, etc. Following the Smalltalk binary selector convention. Multi-character, longest match among declared operators.
- **Position discriminates data from operations**: prefix (contiguous, start of token) = pattern-matched constructor (data introduction). Infix (between whitespace-delimited tokens, message-send position) = symbolic operation (fold/elimination). The lexer alternates between "expecting a token" (prefix — try patterns > identifiers > named constructors) and "expecting an operator" (infix — try operators > identifiers for named sends). Whitespace is consumed between tokens in both modes.
- **Operation name rules**: symbolic (`+`, `<=`, `<+>`, `<>`, `==`) or named (`add`, `lessThan`). No spaces — an operation name is a contiguous sequence of non-whitespace characters. Can include grouping characters (`<`, `>`, `(`, `)`, `[`, `]`, `{`, `}`) as part of the name. Recognized in infix position only. Longest match among declared operators. **Can never be patterns** — they're in a different lexical context (expression level, not pattern level). Character set for symbolic operators: any non-whitespace, non-alphanumeric character; multi-character operators are sequences of these.
- **Naming convention**: PascalCase prefix = named constructor. Symbolic prefix (no whitespace) = pattern-matched constructor. camelCase infix = named operation. Symbolic infix = symbolic operation.
- **Uniform binary precedence** (Smalltalk model): ALL binary messages have the same precedence. Evaluated strictly left-to-right. `1 + 2 * 3` parses as `(1 + 2) * 3 = 9`. Explicit parentheses required for mathematical grouping: `1 + (2 * 3) = 7`. NO configurable or hierarchical operator precedence. Precedence between message *types* (unary > binary > keyword) is retained.
- **Escaping in patterns**: special characters (`+ * ? [ ] \`) are escaped with `\` when meant literally. E.g., `[0-9]+\+[0-9]+j` for complex numbers — the `\+` is a literal `+` inside the token, while the unescaped `+` after `[0-9]` is the quantifier.

## Attribute grammars + zipper-grammar (renamed from derivative-parser)
- Parser library now published to JSR as `@lapis-lang/zipper-grammar@2.2.0`.
- v2.1.0 adds: `chain` (monadic bind) for L-attributed one-pass parsing, grammar-native contracts (`@requires`, `@ensures`, `@invariant`, `@rescue`), `diagnostic()` for failure reporting.
- v2.2.0 adds: `_forward` (higher-order attributes — one-pass evaluation via re-parsing substrings under extended context), `TreeExp`/`flattenTree`/`parseTree` (tree-consuming grammars for passes over already-built ASTs), standalone combinators (`sseq`, `plus`, `sepBy`, `between`, `trim`, `keyword`), lexeme helpers (`ws`, `ws1`, `digit`, `digits`, `ident`).
- Two patterns for semantics: (1) multi-pass via `super` (subclass calls super.expr.map(evalFn)), (2) one-pass judgments-as-productions via `@rule expr(Γ): Parser<Type>` with `chain` for left-sibling synthesized → right-sibling inherited flow. With 2.2.0's `_forward`, evaluation is also one-pass (closures re-parse body via `_forward`); tree-consuming grammars handle passes over ASTs.
- Grammar-class subtyping = natural layering for semantic passes: base grammar (syntax) → subclass (name resolution) → subclass (type check) → subclass (law check) → subclass (evaluation). Each pass inherits productions it doesn't override.
- Lapis's enforced structure means hard type-theory cases DON'T ARISE: no polymorphic recursion (no general recursion, declared result types), no let-generalization (subtyping not generics), `super` gives complete AST node (no bidirectional flow needed).
- See zipper-grammar `examples/stlc.ts` for headline example: STLC with 4 interpretations (AST, type checker, one-pass evaluator via `_forward`, proof-bearing) over one abstract grammar.

## Deno migration (completed 2026-07-25)
- Project converted from Node/TypeScript (.mts + package.json + tsconfig.json) to Deno (.ts + deno.json).
- All imports: `.mjs` → `.ts` (relative), `@lapis-lang/derivative-parser` → `jsr:@lapis-lang/zipper-grammar`.
- `deno check src/index.ts` passes clean.
- Devcontainer: `.devcontainer/devcontainer.json` (Ubuntu 24.04 + Deno feature + VS Code Deno extension).
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
1. Fold dispatch: dynamic (method on prototype, comb chain) vs static (match on tag)? Prototype dynamic; LC written static. Reconcile in elaboration.
2. Equality: structural for μ, bisimulation for ν. Formalize = and ≈.
3. Strictness: Lazy τ explicit wrapper recommended.
4. Multi-sorted: simultaneous μ-bindings for mutual recursion.
5. Intersection types: first-class vs elaboration-time constraints? "Static where possible" suggests constraints by default, first-class in live-image mode.
6. **Pattern constructors with captures (tentative).** A pattern constructor could have named captures (`<name: TypeName>`) that extract sub-matches as typed fields, paralleling named constructor fields. E.g., `Rect <real: Nat>\+<imag: Nat>j` for `Complex`. The captures would be the fields, bound in fold handlers by the constructor name. This is conceptually sound (the pattern is a parser, captures are semantic values) but the syntax and handler-dispatch mechanics need validation against a real implementation. Deferred until Stage 1.
7. **Blame in the calculus?** Contracts currently elaborate to folds over `Bool` and `Result` — blame is a runtime concern, not a calculus concern. Wadler's blame calculus ("Well-typed programs can't be blamed", 2009) makes blame labels first-class core entities, enabling the blame theorem to be proved at the calculus level. Lapis's contracts are richer (DbC with `rescue`, LSP subcontracting tied to the subtyping lattice), and the interaction of subtyping + contracts + blame may require calculus-level support. Deferred to Stage 5 (contracts + laws).