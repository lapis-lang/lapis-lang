# LC — The Lapis Core Calculus

> **Status:** Draft v0.1. This document presents LC in TAPL style: syntax, evaluation rules, typing
> rules, and soundness. It is the formal specification that the implementation checks against. For
> design rationale, elaboration of surface constructs, and discussion, see
> [`elaboration.md`](./elaboration.md) and [`design-decisions.md`](../design-decisions.md).

## 1. Overview

LC (formally, $F_{<:\mu\nu}$) is **F<: with recursive and corecursive types**, where **fold and
unfold are the only recursion forms**. Two properties define it:

1. **F<:.** Subtyping subsumes generics.
2. **μ/ν, not general fix.** Data is μ (initial algebra); codata is ν (final coalgebra). No `fix` or
   `Y`. Termination and productivity follow from structure.

The calculus is pure — no effect type appears in the syntax. Named operations appear only as an
**operation signature** environment `Ω` and an `op(t₁, ..., tₙ)` application form; every operation
is _defined_ by an LC term (a fold). The **equational theory** environment `E` records the laws
declared for operations. `Ω` and `E` are environments (like `Γ` and `Δ`), not terms: laws never
appear in the term grammar and never step. See §7 (Algebraic Equivalence).

`cofold [T]` is an elimination form for codata (the dual of fold), not a recursion form — it
observes, it does not recurse.

`match(pₖ)` is a value introduced by the lexer (external to the calculus; the LC concrete syntax
spells it `match("p")` — a quoted pattern source, §2.2). It appears as a term and a value, but no
evaluation rule produces it; it is an axiom of the operational semantics.

## 2. Syntax

### 2.1 Types

```
σ, τ ::= α                  type variable
       | σ → τ              function type
       | μ α. Σᵢ mᵢ          data type (sum of named variants AND/OR pattern
       |                      constructors — a MIXED carrier carries both
       |                      member kinds; the absorbed pattern-only form is
       |                      the degenerate case with an empty variant set)
       | ν α. Πⱼ oⱼ(σⱼ)      corecursive codata type (product of named observers)
       | @Token              raw matched text
       | Any                 top
       | Nothing             bottom
       | σ ∧ τ              intersection type
```

**`@Token` is spelled with a sigil because no declaration can be.** `typeName` is
`[A-Z][A-Za-z0-9_]*`, so `@Token` is outside the name grammar: a user may declare `data Token`, and
the two are different types. The sigil marks a _core-owned_ type at the one position where it is
written, the same role `#name` plays for an operation reference. `Any` and `Nothing` need no sigil —
they are not μ/ν types either, but their names are reserved by fiat rather than being spellable
declarations.

### 2.2 Terms

```
t, u ::= x                              variable
       | λx:σ. t                        lambda
       | t u                            application
       | Cᵢ(t₁, ..., tₙ)                named variant construction
       | match(pₖ)                      pattern-matched construction
       | fold [T] t {Cᵢ(xⱼ) → tᵢ}       fold (catamorphism)
       | e.oⱼ                           observation
       | unfold [T] t {oⱼ → tⱼ}         unfold (anamorphism)
       | cofold [T] t {oⱼ(xⱼ) → t}      cofold (codata elimination)
       | Λα <: σ. t                     type abstraction
       | t [τ]                          type application
       | let x:σ = t in u               let-binding
       | op(t₁, ..., tₙ)                named operation application
```

`op(t₁, ..., tₙ)` is the application of a _named operation_ — the symbolic identity of a fold
declared in the surface language. It elaborates from surface operator use (`a + b` → `add(a, b)`)
and is _definitional_ sugar: `Ω` maps each operation name to its defining LC term, so
`op(t₁, ..., tₙ)` computes by applying the definition. The form exists so that operation identity
survives `let`-inlining and substitution: an optimizer can recognize two occurrences as the same
algebraic operation, which anonymous folds cannot express. Laws are attached to the operation _name_
in `E`, never to the term.

**Operation names and the keywords.** The op form is positionally disjoint from every keyword form:
the paren is tight (`fold(a, b)` — no whitespace), while every keyword position is
whitespace-delimited (`fold [T] e {...}`, `let x:σ = ...`, `... in u`). An operation may therefore
be named `fold` — the two readings never compete. Disambiguation from variable application is by the
registry gate: `f(a)` parses as an op application only when `f ∈ Ω`, while variable application
requires whitespace (`f a`, never `f(a)`).

**The `match` form in LC concrete syntax.** In the surface language the lexer introduces `match(pₖ)`
implicitly (a literal `42` lexes against `Int`'s pattern). LC's grammar-based realization makes the
introduction explicit: `match("p")` — a quoted pattern source. The pattern must be one of a
registered pattern type's declared patterns (anchored: its FIRST ATOM — the first leaf, descending
through the postfix wrappers `*`/`+`/`?` — is a literal, a class, or a type reference; a leading `.`
rejects, so `Int = -?[0-9]+` anchors while `.*` does not), and the term types as that type
(T-Pattern, §5.1). LC syntax has no other string literals — this is the one deliberate exception:
the payload is a _pattern_ (the constructor), not a term. A delimiter `"` inside the payload is
escaped (`\"`). The bare `Ident` atom for a registered pattern type (§2.3's token) remains the
registry-gated short form; the two routes yield the same value shape. `match` is reserved from
operation names (§2.5's reserved call forms) so the call shape can never be shadowed by an Ω entry.
The surface language's comment form (`/* ... */` — `surface-syntax.md` §1.4) has no core presence:
comments are consumed before the surface-to-core elaboration runs, so LC source carries none, and
the quoted pattern payload here is the one DQ form in the calculus's own concrete syntax.

### 2.3 Values

```
v ::= λx:σ. t                           closure
    | Cᵢ(v₁, ..., vₙ)                   constructed variant (eager: fields are values)
    | match(pₖ)                         matched token (a value of pattern-matched type)
    | unfold [T] s {oⱼ → gⱼ}            codata value (lazy: seed stored, generators deferred)
```

### 2.4 Contexts

Following PLT convention (TAPL; Barendregt): `Γ` (term context), `Δ` (type-variable context), `E`
(equational theory), and `Ω` (operation signature). `Σ` is reserved for the unfold **seed type**
(`Σ`-algebra style signatures use capital Sigma in universal algebra, but `Σ` is already taken here
by the seed type — `Ω` carries no other standard meaning, avoiding the collision).

```
Γ ::= ∅ | Γ, x:σ          term variable context
Δ ::= ∅ | Δ, α <: σ       type variable context (with bounds)
Ω ::= ∅ | Ω, op:σ₁→...→σₙ→τ    operation signature (name ↦ argument/result types)
E ::= ∅ | E, op:ℓ            equational theory (operation ↦ declared laws)
```

`E` and `Ω` are produced by elaboration from surface `fold` declarations (with their `spec`, see
[`elaboration.md`](./elaboration.md) §6): the fold's implementation elaborates to an LC term; its
signature enters `Ω`; its declared `properties` enter `E` after best-effort screening. Judgments are
optionally parameterized by them: typing `Ω; Γ ⊢ t : σ` and algebraic equivalence `Ω; E ⊢ t ≡ u`
(§7).

### 2.5 Operation environments (`Ω` and `E`)

The two environments §2.4 introduces each carry conditions of their own. `E`'s laws are §7's
subject; this section pins what an entry in `Ω` is and what must hold before one is installed.

**Well-formedness.** An entry `op: σ₁→...→σₙ→τ ∈ Ω` carries its defining term `def(op)`, and the two
must agree: `∅ ⊢ def(op) : σ₁ → ... → σₙ → τ`. The condition is part of declaring an operation (the
entry is installed only after the check), not a typing rule — T-Op _trusts_ the entry's `τ` and E-Op
executes its `def(op)`, so without the condition a mismatched declaration would type-check as one
type and evaluate as another: a Preservation violation through Ω rather than through a step.
Checking a definition requires the typing machinery, which is why the condition is a side condition
on `Ω`'s construction rather than a rule in §5; §5.8 is where `T-Op` reads such an entry.

The agreement is **component-wise, not merely arity-and-result**: each of `def(op)`'s parameter
types must equal its declared `σᵢ` (in the lattice, mutual subtyping — a parameter _is_ the declared
type, not merely compatible with it), and the residue must be the declared `τ`. A function-typed `τ`
is legal and is the one case where `def(op)` has more lambdas than `n`
(`mkAdder : <1> → Nat → Nat`); there the residue must equal `τ`, not merely be `<: τ`, since `τ` is
what T-Op reports to callers. `FunType <: Any` by S-Top, so a result of `Any` cannot distinguish an
over-applied definition from a correct one — the residue check is what does.

**Reserved call forms.** `match(pₖ)` is the calculus's one built-in call shape (§2.2), so it is
reserved from operation names: an `Ω` entry named `match` would be indistinguishable from the
language form and would shadow it for every subsequent parse. Because reserved names can never be
operations, a scanner looking for operation references may exclude them without hiding a real one.

**Acyclicity.** `Ω` is acyclic by construction: an entry's `def(op)` may reference only operations
installed **before** it, so self-reference, forward reference, and cycles are all rejected at
declaration. This is a stratification of `Ω` by declaration order, and it is what makes E-Op's
unfolding terminate without a fuel argument (§6.1's progress argument relies on it). Its cost is
that no operation may be recursive **by name** — which is not a restriction on what a program can
compute, because a data fold's recursion is its own induction rather than a self-call (§5.2), and
`unfold` is productive rather than recursive. The remaining question is identity, not recursion:
`Ω`'s keys are operation names, so two types cannot each declare an operation of the same name — see
see `overview.md` §12.50.

**Law authority (provenance ladder).** Laws in `E` are **axioms carrying a provenance tag**:
`primitive` (pinned by the language definition — builtin operations with fixed law sets, authority
by fiat), `discharged` (established by the compiler — finite-domain exhaustion for finite types,
bounded-domain exhaustion for machine-finite types like binary64 Float, or derivation from primitive
laws via fold-induction schemata — implemented, `src/core/derivation.ts`: the move set is the
machine-checked skeleton), or `asserted` (programmer declaration, screened). No tier requires proof
to declare. Soundness of law-directed rewriting is **relative to E**; the `discharged` and
`primitive` tiers are established by their mechanisms, so only `asserted` laws carry declaration
risk. See [`design-decisions.md`](../design-decisions.md) (Laws).

### 2.6 Notation

| Notation                 | Meaning                                                                                |
| ------------------------ | -------------------------------------------------------------------------------------- |
| `μ α. Σᵢ Cᵢ(σᵢ)`         | recursive data type (sum of named variants)                                            |
| `μ α. Σᵢ pᵢ`             | pattern-matched data type (sum of pattern constructors)                                |
| `ν α. Πⱼ oⱼ(σⱼ)`         | corecursive codata type (product of observers)                                         |
| `Token`                  | raw matched text (the one non-μ/ν primitive)                                           |
| `match(pₖ)`              | pattern-matched construction (introduction via lexer match)                            |
| `Fᵢ`                     | field type functor for variant Cᵢ: maps recursive position α to Cᵢ's field types       |
| `Gⱼ`                     | observer type functor for observer oⱼ: maps corecursive position α (Self) to oⱼ's type |
| `Fᵢ(σ)[α := σ]`          | substitute result type σ for recursive position α in variant Cᵢ's fields               |
| `Gⱼ(Σ)[α := Σ]`          | substitute seed type Σ for Self in observer oⱼ's type                                  |
| `fold [T] t {Cᵢ → tᵢ}`   | catamorphism over data `t : T` (handlers tᵢ)                                           |
| `unfold [T] s {oⱼ → gⱼ}` | anamorphism from seed `s : Σ` into codata `T` (generators gⱼ)                          |
| `cofold [T] e {oⱼ → t}`  | codata elimination (behavior fold; handler t receives all observations)                |
| `Λα <: σ. t`             | bounded type abstraction (F<:)                                                         |
| `σ <: τ`                 | subtyping                                                                              |
| `σ ∧ τ`                  | intersection type (protocol conformance)                                               |
| `Any` / `Nothing`        | top / bottom of the subtyping lattice                                                  |
| `op(t₁, ..., tₙ)`        | named operation application (definitional sugar; definition in `Ω`)                    |
| `Ω; E ⊢ t ≡ u`           | algebraic equivalence of `t` and `u` modulo the declared theory (§7)                   |
| `Ω` / `E`                | operation signature / equational theory environments                                   |

## 3. Evaluation

### 3.1 Evaluation Rules

```
match("p") ⇓ tok                                    (E-Pattern)
  where tok is the matched Token — the token is an axiom of the
  operational semantics (§1): no subterm evaluation, the value IS
  the matched text. The grammar-based evaluator realizes the
  lexer's match as a parse-time gate; the value is a `TokenVal` of
  the pattern type carrying the pattern's canonical source.
  (The abstract rule notation writes the form `match(pₖ)` — pₖ is
  the pattern the quoted source carries.)

(λx:σ. t) v → [x ↦ v] t                              (E-App)

fold [T] (Cₖ(vⱼ)) {Cᵢ(xⱼ) → tᵢ}
  → [xⱼ ↦ vⱼ'] tₖ                                    (E-Fold, variant arm)
  where for each field j:
    vⱼ' = fold [T] vⱼ {Cᵢ → tᵢ}   if j is a recursive (Family) field
    vⱼ' = vⱼ                       otherwise

fold [T] (match(pₖ)) {pᵢ → tᵢ}
  → [match ↦ tok] tₖ                                  (E-Fold, pattern arm)
  where tok is the matched Token for pattern pₖ — a token scrutinee
  contributes NO recursion (a single step; a variant scrutinee recurses
  through its Family fields; the two routes never mix within one step)

(unfold [T] s {oⱼ → gⱼ}).oₖ → gₖ(s)                    (E-Obs)

cofold [T] (unfold [T] s {oⱼ → gⱼ}) {oⱼ(xⱼ) → t}
  → [xⱼ ↦ gⱼ(s)] t                                    (E-Cofold)

let x:σ = v in u → [x ↦ v] u                          (E-Let)

(Λα <: σ. t) [τ] → [α ↦ τ] t                          (E-TApp)

op(v₁, ..., vₙ) → def(op) v₁ ... vₙ                    (E-Op)
where Ω carries def(op) = λx₁:σ₁. ... λxₙ:σₙ. t  and  Ω(op) = σ₁ → ... → σₙ → τ

t₁ → t₁'
─────────────────────────────                         (E-App1)
t₁ t₂ → t₁' t₂

t₂ → t₂'
─────────────────────────────                         (E-App2)
v₁ t₂ → v₁ t₂'

t → t'
─────────────────────────────                         (E-FoldArg)
fold [T] t {Cᵢ → tᵢ} → fold [T] t' {Cᵢ → tᵢ}

t → t'
─────────────────────────────                         (E-ObsArg)
t.oₖ → t'.oₖ

t → t'
─────────────────────────────                         (E-LetArg)
let x:σ = t in u → let x:σ = t' in u
t → t'
─────────────────────────────                         (E-CofoldArg)
cofold [T] t {oⱼ → tⱼ} → cofold [T] t' {oⱼ → tⱼ}

tᵢ → tᵢ'   (leftmost, i minimal)
─────────────────────────────                         (E-OpArg)
op(v₁, ..., tᵢ, ..., tₙ) → op(v₁, ..., tᵢ', ..., tₙ)
```

`E-Op` makes named operation application **definitional**: an `op` node computes by applying its
definition, exactly as if the definition had been `let`-bound and called. The named form is
semantically transparent — but it is _not_ inlined eagerly, precisely so that law-aware passes can
recognize and rewrite operation applications before evaluation. Note that laws never add steps: all
algebraic knowledge acts on `≡` (§7), never on `→`.

**`E-Fold` and `E-Cofold` select exactly one handler.** A fold's handler list is a dispatch table —
which entry applies is decided by the scrutinee's constructor — so an implementation that reaches an
unselected arm has stepped by something these rules do not license. The mistake is visible on a
recursive operation: a self-call in an arm the scrutinee never selects is evaluated anyway, the
recursion never reaches its base case, and `E-Fold`'s termination argument (a μ-type's finiteness,
§6.1) no longer holds.

The implementation therefore distinguishes _locating_ a body from _selecting_ it. Lambda, fold,
unfold, and cofold bodies are recorded as spans and re-evaluated by the higher-order attribute
mechanism (`_forward`) when the surrounding form is applied or dispatched. While such a body is
being located, an application inside it must not compute — otherwise the redex fires once during the
scan and again on replay. So the scan is a **capture**, and applications are inert within it: both
`E-App` and `E-Op` yield a placeholder instead of a value, exactly as an unbound binding does
(`src/core/eval_grammar.ts`, the capture phase).

## 4. Subtyping

```
                    Δ ⊢ σ <: σ                    (S-Refl)
         Δ ⊢ σ <: Any                            (S-Top)
        Δ ⊢ Nothing <: σ                        (S-Bot)
   Δ ⊢ σ <: τ    Δ ⊢ τ <: υ
   ───────────────────────────                   (S-Trans)
            Δ ⊢ σ <: υ

   Δ, α <: σ ⊢ α <: σ                            (S-Var)
```

### 4.1 Function subtyping

```
Δ ⊢ τ₁ <: σ₁    Δ ⊢ σ₂ <: τ₂
─────────────────────────────                (S-Fun)
    Δ ⊢ σ₁ → σ₂ <: τ₁ → τ₂
```

### 4.2 Data subtyping (μ-types)

**Width** (more variants = subtype):

```
T = μ α. Σᵢ∈I Cᵢ(Fᵢ(α))     T' = μ α. Σⱼ∈J Cⱼ(F'ⱼ(α))     J ⊆ I
(∀ j ∈ J) Δ ⊢ Fⱼ(α) <: F'ⱼ(α)   (T's field types <: T''s, for shared variants)
────────────────────────────────────────────────────────────────  (S-Data-Width)
                    Δ ⊢ T <: T'
```

**Depth** (field narrowing = subtype):

```
T = μ α. Σᵢ Cᵢ(Fᵢ(α))     T' = μ α. Σᵢ Cᵢ(F'ᵢ(α))     (same variants)
(∀ i) Δ, α <: T' ⊢ Fᵢ(α) <: F'ᵢ(α)   (T's field types <: T''s)
────────────────────────────────────────────────────────────────  (S-Data-Depth)
                    Δ ⊢ T <: T'
```

### 4.3 Codata subtyping (ν-types)

**Width** (more observers = subtype):

```
T = ν α. Πⱼ∈J oⱼ(Gⱼ(α))     T' = ν α. Πⱼ∈I oⱼ(G'ⱼ(α))     J ⊇ I
(∀ i ∈ I) Δ, α <: T' ⊢ G'ᵢ(α) <: Gᵢ(α)   (T''s observer types <: T's, contravariant)
────────────────────────────────────────────────────────────────  (S-Codata-Width)
                    Δ ⊢ T <: T'
```

**Depth** (observer type narrowing = subtype):

```
T = ν α. Πⱼ oⱼ(Gⱼ(α))     T' = ν α. Πⱼ oⱼ(G'ⱼ(α))     (same observers)
(∀ j) Δ, α <: T' ⊢ G'ⱼ(α) <: Gⱼ(α)   (T''s observer types <: T's, contravariant)
────────────────────────────────────────────────────────────────  (S-Codata-Depth)
                    Δ ⊢ T <: T'
```

### 4.4 Intersection subtyping

```
   Δ ⊢ σ <: τ₁    Δ ⊢ σ <: τ₂
   ─────────────────────────────                (S-And-Intro)
        Δ ⊢ σ <: τ₁ ∧ τ₂

   Δ ⊢ σ <: τ₁ ∧ τ₂                             (S-And-Elim)
   ───────────────────────
      Δ ⊢ σ <: τ₁
```

## 5. Typing

```
        x:σ ∈ Γ
   ────────────────                            (T-Var)
     Γ ⊢ x : σ

   Γ, x:σ ⊢ t : τ
   ────────────────────                        (T-Abs)
   Γ ⊢ λx:σ.t : σ → τ

   Γ ⊢ t : σ → τ    Γ ⊢ u : σ
   ──────────────────────────                  (T-App)
        Γ ⊢ t u : τ
```

### 5.1 Data introduction

```
   T = μ α. Σᵢ Cᵢ(Fᵢ(α))     Cₖ ∈ {Cᵢ}
   Γ ⊢ tⱼ : Fₖ(T)[α := T]   (for each field j)
   ────────────────────────────────────────────────────────────────  (T-Variant)
              Γ ⊢ Cₖ(tⱼ) : T

   T = μ α. Σᵢ pᵢ     input matches pₖ ∈ {pᵢ}     tok : Token
   ────────────────────────────────────────────────────────────────  (T-Pattern)
                      Γ ⊢ tok : T
```

### 5.2 Fold (catamorphism — data elimination, merged)

```
T = μ α. Σᵢ Cᵢ(Fᵢ(α))     (variant members)
Γ ⊢ e : T
Γ ⊢ tᵢ : Fᵢ(σ)[α := σ] → σ   (for each variant arm Cᵢ)
────────────────────────────────────────────────────────────────  (T-Fold, variant arm)
Γ ⊢ fold [T] e {Cᵢ(xⱼ) → tᵢ, ...} : σ

T = μ α. Σᵢ pᵢ             (pattern members)
Γ ⊢ e : T
Γ ⊢ tᵢ : Token → σ   (for each pattern arm pᵢ; ONE COMMON σ across the
                      pattern-arm group — a variant arm's σ joins it)
────────────────────────────────────────────────────────────────  (T-Fold, pattern arm)
Γ ⊢ fold [T] e {match("pᵢ") → tᵢ, ...} : σ
```

ONE production, ONE rule name (`T-Fold`), two arm kinds: a fold's handler list may mix variant arms
and pattern arms. The variant arms participate in the σ-fixpoint (their Family bindings rebind each
round); the pattern arms are σ-CONSTANT (their context never mentions σ — their body types enter the
join every round at no cost). A pattern-arm group keeps the strict one-common- σ premise; a
patterns-only carrier degenerates to that group's σ, a variants-only carrier to the variant
fixpoint's σ.

**Data folds are bottom-up; codata unfolds are top-down.** This orientation is what `Fᵢ(σ)[α := σ]`
means and it is the whole content of the word _catamorphism_ here: a variant arm runs **after** its
recursive children have been folded, so a `Family` binding holds the **already-computed result** of
the subterm, never the subterm itself. `Succ pred: Family` is therefore bound to a value of the
fold's _result_ type σ — which is why `Succ(pred) -> Succ(pred)` is the recursion for `add` and
`size`: the arm rebuilds `Succ` around a field that is already a number.

The dual holds for `unfold` (§5.3): a generator runs at the observation that demands it, so a
recursive observer position is the seed's _own_ type, and the codata value is produced lazily,
outermost-observer first. Reading one orientation into the other is the defect this paragraph exists
to prevent — a top-down reading of data makes recursive fields subterms (so `Succ(pred)` would
rebuild a _list_), and a bottom-up reading of codata makes a generator's `self` an already-observed
value rather than the seed.

**The σ-fixpoint.** The rule above is a recursive premise: `σ` appears both in each arm's type and
in the conclusion, so it is read as the limit of

```
σ₀ = ⊥
σₙ₊₁ = ⨆ᵢ  type of tᵢ  under  σ = σₙ
```

where `⊥` is `Nothing` and `⨆` is the lattice join. Two properties of that choice are normative, not
implementation detail, because the natural wrong choice is silent:

- **The seed is the join's identity, never the carrier.** `σ₀` is an operand of the first round's
  join, so seeding it at the carrier `T` makes `T` an _upper bound_ on the fold's result: for
  `Nat = Zero | Succ pred: Family` and `Bool`, `⨆(Nat, Bool) = Any`, and `Any` absorbs every later
  round. A fold into `Bool` then types as `Any`, which no declared `τ <: Bool` accepts — so no
  predicate fold can enter `Ω`. Since `⨆(Nothing, t) = t`, seeding at `⊥` leaves the arm bodies'
  common type as the result while still giving round one a value for the `Family` rebinding.
- **The limit is the join.** Arms whose types have no common supertype below `Any` make `⨆` yield
  `Any`; that is the lattice's answer, and `T-Fold` does not refine it further. The strict
  `typeEquals` premise above belongs to the _pattern_-arm group, which has no fixpoint to widen it.
  A `⊤` result is therefore **well-typed but vague**: `Any` is the top, so `τ <: Any` for every `τ`
  and a fold typed `Any` satisfies any declared `out:` at the result position — while telling
  callers nothing, since `Any <: τ` holds only for `τ = Any`. Whether such a program is one the
  language accepts is an elaboration question, not a typing one: `elaboration.md` §1.3 requires an
  operation to name its result, so the surface reports an inferred `Any` that came from disagreement
  rather than admitting it as a declaration.

The seed's second job is why `⊥` is admissible at all: a `Family` field is rebound to `σₙ` so the
arm body can be re-parsed, which needs `σₙ` to be a real type from the first round. `⊥` is one
(`Nothing <: t` for every `t`, so a first-round body cannot fail for want of a binding), and the
next round's join replaces it with the bodies' own types.

**A capture scan is not a premise.** An implementation locates each arm's body before it knows `σ`,
and the body's type must not be read at that point: the binding a scan gives a `Family` field is a
placeholder for the fixpoint's `σₙ`, never a claim about the field. Binding the placeholder to the
carrier is the tempting choice and it is wrong for exactly the reason the seed is not the carrier —
it makes the carrier an upper bound on every use of a recursive field, so
`Cons(head rest) ->
Succ(rest)` fails while `σ` is still unknown even though the fixpoint assigns it
`Nat`. The placeholder must satisfy every premise the eventual `σₙ` could satisfy, which is `⊥`'s
property and `Any`'s is not: `Any` is the wrong direction, since a premise that needs a `Nat` cannot
accept `Any`, whereas `S-Bot` puts `⊥` below every type. Both the acceptance and the rejection of an
arm therefore remain the fixpoint's: a body that cannot type under the converged `σ` is still
rejected (§5.2's `reparseFailed`), and no arm is admitted that `T-Fold` would not admit.

### 5.3 Observation (codata elimination)

```
T = ν α. Πⱼ oⱼ(Gⱼ(α))     oₖ ∈ {oⱼ}
Γ ⊢ e : T
────────────────────────────────────────────────────────────────  (T-Obs)
Γ ⊢ e.oₖ : Gₖ(T)[α := T]
```

### 5.4 Unfold (anamorphism — codata introduction)

```
T = ν α. Πⱼ oⱼ(Gⱼ(α))
Γ ⊢ s : Σ
Γ ⊢ gⱼ : Σ → Gⱼ(Σ)[α := Σ]   (for each observer oⱼ)
────────────────────────────────────────────────────────────────  (T-Unfold)
Γ ⊢ unfold [T] s {oⱼ → gⱼ} : T
```

### 5.5 Cofold (codata elimination — behavior fold)

`cofold` is the codata dual of `fold`: it eliminates a codata value by observing all observers
simultaneously (the product). `T-Obs` observes one observer at a time; `T-Cofold` observes all at
once, with continuation fields exposed as fold functions.

```
T = ν α. Πⱼ oⱼ(Gⱼ(α))
Γ ⊢ e : T
Γ ⊢ t : Πⱼ(Gⱼ(σ)[α := σ]) → σ
────────────────────────────────────────────────────────────────  (T-Cofold)
Γ ⊢ cofold [T] e {oⱼ(xⱼ) → t} : σ
```

### 5.6 Bounded polymorphism (F<:)

```
   Δ, α <: σ ⊢ t : τ
   ────────────────────────────                 (T-TAbs)
   Δ ⊢ Λα <: σ. t : ∀α <: σ. τ

   Γ ⊢ t : ∀α <: σ. τ    Δ ⊢ T₂ <: σ
   ──────────────────────────────────           (T-TApp)
        Γ ⊢ t [T₂] : τ[α := T₂]
```

### 5.7 Let and subsumption

```
   Γ ⊢ t : σ    Γ, x:σ ⊢ u : τ
   ─────────────────────────────                (T-Let)
   Γ ⊢ let x:σ = t in u : τ

   Γ ⊢ t : σ    Δ ⊢ σ <: τ
   ─────────────────────────────                (T-Sub)
        Γ ⊢ t : τ
```

### 5.8 Named operation application

`op(t₁, ..., tₙ)` types by the signature `Ω` carries (§2.4): the premises check that the operation
is declared, that the arity matches, and that each argument is a subtype of the declared parameter
type. `Ω` is an environment carried by the judgment (`Ω; Γ ⊢ t : σ`, §2.4) — the rule reads it; it
never enters the term grammar.

```
Ω(op) = σ₁ → ... → σₙ → τ     n = arity(op)
Γ ⊢ tᵢ : σᵢ   (for each argument i)
─────────────────────────────────────────────────────────────────  (T-Op)
           Γ ⊢ op(t₁, ..., tₙ) : τ
```

`T-Op` is the application dual of `E-Op` (§3): typing checks the signature; evaluation applies the
definition. Because `op(t₁, ..., tₙ)` is definitional sugar whose meaning is exactly
`def(op) t₁ ... tₙ`, the soundness argument reduces to T-App/E-App on the definition — but the named
form is preserved through elaboration so that operation identity survives substitution and inlining
(§2.2).

**Progress note:** `op(v₁, ..., vₙ)` steps by E-Op whenever all arguments are values; a non-value
argument steps by E-OpArg. Ω is acyclic by construction (§2.5), so the unfolding of nested op
applications terminates by induction on declaration order.

## 6. Soundness

### 6.1 Progress

**Theorem (Progress):** If $\Gamma \vdash t : \sigma$ (with $\Gamma$ closed), then either $t$ is a
value or $t \to t'$ for some $t'$.

**Sketch:** By induction on the typing derivation.

- **Fold:** `fold [T] e {Cᵢ → tᵢ}` — `e` is either a value or steps. If `e = Cₖ(vⱼ)`, the fold steps
  to `tₖ[xⱼ ↦ vⱼ']` (E-Fold, variant arm). If `e = match(pₖ)`, the fold steps to `tₖ[match ↦ tok]`
  (E-Fold, pattern arm). Since `T` is a μ-type (finite), the recursion terminates.

- **Unfold:** `unfold [T] s {oⱼ → gⱼ}` is a value. It does not step until observed. Observation
  `e.oₖ` steps to `gₖ(s)` (E-Obs), productive by the typing of `gₖ`.

- **Cofold:** Steps by observing `e` and applying the handler (E-Cofold). Each step produces one
  observation.

- **Op application:** `op(t₁, ..., tₙ)` — a non-value argument steps by E-OpArg (leftmost); when all
  arguments are values, the application steps by E-Op (applying the definition, which is a
  well-typed term by T-Op's signature premise). The unfolding terminates: Ω is acyclic by
  construction (§2.5), so nested op applications terminate by induction on declaration order.

### 6.2 Preservation

**Theorem (Preservation):** If $\Gamma \vdash t : \sigma$ and $t \to t'$, then
$\Gamma \vdash t' : \sigma$.

**Sketch:** By induction on the typing derivation, case on the step.

- **E-Fold:** `fold [T] (Cₖ(vⱼ)) {Cᵢ → tᵢ} → tₖ[xⱼ ↦ vⱼ']`. By T-Fold, `tₖ : Fₖ(σ)[α:=σ] → σ` and
  `vⱼ' : Fₖ(σ)[α:=σ]`. By the typing of `tₖ`, the result is `σ`.

- **E-Fold (pattern arm):** `fold [T] (match(pₖ)) {pᵢ → tᵢ} → tₖ[match ↦ tok]`. By T-Fold's
  pattern-arm premise, `tₖ : Token → σ` and `tok : Token`. Result is `σ`.

- **E-Obs:** `e.oₖ → gₖ(s)`. By T-Unfold, `gₖ : Σ → Gₖ(Σ)[α:=Σ]` and `s : Σ`. Result is
  `Gₖ(Σ)[α:=Σ]`, consistent with `Gₖ(T)[α:=T]` by the unfold's typing.

- **E-TApp:** `[α ↦ T₂] t`. By the substitution lemma, the result type is `τ[α:=T₂]`, and `T₂ <: σ`
  (the bound) ensures validity.

- **E-Op:** `op(v₁, ..., vₙ) → def(op) v₁ ... vₙ`. By T-Op, `Ω(op) = σ₁ → ... → σₙ → τ` with
  `vᵢ : σᵢ`, and `def(op)` types as `σ₁ → ... → σₙ → τ` (the definitional-sugar premise, §2.5) — so
  the application's type is τ by T-App, iterated over the arguments. Result is `τ`.

- **E-OpArg:** `op(v₁, ..., tᵢ, ..., vₙ) → op(v₁, ..., tᵢ', ..., vₙ)` with `tᵢ → tᵢ'`. By T-Op's
  premise `tᵢ' : σᵢ` (Preservation on the argument, inductively), the application still satisfies
  T-Op at `τ`.

**Substitution lemma:** If `Δ, α <: σ ⊢ τ₁ <: τ₂` and `Δ ⊢ T₂ <: σ`, then
`Δ ⊢ τ₁[α:=T₂] <: τ₂[α:=T₂]` (Pierce & Steffen).

## 7. Algebraic Equivalence

Laws in `E` are **not evaluation rules**. They generate a separate judgment

```
Ω; E ⊢ t ≡ u          t and u are algebraically equivalent
```

an _equational theory_ on top of the operational semantics. Ordinary evaluation (`→`) is unchanged;
the optimizer may replace a term by any member of its `≡`-class without changing meaning (relative
to the declared theory).

### 7.1 Congruence and structural rules

```
                      Ω; E ⊢ t ≡ t                    (Eq-Refl)

   Ω; E ⊢ t ≡ u       Ω; E ⊢ u ≡ w
   ───────────────────────────────                     (Eq-Trans)
             Ω; E ⊢ t ≡ w

   Ω; E ⊢ t ≡ u
   ───────────────                                    (Eq-Sym)
   Ω; E ⊢ u ≡ t

   Ω; E ⊢ t ≡ t'    Ω; E ⊢ u ≡ u'
   ────────────────────────────                        (Eq-App)
        Ω; E ⊢ t u ≡ t' u'

   Ω; E ⊢ tᵢ ≡ tᵢ'   (for each i)
   ──────────────────────────────                      (Eq-Op)
     Ω; E ⊢ op(t₁,...,tₙ) ≡ op(t₁',...,tₙ')

   Ω; E ⊢ t ≡ t'
   ──────────────────────────                          (Eq-Fold)
   Ω; E ⊢ fold [T] t {Cᵢ→tᵢ} ≡ fold [T] t' {Cᵢ→tᵢ}
```

plus congruence for every other term constructor (λ, variant, unfold, cofold, let, Λ, `[ ]`).

### 7.2 Law schemas

Each declared law in `E` contributes an axiom schema. For an operation `⊕ : T → T → T` (arity 2;
other arities generalize):

```
E(⊕) ∋ associative:
   ⊢ ⊕(⊕(a, b), c) ≡ ⊕(a, ⊕(b, c))

E(⊕) ∋ commutative:
   ⊢ ⊕(a, b) ≡ ⊕(b, a)

E(⊕) ∋ identity:e:
   ⊢ ⊕(e, a) ≡ a        ⊢ ⊕(a, e) ≡ a

E(⊕) ∋ idempotent:
   ⊢ ⊕(a, a) ≡ a

E(⊕) ∋ involutory:   (arity 1)
   ⊢ ⊕(⊕(a)) ≡ a

E(⊗) ∋ distributive:⊕:    (relational law — two operations)
   ⊢ ⊗(a, ⊕(b, c)) ≡ ⊕(⊗(a, b), ⊗(a, c))
```

**Unary vs. relational.** `associative`/`commutative`/`identity`/`idempotent`/`involutory` are
**intrinsic** laws about one operation. `distributive:⊕` is **relational** — a law _between_ two
operations, requiring `Ω` to carry both signatures. The core representation keeps the two distinct
(different axiom schemas, different screen arities).

### 7.3 Evaluation vs. equivalence vs. optimization

Three relations, strictly separated:

```
t → t'        evaluation (§3)          computational execution
Ω; E ⊢ t ≡ u  algebraic equivalence    semantic interchangeability, per declared laws
t ↝ t'        optimizer rewrite        a compiler-chosen, directed consequence of ≡
```

The optimizer picks a **direction** for each axiom (e.g. identity-elimination `⊕(e, a) ↝ a`, not the
expansion direction) — a strategic choice, never part of the language's semantics. `≡` is
undirected; `↝` is directed and per-exploit. Associativity + commutativity are _equivalence_;
treating them as evaluation steps would immediately produce nontermination (oscillation), which is
exactly why they live in `≡`.

**Theorem (Law-directed rewrite soundness, relative to E):** If `Ω; E ⊢ t ≡ t'` and `t ↝ t'` by a
rewrite licensed by `E`, then `t` and `t'` have the same denotation in every model of `E`.

The two equalities from [`semantics.md`](./semantics.md) §7 are untouched: structural equality on
data values and bisimulation on codata values are _value_ equalities (what the runtime `=` primitive
observes); `≡` is a _term_ equality (what the optimizer may exploit).

**Parser associativity is not algebraic associativity.** The surface parser groups binary operators
left-associatively: `a + b + c` parses as `(a + b) + c`. That is a _syntactic_ decision about source
text. `E(add) ∋ associative` says `(a+b)+c ≡ a+(b+c)` — a _semantic_ fact about meaning. The two are
independent; the elaborated core term is just whichever shape the parser produced, and the optimizer
may reassociate it under the axiom.
