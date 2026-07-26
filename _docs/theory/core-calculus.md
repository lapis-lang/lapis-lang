# Lapis Core Calculus (LC)

> **Status:** Draft v0.1. This document provides design rationale, commentary,
> and elaboration of surface constructs for the Lapis Core calculus. The formal
> specification — syntax, evaluation rules, typing rules, subtyping rules, and
> soundness in TAPL style — lives in [`lc.md`](./lc.md). This document is the
> *why*; that document is the *what*.

## 1. Design Rationale

LC (formally, $F_{<:\mu\nu}$) is **F<: with recursive and corecursive types**,
where **fold and unfold are the only recursion forms**. Three deliberate choices
shape it:

1. **F<:, not Fω.** No higher-kinded polymorphism. Subtyping (with bounded
   quantification) subsumes generics (Meyer, Bracha). Protocols are predicates over
   the subtyping lattice, not type-constructors. The cost — loss of parametricity —
   is recovered *by declaration* via `properties` (see §2.1 of `language-design.md`).

2. **μ/ν, not general fix.** Data is μ (initial algebra); codata is ν (final
   coalgebra). There is no `fix` or `Y` combinator. Termination of folds and
   productivity of unfolds follow from the F-structure being the measure — no
   separate termination checker. This is the soundness lever.

3. **Iso-recursive, not equi-recursive.** `fold_T`/`unfold_T` are explicit core
   terms, not silent coercions. In TAPL, fold/unfold are type coercions — they
   move between `μX.F(X)` and `F(μX.F(X))` but carry no computation. In Lapis,
   fold and unfold *are* the computation — the catamorphism and anamorphism. They
   are the declaration surface for `properties` (algebraic laws), contracts
   (`@requires`/`@ensures`), recursion scheme modifiers (`<para>`/`<histo>`/`<aux>`),
   and type specs (`<in:`/`<out:`). Making them implicit (equi-recursive) would
   destroy the surface where the user declares the algebraic structure the
   compiler exploits — which is the whole point of the language. The hybrid:
   iso-recursive core and elaboration; equi-recursive surface for pattern matching
   inside fold handlers (the user pattern-matches directly; the fold machinery
   manages the recursive boundary). Subtyping rules use the guarded assumption
   (`α <: T'` in the premise) — the standard iso-recursive treatment
   (Amadio-Cardelli).

4. **Effect-free.** No effect type. Contracts elaborate to `Result`; IO is a Mealy
   data value. The core is sound for pure fold/unfold + contracts-as-results.

## 2. Syntax

### 2.1 Types

```text
σ, τ ::= α                  type variable
       | σ → τ              function type (blocks, predicates, transforms)
       | μ α. Σᵢ Cᵢ(σᵢ)      recursive data type (sum of named variants)
       | μ α. Σᵢ pᵢ          pattern-matched data type (sum of pattern constructors)
       | ν α. Πⱼ oⱼ(σⱼ)      corecursive codata type (product of named observers)
       | Token               raw matched text (the one non-μ primitive)
       | Any                top of the lattice
       | Nothing            bottom of the lattice
       | σ ∧ τ              intersection type (for protocol conformance)
```

- `μ α. Σᵢ Cᵢ(σᵢ)` — a data type named by its variants `Cᵢ`, each carrying fields
  of type `σᵢ`. The bound `α` is the recursive self-reference (`Family` in the
  surface syntax). `Σ` is the sum (tagged union).
- `μ α. Σᵢ pᵢ` — a **pattern-matched data type**: each `pᵢ` is a pattern (a
  restricted regular expression) specifying an infinite set of constructors.
  There are no fields (no `Family`); the sole inhabitant of a matched constructor
  is the `Token` — the raw matched text. `Nat`, `Int`, `String`, `Complex`, etc.
  are pattern-matched data types. This eliminates base types (`ι`): every type
  is `μ` or `ν`, except `Token` (the bridge between the lexer and the language).
  See [`design-decisions.md`](../design-decisions.md) §"No base types".
- `ν α. Πⱼ oⱼ(σⱼ)` — a codata type named by its observers `oⱼ`, each of type
  `σⱼ`. The bound `α` is the corecursive self-reference (`Self` in the surface
  syntax). `Π` is the product (record of observations).
- `Token` — raw matched text from the lexer. The one type that is not `μ` or `ν`.
  It is the implicit field of every pattern-matched constructor. Pattern-matched
  fold handlers receive a `Token` (named `match` in the surface syntax) and
  transform it.
- `Any`/`Nothing` are the lattice bounds. Every type is a subtype of `Any`;
  `Nothing` is a subtype of every type.
- `σ ∧ τ` is the intersection — a value of type `σ ∧ τ` satisfies both. Used to
  express protocol conformance: `τ ∧ P` means "a τ that also satisfies protocol P."

**Note on base types:** Previous drafts of LC included base types `ι` (`Int`,
`String`, `Bool`, ...). These are eliminated: `Bool` is `μ α. (True | False)`
(named constructors), `Char` is `μ α. .` (any single character), `Nat` is
`μ α. [0-9]+` (pattern-matched), `Int` is `μ α. (-[0-9]+ | [0-9]+)`, `String` is
`μ α. "<Char>*"` (type reference — context-free pattern). The only non-`μ`/`ν`
type is `Token`. This unification means every type participates in the subtyping
lattice and the fold/unfold machinery — there are no privileged primitives.

### 2.2 Terms

```
t, u ::= x                              variable
       | λx:σ. t                        lambda (block) — annotated
       | t u                            application
       | Cᵢ(t₁, ..., tₙ)                named variant construction (data introduction)
       | match(pₖ)                      pattern-matched construction (data introduction)
       | fold_T t {Cᵢ(xⱼ) → tᵢ}          fold — data elimination (catamorphism)
       | e.oⱼ                           observation — codata elimination (destructor)
       | unfold_T t {oⱼ → tⱼ}            unfold — codata introduction (anamorphism)
       | cofold_T t {oⱼ(xⱼ) → t}         cofold — codata elimination (anamorphism's dual)
       | Λα <: σ. t                     type abstraction (bounded)
       | t [τ]                          type application
       | let x:σ = t in u               let-binding
```

- `Cᵢ(t₁, ..., tₙ)` — named variant construction. The user provides the field
  values explicitly.
- `match(pₖ)` — pattern-matched construction. The lexer matches input against
  pattern `pₖ` of type `T = μ α. Σᵢ pᵢ`; the matched text (a `Token`) is
  introduced as a value of type `T`. No user-provided fields; the `Token` is the
  implicit `match` field, accessible in fold handlers. See T-Pattern (§4.2b).
- `fold_T t {Cᵢ(xⱼ) → tᵢ}` — fold over a data value `t : T`, with one handler per
  variant. The `xⱼ` bind the *already-folded* results of recursive fields. For
  pattern-matched constructors, the handler receives the `Token` (named `match`).
- `unfold_T t {oⱼ → tⱼ}` — unfold from a seed `t : Σ` into a codata value `: T`,
  with one generator per observer. Each `tⱼ : Σ → Gⱼ(Σ)` produces the next seed.
- `cofold_T t {oⱼ(xⱼ) → t}` — eliminate a codata value by providing a handler per
  observer. This is the codata dual of fold (the "behavior fold" of lapis-js, where
  a single `_` handler receives the observation product). Included for completeness;
  the surface `behavior` fold desugars here.
- `Λα <: σ. t` — bounded type abstraction. The bound `σ` is the upper bound
  (subtyping constraint). This is the F<: mechanism; protocols elaborate to
  bounded quantification.

### 2.3 Contexts

```
Γ ::= ∅ | Γ, x:σ          term variable context
Δ ::= ∅ | Δ, α <: σ       type variable context (with bounds)
```

## 3. Subtyping

Subtyping (`<:`) is the core of the type system — it subsumes generics.

### 3.1 Basic rules

```
                    Δ ⊢ σ <: σ                    (S-Refl)
         Δ ⊢ σ <: Any                            (S-Top)
        Δ ⊢ Nothing <: σ                        (S-Bot)
   Δ ⊢ σ <: τ    Δ ⊢ τ <: υ
   ───────────────────────────                   (S-Trans)
            Δ ⊢ σ <: υ

   Δ, α <: σ ⊢ α <: σ                            (S-Var)
```

### 3.2 Function subtyping (contravariant/covariant)

```
   Δ ⊢ τ₁ <: σ₁    Δ ⊢ σ₂ <: τ₂
   ─────────────────────────────                (S-Fun)
       Δ ⊢ σ₁ → σ₂ <: τ₁ → τ₂
```

### 3.3 Data subtyping (μ-types)

Data subtyping has two dimensions, matching comb inheritance:

**Width subtyping (more variants = subtype):** A data type with *more* variants is a
subtype of one with fewer — every instance of the larger is an instance of the
smaller. This is the `extend` mechanism: `ExtendedColor <: Color` because
`ExtendedColor` has all of `Color`'s variants plus new ones.

```
   T = μ α. Σᵢ∈I Cᵢ(Fᵢ(α))     T' = μ α. Σⱼ∈J Cⱼ(Fⱼ(α))     J ⊆ I
   (∀ j ∈ J) Δ ⊢ Fⱼ(α) <: F'ⱼ(α)   (covariant fields, with α bound)
   ────────────────────────────────────────────────────────────────  (S-Data-Width)
                       Δ ⊢ T <: T'
```

**Depth subtyping (field narrowing = subtype):** A variant whose fields are *more
precise* (subtypes) is a subtype. This is field narrowing: `NumList.Cons` with
`head: Number` is a subtype of `List.Cons` with `head: Object`.

```
   T = μ α. Σᵢ Cᵢ(Fᵢ(α))     T' = μ α. Σᵢ Cᵢ(F'ᵢ(α))     (same variants)
   (∀ i) Δ, α <: T' ⊢ Fᵢ(α) <: F'ᵢ(α)   (covariant fields)
   ────────────────────────────────────────────────────────────────  (S-Data-Depth)
                       Δ ⊢ T <: T'
```

**Note on recursive subtyping:** The rules are *guarded* — the bound `α <: T'`
appears in the premise, allowing the recursive reference to be assumed a subtype
during the derivation (Amadio-Cardelli). This is the standard treatment for
iso-recursive types with subtyping. The implementation uses comb inheritance
(prototype chain + delegation chain) to realize this at runtime.

### 3.4 Codata subtyping (ν-types)

Codata subtyping is the dual — *more observers = supertype* (a type that promises
more observations is a subtype, because it can be used wherever fewer observations
are expected):

```
   T = ν α. Πⱼ∈J oⱼ(Gⱼ(α))     T' = ν α. Πⱼ∈I oⱼ(G'ⱼ(α))     J ⊇ I
   (∀ i ∈ I) Δ, α <: T' ⊢ G'ᵢ(α) <: Gᵢ(α)   (contravariant observers)
   ────────────────────────────────────────────────────────────────  (S-Codata-Width)
                       Δ ⊢ T <: T'
```

(More observers available = subtype; observer types contravariant.)

### 3.5 Intersection subtyping (protocols)

```
   Δ ⊢ σ <: τ₁    Δ ⊢ σ <: τ₂
   ─────────────────────────────                (S-And-Intro)
        Δ ⊢ σ <: τ₁ ∧ τ₂

   Δ ⊢ σ <: τ₁ ∧ τ₂                             (S-And-Elim)
   ───────────────────────
      Δ ⊢ σ <: τ₁
```

Protocol conformance `τ satisfies P` is modeled as `τ <: P` where `P` is a
protocol type (a set of operation signatures). Multiple protocols: `τ <: P₁ ∧ P₂`.

## 4. Typing Rules

### 4.1 Variables and lambda

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

### 4.2 Variant construction (data introduction)

```
   T = μ α. Σᵢ Cᵢ(Fᵢ(α))     Cₖ ∈ {Cᵢ}
   Γ ⊢ tⱼ : Fₖ(σ)[α := T]   (for each field j, recursive positions become T)
   ────────────────────────────────────────────────────────────────  (T-Variant)
              Γ ⊢ Cₖ(tⱼ) : T
```

Constructing variant `Cₖ` of type `T` requires each field to have the declared
type, with the recursive self-reference `α` replaced by `T` itself.

### 4.2b Pattern-matched construction (data introduction)

```
   T = μ α. Σᵢ pᵢ     input matches pₖ ∈ {pᵢ}     tok = matched text
   ────────────────────────────────────────────────────────────────  (T-Pattern)
                      Γ ⊢ tok : T
```

When the lexer matches input against pattern `pₖ` of type `T`, the matched text
`tok : Token` is introduced as a value of type `T`. There are no fields to check
(pattern-matched constructors have no fields). The `Token` is carried as the
implicit `match` field, accessible in fold handlers.

### 4.3 Fold (catamorphism — data elimination)

This is the central rule. Fold replaces each variant constructor with a handler,
recursing into `Family` fields automatically and passing the *already-folded*
results.

```
   T = μ α. Σᵢ Cᵢ(Fᵢ(α))
   Γ ⊢ e : T
   Γ ⊢ hᵢ : Fᵢ(σ)[α := σ] → σ   (for each variant Cᵢ)
   ────────────────────────────────────────────────────────────────  (T-Fold)
   Γ ⊢ fold_T e {Cᵢ(xⱼ) → tᵢ} : σ
```

**Key point:** `Fᵢ(σ)[α := σ]` substitutes the *result type* σ for the recursive
position. So a handler for `Cons(head: Int, tail: Family)` has type
`{head: Int, tail: σ} → σ` — the `tail` field arrives as the already-folded value
of type σ, not as a raw `T`. This is what makes fold terminating: the recursion is
structural (over the finite data), and the handler receives results, not
sub-structures.

**Exhaustiveness:** The handlers must cover all variants of `T` (or a wildcard
handler is provided). Missing handlers are a type error.

**Pattern-matched types:** For `T = μ α. Σᵢ pᵢ` (pattern-matched), the fold has
one handler per pattern, each of type `Token → σ` — the handler receives the
matched text and returns a value of type σ. There is no recursion (pattern-matched
constructors have no `Family` fields), so the fold is a single-step extraction.
A mixed type (both named and pattern constructors) has handlers for each kind.

### 4.4 Observation (codata elimination)

```
   T = ν α. Πⱼ oⱼ(Gⱼ(α))     oₖ ∈ {oⱼ}
   Γ ⊢ e : T
   ────────────────────────────────────────────────────────────────  (T-Obs)
   Γ ⊢ e.oₖ : Gₖ(T)[α := T]
```

Observing `oₖ` on a codata value `e : T` yields the observer's type, with the
corecursive self-reference `α` replaced by `T`. For a continuation observer
`tail: Self`, `Gₖ(T)[α := T] = T` — observing `tail` yields another `T`.

### 4.5 Unfold (anamorphism — codata introduction)

```
   T = ν α. Πⱼ oⱼ(Gⱼ(α))
   Γ ⊢ s : Σ
   Γ ⊢ gⱼ : Σ → Gⱼ(Σ)[α := Σ]   (for each observer oⱼ)
   ────────────────────────────────────────────────────────────────  (T-Unfold)
   Γ ⊢ unfold_T s {oⱼ → gⱼ} : T
```

Unfold builds a codata value from a seed `s : Σ`. Each generator `gⱼ` produces the
value for observer `oⱼ`; for continuation observers, it produces the *next seed*
(of type Σ), which the runtime uses to lazily construct the next observation.

**Productivity:** Unfold is productive by construction — each generator produces
one observation before recursing. This is the dual of fold's termination.

### 4.6 Cofold (codata elimination — behavior fold)

The dual of unfold-as-introduction is fold-as-elimination for codata. In lapis-js
this is the "behavior fold" with a single `_` handler receiving the observation
product. In LC:

```
   T = ν α. Πⱼ oⱼ(Gⱼ(α))
   Γ ⊢ e : T
   Γ ⊢ h : Πⱼ(Gⱼ(σ)[α := σ]) → σ   (single handler for the observation product)
   ────────────────────────────────────────────────────────────────  (T-Cofold)
   Γ ⊢ cofold_T e {oⱼ(xⱼ) → t} : σ
```

Where the handler receives all observations simultaneously (the product), with
continuation fields exposed as *fold functions* (calling them continues the fold).
Not calling a continuation terminates the fold (the base case).

### 4.7 Bounded polymorphism (F<:)

```
   Δ, α <: σ ⊢ t : τ
   ────────────────────────────                 (T-TAbs)
   Δ ⊢ Λα <: σ. t : ∀α <: σ. τ

   Γ ⊢ t : ∀α <: σ. τ    Δ ⊢ υ <: σ
   ──────────────────────────────────           (T-TApp)
        Γ ⊢ t [υ] : τ[α := υ]
```

This is the F<: mechanism. Protocols elaborate to bounded quantification: a
generic function `∀α <: Ordered. α → α` accepts any subtype of `Ordered`.

### 4.8 Let and subsumption

```
   Γ ⊢ t : σ    Γ, x:σ ⊢ u : τ
   ─────────────────────────────                (T-Let)
   Γ ⊢ let x:σ = t in u : τ

   Γ ⊢ t : σ    Δ ⊢ σ <: τ
   ─────────────────────────────                (T-Sub)
        Γ ⊢ t : τ
```

`T-Sub` is the subsumption rule — a term of type σ can be used where a supertype τ
is expected. This is how comb inheritance flows through the type system.

## 5. Elaboration of Advanced Recursion Schemes

The surface language offers `<para>`, `<histo>`, `<aux:>`, `map`, `merge`, `scan`.
These are **not core constructs** — they elaborate to fold/unfold combinations.

### 5.1 Paramorphism (`<para>`)

A paramorphism gives the handler both the folded result *and* the raw sub-node
(`old field`). Elaborates to a fold where the result type is a pair:

```
fold_T e {Cᵢ(xⱼ) → tᵢ}  where  σ = (Result, Raw)
```

The handler receives `xⱼ` as the folded result; `old field` accesses the raw
sub-node via the pair's second component. The fold machinery threads both.

### 5.2 Histomorphism (`<histo>`)

Course-of-values recursion: access to all prior fold results (`prev field`).
Elaborates to a fold where the result type is a stream of results:

```
σ = Stream<Result>   (a ν-type of fold results)
```

`prev field` steps back one level in this stream. The fold produces the stream;
the handler reads from it.

### 5.3 Zygomorphism (`<aux: name>`)

Auxiliary fold: fuse a primary fold with a secondary fold. Elaborates to a single
fold whose result type is a pair:

```
σ = (PrimaryResult, AuxResult)
```

The fold computes both results in one traversal; the handler accesses the
auxiliary via the pair's second component.

### 5.4 Map

Data map (eager, O(n)): elaborates to a fold whose result type is the data type
itself (`σ = T`), with handlers that reconstruct using transformed field values.

Codata map (lazy, O(1)): elaborates to an unfold that wraps each observation with
the transform, threading the same seed.

### 5.5 Merge (deforestation)

`merge(a, b)` composes operations into a single fused operation. Elaboration rules
(applied at definition time):

- **Unfold + fold (hylomorphism):** `merge(unfold, fold)` → a single core term that
  generates-then-consumes without materializing the intermediate structure.
- **Map + fold (prepromorphism):** `merge(map, fold)` → fold with transforms
  pre-applied to fields.
- **Fold + unfold (metamorphism):** `merge(fold, unfold)` → fold to an intermediate
  value, then unfold from it (intermediate is essential, cannot be eliminated).
- **Map-map fusion:** consecutive maps compose into one.
- **Inverse elimination:** `f⁻¹ ∘ f = id` — consecutive inverse pairs cancel.
- **Horner fusion:** `fold(⊕) ∘ fold(⊗)` where `⊗` carries `distributive:⊕` →
  validated pair, sequenced as a single named operation.

### 5.6 Scan (scan lemma)

`scan(foldName)` applies a fold at every recursive subterm, returning all results
in an array (root-first). Elaborates to a fold whose result type is an array of
the fold's result type, accumulating sub-results.

## 6. Contracts as Elaboration

Contract clauses (`demands`, `ensures`, `rescue`, `invariant`) are **not core
constructs**. They elaborate to core terms:

- **`demands: [self | P]`** — a precondition check: the fold/unfold body is wrapped
  so that if `P(self)` is false, a `DemandsError` is raised before the body runs.
  Elaborates to a guard term: `if P(self) then body else raise DemandsError`.
  (Where `if` is itself a fold over `Boolean` — see §7.)

- **`ensures: [self old result | Q]`** — a postcondition: after the body runs,
  `Q(self, old, result)` is checked. Elaborates to: capture `old = snapshot(self)`;
  run body; check `Q`; if false, raise `EnsuresError`.

- **`rescue: [self err args retry | R]`** — structured recovery: wrap the body in
  a `try`/`catch` (elaborated to `Result`-typed core), with `retry` re-invoking the
  body. Elaborates to a `Result`-typed term with a retry counter.

- **`invariant: [self | I]`** — checked before and after every operation.
  Elaborates to: check `I(self)` before; run body; check `I(self)` after.

The core remains effect-free: `raise` and `try/catch` elaborate to `Result`-typed
terms (sum of success/failure), and the runtime interprets `Result` values. This
keeps Progress/Preservation tractable.

**Connection to Wadler's blame calculus.** The current design treats contracts as
pure elaboration — they desugar to folds over `Bool` and `Result`, with no
calculus-level support for blame. Wadler's blame calculus ("Well-typed programs
can't be blamed", 2009) takes a different approach: blame labels are first-class
core entities carried by casts, and the blame theorem (well-typed components can
never be blamed) is proved at the calculus level alongside Progress and
Preservation.

Lapis's contracts are richer than Wadler's casts — they include `rescue`
(recovery) and are tied to the subtyping lattice (LSP subcontracting:
preconditions weaken, postconditions strengthen). The interaction of subtyping +
DbC + blame is hard to formalize purely in elaboration, because subcontracting is
already in LC and the blame theorem needs to talk about which side of a subtyping
relationship is at fault. A future refinement may promote blame labels to the
calculus level (see open question §9.6).

## 7. Boolean and Conditional

There is **no primitive `if`** in LC. `Boolean` is a data type:

```
Bool = μ α. (True | False)
```

`ifTrue:ifFalse:` is a fold over `Bool`:

```
ifTrue:ifFalse: b = fold_Bool b { True → t, False → f }
```

The surface syntax `n = 0 ifTrue: [{}] ifFalse: [...]` is a keyword message send
on the result of `n = 0` (a `Bool`), which desugars to this fold. The "no
conditional" claim is literally true: branching is fold-based dispatch.

## 8. Soundness Sketch

> Full proofs are future work. This section states the theorems and sketches the
> key lemmas, to give the implementation a spec to check against.

### 8.1 Progress

**Theorem (Progress):** If `Γ ⊢ t : σ` (with `Γ` closed), then either `t` is a
value or `t → t'` for some `t'`.

**Sketch:** By induction on the typing derivation. The interesting cases:

- **Fold:** `fold_T e {Cᵢ → hᵢ}` — `e` is either a value (a variant `Cₖ(...)`) or
  steps. If `e = Cₖ(vⱼ)`, the fold steps to `hₖ(vⱼ')` where `vⱼ'` are the
  recursively-folded field values. Since `T` is a μ-type (finite), the recursion
  terminates — the data is a finite tree, and fold descends into it.

- **Unfold:** `unfold_T s {oⱼ → gⱼ}` — this is a *value* (a codata introduction
  form). It does not step until observed. Observation `e.oₖ` steps to
  `gₖ(s)` (producing one observation), which is productive by the typing of `gₖ`.

- **Cofold:** `cofold_T e {oⱼ → t}` — steps by observing `e` and applying the
  handler. Termination depends on the handler not calling continuations
  indefinitely; this is the user's responsibility (as in any fold), but the
  *structure* ensures each step produces one observation.

The absence of general `fix` is essential: without it, the only recursion is
structural (fold) or guarded (unfold), both of which have the measure needed for
Progress.

### 8.2 Preservation

**Theorem (Preservation):** If `Γ ⊢ t : σ` and `t → t'`, then `Γ ⊢ t' : σ`.

**Sketch:** By induction on the typing derivation, case on the step.

- **T-Sub (subsumption):** If `t : σ` and `σ <: τ`, then after a step `t' : σ`
  (by IH), and `t' : τ` by T-Sub. Subtyping is preserved.

- **T-Fold:** The fold step `fold_T (Cₖ(vⱼ)) {Cᵢ → hᵢ} → hₖ(vⱼ')` requires
  `hₖ : Fₖ(σ)[α:=σ] → σ` and `vⱼ' : Fₖ(σ)[α:=σ]` (the folded fields). By the typing
  of `hₖ`, the result is `σ`. The substitution `[α:=σ]` is well-defined because the
  recursive positions are consistently replaced.

- **T-Unfold / T-Obs:** Observation `e.oₖ → gₖ(s)`. By T-Unfold, `gₖ : Σ →
  Gₖ(Σ)[α:=Σ]`, and `s : Σ`, so `gₖ(s) : Gₖ(Σ)[α:=Σ]`. The observation type is
  `Gₖ(T)[α:=T]`; by the unfold's typing, `Σ` is chosen such that this is
  consistent (the seed type determines the observation type). Preservation holds.

- **T-TApp:** Type application substitutes `υ` for `α`. By the substitution lemma
  (types substitute cleanly under bounds), the result type is `τ[α:=υ]`, and
  `υ <: σ` (the bound) ensures the substitution is valid.

**Substitution lemma:** If `Δ, α <: σ ⊢ τ₁ <: τ₂` and `Δ ⊢ υ <: σ`, then
`Δ ⊢ τ₁[α:=υ] <: τ₂[α:=υ]`. Standard for F<: (Pierce & Steffen).

### 8.3 What is *not* proved here

- **Law soundness** ("declared `properties` hold for all inputs") is a *separate*
  theorem, not required for type soundness. A program with a false `associative`
  declaration is still type-safe; it fails its law check (statically or at
  runtime). See `contracts-and-laws.md` (planned).

- **Contract soundness** (demands/ensures/rescue preserve invariants) is also
  separate — it's a property of the elaboration, not the core calculus.

- **Termination of cofold** is not guaranteed by the calculus alone (a cofold
  handler that always calls continuations diverges). This matches lapis-js, where
  behavior folds are user-controlled. The core guarantees *productivity* of unfold
  (each step yields an observation) but not *termination* of cofold (the consumer
  decides when to stop). This is the standard codata position.

## 9. Open Questions for the Core

1. **Fold dispatch model.** Is fold dynamic-dispatch (method on variant prototype,
   inherited via comb chain) or static-dispatch (pattern match on tag)? The
   prototype uses dynamic; LC as written above is static (handlers keyed on
   variant name). The elaboration must reconcile: comb inheritance means an
   extended fold inherits parent handlers — this is dynamic dispatch in practice.
   *Decision needed:* model fold as a method dispatch in the core, or as a static
   match with elaboration resolving inheritance.

2. **Equality.** Structural equality for μ (frozen objects, field-by-field);
   bisimulation for ν (same observations ⇒ equivalent). `instanceof` across the
   comb chain is subtype-test + structural-identity. Formalize `=` and `≈`.

3. **Strictness of data fields.** LC as written is eager for data. If a field
   needs laziness, is it `Lazy τ` (an explicit type) or a `behavior`-typed field?
   Recommendation: explicit `Lazy τ` = `ν α. {force: τ}` — a trivial codata
   wrapper. Keeps the eager side total-by-construction.

4. **Multi-sorted algebras.** Multiple μ-types referencing each other (cross-sort
   fields). LC handles this (types reference types), but mutual recursion needs
   simultaneous μ-bindings: `μ α₁. ..., μ α₂. ...`. The elaboration must handle
   deferred materialization (declare all, then materialize).

5. **Intersection types and protocol conformance.** Is `τ ∧ P` a first-class type
   or an elaboration-time constraint? If first-class, the subtyping rules need
   distribution laws (`(σ → τ) ∧ P` etc.). If elaboration-time, protocols are
   constraints discharged at conformance checking, not runtime types. The
   "static where possible, dynamic when needed" philosophy suggests: constraints
   by default, first-class in live-image mode.

6. **Blame in the calculus?** Contracts currently elaborate to folds over `Bool`
   and `Result` — blame is a runtime concern, not a calculus concern. Wadler's
   blame calculus makes blame labels first-class core entities, enabling the
   blame theorem (well-typed components can't be blamed) to be proved at the
   calculus level. Lapis's contracts are richer (DbC with `rescue`, LSP
   subcontracting tied to the subtyping lattice), and the interaction of
   subtyping + contracts + blame may require calculus-level support to formalize
   the blame theorem. Deferred to Stage 5 (contracts + laws).

## 10. Notation Summary

| Notation | Meaning |
|---|---|
| `μ α. Σᵢ Cᵢ(σᵢ)` | recursive data type (sum of named variants) |
| `μ α. Σᵢ pᵢ` | pattern-matched data type (sum of pattern constructors) |
| `Token` | raw matched text (the one non-μ/ν primitive) |
| `match(pₖ)` | pattern-matched construction (introduction via lexer match) |
| `ν α. Πⱼ oⱼ(σⱼ)` | corecursive codata type (product of observers) |
| `Fᵢ(σ)[α := σ]` | substitute result type σ for recursive position α in variant Cᵢ's fields |
| `Gⱼ(Σ)[α := Σ]` | substitute seed type Σ for Self in observer oⱼ's type |
| `fold_T e {Cᵢ → hᵢ}` | catamorphism over data `e : T` |
| `unfold_T s {oⱼ → gⱼ}` | anamorphism from seed `s : Σ` into codata `T` |
| `cofold_T e {oⱼ → t}` | codata elimination (behavior fold) |
| `Λα <: σ. t` | bounded type abstraction (F<:) |
| `σ <: τ` | subtyping |
| `σ ∧ τ` | intersection type (protocol conformance) |
| `Any` / `Nothing` | top / bottom of the subtyping lattice |