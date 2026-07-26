# LC — The Lapis Core Calculus

> **Status:** Draft v0.1. This document presents LC in TAPL style: syntax,
> evaluation rules, typing rules, and soundness. It is the formal specification
> that the implementation checks against. For design rationale, elaboration of
> surface constructs, and discussion, see [`elaboration.md`](./elaboration.md)
> and [`design-decisions.md`](../design-decisions.md).

## 1. Overview

LC (formally, $F_{<:\mu\nu}$) is **F<: with recursive and corecursive types**,
where **fold and unfold are the only recursion forms**. Two properties define it:

1. **F<:.** Subtyping subsumes generics.
2. **μ/ν, not general fix.** Data is μ (initial algebra); codata is ν (final
   coalgebra). No `fix` or `Y`. Termination and productivity follow from structure.

The calculus is pure — no effect type or operation appears in the syntax.

`cofold [T]` is an elimination form for codata (the dual of fold), not a
recursion form — it observes, it does not recurse.

`match(pₖ)` is a value introduced by the lexer (external to the calculus).
It appears as a term and a value, but no evaluation rule produces it; it is
an axiom of the operational semantics.

## 2. Syntax

### 2.1 Types

```
σ, τ ::= α                  type variable
       | σ → τ              function type
       | μ α. Σᵢ Cᵢ(σᵢ)      recursive data type (sum of named variants)
       | μ α. Σᵢ pᵢ          pattern-matched data type (sum of pattern constructors)
       | ν α. Πⱼ oⱼ(σⱼ)      corecursive codata type (product of named observers)
       | Token               raw matched text
       | Any                 top
       | Nothing             bottom
       | σ ∧ τ              intersection type
```

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
```

### 2.3 Values

```
v ::= λx:σ. t                           closure
    | Cᵢ(v₁, ..., vₙ)                   constructed variant (eager: fields are values)
    | match(pₖ)                         matched token (a value of pattern-matched type)
    | unfold [T] s {oⱼ → gⱼ}            codata value (lazy: seed stored, generators deferred)
```

### 2.4 Contexts

```
Γ ::= ∅ | Γ, x:σ          term variable context
Δ ::= ∅ | Δ, α <: σ       type variable context (with bounds)
```

### 2.5 Notation

| Notation | Meaning |
|---|---|
| `μ α. Σᵢ Cᵢ(σᵢ)` | recursive data type (sum of named variants) |
| `μ α. Σᵢ pᵢ` | pattern-matched data type (sum of pattern constructors) |
| `ν α. Πⱼ oⱼ(σⱼ)` | corecursive codata type (product of observers) |
| `Token` | raw matched text (the one non-μ/ν primitive) |
| `match(pₖ)` | pattern-matched construction (introduction via lexer match) |
| `Fᵢ` | field type functor for variant Cᵢ: maps recursive position α to Cᵢ's field types |
| `Gⱼ` | observer type functor for observer oⱼ: maps corecursive position α (Self) to oⱼ's type |
| `Fᵢ(σ)[α := σ]` | substitute result type σ for recursive position α in variant Cᵢ's fields |
| `Gⱼ(Σ)[α := Σ]` | substitute seed type Σ for Self in observer oⱼ's type |
| `fold [T] t {Cᵢ → tᵢ}` | catamorphism over data `t : T` (handlers tᵢ) |
| `unfold [T] s {oⱼ → gⱼ}` | anamorphism from seed `s : Σ` into codata `T` (generators gⱼ) |
| `cofold [T] e {oⱼ → t}` | codata elimination (behavior fold; handler t receives all observations) |
| `Λα <: σ. t` | bounded type abstraction (F<:) |
| `σ <: τ` | subtyping |
| `σ ∧ τ` | intersection type (protocol conformance) |
| `Any` / `Nothing` | top / bottom of the subtyping lattice |

## 3. Evaluation

### 3.1 Evaluation Rules

```
(λx:σ. t) v → [x ↦ v] t                              (E-App)

fold [T] (Cₖ(vⱼ)) {Cᵢ(xⱼ) → tᵢ}
  → [xⱼ ↦ vⱼ'] tₖ                                    (E-Fold)
  where for each field j:
    vⱼ' = fold [T] vⱼ {Cᵢ → tᵢ}   if j is a recursive (Family) field
    vⱼ' = vⱼ                       otherwise

fold [T] (match(pₖ)) {pᵢ → tᵢ}
  → [match ↦ tok] tₖ                                  (E-FoldMatch)
  where tok is the matched Token for pattern pₖ

(unfold [T] s {oⱼ → gⱼ}).oₖ → gₖ(s)                    (E-Obs)

cofold [T] (unfold [T] s {oⱼ → gⱼ}) {oⱼ(xⱼ) → t}
  → [xⱼ ↦ gⱼ(s)] t                                    (E-Cofold)

let x:σ = v in u → [x ↦ v] u                          (E-Let)

(Λα <: σ. t) [τ] → [α ↦ τ] t                          (E-TApp)

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
```

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

### 5.2 Fold (catamorphism — data elimination)

```
   T = μ α. Σᵢ Cᵢ(Fᵢ(α))
   Γ ⊢ e : T
   Γ ⊢ tᵢ : Fᵢ(σ)[α := σ] → σ   (for each variant Cᵢ)
   ────────────────────────────────────────────────────────────────  (T-Fold)
   Γ ⊢ fold [T] e {Cᵢ(xⱼ) → tᵢ} : σ
```

### 5.2b Pattern-matched fold

```
   T = μ α. Σᵢ pᵢ
   Γ ⊢ e : T
   Γ ⊢ tᵢ : Token → σ   (for each pattern pᵢ)
   ────────────────────────────────────────────────────────────────  (T-FoldMatch)
   Γ ⊢ fold [T] e {pᵢ → tᵢ} : σ
```

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

`cofold` is the codata dual of `fold`: it eliminates a codata value by
observing all observers simultaneously (the product). `T-Obs` observes one
observer at a time; `T-Cofold` observes all at once, with continuation fields
exposed as fold functions.

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

## 6. Soundness

### 6.1 Progress

**Theorem (Progress):** If $\Gamma \vdash t : \sigma$ (with $\Gamma$ closed),
then either $t$ is a value or $t \to t'$ for some $t'$.

**Sketch:** By induction on the typing derivation.

- **Fold:** `fold [T] e {Cᵢ → tᵢ}` — `e` is either a value or steps. If
  `e = Cₖ(vⱼ)`, the fold steps to `tₖ[xⱼ ↦ vⱼ']` (E-Fold). If `e = match(pₖ)`, the
  fold steps to `tₖ[match ↦ tok]` (E-FoldMatch). Since `T` is a μ-type (finite), the
  recursion terminates.

- **Unfold:** `unfold [T] s {oⱼ → gⱼ}` is a value. It does not step until observed.
  Observation `e.oₖ` steps to `gₖ(s)` (E-Obs), productive by the typing of `gₖ`.

- **Cofold:** Steps by observing `e` and applying the handler (E-Cofold). Each
  step produces one observation.

### 6.2 Preservation

**Theorem (Preservation):** If $\Gamma \vdash t : \sigma$ and $t \to t'$,
then $\Gamma \vdash t' : \sigma$.

**Sketch:** By induction on the typing derivation, case on the step.

- **E-Fold:** `fold [T] (Cₖ(vⱼ)) {Cᵢ → tᵢ} → tₖ[xⱼ ↦ vⱼ']`. By T-Fold,
  `tₖ : Fₖ(σ)[α:=σ] → σ` and `vⱼ' : Fₖ(σ)[α:=σ]`. By the typing of `tₖ`, the
  result is `σ`.

- **E-FoldMatch:** `fold [T] (match(pₖ)) {pᵢ → tᵢ} → tₖ[match ↦ tok]`. By
  T-FoldMatch, `tₖ : Token → σ` and `tok : Token`. Result is `σ`.

- **E-Obs:** `e.oₖ → gₖ(s)`. By T-Unfold, `gₖ : Σ → Gₖ(Σ)[α:=Σ]` and `s : Σ`.
  Result is `Gₖ(Σ)[α:=Σ]`, consistent with `Gₖ(T)[α:=T]` by the unfold's typing.

- **E-TApp:** `[α ↦ T₂] t`. By the substitution lemma, the result type is
  `τ[α:=T₂]`, and `T₂ <: σ` (the bound) ensures validity.

**Substitution lemma:** If `Δ, α <: σ ⊢ τ₁ <: τ₂` and `Δ ⊢ T₂ <: σ`, then
`Δ ⊢ τ₁[α:=T₂] <: τ₂[α:=T₂]` (Pierce & Steffen).
