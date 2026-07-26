# Lapis Semantics

> **Status:** Draft v0.1. This document defines the meaning of Lapis programs:
> denotational semantics (what programs *mean*), operational semantics (how
> programs *compute*), and the bialgebraic laws that connect them. It also
> specifies the evaluation strategy (eager data / lazy codata) and the
> attribute-grammar structure for static analysis passes.

## 1. The Organizing Principle: Hutton's Duality

Hutton (1998) showed that **fold structures denotational semantics** and **unfold
structures operational semantics**. This is not a metaphor — it is a literal
isomorphism:

| Semantics | Recursion form | Direction | What it does |
|---|---|---|---|
| Denotational | Fold (catamorphism) | Bottom-up (leaves → root) | Maps syntax to semantic values: `〚·〛 : AST → Value` |
| Operational | Unfold (anamorphism) | Top-down (seed → trace) | Generates transition sequences: `→ : State → State` |

For most languages, this is a theoretical observation — the language has `fold`
and `unfold` in a library, and the semantics is written separately. **For Lapis,
this is the definition.** Fold and unfold are the *only* recursion forms in the
language. So:

- The **denotational semantics of a `data` type** *is* its fold operations. Each
  `fold` declaration defines the meaning function for that type — the handlers
  *are* the denotation of each variant.
- The **operational semantics of a `behavior` type** *is* its unfold operations.
  Each `unfold` declaration defines the transition function for that type — the
  generators *are* the dynamics of each observer.

This makes Lapis unusually self-describing: the semantics is not an external
mathematical structure imposed on the language, but the language's own
constructs read at the meta-level.

## 2. Denotational Semantics

### 2.1 Meaning as Fold

The meaning function `〚·〛` maps Lapis core terms to semantic values. Following
Hutton, we define it as a fold over the syntax tree.

**Semantic domains:**

```
Val ::= VVariant(T, C, [Val])        a constructed variant: type T, constructor C, field values
      | VMatch(T, Token)             a pattern-matched value: type T, matched text
      | VCodata(T, Σ)                a codata value: type T, hidden seed state Σ
      | VFun(Val → Val)              a function value (closure)
      | VResult(Val) | VError(Error)  contract elaboration results
```

Note: `VInt` and `VStr` are eliminated — integers and strings are pattern-matched
data types (`Nat = μ α. [0-9]+`, `String = μ α. "<Char>*"`), so their values are
`VMatch(Nat, "42")` and `VMatch(String, "hello")` respectively. The fold handler
for a pattern-matched type transforms the `Token` into whatever representation the
runtime needs (e.g., a native integer).

**The meaning function is a fold over the AST:**

```
〚x〛_ρ         = ρ(x)                          (variable lookup in environment ρ)
〚λx:σ. t〛_ρ   = VFun(λv. 〚t〛_{ρ, x↦v})       (lambda → closure)
〚t u〛_ρ       = (〚t〛_ρ)(〚u〛_ρ)               (application)
〚Cᵢ(tⱼ)〛_ρ    = VVariant(T, Cᵢ, [〚tⱼ〛_ρ])     (named variant construction — eager: fields evaluated now)
〚match(pₖ)〛   = VMatch(T, tok)                 (pattern-matched construction — tok is the matched Token)
〚fold_T e {Cᵢ(xⱼ) → tᵢ}〛_ρ = fold_T 〚e〛_ρ h    (fold — see below)
〚e.oₖ〛_ρ      = observe_oₖ(〚e〛_ρ)              (observation — lazy: forces the codata value)
〚unfold_T s {oⱼ → gⱼ}〛_ρ = VCodata(T, 〚s〛_ρ)  (unfold — lazy: seed stored, not evaluated)
```

### 2.2 The Fold Semantics

The denotation of `fold_T e {Cᵢ(xⱼ) → tᵢ}` is the catamorphism over the data
value `e`. This is where the eager/structural nature of data is realized:

```
fold_T (VVariant(T, Cₖ, [vⱼ])) h
  = hₖ([fold_T vⱼ' h | vⱼ' ∈ recursiveFields(vⱼ)] ++ [vⱼ | vⱼ ∈ nonRecursiveFields(vⱼ)])
```

Where:
- `hₖ` is the handler for variant `Cₖ`, evaluated in the environment extended
  with the bound field names `xⱼ`.
- **Recursive fields** (`Family` positions) are *already folded* — the recursion
  descends into them first, producing `Val` results, which are passed to the
  handler. This is the bottom-up (leaves → root) traversal.
- **Non-recursive fields** are passed as-is (their `Val` already computed at
  construction time, since data is eager).

**Termination:** The data value `VVariant(T, Cₖ, [vⱼ])` is a finite tree (data is
finite by construction — μ-types are initial algebras, the least fixed point).
The fold descends into recursive fields, which are strictly smaller sub-trees.
By well-founded induction on the tree structure, the fold terminates.

**Pattern-matched fold:** For `VMatch(T, tok)`, the fold is a single-step
extraction: `fold_T (VMatch(T, tok)) h = hₖ(tok)` where `hₖ` is the handler for
the pattern that matched. There is no recursion (pattern-matched constructors
have no `Family` fields). The handler receives the `Token` and transforms it.

**Stack safety:** The implementation uses iterative post-order traversal with an
explicit work stack (as in lapis-js), not recursive function calls. This makes
folds over deep structures (e.g., 100k-element lists) safe without tail-call
optimization.

### 2.3 The Unfold Semantics (Denotational)

The denotation of `unfold_T s {oⱼ → gⱼ}` is a codata value — a *thunk* that
defers computation until observation:

```
〚unfold_T s {oⱼ → gⱼ}〛_ρ = VCodata(T, 〚s〛_ρ)
```

The seed `〚s〛_ρ` is stored but **not evaluated further**. The generators `gⱼ`
are not run at construction time. This is the lazy codata strategy.

### 2.4 The Observation Semantics

When a codata value is observed (`e.oₖ`), the corresponding generator runs:

```
observe_oₖ(VCodata(T, σ))
  = let gₖ = generatorFor(T, oₖ) in
    let result = gₖ(σ) in
    case result of
      VVal(v) => v                           (a simple value: return it)
      VSeed(σ') => VCodata(T, σ')            (a continuation: produce next codata value, memoized)
```

**Memoization:** Continuation observations (`Self`-typed) are memoized —
observing `e.tail` twice returns the same `VCodata` value. Simple observations
are recomputed on each access (matching lapis-js semantics).

**Productivity:** Each observation produces one value before potentially
generating a continuation. The codata value is potentially infinite (ν-types are
final coalgebras, the greatest fixed point), but each observation is finite.

### 2.5 Eager Data, Lazy Codata — Formalized

The denotational semantics encodes the evaluation strategy directly:

| Construct | When are sub-terms evaluated? | Strategy |
|---|---|---|
| `Cᵢ(tⱼ)` (variant construction) | All `tⱼ` evaluated immediately | **Eager** |
| `fold_T e {...}` | `e` evaluated, then traversal is eager | **Eager** |
| `unfold_T s {...}` | `s` evaluated; generators deferred | **Lazy** |
| `e.oₖ` (observation) | Forces the codata value, runs generator | **Lazy** (on-demand) |
| `t u` (application) | `t` and `u` evaluated, then function applied | **Eager** (call-by-value) |
| `λx:σ. t` (lambda) | Body deferred until application | **Lazy** (body) |

The strategy is **fixed by construct kind**, not by annotation. Data operations
are eager; codata operations are lazy. The user does not choose — the declaration
(`data` vs `behavior`) chooses.

### 2.6 Church–Rosser and Compiler Freedom

**Within the eager strategy (data):** The eager reduction is confluent for
terminating terms (Church–Rosser property). This means the compiler can:

- Reorder independent strict computations
- Common-subexpression-eliminate
- Short-circuit (e.g., identity guards on folds — see §4.3)
- Memoize pure computations

...without changing the observable result, because any reduction order that
terminates yields the same normal form.

**Within the lazy strategy (codata):** The lazy reduction is likewise confluent
for productive observations. The compiler can:

- Discard unforced thunks (garbage collect unused continuations)
- Share forced thunks (memoization)
- Reorder independent observations

...without changing the observable result.

**What Church–Rosser does *not* justify:** Cross-strategy reordering. You cannot
move an eager data computation into a lazy codata context (or vice versa) and
expect the same result, because the two strategies differ on divergence and
error-ordering. The boundary is fixed by declaration kind, and the compiler
respects it.

## 3. Operational Semantics

### 3.1 Dynamics as Unfold

Following Hutton, the operational semantics is an unfold: from an initial state
(seed), the transition function generates a sequence of states (a trace).

For Lapis, the "states" are core terms, and the "transition function" is the
small-step reduction relation `→`. The trace of a term `t` is:

```
trace(t) = unfold (λs. step(s)) t
```

Where `step` produces either `Some(t')` (the term takes a step to `t'`) or
`None` (the term is a value / stuck). This is an anamorphism over the reduction
sequence.

### 3.2 Small-Step Reduction Rules

The operational semantics is defined by the following reduction rules. These are
the *core* rules — contract elaboration and law-exploitation optimizations are
layered on top (see §4).

**Application:**

```
(λx:σ. t) v → t[x := v]                    (E-App)
```

**Fold (data elimination):**

```
fold_T (Cₖ(vⱼ)) {Cᵢ(xⱼ) → tᵢ} → tₖ[xⱼ := fold_recursive(vⱼ)]
```

Where `fold_recursive(vⱼ)` replaces each recursive field `vⱼ` with
`fold_T vⱼ {Cᵢ(xⱼ) → tᵢ}` (the recursive fold result) and leaves non-recursive
fields as `vⱼ`. This is the single-step version; the implementation uses
iterative post-order traversal for stack safety.

**Observation (codata elimination):**

```
(unfold_T s {oⱼ → gⱼ}).oₖ → gₖ(s)    (if oₖ is a simple observer)
(unfold_T s {oⱼ → gⱼ}).oₖ → unfold_T (gₖ(s)) {oⱼ → gⱼ}    (if oₖ is a continuation)
```

For a continuation observer, observing `oₖ` produces a *new* codata value with
the next seed. This is the productive step — one observation is yielded before
the next continuation is available.

**Let:**

```
let x:σ = v in t → t[x := v]                (E-Let)
```

**Type application:**

```
(Λα <: σ. t)[τ] → t[α := τ]                 (E-TApp)
```

### 3.3 Values

A term is a **value** (a normal form) when it cannot take a step:

```
Values:
  v ::= λx:σ. t              (closure — a value)
       | Λα <: σ. t           (type abstraction — a value)
       | Cᵢ(vⱼ)              (fully constructed variant — a value when all fields are values)
       | unfold_T s {oⱼ → gⱼ}  (codata introduction — a value; generators deferred)
```

Note that `unfold_T s {oⱼ → gⱼ}` is a value even though `s` may not be fully
reduced — codata introduction is a value form because it defers computation. The
seed `s` is evaluated (eager application of the unfold's argument), but the
generators are not run until observation.

### 3.4 Progress and Preservation (Operational)

The operational semantics satisfies Progress and Preservation (see
[`core-calculus.md`](./core-calculus.md) §8). The key points:

- **Progress:** Every well-typed closed term is either a value or can take a
  step. The interesting case is fold: `fold_T (Cₖ(vⱼ)) {Cᵢ → tᵢ}` always steps
  because `Cₖ` has a handler (exhaustiveness is enforced). Unfold is already a
  value; it steps only when observed.

- **Preservation:** Each step preserves the type. The fold step substitutes
  folded results (of type σ) for recursive fields, and the handler `tₖ` has type
  σ by the T-Fold rule. The observation step produces a value of the observer's
  type by T-Obs.

## 4. Bialgebraic Semantics (Turi-Plotkin)

### 4.1 The Bialgebraic Connection

Turi & Plotkin (1997) showed that denotational semantics (fold) and operational
semantics (unfold) are not independent — they are connected by a **bialgebraic
structure** that makes them compatible.

The key insight: the syntax functor `F` (which describes the shape of the AST)
has both an algebra (the denotational semantics: `F(Val) → Val`) and a coalgebra
(the operational semantics: `F(State) → State`). A **bialgebra** is a structure
that is simultaneously an algebra and a coalgebra, with a compatibility
condition.

For Lapis, this means:

- The **fold** (denotational semantics) and the **unfold** (operational
  semantics) agree: the meaning of a term computed bottom-up (denotational)
  equals the meaning of the term computed by running the reduction sequence to
  a normal form (operational).
- This is the **adequacy** theorem: `〚t〛 = 〚t'〛` whenever `t →* t'` and `t'` is
  a value.

### 4.2 The λ- and co-λ-Homomorphism Properties

In the bialgebraic framework:

- **Fold is a λ-homomorphism:** The meaning function `〚·〛` commutes with the
  algebra structure. For a variant `Cᵢ(tⱼ)`:

  ```
  〚Cᵢ(tⱼ)〛 = hᵢ(〚tⱼ〛)
  ```

  The meaning of a construction is the handler applied to the meanings of the
  sub-terms. This is exactly the fold equation.

- **Unfold is a co-λ-homomorphism:** The transition function commutes with the
  coalgebra structure. For an observation `e.oₖ`:

  ```
  step(e.oₖ) = gₖ(step(e))
  ```

  The transition of an observation is the generator applied to the transition of
  the observed value. This is exactly the unfold equation.

These properties are not additional axioms — they *follow* from the typing rules
(T-Fold and T-Unfold in [`core-calculus.md`](./core-calculus.md) §4). The
bialgebraic structure is *built into* the type system.

### 4.3 Law Exploitation as Bialgebraic Optimization

The algebraic law declarations (`properties`) are the point where the bialgebraic
structure becomes *useful* for optimization:

- **Identity guard:** `identity:E` on a fold means `fold_T E {Cᵢ → tᵢ} = E`. The
  compiler short-circuits: when the identity element is encountered as an
  argument, the fold is not entered. This is justified by the algebra law
  `f(E, x) = x`, which holds because the fold is a homomorphism and the law is
  declared and verified.

- **Horner fusion:** `distributive:sum` on a fold means
  `fold(⊕) ∘ fold(⊗) = fold(⊗-then-⊕)`. The compiler fuses two folds into one
  traversal. This is justified by the distributivity law, which holds because
  both folds are homomorphisms and distributivity is declared and verified.

- **Involutory cancellation:** `involutory` on an operation means `f(f(x)) = x`.
  The compiler cancels consecutive pairs in a merge pipeline. This is justified
  by the involutory law.

In each case, the **enforcement** (every operation is a fold/unfold) guarantees
the **homomorphism property**, which makes the **law** applicable, which enables
the **optimization**. This is the bialgebraic pipeline from structure to laws to
performance.

## 5. Attribute Grammar Equations for Static Analysis

### 5.1 The Grammar-Subclass Layering

Following the derivative-parser library's executable-grammar model (Bracha 2007),
static analysis passes are structured as **grammar subclasses** — each pass
inherits the productions it doesn't override and redefines only the ones that
bind or check.

```
LapisGrammar              (base: syntax → AST)
  ↳ NameResolution        (subclass: threads environment, produces resolved AST)
    ↳ TypeChecking        (subclass: synthesizes types, produces typed AST)
      ↳ LawChecking       (subclass: verifies properties, produces verified AST)
```

Each layer is an **attribute grammar** over the AST: synthesized attributes flow
bottom-up (types, resolved names), inherited attributes flow top-down
(environments, expected types).

### 5.2 Name Resolution (Inherited: Environment)

Name resolution threads a binding environment top-down. The inherited attribute
is `env : Map<String, Binding>`.

```
NameResolution.block(params, body):
  env' = env ∪ { params ↦ fresh bindings }
  resolve(body, env')

NameResolution.foldDecl(name, spec, arms):
  env' = env ∪ { name ↦ fold binding }
  resolve(arms, env')    — each arm's field bindings added to env'

NameResolution.variantRef(name):
  if name ∈ env: return resolved reference
  else: error "unbound reference: name"
```

Productions that don't bind names (literals, binary operators, observations)
inherit unchanged from the base grammar — the subclass doesn't override them.

### 5.3 Type Checking (Synthesized: Type; Inherited: Expected)

Type checking synthesizes a type bottom-up and threads an expected type
top-down. The synthesized attribute is `τ : Type`; the inherited attribute is
`expected : Type | None`.

```
TypeChecking.variant(Cᵢ, fields):
  τ_fields = [check(fieldⱼ, expectedⱼ) for fieldⱼ]
  τ = T    (the data type, from the resolved declaration)
  return τ

TypeChecking.fold(e, handlers):
  τ_e = check(e, None)           — must be a data type T
  for each handler Cᵢ(xⱼ) → tᵢ:
    τ_handler = check(tᵢ, expected)    — handler body must produce expected type
    verify field types: Fᵢ(σ)[α:=σ]    — recursive fields get σ, non-recursive get declared type
  return σ    (the fold result type)

TypeChecking.unfold(seed, generators):
  τ_seed = check(seed, None)     — must be the seed type Σ
  for each generator oⱼ → gⱼ:
    τ_gen = check(gⱼ, None)      — must be Σ → Gⱼ(Σ)[α:=Σ]
  return T    (the codata type)

TypeChecking.subsumption:
  if synthesized τ and expected τ' with τ' <: τ:
    insert T-Sub (subsumption)
  else:
    type error
```

### 5.4 Law Checking (Synthesized: Law obligations)

Law checking verifies declared `properties` against generated samples. This pass
runs after type checking (it needs typed terms to generate valid samples).

```
LawChecking.foldDecl(name, spec, arms):
  if spec has properties: [p₁, p₂, ...]:
    samples = generateSamples(type T)    — singletons, primitive records, shallow recursive
    for each property pᵢ:
      for each sample tuple (s₁, ..., sₙ) relevant to pᵢ:
        result = evaluate(fold with samples)
        if result violates pᵢ:
          throw LawError(name, pᵢ, [s₁, ..., sₙ])
  return verified declaration
```

**Sample generation:** For a data type `T = μ α. Σᵢ Cᵢ(Fᵢ(α))`:
- Singleton variants: one sample each.
- Primitive-field variants: up to three value combinations per variant.
- Recursive-field variants: one shallow recursive sample (one level deep, base
  case for the recursion).

This is *probabilistic* checking, not complete verification — it can miss
counterexamples that only appear at greater depth. The "static where possible,
dynamic when needed" philosophy accepts this: the compiler discharges what it
can, and the runtime can re-check on actual inputs.

### 5.5 When to Use Hand-Written Walkers

The grammar-subclass layering works for:
- **Synthesized-only passes** (types flow up): type checking, law checking.
- **Single-inherited passes** (one environment flows down): name resolution.

It gets awkward for passes needing **bidirectional** attribute flow with mutual
dependency — the classic AG knot-tying problem. Examples:
- **Polymorphic recursion inference** (the type of a recursive call depends on
  the type of the body, which depends on the recursive call).
- **Exhaustiveness checking with subtyping** (whether a fold's handlers cover all
  variants depends on the subtyping hierarchy, which may involve mutual
  references between types).

For these, a hand-written two-pass walker (collect, then check) is clearer than
forcing the grammar-subclass shape. The principle: **use the grammar-subclass
layering as the default structure; allow hand-written walkers where AG flow is
genuinely bidirectional.**

## 6. Contract Semantics

### 6.1 Contract Assessment Flow

Contracts elaborate to core terms (see [`core-calculus.md`](./core-calculus.md)
§6). The operational semantics of a contracted operation is:

```
op(args) with contracts:
  1. Check invariant(self)           — if false: InvariantError (implementer's fault)
  2. Check demands(self, args)       — if false: DemandsError (caller's fault)
  3. Capture old = snapshot(self)
  4. result = body(self, args)       — may throw
  5. Check ensures(self, old, result, args)  — if false: EnsuresError (implementer's fault)
  6. Check invariant(self)           — if false: InvariantError
  7. Return result
```

**Error path (body or ensures throws):**

```
  4'. result = body(self, args) → throws
  5'. rescue(self, error, args, retry):
      - if retry(newArgs) called: go to step 2 with newArgs (retry counter decremented)
      - if rescue returns value: that becomes result, go to step 6
      - if rescue throws: check invariant, propagate error
```

**DemandsError is never caught by rescue** — precondition failures are always
propagated to the caller. This is the blame model: demands = caller's fault,
ensures/invariant = implementer's fault.

### 6.2 Observation-Gated Contracts on Codata

For codata (behavior) operations, contracts are **observation-gated**:

- `demands` on an unfold is checked when the unfold is *called* (the seed is
  validated at construction time of the codata value).
- `ensures` on an unfold is checked when an *observation* is forced — the
  generator runs, produces a value, and the ensures clause is checked against
  that value.
- `rescue` on an unfold fires when a generator *throws* during observation.

This matches the lazy evaluation strategy: contracts fire at observation time,
not at construction time. If the caller never observes a codata value, its
contracts never fire. This is **correct** — it mirrors the laziness of the codata
itself — but must be stated explicitly as a semantic property, not a surprise.

### 6.3 LSP Subcontracting

When a child type extends a parent (comb inheritance) and both define contracts
for the same operation, the contracts compose per the Liskov Substitution
Principle:

| Clause | Composition | Rationale |
|---|---|---|
| `demands` | OR (weaken) | Child accepts more inputs than parent |
| `ensures` | AND (strengthen) | Child guarantees everything parent guarantees, plus more |
| `invariant` | AND (strengthen) | All invariants in the hierarchy must hold |
| `rescue` | Override or inherit | Child's rescue replaces parent's; if absent, parent's is inherited |

The effective contract is:

```
demands_eff = demands_parent OR demands_child
ensures_eff = ensures_parent AND ensures_child
invariant_eff = invariant_parent AND invariant_child
rescue_eff = rescue_child if present, else rescue_parent
```

This is checked at elaboration time (when the child's `.ops()` is processed) and
enforced at runtime.

## 7. Equality

### 7.1 Data Equality (Structural)

Data values (μ-types) are **structurally equal** if they are the same variant
with structurally equal fields:

```
VVariant(T, C, [vⱼ]) = VVariant(T, C, [wⱼ])  iff  ∀j. vⱼ = wⱼ
```

Since data is eager and frozen (immutable), structural equality is well-defined
and decidable. Two data values are equal iff they have the same shape and the
same field values.

### 7.2 Codata Equality (Observational / Bisimulation)

Codata values (ν-types) are **observationally equal** (bisimilar) if they produce
the same observations forever:

```
VCodata(T, σ) ≈ VCodata(T, σ')  iff  ∀oⱼ. observe_oⱼ(σ) ≈ observe_oⱼ(σ')
```

Where `≈` on observation results is:
- For simple values: structural equality.
- For continuations: bisimulation (recursive definition).

Bisimulation is **coinductive** — it is the greatest fixed point of the
observation-equivalence relation. In general, bisimulation is undecidable for
arbitrary codata; the language provides `≈` as a declared/checked property, not
a computable primitive. Practical equality checks use bounded observation
(check N levels deep) or declared bisimulation invariants.

### 7.3 `instanceof` and Subtype Testing

`instanceof` across the comb-inheritance chain is a **subtype test**, not an
equality test:

```
v instanceof T  iff  typeOf(v) <: T
```

Where `<:` is the subtyping relation from [`core-calculus.md`](./core-calculus.md)
§3. Comb inheritance (prototype chain + delegation chain) makes this work at
runtime: an instance of `ExtendedColor.Yellow` is `instanceof ExtendedColor`,
`instanceof Color`, and `instanceof Any` — all via the delegation chain.

`instanceof` is **not** structural equality — it tests membership in a type
family, not value equality. This distinction must be clear in the semantics:
`= ` is structural equality (data) or bisimulation (codata); `instanceof` is
subtype membership.

## 8. Semantic Properties Summary

| Property | Statement | Status |
|---|---|---|
| **Termination of fold** | `fold_T e {Cᵢ → tᵢ}` terminates for all finite `e : T` | Guaranteed by μ-type finiteness + structural recursion |
| **Productivity of unfold** | `unfold_T s {oⱼ → gⱼ}` produces one observation before recursing | Guaranteed by ν-type guardedness |
| **Progress** | Every well-typed closed term is a value or steps | See core-calculus.md §8.1 |
| **Preservation** | If `t : σ` and `t → t'` then `t' : σ` | See core-calculus.md §8.2 |
| **Adequacy** | `〚t〛 = 〚t'〛` when `t →* t'` and `t'` is a value | Bialgebraic property (Turi-Plotkin); follows from fold/unfold homomorphism |
| **Confluence (eager)** | Eager reduction is confluent for terminating terms | Church–Rosser; justifies compiler rewrites within eager strategy |
| **Confluence (lazy)** | Lazy reduction is confluent for productive observations | Church–Rosser (dual); justifies compiler rewrites within lazy strategy |
| **Law soundness** | Declared `properties` hold for all inputs | *Separate* theorem; best-effort (static where possible, dynamic when needed) |
| **Contract soundness** | Contracts preserve invariants; blame is correct | Property of the elaboration; demands=caller, ensures/invariant=implementer |

## 9. Open Questions

1. **Adequacy proof.** The bialgebraic adequacy theorem (`〚t〛 = 〚t'〛` when
   `t →* v`) is sketched via the Turi-Plotkin framework but not formally proved.
   The proof requires showing that the denotational fold and the operational
   unfold are compatible bialgebra structures. This is future work.

2. **Bisimulation decidability.** Codata equality (§7.2) is coinductive and
   generally undecidable. What bounded-observation strategy does the language
   provide? What declared bisimulation invariants are checkable?

3. **Contract semantics and evaluation order.** The observation-gating of codata
   contracts (§6.2) means contract behavior depends on the lazy strategy. Is
   there a *denotational* characterization of contracts that is
   strategy-independent? (The `Result`-typed elaboration is one, but it doesn't
   capture the observation-gating.)

4. **Multi-sorted mutual recursion.** The semantics as written handles single
   μ/ν types. Mutual recursion (multiple data types referencing each other)
   requires simultaneous fixed points: `μ α₁. ..., μ α₂. ...`. The fold/unfold
   semantics generalize (the recursion is over a tuple of types), but the
   formalization needs to be written down.

5. **Cofold termination.** Cofold (codata elimination, §4.6 of core-calculus.md)
   is not guaranteed to terminate — the handler decides when to stop calling
   continuations. This is the standard codata position (the consumer controls
   termination), but it means the operational semantics of cofold is
   *partial*. Is this acceptable, or should cofold have a termination measure
   (e.g., a fuel parameter)?

## 10. References

- Hutton, G., "Fold and Unfold for Program Semantics" (1998) — fold = denotational, unfold = operational
- Turi, D. & Plotkin, G., "Towards a Mathematical Operational Semantics" (1997) — bialgebraic semantics
- Meertens, L., "Algorithmics — Towards Programming as a Mathematical Activity" (1986) — BMF
- Malcolm, G., "Algebraic Data Types and Program Transformation" (1990) — homomorphisms, fusion
- Bird, R., "An Introduction to the Theory of Lists" (1987) — program calculation
- Amadio, R. & Cardelli, L., "Subtyping Recursive Types" (1993) — μ-type semantics
- Winskel, G., "The Formal Semantics of Programming Languages" (1993) — denotational/operational foundations
- Bracha, G., "Executable Grammars in Newspeak" (2007) — grammar-subclass layering for analysis
- Knuth, D. E., "Semantics of Context-Free Languages" (1968) — attribute grammars