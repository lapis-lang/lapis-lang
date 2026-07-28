# Grammar as Semantics

> **Status:** Draft v0.1. This document specifies the implementation architecture for Lapis's
> semantic analysis passes: how grammar subclassing, the `chain` combinator, and grammar-native
> contracts together turn the parser into the compiler pipeline. The formal typing rules live in
> [`lc.md`](./lc.md); the denotational/operational semantics live in
> [`semantics.md`](./semantics.md). This document is about _how those rules are implemented_.

## 1. The Thesis

In most compilers, the parser produces an AST and then a separate pipeline of passes (name
resolution, type checking, evaluation) walks that AST. Each pass is a distinct data structure and a
distinct traversal.

Lapis uses a different model, inherited from Bracha's executable-grammar work and realized in
[`zipper-grammar`](https://jsr.io/@lapis-lang/zipper-grammar): **the grammar class hierarchy _is_
the compiler pipeline.** Each semantic pass is a subclass of the grammar that overrides the
productions needing semantic action and inherits the rest unchanged via `super`. The result is that:

- A typing judgment `Γ ⊢ e : τ` becomes a parameterised production `expr(Γ): Parser<Type>`.
- An evaluation judgment `ρ ⊢ e ⇓ v` becomes `expr(ρ): Parser<Value>`.
- An inference rule's premises become `@requires` contracts; its conclusion becomes `@ensures`.
- Rejection (empty parse forest) _is_ the type error.

The grammar is no longer merely recognising syntax — it is _deriving judgments_. This is the
"judgments as productions" pattern, and it is the architectural backbone of the Lapis compiler.

## 2. The `super`-Based Multi-Pass Model

### 2.1 The Pipeline

The semantic passes form a linear subclass chain. Each layer calls `super` to get the previous
layer's complete output, threads its own context as method arguments (inherited attributes), and
returns a richer result (synthesized attributes):

```
LapisGrammar              (characters → AST)           — src/grammar.ts
  → LapisNameResolver     (AST → resolved AST)         — src/nameresolver.ts
    → LapisTypeChecker    (resolved AST → typed AST)   — src/typechecker.ts
      → LapisLawChecker    (typed AST → verified AST)  — src/lawchecker.ts (planned)
        → LapisEvaluator   (verified AST → Values)      — src/evaluator.ts (planned)
```

The base grammar (`LapisGrammar` in `src/grammar.ts`) is abstract: it declares all productions as
`@rule` getters/methods but performs no semantic action. The concrete parser (`LapisParser`)
subclasses it and implements factory methods to build class-based AST nodes (`src/ast.ts`).

Each subsequent pass subclasses the previous one. A pass overrides only the productions that bind or
reference names, check types, verify laws, or evaluate. For all other productions, the base
grammar's parsing runs unchanged via `super`, and the result is the same as the previous layer's
output. This is the "grammar subclassing = semantic pass" model — each pass only spells out what it
_changes_.

### 2.2 The `@rule` Decorator and `super` Override Semantics

Productions are declared with the `@rule` decorator, which wraps a getter or method in a memoised
lazy reference (backed by a `DelayedExp` node). This makes the grammar graph properly recursive
without manual thunks:

```typescript
@rule get expr(): Parser<S['expr']> {
    return this.or(/* ... */);
}
```

**Subclass override semantics** (from the zipper-grammar library): a subclass
`@rule override get expr() { ... }` defines a _new_ getter function, so it occupies a different
cache slot from the parent's. Calling `super.expr` from inside the override accesses the parent's
(decorated) getter and hits the parent's cache slot. This is what makes the multi-pass model work —
each pass can call `super` to get the previous layer's result for a production, then post-process
it, without re-running the base parser.

### 2.3 Parameterised Productions (Context-Sensitive)

Productions can take arguments, making them context-sensitive:

```typescript
@rule exprProd(ctx: unknown): Parser<S['expr']> { ... }
```

The cache key is `(this, method, treeKey([args]))` — each (instance, method, arg-tuple) triple gets
its own `DelayedExp` slot. This is how the inherited context (Γ for type checking, ρ for evaluation)
threads through the grammar.

### 2.4 Current Implementation Status

The current `nameresolver.ts` and `typechecker.ts` are **tree-walking** implementations, not grammar
subclasses. This is a deliberate simplification for the first implementation (documented in
`nameresolver.ts`):

> The `super` pattern allows single-pass (parse + resolve simultaneously), but for the first
> implementation we use a two-pass approach: parse to AST, then walk the AST and resolve names. This
> is simpler to implement and test. The single-pass version can be achieved later by overriding
> productions in a subclass.

The refactor to the grammar-subclass pattern is the next implementation step (see §6 below). The
`stlc.ts` example in zipper-grammar demonstrates the target architecture for a simpler calculus.

## 3. One-Pass Context Threading via `chain`

### 3.1 The Problem `chain` Solves

Without `chain`, the `seq` combinator builds all children eagerly at grammar _construction_ time.
This means a parsed value (e.g., a type annotation `τ`) cannot flow into a sibling's parser (e.g.,
the lambda body) — both are constructed before either is parsed.

The `chain` combinator (monadic bind) breaks this: it parses the first parser, then — _after_ it
completes — calls a function with the result to construct the second parser. This lets a left
sibling's _synthesized_ value determine the right sibling's _inherited_ context, which is exactly
the **L-attributed grammar** pattern.

```typescript
// From zipper-grammar's stlc.ts — the lambda production:
@rule
protected lambdaProd(ctx: unknown): Parser<S['expr']> {
    return this.seq(
        this.lambdaHead, this.ident, this.ws, this.char(':'),
        this.ws, this.type, this.ws, this.char('.'), this.ws,
    ).chain(([, param, , , , ty]) => {
        // τ is now available; extend ctx and parse body.
        return this.exprProd(this.extendCtx(ctx, param, ty))
            .map((body) => this.lam(param, ty, body));
    }).map(([, result]) => result);
}
```

The `chain` fires _after_ `τ` is parsed, so the extended context `Γ + {x:τ}` is available when
`body` is parsed. No two-pass AST-then-evaluate needed; the typing judgment is computed _during
parsing_.

### 3.2 The L-Attributed Property

This works because Lapis's grammar is **L-attributed**: all inherited attributes flow left-to-right
(from parent to child, or from left sibling to right sibling), and all synthesized attributes flow
bottom-up (child to parent). The `chain` combinator is the mechanism for the left-to-right flow:

```
parse annotation τ  ──chain──►  parse body under Γ + {x:τ}
     (synthesized)                (inherited, extended)
```

This is sufficient for Lapis's type system because the context (Γ or ρ) only grows as we descend —
we never need to look _ahead_ or _up_ to type-check a sub-expression. The grammar's left-to-right
structure matches the type system's information flow.

### 3.3 When `seq` Suffices vs. When `chain` Is Needed

- **`seq` suffices** when the context is read-only (never extended during parsing). The pure AST
  builder (`STLCAST` in the example) uses `seq` only — it ignores context entirely.
- **`chain` is needed** when a parsed value must extend the context for a subsequent sibling. Type
  checking and evaluation both need `chain` because lambda/let bind names that extend Γ or ρ for
  their bodies.

## 4. Why the Hard Type-Theory Cases Don't Arise

General type systems face several notoriously difficult problems that make one-pass type checking
impossible. **Lapis's enforced structure eliminates them by construction.** This is not a claim
about clever implementation — it is a consequence of the language design.

### 4.1 No Polymorphic Recursion

**The problem:** Polymorphic recursion (a function calls itself at a different type than its
definition) makes type inference undecidable in general. It requires a fixpoint iteration over types
that cannot be done in one pass.

**Why Lapis doesn't have it:** Lapis has no general recursion. The only recursion is `fold`
(terminating, over finite data) and `unfold` (productive, guarded). A `fold`'s result type is
**declared in the spec**, not inferred from the handler bodies. The recursive positions (`Family`
fields) are folded to the declared result type by construction — there is no recursive call whose
type must be unified with a different instantiation.

Without polymorphic recursion, the type of every recursive position is known before the handler body
is checked. One pass suffices.

### 4.2 No Let-Generalization

**The problem:** In ML/Haskell, `let x = e in body` generalizes the type of `e` to a polymorphic
scheme `∀α. τ` if `e` is pure and `α` doesn't appear in the environment. This requires a
_generalization_ step (finding free type variables and quantifying them) that is inherently a
boundary between two scopes — it cannot be done purely left-to-right.

**Why Lapis doesn't have it:** Lapis uses subtyping, not parametric polymorphism (see
[`language-design.md`](./language-design.md) §2.1). There are no type variables to generalize, no
`∀` quantifier in the core, and no polymorphic schemes. A `let` binding simply adds `x:σ` to Γ where
`σ` is the declared (or inferred) monomorphic type. The context grows; no generalization step
intervenes.

### 4.3 `super` Gives the Complete AST Node

**The problem:** Some type systems require bidirectional information flow — a node's type depends on
both its children (synthesized) and its parent (inherited via an expected type). This is the
"bidirectional type checking" pattern, which needs an expected type to flow _down_ from the parent.

**Why Lapis doesn't need it:** The `super` pattern gives each pass the _complete_ AST node from the
previous layer, not a streaming view. A type checker overriding a production can inspect the full
resolved AST node (via `super`) and check types against it with complete knowledge. There is no need
for a separate inherited expected-type attribute because the declaration already carries the type
annotation (Lapis's surface syntax requires type annotations on declarations — see
[`surface-syntax.md`](./surface-syntax.md)).

### 4.4 Summary

| Hard case              | Why it's hard in general                  | Why Lapis avoids it                                      |
| ---------------------- | ----------------------------------------- | -------------------------------------------------------- |
| Polymorphic recursion  | Undecidable; requires type fixpoint       | No general recursion; fold result types are declared     |
| Let-generalization     | Scope boundary; requires ∀ quantification | Subtyping, not generics; no type variables to generalize |
| Bidirectional checking | Needs expected type flowing down          | `super` gives complete node; annotations carry types     |

These are not implementation conveniences — they are structural consequences of the language design.
The enforced fold/unfold-only recursion and the subtyping-over-generics decision each eliminate a
class of type-theory difficulty. This is the "enforcement makes things simpler" thesis made concrete
at the implementation level.

## 5. Grammar-Native Contracts as Inference-Rule Encoding

### 5.1 The Mapping

zipper-grammar v2.1.0 provides four contract decorators that map directly onto the structure of
inference rules:

| Inference rule component | Contract decorator | Failure behavior                                               |
| ------------------------ | ------------------ | -------------------------------------------------------------- |
| Premise (antecedent)     | `@requires(pred)`  | Graceful: returns `undefined`, parse branch produces `empty()` |
| Conclusion (consequent)  | `@ensures(pred)`   | Throws `ContractError` (a violated postcondition is a bug)     |
| Well-formedness          | `@invariant(pred)` | Throws `ContractError` (checked before/after each action)      |
| Parse-failure recovery   | `@rescue(handler)` | Returns diagnostic or alternative parser                       |

The key insight: **`@requires` fails gracefully** (returns `undefined`, causing the calling
`chain`/`.map` to produce `empty()`), while `@ensures` and `@invariant` throw. This is the domain
adaptation: a failed _premise_ means the inference rule doesn't apply, so the parse branch is
rejected (empty forest). A failed _conclusion_ means the semantic action has a bug (it produced a
result that violates the rule's conclusion), which is a programming error, not a parse failure.

### 5.2 Subcontracting via the Inheritance Chain

Contracts compose across the grammar subclass chain following Liskov subcontracting:

- **`@requires`** (preconditions): **OR-ed** (weakened) across the chain. A subclass accepts a
  _superset_ of the inputs its parent accepted.
- **`@ensures`** (postconditions): **AND-ed** (strengthened) across the chain. A subclass guarantees
  a _more specific_ postcondition than its parent.
- **`@invariant`** (class invariants): **AND-ed** (strengthened) across the chain.
- **`@rescue`** (recovery handlers): **inherited** unless overridden (most-derived wins).

This falls out of the metadata storage: predicates are stored on `Class[Symbol.metadata]` via the
TS5 stage-3 decorator API, and the Proxy dispatch layer walks the prototype chain to collect them. A
subclass's predicates compose with its ancestors' automatically — no manual super-call wiring
needed.

### 5.3 The Enforcement Mechanism

The contracts are enforced by a `Proxy` that wraps every `Grammar` instance at construction time.
The Proxy's `get` trap intercepts method calls and wraps them with contract checks in the order:

```
invariant(before) → @requires → method body → @ensures → invariant(after)
```

The Proxy is **transparent to `@rule` memoization**: the `WeakMap` cache keys on the unwrapped
target, which the Proxy forwards to. When `checkedMode` is disabled (a per-instance or global flag),
no Proxy is created — zero overhead in production.

Importantly, contracts decorate **semantic-action methods** (e.g., `app`, `lam`, `varRef`) — plain
methods called inside `.map()` callbacks — _not_ `@rule` productions. This composes with the
existing `@rule` machinery without engine changes.

### 5.4 Concrete Example: T-App as a Contracted Semantic Action

From zipper-grammar's `stlc.ts`, the application typing rule encoded as a contracted method:

```typescript
// The App inference rule:
//   Γ ⊢ fn : τ₁ → τ₂    Γ ⊢ arg : τ₁
//   ──────────────────────────────────  (App)
//   Γ ⊢ fn arg : τ₂

@requires((_self: STLCTypeCheck, fn: Type, arg: Type) =>
    fn instanceof TFun && typeEq(fn.dom, arg)   // premise: fn is a function, domain matches
)
@ensures((
    _self: STLCTypeCheck,
    _args: [Type, Type],
    _old: STLCTypeCheck,
    result: Type,
) => result instanceof TVar || result instanceof TFun   // conclusion: result is a valid Type
)
protected app(fn: Type, _arg: Type): Type {
    // The premise is enforced by @requires; the body is the rule's conclusion.
    return (fn as TFun).cod;
}
```

If the premise fails (e.g., `fn` is not a function type, or the domain doesn't match), `@requires`
returns `undefined`, the calling `chain` produces `empty()`, and the ill-typed branch is rejected.
The parse forest is empty — **rejection _is_ the type error**.

### 5.5 Concrete Example: T-Var as a Contracted Semantic Action

```typescript
// The Var inference rule:
//   Γ(x) = τ
//   ─────────────  (Var)
//   Γ ⊢ x : τ

@requires((_self: STLCTypeCheck, name: string, ctx: unknown) =>
    ctx instanceof TypeEnv && ctx.lookup(name) !== undefined   // premise: x is bound in Γ
)
protected varRef(name: string, ctx: unknown): Type {
    return (ctx as TypeEnv).lookup(name) as Type;   // conclusion: the type from Γ
}
```

An unbound variable fails the premise, produces `undefined`, and the parse branch yields an empty
forest — the variable is rejected, not thrown.

## 6. Application to Lapis: T-Fold as a Contracted Production

The typing rule for `fold` (from [`lc.md`](./lc.md) §5.2) is:

```
Γ ⊢ e : T    Γ ⊢ hᵢ : Fᵢ(σ)[α:=σ] → σ    (for each variant Cᵢ)
─────────────────────────────────────────────────────────────  (T-Fold)
Γ ⊢ fold_T e {Cᵢ(xⱼ) → tᵢ} : σ
```

In the grammar-as-semantics model, this becomes a parameterised production
`foldProd(Γ): Parser<Type>` with contracted semantic actions:

```typescript
@requires((_self: LapisTypeChecker, eType: LapisType, handlers: HandlerTypes) => {
    // Premise 1: e has type T (the data type being folded)
    // Premise 2: each handler hᵢ has type Fᵢ(σ)[α:=σ] → σ
    //   — i.e., each handler accepts the variant's fields (with recursive
    //     positions at type σ, the result type) and returns σ.
    return isSubtypeOf(eType, T) && handlers.every(h => checkHandlerType(h, σ));
})
@ensures((_self, _args, _old, result: LapisType) =>
    // Conclusion: the fold has type σ (the declared result type)
    result.equals(σ)
)
protected fold(eType: LapisType, handlers: HandlerTypes): LapisType {
    return σ;  // The result type, declared in the fold's spec
}
```

The `chain` combinator threads Γ through the handler bodies: each handler is checked under Γ
extended with the variant's field names, and the result type σ is declared in the fold's spec (not
inferred), so no fixpoint iteration is needed.

### 6.1 Why T-Fold Is One-Pass

The fold's result type σ is **declared** in the spec, not inferred. This means:

1. When we enter `foldProd(Γ)`, σ is already known (from the spec).
2. Each handler body is checked against the expected type `Fᵢ(σ)[α:=σ] → σ` — the recursive
   positions are at type σ (known), the non-recursive positions are at their declared types (known),
   and the result is σ (known).
3. No unification across handlers is needed — they all share the same σ by declaration.

This is the structural reason §4.1 gives: because fold result types are declared, there is no
polymorphic recursion to resolve, and the entire fold can be type-checked in a single left-to-right
pass.

## 7. Higher-Order Attributes and Tree-Consuming Grammars

> **Note:** The features in this section are from zipper-grammar 2.2.0+, which is now the current
> version (3.0.0). The 3.0.0 API adds typed contract predicates (`@requires`/`@ensures` infer
> `Parameters<F>` and `ReturnType<F>` from the decorated method; `old` is typed as
> `OldSnapshot<This>`).

zipper-grammar 2.2.0 introduces two capabilities that further unify the architecture: **higher-order
attributes** (one-pass evaluation via `_forward`) and **tree-consuming grammars** (via `TreeExp` /
`flattenTree`). Together, they eliminate most cases where a separate recursive function was
previously needed.

### 7.1 Higher-Order Attributes (`_forward`)

In 2.1.0, evaluation of closures required multi-pass (Pattern 1): parse to AST, then walk the AST
with a separate recursive `evalTerm` function. The body text was consumed once during parsing;
re-evaluating it under a different environment meant re-walking the AST node, not re-parsing the
source.

2.2.0's `_forward(input, span, start)` changes this. It re-parses a substring of the original input
under a different inherited context, _within the same grammar instance_. For evaluation, `app`
captures the closure body's source span and re-parses that substring under the extended environment:

```typescript
class STLCEval extends AbstractSTLC<{ expr: Value; atom: Value; type: Type }> {
    protected app(fn: Value, arg: Value): Value {
        const bodyEnv = fn.env.extend(fn.param, arg)
        return [...this._forward(this._input, fn.bodySpan, this.exprProd(bodyEnv))][0]
    }
}
```

The evaluator is now a one-pass grammar subclass — the same shape as the type checker. No separate
recursive function, no intermediate AST. Per-pass memo isolation (stale-position detection in
`goDown`) makes the nested re-entry safe.

**Applicability to Lapis:** The evaluator can be a one-pass grammar subclass. Closures capture the
body's source span; application re-parses the body under the extended environment via `_forward`.
This unifies the architecture: _every_ pass — name resolution, type checking, evaluation — is a
grammar subclass. The "multi-pass fallback with a separate recursive function" is no longer needed
for evaluation.

### 7.2 Tree-Consuming Grammars (`TreeExp`, `flattenTree`)

For passes whose input is an already-built tree (an AST or derivation tree) rather than source text,
the engine supports tree-consuming grammars. `flattenTree` converts a tree into a preorder token
stream; `TreeExp` matches a tree node by class name and dispatches to child sub-parsers by position;
`parseTree` drives the parse over the flattened token stream.

```typescript
class TreeEval extends Grammar<{ expr: number }> {
    @rule
    get expr(): Parser<number> {
        return or(this.numNode, this.addNode)
    }
    protected get addNode(): Parser<number> {
        return parserOf(
            new TreeExp(
                "Add",
                [this.expr._exp, this.expr._exp],
                (_n, [l, r]) => (l as number) + (r as number),
            ),
        )
    }
}

const toks = flattenTree(tree, childrenOf)
const [v] = [...new TreeEval().parseTree(toks)]
```

**Applicability to Lapis:** Passes that consume a prior pass's output tree — e.g., a law checker
walking the typed AST, or an evaluator walking a desugared tree — can now _also_ be grammar
subclasses, not separate recursive functions. Whether the input is source text or a tree, the
architecture is the same: grammar-class methods with `@requires`/`@ensures` contracts.

### 7.3 What This Means for Lapis's Passes

| Pass                   | Input             | Pattern        | Mechanism                                              |
| ---------------------- | ----------------- | -------------- | ------------------------------------------------------ |
| Name resolution        | Source text       | One-pass       | `chain` (context grows)                                |
| Type checking          | Source text       | One-pass       | `chain` (context grows; fold result types declared)    |
| Evaluation             | Source text       | One-pass       | `_forward` (closures re-parse body under extended env) |
| Law checking           | Typed AST (tree)  | Tree-consuming | `TreeExp` / `flattenTree`                              |
| Desugaring (if needed) | Source AST (tree) | Tree-consuming | `TreeExp` / `flattenTree`                              |

The multi-pass fallback (Pattern 1 — a separate recursive function) is now reserved for cases where
neither `_forward` nor tree-consuming grammars apply. For Lapis's current design, that may be none
of them.

## 8. Relationship to Attribute Grammars

The grammar-as-semantics model is an **executable attribute grammar**:

| Attribute grammar concept             | zipper-grammar realization                    |
| ------------------------------------- | --------------------------------------------- |
| Inherited attribute                   | Method parameter (`ctx`) threaded via `chain` |
| Synthesized attribute                 | Method return value (the `Parser<T>` result)  |
| Copy rule (pass attribute unchanged)  | Default `super` call (no override)            |
| Semantic rule (compute new attribute) | Override + `@requires`/`@ensures`             |
| L-attributed (left-to-right flow)     | `chain` (monadic bind)                        |
| S-attributed (bottom-up only)         | `seq` + `.map` (no `chain` needed)            |

The `semantics.md` document (§5) specifies the attribute-grammar equations for static analysis. This
document specifies _how those equations are executed_: as grammar subclass methods with `chain` for
inherited-attribute threading and contracts for inference-rule encoding.

## 9. Refactoring the Current Implementation

The current `nameresolver.ts` and `typechecker.ts` are tree-walking implementations. The refactor to
the grammar-subclass pattern follows the `stlc.ts` example:

### 9.1 Name Resolver

1. Subclass `LapisGrammar` (or `LapisParser`) as `LapisNameResolver`.
2. Override productions that bind or reference names (`dataDecl`, `behaviorDecl`, `foldDecl`,
   `variantRef`, etc.).
3. Thread `NameEnv` as the `ctx` parameter via `chain`.
4. Override `extendCtx` to add declarations to `NameEnv`.
5. For productions that don't touch names, inherit via `super` (no override).

The two-pass structure within name resolution (collect declarations, then resolve references — see
`nameresolver.ts` `resolveModule`) handles forward references and mutual recursion. In the
single-pass version, this becomes a `@requires` contract: a reference to a not-yet-collected name
fails the premise and is rejected. Forward references are handled by collecting all declarations in
a pre-pass (the `@invariant` or a class-level initialization) before parsing references.

### 9.2 Type Checker

1. Subclass `LapisNameResolver` as `LapisTypeChecker`.
2. Override productions that have typing rules (`foldDecl`, `unfoldDecl`, `variantRef`, `blockLit`,
   `keywordSend`, etc.).
3. Thread `TypeEnv` (Γ) as the `ctx` parameter via `chain`.
4. Encode each typing rule's premises as `@requires` and conclusions as `@ensures` (per §5.4, §5.5,
   §6).
5. Override `extendCtx` to add type bindings to Γ.
6. For productions with no typing rule (e.g., whitespace, comments), inherit via `super`.

### 9.3 What the Refactor Buys

- **One-pass type checking** where the current implementation is two-pass (parse to AST, then walk).
- **One-pass evaluation** via `_forward` (2.2.0): closures re-parse their body under an extended
  environment, no separate recursive function needed.
- **Tree-consuming law checking** via `TreeExp` / `flattenTree` (2.2.0): the law checker walks the
  typed AST as a grammar subclass, not a separate function.
- **Inference-rule encoding** as contracts, making the typing rules executable and checkable (a
  violated `@ensures` is a compiler bug caught at check time).
- **Subcontracting** across the pass chain: the type checker's preconditions compose with the name
  resolver's (OR-ed), and its postconditions compose (AND-ed) — the pipeline's correctness contracts
  compose automatically.
- **Uniform architecture**: the parser, name resolver, type checker, law checker, and evaluator are
  all the same kind of thing (grammar subclasses), not five different data structures and traversal
  patterns. With 2.2.0's `_forward` and tree-consuming grammars, even evaluation and tree-walking
  passes are grammar subclasses — no separate recursive functions.

## 10. References

- **zipper-grammar** —
  [`jsr:@lapis-lang/zipper-grammar@3.0.0`](https://jsr.io/@lapis-lang/zipper-grammar): `Grammar`
  base class, `@rule` decorator, `chain` combinator, `@requires` / `@ensures` / `@invariant` /
  `@rescue` contracts (with typed predicates — `Parameters<F>`/`ReturnType<F>` inferred,
  `OldSnapshot<This>` for `old`), `_forward` (higher-order attributes for one-pass evaluation),
  `TreeExp` / `flattenTree` (tree-consuming grammars), standalone combinators (`sseq`, `plus`,
  `sepBy`, `between`, `trim`, `keyword`), and lexeme helpers. See `examples/stlc.ts` for the
  headline example (STLC with 4 interpretations over one grammar, including one-pass evaluation via
  `_forward`).
- **Bracha, G.** — Executable grammars / pluggable type systems: the grammar-subclassing model that
  zipper-grammar realizes.
- **Attribute grammars** — Knuth's original concept; the L-attributed / S-attributed distinction
  maps to `chain` vs. `seq`. Higher-order attributes (re-entering the engine over a fragment) extend
  the attribute-grammar model to handle closures and runtime tree growth.
- **Liskov subcontracting** — `@requires` OR-ed (weakened), `@ensures` AND-ed (strengthened) across
  the inheritance chain.
- **Curry–Howard** — "Proofs as parse trees": a successful parse under the type-checking grammar
  _is_ a typing derivation (see `STLCTyped` in `stlc.ts`).
