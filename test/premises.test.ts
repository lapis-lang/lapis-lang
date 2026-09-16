/**
 * Production-path premise enforcement tests — verify that failed typing-rule
 * premises reject the parse branch (empty forest) rather than leaking
 * `undefined` or a permissive-`Any` sentinel into the parse forest.
 *
 * `@requires` is declarative metadata for the rule model; runtime enforcement
 * lives in the production-path overrides (`varProd`, `variantProd`, `obsProd`,
 * `foldProd`, `unfoldProd`, `cofoldProd`), which return `empty<Type>()` on a
 * failed premise. A contracted action is only called on the verified path.
 *
 * Rejection (empty parse forest) = type error, uniformly across all rules.
 *
 * The evaluator (`LCEval`) mirrors the fold-family kind checks: a wrong-kind
 * type annotation rejects the branch (`empty<Value>()`) instead of throwing
 * out of the parse.
 */

import { assert, assertEquals } from "@std/assert"
import { LCEval, LCTypeCheck, SpanCodataVal, VariantVal } from "../src/index.ts"
import { type Value, ValueEnv } from "../src/core/values.ts"
import { Any, Nothing, type Type, TypeEnv } from "../src/core/types.ts"
import { createTestFixtures } from "./fixtures.ts"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry, stack, stream, nat } = createTestFixtures()

/** Type-check `src` under Γ with the test registry, returning the forest. */
function typeForestOf(src: string, gamma: TypeEnv = new TypeEnv()): Set<Type> {
    return new LCTypeCheck().setRegistry(registry).parseWith(src, gamma)
}

// ── T-Var: unbound variables are rejected ────────────────────────────────────
//
// `varProd` checks `Γ(x) ≠ undefined` inline; the contracted `varRef` action
// is never reached with an unbound name, so `undefined` cannot leak.

Deno.test("T-Var: an unbound variable is rejected (empty forest)", () => {
    assertEquals(
        typeForestOf("y").size,
        0,
        "an unbound variable must produce an empty forest, never [undefined]",
    )
})

Deno.test("T-Var: a bound variable still type-checks", () => {
    const result = typeForestOf("y", new TypeEnv().extend("y", nat))
    assertEquals(result.size, 1)
    assertEquals([...result][0], nat)
})

Deno.test("T-Var: an unbound variable inside an application is rejected", () => {
    assertEquals(
        typeForestOf("y Zero()").size,
        0,
        "an unbound fn must reject the whole application",
    )
})

Deno.test("T-Var: an unbound variable inside an argument is rejected", () => {
    assertEquals(
        typeForestOf("(\\x:Nat. x) y").size,
        0,
        "an unbound argument must reject the whole application",
    )
})

Deno.test("T-Var: an unbound variable in a lambda body is rejected", () => {
    assertEquals(
        typeForestOf("\\x:Nat. y").size,
        0,
        "the body's unbound variable must reject the lambda",
    )
})

Deno.test("T-Var: a lambda-bound variable shadows nothing — scope ends at the dot", () => {
    assertEquals(
        typeForestOf("(\\x:Nat. x) x").size,
        0,
        "the argument-position x is outside the binder's scope",
    )
})

// ── T-Let × T-Var: the isSubtype guard closes the Any-absorption hole ────────
//
// Before the guard, `isSubtype(undefined, Any)` held via S-Top, so a leaked
// `undefined` def silently satisfied T-Let's premise under an `Any` annotation.

Deno.test("T-Let: let x:Any = <unbound y> in x is rejected", () => {
    assertEquals(
        typeForestOf("let x:Any = y in x").size,
        0,
        "an undefined def type must not satisfy T-Let's premise via S-Top",
    )
})

Deno.test("T-Let: let x:Any = UnknownVariant() in x is rejected", () => {
    // The permissive-Any sentinel inside `variantCon` is unreachable on the
    // production path: `variantProd` rejects the unknown variant first. Under
    // an `Any` annotation the sentinel would have been the declared type
    // (isSubtype(Any, Any) via S-Refl) and the ill-typed def was accepted.
    assertEquals(
        typeForestOf("let x:Any = UnknownVariant() in x").size,
        0,
        "an unknown variant def must be rejected, not absorbed by Any",
    )
})

// ── T-Variant: registry, arity, and field premises are enforced ──────────────

Deno.test("T-Variant: an unknown variant is rejected everywhere, not just under Any", () => {
    assertEquals(
        typeForestOf("UnknownVariant()").size,
        0,
        "a bare unknown variant must be rejected",
    )
    assertEquals(
        typeForestOf("Push(UnknownVariant(), Empty())").size,
        0,
        "an unknown variant in a field position must reject the construction",
    )
})

Deno.test("T-Variant: an unknown observer name lexes as a variable, not a variant", () => {
    // PascalCase lexemes are variants; a lowercase name that fails the variant
    // gate falls through to varProd, where the T-Var premise rejects it.
    assertEquals(
        typeForestOf("unknownVariant()").size,
        0,
        "a lowercase unknown call form must not parse",
    )
})

Deno.test("T-Variant: arity mismatch is rejected", () => {
    assertEquals(
        typeForestOf("Push(Empty())").size,
        0,
        "too few fields must be rejected",
    )
    assertEquals(
        typeForestOf("Push(Zero(), Empty(), Empty())").size,
        0,
        "too many fields must be rejected",
    )
})

Deno.test("T-Variant: a field type mismatch is rejected", () => {
    // Push's first field is Any, but the recursive `rest` slot demands Stack.
    assertEquals(
        typeForestOf("Push(Zero(), Zero())").size,
        0,
        "a Nat in the recursive Stack slot must be rejected",
    )
})

Deno.test("T-Variant: well-typed constructions are unaffected", () => {
    assertEquals(typeForestOf("Push(Zero(), Empty())").size, 1)
    assertEquals(typeForestOf("Empty()").size, 1)
})

// ── T-Obs: observer and scrutinee premises are enforced ──────────────────────

Deno.test("T-Obs: an unknown observer is rejected", () => {
    // `nothing` is not declared on any registered codata type.
    assertEquals(
        typeForestOf("Empty().nothing").size,
        0,
        "an unknown observer must be rejected",
    )
})

Deno.test("T-Obs: a scrutinee that is not a codata subtype is rejected", () => {
    // Empty() : Stack — Stack does not observe `head`.
    assertEquals(
        typeForestOf("Empty().head").size,
        0,
        "observing a data value as codata must be rejected",
    )
})

Deno.test("T-Obs: a chain rejects at the first failing observation", () => {
    // unfold ... : Stream — `head` is a Stream observation (succeeds), `nope`
    // is not (fails). The whole chain is rejected.
    assertEquals(
        typeForestOf("(unfold [Stream] Zero() { head -> self, tail -> self }).head.nope").size,
        0,
        "the first unknown observer in a chain must reject the chain",
    )
})

Deno.test("T-Obs: a well-typed observation chain is unaffected", () => {
    assertEquals(
        typeForestOf("(unfold [Stream] Zero() { head -> self, tail -> self }).tail.tail").size,
        1,
    )
})

// ── T-Fold: scrutinee and exhaustiveness premises are enforced ───────────────

const stackFold = "fold [Stack] %s { Empty() -> Empty(), Push(v rest) -> rest }"

Deno.test("T-Fold: a scrutinee that is not a subtype of T is rejected", () => {
    // Zero() : Nat, not a Stack.
    assertEquals(
        typeForestOf(stackFold.replace("%s", "Zero()")).size,
        0,
        "folding a Nat as a Stack must be rejected",
    )
})

Deno.test("T-Fold: non-exhaustive handlers are rejected", () => {
    assertEquals(
        typeForestOf("fold [Stack] Empty() { Empty() -> Empty() }").size,
        0,
        "a missing Push handler must be rejected",
    )
})

Deno.test("T-Fold: the Nothing scrutinee does not bypass exhaustiveness", () => {
    // x : Nothing satisfies premise 1 via S-Bot, but the missing Push handler
    // is a genuine premise violation — rejection, not a spurious result.
    assertEquals(
        typeForestOf("fold [Stack] x { Empty() -> Empty() }", new TypeEnv().extend("x", Nothing))
            .size,
        0,
        "S-Bot must not mask a missing handler",
    )
})

Deno.test("T-Fold: a well-typed fold is unaffected", () => {
    assertEquals(typeForestOf(stackFold.replace("%s", "Empty()")).size, 1)
    assertEquals([...typeForestOf(stackFold.replace("%s", "Empty()"))][0], stack)
})

// ── T-Unfold: generator exhaustiveness is enforced ───────────────────────────

Deno.test("T-Unfold: non-exhaustive generators are rejected", () => {
    assertEquals(
        typeForestOf("unfold [Stream] Zero() { head -> self }").size,
        0,
        "a missing tail generator must be rejected",
    )
})

Deno.test("T-Unfold: an unknown generator name is rejected", () => {
    // `unfoldGenerator` rejects names that are not observers of the codata
    // type, so the generator list can never contain one — the exhaustiveness
    // premise then fails on the missing observer.
    assertEquals(
        typeForestOf("unfold [Stream] Zero() { nope -> self, head -> self }").size,
        0,
        "an unknown generator must be rejected",
    )
})

Deno.test("T-Unfold: a well-typed unfold is unaffected", () => {
    const result = typeForestOf("unfold [Stream] Zero() { head -> self, tail -> self }")
    assertEquals(result.size, 1)
    assertEquals([...result][0], stream)
})

Deno.test("T-Unfold: a generator body violating its observer result type is rejected", () => {
    // tail must produce a Stream (continuation observer); Zero() : Nat.
    assertEquals(
        typeForestOf("unfold [Stream] Zero() { head -> Zero(), tail -> Zero() }").size,
        0,
        "a generator body must be a subtype of its observer's result type",
    )
})

Deno.test("T-Unfold: a plain-observer generator violating the declared type is rejected", () => {
    // NatStream declares head : Nat — a function body violates it.
    const result = typeForestOf(
        "unfold [NatStream] Zero() { head -> \\x:Any. x, tail -> self }",
    )
    assertEquals(
        result.size,
        0,
        "a FunType body for a Nat-valued observer must be rejected",
    )
})

Deno.test("T-Unfold: the canonical continuation producer still types", () => {
    // `tail -> self` is the canonical codata producer: E-Obs binds the seed
    // value to `self` when a generator runs, so the typing keeps `self` as
    // the base binds it and the result premise passes (Any <: Stream).
    const result = typeForestOf("unfold [Stream] Zero() { head -> self, tail -> self }")
    assertEquals(result.size, 1)
    assertEquals([...result][0], stream)
})

Deno.test("T-Fold: a handler body that fails after σ refinement is rejected", () => {
    // The Empty handler is function-valued, so σ refines to a FunType via
    // S-Fun's contravariant domain join. The Push handler then applies a
    // Stack-typed lambda to the recursive binding, which under the refined σ
    // (Stack → Stack) fails to re-parse. The failure must reject the fold —
    // never be laundered into an `Any` body type that satisfies the join.
    assertEquals(
        typeForestOf(
            "fold [Stack] Empty() { Empty() -> \\x:Stack. Empty(), Push(v rest) -> \\x:Any. (\\y:Stack. Empty()) rest }",
        ).size,
        0,
        "a reparse failure at the refined σ must reject the fold",
    )
})

Deno.test("T-Fold: a fold whose bodies agree under refinement is unaffected", () => {
    // Regression pin: legitimate refinement (recursive slot usage) still converges.
    const result = typeForestOf(
        "fold [Stack] Empty() { Empty() -> Empty(), Push(v rest) -> Push(Zero(), rest) }",
    )
    assertEquals(result.size, 1)
    assertEquals([...result][0], stack)
})

// ── T-Cofold: the scrutinee premise is enforced ──────────────────────────────

Deno.test("T-Cofold: a scrutinee that is not a codata subtype is rejected", () => {
    assertEquals(
        typeForestOf("cofold [Stream] Zero() { head(h) -> Zero() }").size,
        0,
        "cofolding a Nat as a Stream must be rejected",
    )
})

Deno.test("T-Cofold: a well-typed cofold is unaffected", () => {
    const result = typeForestOf(
        "cofold [Stream] (unfold [Stream] Zero() { head -> self, tail -> self }) { head(h) -> h }",
    )
    assertEquals(result.size, 1)
})

// ── Wrong-kind type annotations are rejected, not thrown ─────────────────────
//
// The fold-family productions check the annotation's kind as a premise
// (DataType for fold, CodataType for unfold/cofold). An annotation of the
// wrong kind fails that premise and rejects the branch (`empty<Type>()`) —
// the same rejection semantics as every other premise, never a throw out of
// the parse.

Deno.test("T-Unfold: an annotation of the wrong kind (Nat is not codata) is rejected", () => {
    assertEquals(
        typeForestOf("unfold [Nat] Zero() { head -> self, tail -> self }").size,
        0,
        "a DataType annotation for unfold must reject the branch, not throw",
    )
})

Deno.test("T-Cofold: an annotation of the wrong kind (Nat is not codata) is rejected", () => {
    assertEquals(
        typeForestOf("cofold [Nat] Zero() { head(h) -> Zero() }").size,
        0,
        "a DataType annotation for cofold must reject the branch, not throw",
    )
})

Deno.test("T-Fold: an annotation of the wrong kind (Stream is not data) is rejected", () => {
    assertEquals(
        typeForestOf("fold [Stream] Empty() { Empty() -> Empty(), Push(v rest) -> rest }").size,
        0,
        "a CodataType annotation for fold must reject the branch, not throw",
    )
})

Deno.test("rejection: a wrong-kind annotation rejects the enclosing let", () => {
    assertEquals(
        typeForestOf(
            "let x:Any = unfold [Nat] Zero() { head -> self, tail -> self } in Zero()",
        ).size,
        0,
        "the wrong-kind annotation must reject the whole let",
    )
})

// ── Composition: rejection propagates through enclosing productions ─────────

Deno.test("rejection: a rejected subterm rejects the enclosing let", () => {
    assertEquals(
        typeForestOf("let x:Nat = UnknownVariant() in Zero()").size,
        0,
        "the ill-typed def must reject the whole let",
    )
})

Deno.test("rejection: a rejected subterm rejects the enclosing fold handler", () => {
    assertEquals(
        typeForestOf("fold [Stack] Empty() { Empty() -> y, Push(v rest) -> rest }").size,
        0,
        "an unbound variable in a handler body must reject the fold",
    )
})

Deno.test("rejection: a rejected subterm rejects the enclosing unfold generator", () => {
    assertEquals(
        typeForestOf("unfold [Stream] Zero() { head -> y, tail -> self }").size,
        0,
        "an unbound variable in a generator body must reject the unfold",
    )
})

// ── isSubtype/join/meet: the well-formedness guard is load-bearing ───────────
//
// The guard makes leaked sentinels fail premises loudly instead of satisfying
// them (S-Top would otherwise accept isSubtype(undefined, Any)).

Deno.test("subtyping: the guards are invisible to well-formed inputs", () => {
    // Regression pin: legitimate lattice behaviour is unchanged.
    const result = typeForestOf("let y:Any = x in y", new TypeEnv().extend("x", Any))
    assertEquals(result.size, 1)
    assertEquals([...result][0], Any)
})

// ── LCEval: wrong-kind type annotations are rejected, not thrown ─────────────
//
// The evaluator mirrors the type checker's fold-family kind checks: DataType
// for fold, CodataType for unfold/cofold. A wrong-kind annotation rejects the
// branch (`empty<Value>()`) — same rejection semantics, mirrored across both
// grammar subclasses.

/** Evaluate `src` under ρ with the test registry, returning the forest. */
function evalForestOf(src: string, rho: ValueEnv = new ValueEnv()): Set<Value> {
    return new LCEval().setRegistry(registry).parseWith(src, rho)
}

Deno.test("E-Unfold: an annotation of the wrong kind (Nat is not codata) is rejected", () => {
    assertEquals(
        evalForestOf("unfold [Nat] Zero() { head -> self, tail -> self }").size,
        0,
        "a DataType annotation for unfold must reject the branch, not throw",
    )
})

Deno.test("E-Cofold: an annotation of the wrong kind (Nat is not codata) is rejected", () => {
    assertEquals(
        evalForestOf("cofold [Nat] Zero() { head(h) -> Zero() }").size,
        0,
        "a DataType annotation for cofold must reject the branch, not throw",
    )
})

Deno.test("E-Fold: an annotation of the wrong kind (Stream is not data) is rejected", () => {
    assertEquals(
        evalForestOf("fold [Stream] Empty() { Empty() -> Empty(), Push(v rest) -> rest }").size,
        0,
        "a CodataType annotation for fold must reject the branch, not throw",
    )
})

Deno.test("E-Eval: a wrong-kind annotation rejects the enclosing let", () => {
    assertEquals(
        evalForestOf(
            "let x:Any = unfold [Nat] Zero() { head -> self, tail -> self } in Zero()",
        ).size,
        0,
        "the wrong-kind annotation must reject the whole let",
    )
})

Deno.test("E-Eval: right-kind fold-family forms still evaluate", () => {
    // Sanity pin: the kind checks do not disturb legitimate evaluation.
    const unfold = evalForestOf(
        "unfold [Stream] Zero() { head -> Zero(), tail -> self }",
    )
    assertEquals(unfold.size, 1)
    const [val] = unfold
    assert(val instanceof SpanCodataVal)
    assertEquals(val.codataType, stream)

    const fold = evalForestOf(
        "fold [Stack] Empty() { Empty() -> Empty(), Push(v rest) -> rest }",
    )
    assertEquals(fold.size, 1)
    const [folded] = fold
    assert(folded instanceof VariantVal)
    assertEquals(folded.variantName, "Empty")
})
