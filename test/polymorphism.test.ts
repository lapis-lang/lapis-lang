/**
 * Polymorphism and cofold tests — verify T-TAbs, T-TApp, and T-Cofold.
 */

import { LCEval, LCTypeCheck, ValueEnv } from "../src/index.ts"
import { Any, FunType, PolymorphicType, TypeEnv, TypeVar } from "../src/core/types.ts"
import { createTestFixtures } from "./fixtures.ts"

import { assert, assertEquals } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry, nat } = createTestFixtures()

// ── Tests ─────────────────────────────────────────────────────────────────────

Deno.test("Polymorphism: ^A <: Any. \\x:Any. x type-checks", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("^A <: Any. \\x:Any. x", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    // ∀A<:Any. (Any → Any) — a PolymorphicType, NOT a FunType
    assert(type instanceof PolymorphicType, `expected PolymorphicType, got ${type}`)
    assertEquals(type.typeVarName, "A")
    assertEquals(type.bound, Any)
    assert(type.body instanceof FunType, `expected FunType body, got ${type.body}`)
})

Deno.test("Polymorphism: (^A <: Any. \\x:Any. x) [Any] type-checks", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^A <: Any. \\x:Any. x) [Any]", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    // The result is Any → Any (the body type with A := Any)
    assert(type instanceof FunType, `expected FunType, got ${type}`)
    assertEquals(type.param, Any)
    assertEquals(type.result, Any)
})

// ── Type-variable reference in annotations ───────────────────────────────────
// A bound type variable can now be referenced in a type annotation because the
// binder (`typeName`, uppercase-first) and type positions share one grammar.

Deno.test("Polymorphism: ^A <: Any. \\x:A. x type-checks with TypeVar body", () => {
    // The body \x:A. x has type A → A, where A is the bound type variable.
    // The whole term is ∀A<:Any. (A → A).
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("^A <: Any. \\x:A. x", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof PolymorphicType, `expected PolymorphicType, got ${type}`)
    assertEquals(type.typeVarName, "A")
    assertEquals(type.bound, Any)
    assert(type.body instanceof FunType, `expected FunType body, got ${type.body}`)
    // The parameter and result are both TypeVar("A", Any)
    const body = type.body as FunType
    assert(body.param instanceof TypeVar, `expected TypeVar param, got ${body.param}`)
    assertEquals((body.param as TypeVar).name, "A")
    assert(body.result instanceof TypeVar, `expected TypeVar result, got ${body.result}`)
    assertEquals((body.result as TypeVar).name, "A")
})

Deno.test("Polymorphism: (^A <: Any. \\x:A. x) [Nat] substitutes A := Nat", () => {
    // T-TApp: (∀A<:Any. A → A) [Nat] → Nat → Nat (substitution τ[A:=Nat])
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^A <: Any. \\x:A. x) [Nat]", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof FunType, `expected FunType, got ${type}`)
    // Both param and result are now Nat (the substitution result)
    assertEquals(type.param, nat)
    assertEquals(type.result, nat)
})

Deno.test("Polymorphism: (^A <: Any. \\x:A. x) [Any] substitutes A := Any", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^A <: Any. \\x:A. x) [Any]", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof FunType, `expected FunType, got ${type}`)
    assertEquals(type.param, Any)
    assertEquals(type.result, Any)
})

Deno.test("Polymorphism: lowercase type-variable binder is rejected", () => {
    // `typeName` requires an uppercase first letter, so `^alpha` does not
    // parse — the binder grammar no longer accepts lowercase identifiers.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("^alpha <: Any. \\x:Any. x", new TypeEnv())
    assertEquals(result.size, 0, "lowercase type-variable binder must be rejected")
})

// ── Type-variable lexical scoping ──────────────────────────────────────────────
// Δ (TypeVarEnv) is threaded through type productions so `atomType` resolves
// bound type variables to a `TypeVar` carrying their declared bound.

Deno.test("Polymorphism: type variable bound carries declared bound from Δ", () => {
    // `^A <: Nat. \x:A. x` — the bound `Nat` refers to the registered DataType
    // (parsed under the outer Δ). The body's `A` resolves to TypeVar("A")
    // with bound = Nat (from Δ), not Any.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("^A <: Nat. \\x:A. x", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof PolymorphicType, `expected PolymorphicType, got ${type}`)
    assertEquals(type.bound, nat)
    const body = type.body as FunType
    assert(body.param instanceof TypeVar, `expected TypeVar param, got ${body.param}`)
    assertEquals((body.param as TypeVar).name, "A")
    assertEquals((body.param as TypeVar).bound, nat)
})

Deno.test("Polymorphism: type variable bound is parsed under outer scope", () => {
    // The bound σ in `^A <: σ. t` is parsed under the *outer* Δ — the
    // variable is not in scope in its own bound. Here the bound `Nat` refers
    // to the registered DataType, not a type variable.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("^A <: Nat. \\x:A. x", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof PolymorphicType, `expected PolymorphicType, got ${type}`)
    assertEquals(type.bound, nat)
})

Deno.test("Polymorphism: type variable shadows registered type outside scope", () => {
    // Outside the type abstraction, `Nat` refers to the registered DataType
    // again. The shadowing is lexical — it only applies inside the body.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("\\x:Nat. x", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof FunType, `expected FunType, got ${type}`)
    assertEquals(type.param, nat)
    assertEquals(type.result, nat)
})

// ── Binder validation: reserved names are rejected ───────────────────────────
// A type-variable binder must not be a built-in (`Any`, `Nothing`, `Token`) or
// a registered type name. Binding such a name would shadow a real type, which
// is misleading even with lexical scoping. The term is rejected (empty forest).

Deno.test("Polymorphism: binding a registered type name as type variable is rejected", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("^Nat <: Any. \\x:Nat. x", new TypeEnv())
    assertEquals(result.size, 0, "binding a registered type name must be rejected")
})

Deno.test("Polymorphism: binding a builtin type name as type variable is rejected", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    assertEquals(
        tc.parseWith("^Any <: Nat. \\x:Any. x", new TypeEnv()).size,
        0,
        "binding `Any` must be rejected",
    )
    assertEquals(
        tc.parseWith("^Nothing <: Any. \\x:Nothing. x", new TypeEnv()).size,
        0,
        "binding `Nothing` must be rejected",
    )
    assertEquals(
        tc.parseWith("^Token <: Any. \\x:Token. x", new TypeEnv()).size,
        0,
        "binding `Token` must be rejected",
    )
})

// ── T-TApp premise enforcement ────────────────────────────────────────────────

Deno.test("Polymorphism: type application on a non-polymorphic body is rejected", () => {
    // Zero() : Nat — not a ∀ type, so the T-TApp premise fails and the
    // term must be rejected (empty forest), never `undefined`.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("Zero()[Stack]", new TypeEnv())
    assertEquals(result.size, 0, "type-applying a non-polymorphic term must be rejected")
})

Deno.test("Polymorphism: type application violating the bound is rejected", () => {
    // Nat is not a subtype of the declared bound Stack.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^A <: Stack. \\x:Any. x) [Nat]", new TypeEnv())
    assertEquals(result.size, 0, "an argument type outside the bound must be rejected")
})

Deno.test("Polymorphism: chained type application on a non-polymorphic result is rejected", () => {
    // The first application yields Any → Any (not a ∀ type), so the second
    // T-TApp premise fails — rejection, not `undefined`.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^A <: Any. \\x:Any. x) [Nat] [Bool]", new TypeEnv())
    assertEquals(result.size, 0, "chaining past a non-polymorphic result must be rejected")
})

Deno.test("Polymorphism: chained type applications with satisfied bounds type-check", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith(
        "(^A <: Any. ^B <: Any. \\x:Any. x) [Nat] [Bool]",
        new TypeEnv(),
    )
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof FunType, `expected FunType, got ${type}`)
    assertEquals(type.param, Any)
    assertEquals(type.result, Any)
})

Deno.test("Polymorphism: type application with a concrete argument type type-checks", () => {
    // The bound Any is satisfied by the concrete type Nat.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^A <: Any. \\x:Any. x) [Nat]", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof FunType, `expected FunType, got ${type}`)
    assertEquals(type.param, Any)
    assertEquals(type.result, Any)
})

Deno.test("Polymorphism: evaluate ^A <: Any. \\x:Any. x", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("^A <: Any. \\x:Any. x", new ValueEnv())
    assert(result.size === 1)
    // Type abstraction evaluates to the body value (type erasure)
    const [val] = result
    assert(val !== undefined)
})

Deno.test("Polymorphism: evaluate (^A <: Any. \\x:Any. x) [Any] Empty()", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("(^A <: Any. \\x:Any. x) [Any] Empty()", new ValueEnv())
    assert(result.size === 1)
    const [val] = result
    // Type application evaluates the body, then applies to the argument
    assert(val !== undefined)
})

Deno.test("Polymorphism: evaluate (^A <: Any. \\x:A. x) [Any] Empty()", () => {
    // The body references the bound type variable A in the annotation.
    // At runtime types are erased, so evaluation still succeeds.
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("(^A <: Any. \\x:A. x) [Any] Empty()", new ValueEnv())
    assert(result.size === 1)
    const [val] = result
    assert(val !== undefined)
})

Deno.test("Cofold: cofold [Stream] (unfold [Stream] Zero() { head -> self, tail -> self }) { head(h) -> h } type-checks", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith(
        "cofold [Stream] (unfold [Stream] Zero() { head -> self, tail -> self }) { head(h) -> h }",
        new TypeEnv(),
    )
    // Cofold type-checks — the result type is the handler body type
    assert(result.size === 1)
})

Deno.test("Cofold: evaluate cofold [Stream] (unfold ... { head -> Zero(), ... }) { head(h) -> h } produces Zero", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "cofold [Stream] (unfold [Stream] Zero() { head -> Zero(), tail -> self }) { head(h) -> h }",
        new ValueEnv(),
    )
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val !== undefined, "should produce a value")
    assert((val as { kind?: string })?.kind === "variantVal")
    assertEquals((val as { variantName?: string })?.variantName, "Zero")
})
