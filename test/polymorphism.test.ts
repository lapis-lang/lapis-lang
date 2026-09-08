/**
 * Polymorphism and cofold tests — verify T-TAbs, T-TApp, and T-Cofold.
 */

import { LCEval, LCTypeCheck, ValueEnv } from "../src/index.ts"
import { Any, FunType, PolymorphicType, TypeEnv } from "../src/core/types.ts"
import { createTestFixtures } from "./fixtures.ts"

import { assert, assertEquals } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry } = createTestFixtures()

// ── Tests ─────────────────────────────────────────────────────────────────────

Deno.test("Polymorphism: ^alpha <: Any. \\x:Any. x type-checks", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("^alpha <: Any. \\x:Any. x", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    // ∀α<:Any. (Any → Any) — a PolymorphicType, NOT a FunType
    assert(type instanceof PolymorphicType, `expected PolymorphicType, got ${type}`)
    assertEquals(type.typeVarName, "alpha")
    assertEquals(type.bound, Any)
    assert(type.body instanceof FunType, `expected FunType body, got ${type.body}`)
})

Deno.test("Polymorphism: (^alpha <: Any. \\x:Any. x) [Any] type-checks", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^alpha <: Any. \\x:Any. x) [Any]", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    // The result is Any → Any (the body type with α := Any)
    assert(type instanceof FunType, `expected FunType, got ${type}`)
    assertEquals(type.param, Any)
    assertEquals(type.result, Any)
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
    const result = tc.parseWith("(^alpha <: Stack. \\x:Any. x) [Nat]", new TypeEnv())
    assertEquals(result.size, 0, "an argument type outside the bound must be rejected")
})

Deno.test("Polymorphism: chained type application on a non-polymorphic result is rejected", () => {
    // The first application yields Any → Any (not a ∀ type), so the second
    // T-TApp premise fails — rejection, not `undefined`.
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^alpha <: Any. \\x:Any. x) [Nat] [Bool]", new TypeEnv())
    assertEquals(result.size, 0, "chaining past a non-polymorphic result must be rejected")
})

Deno.test("Polymorphism: chained type applications with satisfied bounds type-check", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith(
        "(^alpha <: Any. ^beta <: Any. \\x:Any. x) [Nat] [Bool]",
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
    const result = tc.parseWith("(^alpha <: Any. \\x:Any. x) [Nat]", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assert(type instanceof FunType, `expected FunType, got ${type}`)
    assertEquals(type.param, Any)
    assertEquals(type.result, Any)
})

Deno.test("Polymorphism: evaluate ^alpha <: Any. \\x:Any. x", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("^alpha <: Any. \\x:Any. x", new ValueEnv())
    assert(result.size === 1)
    // Type abstraction evaluates to the body value (type erasure)
    const [val] = result
    assert(val !== undefined)
})

Deno.test("Polymorphism: evaluate (^alpha <: Any. \\x:Any. x) [Any] Empty()", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("(^alpha <: Any. \\x:Any. x) [Any] Empty()", new ValueEnv())
    assert(result.size === 1)
    const [val] = result
    // Type application evaluates the body, then applies to the argument
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
