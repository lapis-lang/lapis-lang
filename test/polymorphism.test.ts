/**
 * Polymorphism and cofold tests — verify T-TAbs, T-TApp, and T-Cofold.
 */

import { LCEval, LCTypeCheck } from "../src/index.ts"
import { TypeEnv } from "../src/core/types.ts"
import { ValueEnv } from "../src/core/values.ts"
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
    assertEquals(type.constructor.name, "PolymorphicType")
})

Deno.test("Polymorphism: (^alpha <: Any. \\x:Any. x) [Any] type-checks", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("(^alpha <: Any. \\x:Any. x) [Any]", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    // The result is Any → Any (the body type with α := Any)
    assertEquals(type.constructor.name, "FunType")
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
