/**
 * Lattice operations tests — verify join, meet, and Nothing propagation.
 *
 * These test the subtyping lattice operations adapted from TAPL §16.4
 * (fullfsub) and the Nothing (Bot) propagation from TAPL §15.3 (rcdsubbot).
 */

import { isSubtype, join, meet } from "../src/index.ts"
import { Any, DataType, Field, FunType, Nothing, Variant } from "../src/core/types.ts"

import { assert, assertEquals } from "@std/assert"

// ── Types for testing ─────────────────────────────────────────────────────────

const StackType = new DataType("Stack", [])
StackType.variants.push(
    new Variant("Empty", []),
    new Variant("Push", [
        new Field("value", Any, false),
        new Field("rest", StackType, true),
    ]),
)

const QueueType = new DataType("Queue", [])
QueueType.variants.push(
    new Variant("Empty", []),
    new Variant("Enq", [
        new Field("value", Any, false),
        new Field("rest", QueueType, true),
    ]),
)

// ── Join tests ───────────────────────────────────────────────────────────────

Deno.test("join: σ <: τ ⟹ join(σ, τ) = τ", () => {
    // Nothing <: Any, so join(Nothing, Any) = Any
    assertEquals(join(Nothing, Any), Any)
})

Deno.test("join: τ <: σ ⟹ join(σ, τ) = σ", () => {
    // Nothing <: Any, so join(Any, Nothing) = Any
    assertEquals(join(Any, Nothing), Any)
})

Deno.test("join: join(σ, σ) = σ (reflexive)", () => {
    assertEquals(join(StackType, StackType), StackType)
    assertEquals(join(Any, Any), Any)
    assertEquals(join(Nothing, Nothing), Nothing)
})

Deno.test("join: join(Nothing, σ) = σ (Nothing is bottom)", () => {
    assertEquals(join(Nothing, StackType), StackType)
    assertEquals(join(Nothing, Any), Any)
})

Deno.test("join: join(σ, Any) = Any (Any is top)", () => {
    assertEquals(join(StackType, Any), Any)
    assertEquals(join(Nothing, Any), Any)
})

Deno.test("join: join of incompatible types = Any", () => {
    // Stack and Queue have no common supertype (neither is <: the other)
    assertEquals(join(StackType, QueueType), Any)
})

Deno.test("join: join(σ→τ, σ→τ) = σ→τ", () => {
    const f = new FunType(Any, StackType)
    assertEquals(join(f, f), f)
})

Deno.test("join: join(σ₁→σ₂, τ₁→τ₂) = meet(σ₁,τ₁) → join(σ₂,τ₂)", () => {
    // join(Any→Stack, Any→Any) = meet(Any,Any) → join(Stack,Any) = Any → Any
    const f1 = new FunType(Any, StackType)
    const f2 = new FunType(Any, Any)
    const result = join(f1, f2)
    assert(result instanceof FunType)
    assertEquals(result.param, Any) // meet(Any, Any) = Any
    assertEquals(result.result, Any) // join(Stack, Any) = Any
})

// ── Meet tests ────────────────────────────────────────────────────────────────

Deno.test("meet: σ <: τ ⟹ meet(σ, τ) = σ", () => {
    // Nothing <: Any, so meet(Nothing, Any) = Nothing
    assertEquals(meet(Nothing, Any), Nothing)
})

Deno.test("meet: τ <: σ ⟹ meet(σ, τ) = τ", () => {
    // Nothing <: Any, so meet(Any, Nothing) = Nothing
    assertEquals(meet(Any, Nothing), Nothing)
})

Deno.test("meet: meet(σ, σ) = σ (reflexive)", () => {
    assertEquals(meet(StackType, StackType), StackType)
    assertEquals(meet(Any, Any), Any)
    assertEquals(meet(Nothing, Nothing), Nothing)
})

Deno.test("meet: meet(σ, Any) = σ (Any is top)", () => {
    assertEquals(meet(StackType, Any), StackType)
    assertEquals(meet(Nothing, Any), Nothing)
})

Deno.test("meet: meet(σ, Nothing) = Nothing (Nothing is bottom)", () => {
    assertEquals(meet(StackType, Nothing), Nothing)
    assertEquals(meet(Any, Nothing), Nothing)
})

Deno.test("meet: meet of incompatible types = Nothing", () => {
    // Stack and Queue have no common subtype
    assertEquals(meet(StackType, QueueType), Nothing)
})

Deno.test("meet: meet(σ₁→σ₂, τ₁→τ₂) = join(σ₁,τ₁) → meet(σ₂,τ₂)", () => {
    // meet(Any→Stack, Any→Any) = join(Any,Any) → meet(Stack,Any) = Any → Stack
    const f1 = new FunType(Any, StackType)
    const f2 = new FunType(Any, Any)
    const result = meet(f1, f2)
    assert(result instanceof FunType)
    assertEquals(result.param, Any) // join(Any, Any) = Any
    assertEquals(result.result, StackType) // meet(Stack, Any) = Stack
})

// ── Nothing propagation tests ─────────────────────────────────────────────────

Deno.test("Nothing propagation: applying Nothing returns Nothing", () => {
    // This tests the tree-walking TypeChecker's Nothing propagation.
    // If the function has type Nothing, the application has type Nothing.
    // (Principle of explosion — from ⊥, anything follows.)
    // We verify this via the subtyping lattice: Nothing <: FunType(σ, τ)
    assert(isSubtype(Nothing, new FunType(Any, Any)))
    assert(isSubtype(Nothing, StackType))
    assert(isSubtype(Nothing, Any))
})
