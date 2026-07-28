/**
 * LCEval tests — verify the grammar-based one-pass evaluator works.
 *
 * These tests parse LC text and evaluate it in a single pass using _forward
 * for closure body re-evaluation. No intermediate AST, no tree-walking.
 */

import { LCEval, SpanCodataVal } from "../src/index.ts"
import { Any, CodataType, DataType, Field, Observer, Variant } from "../src/core/types.ts"
import { SpanClosure, ValueEnv, VariantVal } from "../src/core/values.ts"
import { TypeRegistry } from "../src/core/grammar.ts"

import { assert, assertEquals } from "@std/assert"

// ── Define the Stack data type ────────────────────────────────────────────────

const StackType = new DataType("Stack", [])
StackType.variants.push(
    new Variant("Empty", []),
    new Variant("Push", [
        new Field("value", Any, false),
        new Field("rest", StackType, true),
    ]),
)

// ── Define the Stream codata type ─────────────────────────────────────────────

const StreamType = new CodataType("Stream", [])
;(StreamType as unknown as { observers: Observer[] }).observers = [
    new Observer("head", Any, false),
    new Observer("tail", StreamType, true),
]

// ── Registry ──────────────────────────────────────────────────────────────────

const registry = new TypeRegistry()
registry.register(StackType)
registry.register(StreamType)

// ── Tests ─────────────────────────────────────────────────────────────────────

Deno.test("LCEval: \\x:Any. x evaluates to a closure", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("\\x:Any. x", new ValueEnv())
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof SpanClosure)
    assertEquals(val.param, "x")
})

Deno.test("LCEval: (\\x:Any. x) Empty() evaluates to Empty", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("(\\x:Any. x) Empty()", new ValueEnv())
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Empty")
})

Deno.test("LCEval: let x:Any = Empty() in x evaluates to Empty", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("let x:Any = Empty() in x", new ValueEnv())
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Empty")
})

Deno.test("LCEval: Empty() evaluates to VariantVal", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("Empty()", new ValueEnv())
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Empty")
})

Deno.test("LCEval: Push(Empty(), Empty()) evaluates to VariantVal", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("Push(Empty(), Empty())", new ValueEnv())
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Push")
    assertEquals(val.fields.get("value")?.kind, "variantVal")
    assertEquals(val.fields.get("rest")?.kind, "variantVal")
})

Deno.test("LCEval: fold [Stack] Empty() { Empty() -> Empty(), Push(v rest) -> rest } evaluates to Empty", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "fold [Stack] Empty() { Empty() -> Empty(), Push(v rest) -> rest }",
        new ValueEnv(),
    )
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof VariantVal)
    // fold on Empty() → Empty handler → Empty()
    assertEquals(val.variantName, "Empty")
})

Deno.test("LCEval: fold [Stack] Push(Empty(), Empty()) { Empty() -> Empty(), Push(v rest) -> rest } evaluates to Empty", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "fold [Stack] Push(Empty(), Empty()) { Empty() -> Empty(), Push(v rest) -> rest }",
        new ValueEnv(),
    )
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof VariantVal)
    // fold on Push(Empty(), Empty()) → Push handler → rest = Empty()
    assertEquals(val.variantName, "Empty")
})

Deno.test("LCEval: unfold [Stream] Empty() { head -> Empty(), tail -> self } evaluates to codata value", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "unfold [Stream] Empty() { head -> Empty(), tail -> self }",
        new ValueEnv(),
    )
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof SpanCodataVal)
    assertEquals(val.codataType, StreamType)
})

Deno.test("LCEval: (unfold [Stream] Empty() { head -> Empty(), tail -> self }).head evaluates to Empty", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "(unfold [Stream] Empty() { head -> Empty(), tail -> self }).head",
        new ValueEnv(),
    )
    assert(result.size >= 1, "should have at least one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Empty")
})
