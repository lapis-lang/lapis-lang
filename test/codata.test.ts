/**
 * Codata types test — verifies unfold, observation, type-checking,
 * and evaluation on a Stream codata type using concrete syntax.
 */

import { LCEval, LCTypeCheck, TypeRegistry } from "../src/index.ts"
import { Any, CodataType, DataType, Field, Observer, TypeEnv, Variant } from "../src/core/types.ts"
import { ValueEnv, VariantVal } from "../src/core/values.ts"
import { SpanCodataVal } from "../src/core/eval_grammar.ts"

import { assert, assertEquals } from "@std/assert"

// ── Define the Stream codata type ─────────────────────────────────────────────

const StreamType = new CodataType("Stream", [])
;(StreamType as unknown as { observers: Observer[] }).observers = [
    new Observer("head", Any, false),
    new Observer("tail", StreamType, true),
]

// ── Define a Nat data type for stream elements ───────────────────────────────

const NatType = new DataType("Nat", [])
NatType.variants.push(
    new Variant("Zero", []),
    new Variant("Succ", [new Field("pred", NatType, true)]),
)

// ── Registry ──────────────────────────────────────────────────────────────────

const registry = new TypeRegistry()
registry.register(StreamType)
registry.register(NatType)

// ── Tests ─────────────────────────────────────────────────────────────────────

Deno.test("Codata: type-check unfold [Stream] Zero() { head -> self, tail -> self }", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith(
        "unfold [Stream] Zero() { head -> self, tail -> self }",
        new TypeEnv(),
    )
    assert(result.size === 1)
    const [type] = result
    assertEquals(type, StreamType)
})

Deno.test("Codata: evaluate unfold produces codata value", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "unfold [Stream] Zero() { head -> Zero(), tail -> self }",
        new ValueEnv(),
    )
    assert(result.size === 1)
    const [val] = result
    assert(val instanceof SpanCodataVal)
    assertEquals(val.codataType, StreamType)
})

Deno.test("Codata: evaluate observation (head) produces Zero", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "(unfold [Stream] Zero() { head -> Zero(), tail -> self }).head",
        new ValueEnv(),
    )
    assert(result.size === 1)
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Zero")
})

Deno.test("Codata: type-check observation (head) has type Any", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith(
        "(unfold [Stream] Zero() { head -> self, tail -> self }).head",
        new TypeEnv(),
    )
    assert(result.size === 1)
    const [type] = result
    assertEquals(type, Any)
})

Deno.test("Codata: type-check observation (tail) has type Stream", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith(
        "(unfold [Stream] Zero() { head -> self, tail -> self }).tail",
        new TypeEnv(),
    )
    assert(result.size === 1)
    const [type] = result
    assertEquals(type, StreamType)
})
