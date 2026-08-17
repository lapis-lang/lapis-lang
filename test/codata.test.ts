/**
 * Codata types test — verifies unfold, observation, type-checking,
 * and evaluation on a Stream codata type using concrete syntax.
 */

import { LCEval, LCTypeCheck } from "../src/index.ts"
import { Any, TypeEnv } from "../src/core/types.ts"
import { ValueEnv, VariantVal } from "../src/core/values.ts"
import { SpanCodataVal } from "../src/core/eval_grammar.ts"
import { createTestFixtures } from "./fixtures.ts"

import { assert, assertEquals } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry, stream: StreamType } = createTestFixtures()

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
