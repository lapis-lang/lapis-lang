/**
 * Data types test — verifies variant construction, fold, type-checking,
 * and evaluation on a Stack data type using concrete syntax.
 */

import { LCAST, LCEval, LCTypeCheck } from "../src/index.ts"
import { TypeEnv } from "../src/core/types.ts"
import { ValueEnv, VariantVal } from "../src/core/values.ts"
import { createTestFixtures } from "./fixtures.ts"

import { assert, assertEquals } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry, stack: StackType } = createTestFixtures()

// ── Tests ─────────────────────────────────────────────────────────────────────

Deno.test("Data: type-check Empty() has type Stack", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("Empty()", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assertEquals(type, StackType)
})

Deno.test("Data: type-check Push(Empty(), Empty()) has type Stack", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith("Push(Empty(), Empty())", new TypeEnv())
    assert(result.size === 1)
    const [type] = result
    assertEquals(type, StackType)
})

Deno.test("Data: evaluate Empty() produces VariantVal", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("Empty()", new ValueEnv())
    assert(result.size === 1)
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Empty")
})

Deno.test("Data: evaluate Push(Empty(), Empty()) produces VariantVal", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith("Push(Empty(), Empty())", new ValueEnv())
    assert(result.size === 1)
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Push")
    assertEquals(val.fields.get("value")?.kind, "variantVal")
    assertEquals(val.fields.get("rest")?.kind, "variantVal")
})

Deno.test("Data: fold [Stack] Empty() { ... } type-checks as Stack", () => {
    const tc = new LCTypeCheck().setRegistry(registry)
    const result = tc.parseWith(
        "fold [Stack] Empty() { Empty() -> Empty(), Push(v rest) -> rest }",
        new TypeEnv(),
    )
    assert(result.size === 1)
    const [type] = result
    assertEquals(type, StackType)
})

Deno.test("Data: fold [Stack] Empty() { ... } evaluates to Empty", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "fold [Stack] Empty() { Empty() -> Empty(), Push(v rest) -> rest }",
        new ValueEnv(),
    )
    assert(result.size === 1)
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Empty")
})

Deno.test("Data: fold [Stack] Push(Empty(), Empty()) { ... } evaluates to Empty", () => {
    const ev = new LCEval().setRegistry(registry)
    const result = ev.parseWith(
        "fold [Stack] Push(Empty(), Empty()) { Empty() -> Empty(), Push(v rest) -> rest }",
        new ValueEnv(),
    )
    assert(result.size === 1)
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Empty")
})

Deno.test("Data: AST parse Empty() produces VariantCon", () => {
    const ast = new LCAST().setRegistry(registry)
    const result = ast.parse("Empty()")
    assert(result.size === 1)
    const [term] = [...result]
    assert(term !== undefined)
    assertEquals((term as { kind: string }).kind, "variantCon")
})
