/**
 * Concrete syntax tests for the LC grammar.
 *
 * Semantic meaning belongs to the typing and evaluation grammars. These tests
 * only establish that source text is accepted as a complete derivation and
 * that the retained tree exposes the expected production structure.
 *
 * Parse acceptance is verified through `LCTypeCheck.parseToTree`: if the
 * grammar accepts the input, the parse forest is non-empty and the retained
 * derivation tree covers the full source span.
 */

import { assert, assertEquals } from "@std/assert"
import { LCTypeCheck } from "../src/index.ts"
import { createTestFixtures } from "./fixtures.ts"

const { registry } = createTestFixtures()
const tc = new LCTypeCheck().setRegistry(registry)

function parse(input: string) {
    return tc.parseToTree(input)
}

Deno.test("Syntax: lambda and application consume the complete input", () => {
    const { forest, trees } = parse("(\\x:Any. x) (\\y:Any. y)")
    assertEquals(forest.size, 1)
    assertEquals(trees.length, 1)
    assertEquals(trees[0]!.root.span, { start: 0, end: 23 })
})

Deno.test("Syntax: data constructor tree retains nested structure", () => {
    const { forest, trees } = parse("Push(Empty(), Empty())")
    assertEquals(forest.size, 1)
    assertEquals(trees.length, 1)
    assert(trees[0]!.root.children.length > 0)
    assertEquals(trees[0]!.root.span, { start: 0, end: 22 })
})

Deno.test("Syntax: malformed input is rejected as a complete derivation", () => {
    const { forest } = parse("\\x:Any. (")
    assertEquals(forest.size, 0)
})

Deno.test("Syntax: type arrows accept both concrete spellings", () => {
    assertEquals(parse("\\x:Any -> Any. x").forest.size, 1)
    assertEquals(parse("\\x:Any → Any. x").forest.size, 1)
})
