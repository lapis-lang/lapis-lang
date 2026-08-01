/**
 * Concrete syntax tests for the LC grammar.
 *
 * Semantic meaning belongs to the typing and evaluation grammars. These tests
 * only establish that source text is accepted as a complete derivation and
 * that the retained tree exposes the expected production structure.
 */

import { assert, assertEquals } from "@std/assert"
import { LCAST, TypeRegistry } from "../src/index.ts"
import { Any, DataType, Field, Variant } from "../src/core/types.ts"

const stack = new DataType("Stack", [])
stack.variants.push(
    new Variant("Empty", []),
    new Variant("Push", [new Field("value", Any, false), new Field("rest", stack, true)]),
)

const registry = new TypeRegistry()
registry.register(stack)
const ast = new LCAST().setRegistry(registry)

function parse(input: string) {
    return ast.parseToTree(input)
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
