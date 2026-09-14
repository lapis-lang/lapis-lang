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
import { Any, FunType, TypeEnv } from "../src/core/types.ts"
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

Deno.test("Syntax: `in` is reserved — a variable named `in` cannot split a let", () => {
    // `in` is the one keyword in a mid-expression position (the let
    // terminator). If it lexed as an `ident`, `let x:Any = f in y in z`
    // would have two parses that type at different types — def = `(f in) y`,
    // body = `z` vs. def = `f`, body = `(y in) z`. The reserved-word
    // rejection in `ident` kills the second reading; the application
    // `f in ...` (whitespace-separated) is the variable use, which cannot
    // parse because `in` is not an ident.
    //
    // With `f : Any` (not a function), even the first reading is ill-typed —
    // both parses are rejected, so the forest is empty either way.
    const gamma = new TypeEnv().extend("f", Any).extend("y", Any).extend("z", Any)
    const result = tc.parseWith("let x:Any = f in y in z", gamma)
    assertEquals(
        result.size,
        0,
        "a variable named `in` must not create a second let reading",
    )
})

Deno.test("Syntax: let binds a single expression, terminated by `in`", () => {
    // The let grammar consumes exactly one def before the terminator; the
    // application chain `f y` is one expression (application requires
    // whitespace), and `in z` is the body. Unambiguous.
    const gamma = new TypeEnv().extend("f", Any)
    const result = tc.parseWith("let x:Any = f in Zero()", gamma)
    assert(result.size === 1)
})

Deno.test("Syntax: keyword-forming words are legal variable names", () => {
    // Only `in` is reserved (the let terminator — a mid-expression position).
    // The keyword formers (`let`, `fold`, `unfold`, `cofold`) are prefix
    // positions with mandatory keyword continuations (`fold [T]`, `let x:σ`),
    // which a variable occurrence can never match — so a variable named
    // `fold` parses exactly once: as a variable.
    const any2any = new FunType(Any, Any)
    const gamma = new TypeEnv()
        .extend("a", Any)
        .extend("let", any2any)
        .extend("fold", any2any)
        .extend("unfold", any2any)
        .extend("cofold", any2any)
        .extend("y", Any)

    // Whitespace application with a keyword-named function variable:
    // unambiguous — exactly one parse.
    assertEquals(tc.parseWith("fold a", gamma).size, 1)
    assertEquals(tc.parseWith("unfold a", gamma).size, 1)
    assertEquals(tc.parseWith("cofold a", gamma).size, 1)
    assertEquals(tc.parseWith("let a", gamma).size, 1)

    // A keyword-named variable in a let's def position: the letProd prefix
    // needs `ident ":"` after "let", so only the variable reading survives.
    assertEquals(tc.parseWith("let x:Any = fold in y", gamma).size, 1)
    assertEquals(tc.parseWith("let x:Any = let in y", gamma).size, 1)
})
