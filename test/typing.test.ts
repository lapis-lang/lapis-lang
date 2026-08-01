/**
 * Type checker grammar tests — verify LCTypeCheck parses and type-checks
 * LC terms from concrete syntax.
 */

import { LCTypeCheck } from "../src/index.ts"
import { Any, FunType, TypeEnv } from "../src/core/types.ts"
import { assert, assertEquals } from "@std/assert"

Deno.test("TypeCheck: \\x:Any. x has type Any → Any", () => {
    const tc = new LCTypeCheck()
    const result = tc.parseWith("\\x:Any. x", new TypeEnv())
    assert(result.size === 1, "should have at least one parse")
    const [type] = result
    assert(type instanceof FunType)
    assertEquals(type.param, Any)
    assertEquals(type.result, Any)
})

Deno.test("TypeCheck: \\x:Any. \\y:Any. x has type Any → Any → Any", () => {
    const tc = new LCTypeCheck()
    const result = tc.parseWith("\\x:Any. \\y:Any. x", new TypeEnv())
    assert(result.size === 1, "should have at least one parse")
    const [type] = result
    assert(type instanceof FunType)
    assert(type.result instanceof FunType)
})

Deno.test("TypeCheck: (\\x:Any. x) (\\y:Any. y) type-checks", () => {
    const tc = new LCTypeCheck()
    const result = tc.parseWith("(\\x:Any. x) (\\y:Any. y)", new TypeEnv())
    // Should type-check: applying identity to identity
    assert(result.size === 1, "should have at least one parse")
})

Deno.test("TypeCheck: ill-typed application produces empty forest", () => {
    const tc = new LCTypeCheck()
    const result = tc.parseWith("\\x:Any. x x", new TypeEnv())
    assertEquals(result.size, 0, "an application of Any must be rejected")
})

Deno.test("TypeCheck: let x:Any = \\y:Any. y in x", () => {
    const tc = new LCTypeCheck()
    const result = tc.parseWith("let x:Any = \\y:Any. y in x", new TypeEnv())
    assert(result.size === 1, "should have at least one parse")
    const [type] = result
    // x : Any, so the result is Any
    assertEquals(type, Any)
})
