/**
 * Type checker grammar tests — verify LCTypeCheck parses and type-checks
 * LC terms from concrete syntax.
 */

import { LCTypeCheck } from "../src/index.ts"
import { Any, FunType, Nothing, type Type, TypeEnv } from "../src/core/types.ts"
import { createTestFixtures } from "./fixtures.ts"
import { assert, assertEquals } from "@std/assert"

// ── Fixtures for subsumption tests ───────────────────────────────────────────

const { registry, nat } = createTestFixtures()

/** Type-check `src` under Γ with the test registry, returning the forest. */
function typeForestOf(src: string, gamma: TypeEnv = new TypeEnv()): Set<Type> {
    return new LCTypeCheck().setRegistry(registry).parseWith(src, gamma)
}

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

// ── T-Sub: subsumption at let-bindings ───────────────────────────────────────
//
// T-Let premise 1: Γ ⊢ t : σ  ∧  σ <: τ  ⟹  Γ ⊢ let x:τ = t in u : (type of u)
// The def's type σ must be a subtype of the declared type τ. If not, the term
// is ill-typed (empty parse forest). Subsumption is implicit — no standalone
// T-Sub production; each consumer site checks isSubtype in its own premise.

Deno.test("T-Sub: let x:Any = Zero() in x — Nothing not needed, Nat <: Any", () => {
    // Zero() : Nat, Nat <: Any → accepted; body sees x : Any
    const result = typeForestOf("let x:Any = Zero() in x")
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Any)
})

Deno.test("T-Sub: let x:Any = \\y:Nat. y in x — FunType <: Any via S-Top", () => {
    // \\y:Nat. y : Nat → Nat, (Nat → Nat) <: Any → accepted
    const result = typeForestOf("let x:Any = \\y:Nat. y in x")
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Any)
})

Deno.test("T-Sub: let x:Nat = Zero() in x — Nat <: Nat via S-Refl", () => {
    // Zero() : Nat, Nat <: Nat → accepted; body sees x : Nat
    const result = typeForestOf("let x:Nat = Zero() in x")
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, nat)
})

Deno.test("T-Sub: let x:Nat = \\y:Any. y in x — FunType not <: Nat, rejected", () => {
    // \\y:Any. y : Any → Any, (Any → Any) is not <: Nat → ill-typed
    const result = typeForestOf("let x:Nat = \\y:Any. y in x")
    assertEquals(result.size, 0, "a function bound to a Nat declaration must be rejected")
})

Deno.test("T-Sub: let x:Nat = True() in x — Bool not <: Nat, rejected", () => {
    // True() : Bool, Bool is not <: Nat → ill-typed
    const result = typeForestOf("let x:Nat = True() in x")
    assertEquals(result.size, 0, "a Bool bound to a Nat declaration must be rejected")
})

Deno.test("T-Sub: let y:Any = x in Zero() — x:Nothing, Nothing <: Any (S-Bot)", () => {
    // x : Nothing, Nothing <: Any → accepted; body type is Nat
    const result = typeForestOf("let y:Any = x in Zero()", new TypeEnv().extend("x", Nothing))
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, nat)
})

Deno.test("T-Sub: let y:Nat = x in Zero() — x:Nothing, Nothing <: Nat (S-Bot)", () => {
    // x : Nothing, Nothing <: Nat → accepted; body type is Nat
    const result = typeForestOf("let y:Nat = x in Zero()", new TypeEnv().extend("x", Nothing))
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, nat)
})

Deno.test("T-Sub: let y:Nat = x in y — x:Nothing, Nothing <: Nat, body sees declared Nat", () => {
    // x : Nothing, Nothing <: Nat → accepted; body sees y : Nat
    const result = typeForestOf("let y:Nat = x in y", new TypeEnv().extend("x", Nothing))
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, nat)
})

Deno.test("T-Sub: let y:Any = x in y — x:Any, Any <: Any via S-Refl", () => {
    // x : Any, Any <: Any via S-Refl → accepted; body sees y : Any
    const result = typeForestOf("let y:Any = x in y", new TypeEnv().extend("x", Any))
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Any)
})

Deno.test("T-Sub: let y:Nat = x in y — x:Any, Any not <: Nat, rejected", () => {
    // x : Any, Any is not <: Nat → ill-typed
    const result = typeForestOf("let y:Nat = x in y", new TypeEnv().extend("x", Any))
    assertEquals(result.size, 0, "an Any-typed def bound to a Nat declaration must be rejected")
})

Deno.test("T-Sub: nested let — subsumption at each binding", () => {
    // Inner: let z:Nat = Zero() in z  → Nat <: Nat, body : Nat
    // Outer: let y:Any = (let z:Nat = Zero() in z) in y  → Nat <: Any, body : Any
    const result = typeForestOf("let y:Any = (let z:Nat = Zero() in z) in y")
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Any)
})
