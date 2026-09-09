/**
 * Nothing propagation tests — verify the bottom type propagates through
 * variant construction, observation, fold, cofold, and unfold.
 *
 * Semantics: an eagerly-evaluated subterm of type `Nothing` makes the
 * surrounding term uninhabited — the production returns `Nothing`
 * (principle of explosion). Since `Nothing <: σ` for all σ, the result
 * still flows anywhere via subsumption.
 *
 * Ordering guarantee: `Nothing` propagation applies only when the term is
 * otherwise well-typed. A genuine premise violation (unknown name,
 * non-exhaustive handlers) still yields that rule's own failure signal —
 * rejection (empty forest) or `Any`, depending on the site — never a
 * spurious `Nothing`.
 *
 * Boundary: `app` in the fn position rejects a `Nothing` function (empty
 * forest) rather than propagating, and `app`/`let` in the arg/def positions
 * do not propagate (the subterm is consumed, not observed) — see the
 * composition tests at the bottom.
 */

import { LCTypeCheck } from "../src/index.ts"
import { Any, Nothing, type Type, TypeEnv } from "../src/core/types.ts"
import { createTestFixtures } from "./fixtures.ts"

import { assert, assertEquals } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry, stack, stream, bool, nat } = createTestFixtures()

/** Γ with x : Nothing — the uninhabited binding used by every test. */
function nothingEnv(): TypeEnv {
    return new TypeEnv().extend("x", Nothing)
}

/** Type-check `src` under Γ, returning the parse forest. */
function typeForestOf(src: string, gamma: TypeEnv = new TypeEnv()): Set<Type> {
    const tc = new LCTypeCheck().setRegistry(registry)
    return tc.parseWith(src, gamma)
}

// ── T-Variant: Nothing arg propagates ────────────────────────────────────────

Deno.test("Nothing propagation: variant construction with Nothing arg is Nothing", () => {
    const result = typeForestOf("Push(x, Empty())", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Nothing)
})

Deno.test("Nothing propagation: variant construction with Nothing recursive arg is Nothing", () => {
    const result = typeForestOf("Push(Zero(), x)", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Nothing)
})

Deno.test("Nothing propagation: variant construction with well-typed arg is Stack", () => {
    const result = typeForestOf("Push(Zero(), Empty())", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, stack)
})

Deno.test("Nothing propagation: variant arg type error is not masked by Nothing", () => {
    // x : Nothing (arg 0), b : Bool (arg 1, in the recursive Stack position).
    // The Bool arg violates the premise, so the construction is ill-typed —
    // the error signal (Any) must win over Nothing propagation.
    const gamma = nothingEnv().extend("b", bool)
    const result = typeForestOf("Push(x, b)", gamma)
    assert(result.size === 1, "should have exactly one parse")
    assertEquals([...result][0], Any)
})

Deno.test("Nothing propagation: extra variant arg is ill-typed, not masked by Nothing", () => {
    // Empty() takes no fields; a Nothing-typed extra arg must not make an
    // arity-mismatched construction look inhabited.
    const result = typeForestOf("Empty(x)", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    assertEquals([...result][0], Any)
})

// ── T-Obs: Nothing scrutinee propagates ───────────────────────────────────────

Deno.test("Nothing propagation: observation on Nothing scrutinee is Nothing", () => {
    const result = typeForestOf("x.head", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Nothing)
})

Deno.test("Nothing propagation: observation on Nothing scrutinee (continuation) is Nothing", () => {
    const result = typeForestOf("x.tail", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Nothing)
})

Deno.test("Nothing propagation: observation on Stream scrutinee is Any", () => {
    const result = typeForestOf(
        "(unfold [Stream] Zero() { head -> self, tail -> self }).head",
    )
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Any)
})

// ── T-Fold: Nothing scrutinee propagates ──────────────────────────────────────

Deno.test("Nothing propagation: fold with Nothing scrutinee is Nothing", () => {
    const result = typeForestOf(
        "fold [Stack] x { Empty() -> Empty(), Push(v rest) -> rest }",
        nothingEnv(),
    )
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Nothing)
})

Deno.test("Nothing propagation: fold with Stack scrutinee is Stack", () => {
    const result = typeForestOf(
        "fold [Stack] Empty() { Empty() -> Empty(), Push(v rest) -> rest }",
    )
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, stack)
})

Deno.test("Nothing propagation: non-exhaustive fold with Nothing scrutinee is ill-typed", () => {
    // Missing the Push handler — a genuine premise violation. The error
    // signal (Any) must win over Nothing propagation.
    const result = typeForestOf(
        "fold [Stack] x { Empty() -> Empty() }",
        nothingEnv(),
    )
    assert(result.size === 1, "should have exactly one parse")
    assertEquals([...result][0], Any)
})

// ── T-Unfold: Nothing seed propagates ─────────────────────────────────────────

Deno.test("Nothing propagation: unfold with Nothing seed is Nothing", () => {
    const result = typeForestOf(
        "unfold [Stream] x { head -> self, tail -> self }",
        nothingEnv(),
    )
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Nothing)
})

Deno.test("Nothing propagation: unfold with Nat seed is Stream", () => {
    const result = typeForestOf(
        "unfold [Stream] Zero() { head -> self, tail -> self }",
    )
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, stream)
})

Deno.test("Nothing propagation: non-exhaustive unfold with Nothing seed is ill-typed", () => {
    // Missing the tail generator — a genuine premise violation. The error
    // signal (Any) must win over Nothing propagation.
    const result = typeForestOf(
        "unfold [Stream] x { head -> self }",
        nothingEnv(),
    )
    assert(result.size === 1, "should have exactly one parse")
    assertEquals([...result][0], Any)
})

// ── T-Cofold: Nothing scrutinee propagates ───────────────────────────────────

Deno.test("Nothing propagation: cofold with Nothing scrutinee is Nothing", () => {
    const result = typeForestOf(
        "cofold [Stream] x { head(h) -> Zero() }",
        nothingEnv(),
    )
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Nothing)
})

Deno.test("Nothing propagation: cofold scrutinee type error is not masked by Nothing", () => {
    // Zero() : Nat, not a subtype of Stream — a genuine premise violation.
    const result = typeForestOf("cofold [Stream] Zero() { head(h) -> Zero() }")
    assert(result.size === 1, "should have exactly one parse")
    assertEquals([...result][0], Any)
})

// ── Composition: Nothing flows through nested productions ────────────────────

Deno.test("Nothing propagation: nested variant construction propagates Nothing", () => {
    // Push(x, Empty()) : Nothing, so Push(Push(x, Empty()), Empty()) : Nothing.
    const result = typeForestOf("Push(Push(x, Empty()), Empty())", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, Nothing)
})

// ── Boundary: positions that do NOT propagate ─────────────────────────────────

Deno.test("Nothing boundary: application in fn position rejects a Nothing function", () => {
    // x : Nothing is not a FunType, so T-App's premise fails — rejection
    // (empty forest), not propagation. Note: TAPL rcdsubbot propagates
    // TyBot → TyBot here; this checker rejects instead.
    const result = typeForestOf("x y", nothingEnv().extend("y", Any))
    assertEquals(result.size, 0, "applying Nothing must be rejected")
})

Deno.test("Nothing boundary: application in arg position does not propagate", () => {
    // \\y:Any. Push(y, Empty()) : Any → Stack, applied to x : Nothing.
    // T-App's premise holds (Nothing <: Any), and the result is Stack —
    // the Nothing is consumed by the lambda, not propagated through app.
    const result = typeForestOf("(\\y:Any. Push(y, Empty())) x", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, stack)
})

Deno.test("Nothing boundary: let definition position does not propagate", () => {
    // The def is eagerly evaluated but consumed by the binding — the body
    // type is the result, matching TAPL (T-Let does not propagate Bot).
    const result = typeForestOf("let y:Any = x in Zero()", nothingEnv())
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, nat)
})
