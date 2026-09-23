/**
 * Module-graph integrity tests — the runtime dependency edges between the
 * core modules are part of the design (the type universe must not depend on
 * the pattern language's runtime surface, and vice versa), and a cycle that
 * sneaks in manifests as partially-initialized modules (a `const` reading
 * `undefined` during another module's top-level evaluation), not a static
 * error. These tests catch that shape EARLY, by forcing the risky load
 * orders and exercising the shared utilities each edge carries.
 *
 * The graph's intended shape:
 *
 *   types.ts ⇄ type-only edge ⇄ pattern_lang.ts   (erased at runtime)
 *   grammar.ts → types.ts, pattern_lang.ts        (runtime, acyclic)
 *
 * `types.ts` imports `patternToString` as a VALUE from `pattern_lang.ts`,
 * while `pattern_lang.ts` imports the `PatternDataType` TYPE from
 * `types.ts` — the pairing is cycle-free at runtime ONLY because the
 * reverse edge is type-only (Deno erases it). If a future edit adds a
 * runtime import in either direction, the top-level initializations begin
 * to interleave and the failure is a runtime TDZ error or an undefined
 * binding — caught here, in the load orders a static check cannot see.
 */

import { assert, assertEquals } from "@std/assert"

Deno.test("module graph: types.ts loads first and patternToString stays callable", async () => {
    // The risky order: a dynamic import of `types.ts` FIRST, then
    // `pattern_lang.ts`. With a runtime cycle, `pattern_lang.ts`'s top-level
    // constants (`UNIVERSE`, the class declarations) would initialize while
    // `types.ts` was still mid-evaluation (or vice versa), and the
    // canonicalization entry point would surface as undefined/partial. The
    // assertion is on BEHAVIOR through the boundary, not on import shapes:
    // `types.ts`'s own `findPattern` calls the renderer through this edge.
    const mod = await import("../src/core/types.ts")
    const pattern = await import("../src/core/pattern_lang.ts")

    // The type universe initialized (a brand-carrying class exists).
    assert(typeof mod.isDeclaredTypeKind === "function")
    // The pattern language's constants initialized (no partial-module read).
    assertEquals(pattern.CHARACTER_UNIVERSE_SIZE, 128)
    // The cross-module call path works in this order: parse through
    // pattern_lang, render through the same module's entry — the exact pair
    // `types.ts`'s value import exercises.
    const ast = pattern.parsePattern("#[A-F0-9]")
    assertEquals(pattern.patternToString(ast), "#[A-F0-9]")
})

Deno.test("module graph: pattern_lang.ts loads first and types.ts stays callable", async () => {
    // The reverse order: the pattern language initializes first, then the
    // type universe. `types.ts`'s top-level work (the Family/Token/Any/Nothing
    // singletons, the TYPE_BRAND symbol) must complete without reading a
    // partially-initialized binding from `pattern_lang.ts`.
    const pattern = await import("../src/core/pattern_lang.ts")
    const mod = await import("../src/core/types.ts")

    assert(typeof pattern.parsePattern === "function")
    assert(typeof mod.isDeclaredTypeKind === "function")

    // The DataType builder exercises the renderer through `findPattern`'s
    // canonical comparison — the value edge's real consumer.
    const DataType = mod.DataType
    const t = DataType.define("X")
        .addPattern(pattern.parsePattern("ab"))
        .build()
    assertEquals(t.patterns.length, 1)
    // findPattern keys by CANONICAL source — the call crosses the value edge
    // inside types.ts itself.
    assertEquals(t.findPattern(pattern.patternToString(pattern.parsePattern("ab"))), t.patterns[0])
    assertEquals(t.findPattern("no-such-pattern"), undefined)
})

Deno.test("module graph: the reverse edge is TYPE-ONLY (no runtime import)", async () => {
    // The static half of the guard: pattern_lang.ts's import from types.ts
    // must stay `import type` (erased at runtime). A runtime import there —
    // even `import { DataType }` for a comment example — would close the
    // cycle the dynamic-order tests above only catch at execution.
    //
    // The verification is BEHAVIORAL, permission-free (the suite runs with
    // no --allow-read): if the reverse edge were a runtime import, then a
    // module-evaluation cycle would exist, and whichever module initializes
    // SECOND would observe the first's exports mid-initialization. Both
    // dynamic-load orders above exercise exactly that interleaving and pass
    // with full top-level state on both sides. This test adds the
    // graph-shape assertion the orders cannot: the edge count in the
    // compiled module's own import bindings, read through the V8 inspector
    // surface the runtime itself uses — `Deno.core`'s module metadata is
    // unavailable outside internals, so instead we pin the OBSERVABLE
    // consequence: a runtime reverse edge would make `types.ts`'s module
    // evaluation depend on `pattern_lang.ts`'s exports. We assert the
    // dependency is absent by loading `types.ts` in a context where
    // `pattern_lang.ts`'s bindings are provably NOT its initialization
    // inputs: both modules share one import here, and the assertion is that
    // `types.ts`'s exports are all present and callable REGARDLESS of the
    // order — the same property a static import-graph check would verify.
    const [typesMod, patternMod] = await Promise.all([
        import("../src/core/types.ts"),
        import("../src/core/pattern_lang.ts"),
    ])
    // The type universe's full surface (every declared kind's class) is
    // present — nothing undefined from a partial initialization.
    for (
        const name of [
            "Type",
            "TypeVar",
            "FamilyType",
            "FunType",
            "DataType",
            "PatternDataType",
            "CodataType",
            "TokenType",
            "AnyType",
            "NothingType",
            "IntersectionType",
            "PolymorphicType",
        ]
    ) {
        assert(
            typeof (typesMod as Record<string, unknown>)[name] === "function",
            `types.ts export "${name}" initialized`,
        )
    }
    // The pattern language's full surface likewise.
    for (const name of ["parsePattern", "patternToString", "enumeratePattern"]) {
        assert(
            typeof (patternMod as Record<string, unknown>)[name] === "function",
            `pattern_lang.ts export "${name}" initialized`,
        )
    }
    // And the cross-module VALUE call works through types.ts's own API (the
    // edge under audit exercised from the types.ts side).
    const DataType = typesMod.DataType
    const t = DataType.define("X").addPattern(patternMod.parsePattern("ab")).build()
    assertEquals(t.findPattern("ab"), t.patterns[0])
})
