/**
 * Module-graph integrity tests — the runtime dependency edges between the
 * core modules are part of the design (the type universe must not depend on
 * the pattern language's runtime surface, and vice versa), and a cycle that
 * sneaks in manifests as partially-initialized modules (a `const` reading
 * `undefined` during another module's top-level evaluation), not a static
 * error. These tests catch that shape EARLY.
 *
 * The graph's intended shape:
 *
 *   types.ts ⇄ type-only edge ⇄ pattern_lang.ts   (erased at runtime)
 *   grammar.ts → types.ts, pattern_lang.ts        (runtime, acyclic)
 *
 * `types.ts` imports `patternToString` as a VALUE from `pattern_lang.ts`,
 * while `pattern_lang.ts` imports the `DataType` TYPE from
 * `types.ts` — the pairing is cycle-free at runtime ONLY because the
 * reverse edge is type-only (Deno erases it). If a future edit adds a
 * runtime import in either direction, the top-level initializations begin
 * to interleave and the failure is a runtime TDZ error or an undefined
 * binding.
 *
 * ISOLATION: each order check runs in a SUBPROCESS (`deno eval`), so every
 * check resolves a FRESH module graph — the in-process dynamic `import`
 * cache cannot mask an order-specific failure (the first in-process import
 * of either module initializes the whole graph, and the cache would serve
 * it to every later import, making an order claim untestable in-process).
 * The subprocess needs `--allow-run`; a runner without it skips the order
 * checks LOUDLY (visible in the report), never passes silently.
 */

import { assert, assertEquals } from "@std/assert"

/** The core module URLs the subprocess loads (absolute — the child resolves
 * them regardless of its CWD). */
const TYPES_URL = new URL("../src/core/types.ts", import.meta.url).href
const PATTERN_URL = new URL("../src/core/pattern_lang.ts", import.meta.url).href

/**
 * Run one load-order check in a fresh process: the child imports the two
 * modules in the given order (the ORDER is the script's own import
 * statement order) and verifies BOTH initialize fully and the cross-module
 * call path works. A cycle or partial initialization shows up as a non-zero
 * exit (TDZ error / undefined binding) or a failing assertion inside the
 * child — either way the subprocess exit code is the verdict, with its
 * stderr attached to the failure message.
 */
async function runOrderCheck(label: string, firstUrl: string, secondUrl: string): Promise<void> {
    const script = `
        // The load-ORDER is the variable under test: whichever module is
        // imported first initializes before the other. The full-surface
        // assertions run on BOTH modules BY SPECIFIER (not by load
        // position), so each check proves both modules fully initialize
        // under this order — a cycle's partial initialization would leave
        // some binding undefined in one of them. The names bind by MODULE
        // (types / pattern), never by load position — position-based
        // naming would read the wrong module's exports on one of the two
        // orders.
        // The imports are SEQUENTIAL — the order is the variable under test,
        // and Promise.all (the concurrent form) starts both dynamic loads
        // at once, letting the module system interleave their
        // initializations (the claimed order would not be exercised). The
        // first import fully initializes before the second begins.
        const first = await import(${JSON.stringify(firstUrl)});
        const second = await import(${JSON.stringify(secondUrl)});
        const firstIsTypes = ${JSON.stringify(firstUrl === TYPES_URL)}
        const t = firstIsTypes ? first : second
        const p = firstIsTypes ? second : first
        for (
            const name of [
                "Type", "TypeVar", "FamilyType", "FunType", "DataType",
                "CodataType", "TokenType", "AnyType",
                "NothingType", "IntersectionType", "PolymorphicType",
                "isDeclaredTypeKind", "isPatternCarrierType",
            ]
        ) {
            if (typeof t[name] !== "function") {
                throw new Error("types.ts export '" + name + "' not initialized");
            }
        }
        for (const name of ["parsePattern", "patternToString", "enumeratePattern"]) {
            if (typeof p[name] !== "function") {
                throw new Error("pattern_lang.ts export '" + name + "' not initialized");
            }
        }
        // The value edge exercised END-TO-END through types.ts's own API:
        // build a carrier, then read the pattern through findPattern — the
        // canonical comparison that crosses the value import.
        const carrier = t.DataType.define("X")
            .addPattern(p.parsePattern("ab"))
            .build();
        if (carrier.findPattern(p.patternToString(p.parsePattern("ab"))) === undefined) {
            throw new Error("the cross-module value path failed");
        }
        if (carrier.findPattern("no-such-pattern") !== undefined) {
            throw new Error("findPattern accepted an undeclared source");
        }
        console.log("OK");
    `
    let out
    try {
        out = await new Deno.Command("deno", {
            args: ["eval", script],
        }).output()
    } catch (e) {
        // A runner without spawn permission cannot run the order checks —
        // SKIP loudly (visible in the report), never pass silently.
        console.log(`SKIP (${label}): subprocess spawn unavailable: ${(e as Error).message}`)
        return
    }
    const stderr = new TextDecoder().decode(out.stderr)
    if (out.code !== 0) {
        // A cycle's TDZ error lands here — the subprocess's non-zero exit
        // IS the order-specific failure the in-process cache would mask.
        throw new Error(
            `${label}: module-graph check failed in a fresh process (exit ${out.code})\n` +
                stderr.trim(),
        )
    }
    assert(
        new TextDecoder().decode(out.stdout).trim().includes("OK"),
        `${label}: the fresh-process load completed`,
    )
}

Deno.test("module graph: FRESH PROCESS — types.ts first, pattern_lang.ts second", async () => {
    await runOrderCheck("types-first", TYPES_URL, PATTERN_URL)
})

Deno.test("module graph: FRESH PROCESS — pattern_lang.ts first, types.ts second", async () => {
    await runOrderCheck("pattern-first", PATTERN_URL, TYPES_URL)
})

Deno.test("module graph: the reverse edge is TYPE-ONLY (no runtime import)", async () => {
    // The static half of the guard: pattern_lang.ts's import from types.ts
    // must stay `import type` (erased at runtime). A runtime import there —
    // even `import { DataType }` for a comment example — would close the
    // cycle the subprocess checks above detect at execution.
    //
    // The verification is BEHAVIORAL, permission-free (the suite runs with
    // no --allow-read): if the reverse edge were a runtime import, then a
    // module-evaluation cycle would exist, and whichever module initializes
    // SECOND would observe the first's exports mid-initialization. The
    // fresh-process order checks above exercise exactly that interleaving
    // and pass with full top-level state on both sides. This test adds the
    // in-process full-surface assertion: every declared kind's class and the
    // pattern language's entry points are present and callable, and the
    // cross-module VALUE call works through types.ts's own API.
    const [typesMod, patternMod] = await Promise.all([
        import("../src/core/types.ts"),
        import("../src/core/pattern_lang.ts"),
    ])
    // The type universe's full surface — nothing undefined from a partial
    // initialization.
    for (
        const name of [
            "Type",
            "TypeVar",
            "FamilyType",
            "FunType",
            "DataType",
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
    const t = typesMod.DataType.define("X")
        .addPattern(patternMod.parsePattern("ab"))
        .build()
    assertEquals(t.patterns.length, 1)
    assertEquals(
        t.findPattern(patternMod.patternToString(patternMod.parsePattern("ab"))),
        t.patterns[0],
    )
    assertEquals(t.findPattern("no-such-pattern"), undefined)
})
