/**
 * Generative counterexample search tests — the dynamic dual of the static
 * metatheory verification in `metatheory.test.ts`.
 *
 * Where `checkProgress`/`checkPreservation` reason about the inference-rule
 * *structure* (the `@requires`/`@ensures` metadata), `findCounterexamples`
 * *generates* well-formed terms from the grammar and checks Progress and
 * Preservation dynamically — catching soundness bugs the static analysis
 * misses (e.g., an underspecified `@requires` premise that the static check
 * cannot distinguish from a real grammar bug).
 *
 * Together they give high confidence: static for the rule structure,
 * generative for the grammar behavior.
 *
 * Limitation: the library's `inferValueType` uses duck typing to identify
 * value shapes — it checks for `{param, type, bodySpan, env}` to recognize
 * closures. `SpanClosure` exposes a `type` getter (aliasing `paramType`) so
 * closures are recognized and the dynamic Preservation check is exercised for
 * function-typed terms. `VariantVal` and `SpanCodataVal` are not recognized
 * by `inferValueType` (they lack the closure shape), so Preservation is not
 * dynamically checked for variant/codata values — that coverage is provided
 * by the static `checkPreservation` in `metatheory.test.ts`. The generative
 * search here validates Progress for all generated terms and Preservation
 * for closure-producing terms.
 */

import { type CounterexampleResult, findCounterexamples } from "@lapis-lang/lang-forma"
import { LCEval, LCTypeCheck } from "../src/index.ts"
import { createTestFixtures } from "./fixtures.ts"

import { assert, assertEquals } from "@std/assert"

// ── Helpers ───────────────────────────────────────────────────────────────────

/** Assert that no counterexamples were found, with a detailed failure message. */
function assertNoCounterexamples(result: CounterexampleResult): void {
    if (result.counterexamples.length > 0) {
        const details = result.counterexamples
            .map((ce) => `  ${ce.property}: ${ce.source} — ${ce.explanation}`)
            .join("\n")
        assert(false, `Found counterexamples:\n${details}`)
    }
}

// ── Generation options ────────────────────────────────────────────────────────

/**
 * The LC grammar has many recursive alternatives in `exprProd` (7 branches,
 * 6 of which recurse). The default depth-first strategy gets stuck trying
 * recursive branches first; `branchStrategy: "random"` lets the generator
 * find terminal paths (via `atomProd` → `ident`) within the budget.
 *
 * Two budgets are used:
 * - `fastOpts` — for regular tests that run on every CI build. Lower
 *   depth/backtracks/steps keep worst-case generation time bounded.
 * - `heavyOpts` — for the stress test (gated behind `SLOW_TESTS=1`). Higher
 *   budgets produce deeper terms and more generation attempts.
 */
const fastOpts = {
    maxDepth: 4,
    maxRecursion: 2,
    maxBacktracks: 200,
    maxSteps: 5000,
    branchStrategy: "random" as const,
}

const heavyOpts = {
    maxDepth: 5,
    maxRecursion: 2,
    maxBacktracks: 500,
    maxSteps: 15000,
    branchStrategy: "random" as const,
}

// ── Progress + Preservation ───────────────────────────────────────────────────

Deno.test("counterexamples: Progress + Preservation hold for generated terms (100 runs)", () => {
    const { registry } = createTestFixtures()
    const ev = new LCEval().setRegistry(registry)
    const tc = new LCTypeCheck().setRegistry(registry)

    const result = findCounterexamples(ev, tc, {
        numRuns: 100,
        seed: 0,
        generator: fastOpts,
    })

    // `result.runs` is the requested count, not the number of terms actually
    // generated and checked (many runs may be skipped due to generation
    // failure or ill-typed terms). Asserting it would be tautological.
    assertNoCounterexamples(result)
    assert(result.passed, "Progress should hold for all generated terms")
})

Deno.test("counterexamples: Progress + Preservation hold with different seed (100 runs)", () => {
    const { registry } = createTestFixtures()
    const ev = new LCEval().setRegistry(registry)
    const tc = new LCTypeCheck().setRegistry(registry)

    const result = findCounterexamples(ev, tc, {
        numRuns: 100,
        seed: 42,
        generator: fastOpts,
    })

    assertNoCounterexamples(result)
    assert(result.passed)
})

Deno.test("counterexamples: Progress holds without type checker (eval-only)", () => {
    const { registry } = createTestFixtures()
    const ev = new LCEval().setRegistry(registry)

    // Without a type checker, only Progress is checked (Preservation is skipped).
    const result = findCounterexamples(ev, undefined, {
        numRuns: 100,
        seed: 7,
        generator: fastOpts,
    })

    assertNoCounterexamples(result)
    assert(result.passed)
})

// ── Reproducibility ───────────────────────────────────────────────────────────

Deno.test("counterexamples: same seed produces same result (reproducibility)", () => {
    const { registry } = createTestFixtures()
    const ev = new LCEval().setRegistry(registry)
    const tc = new LCTypeCheck().setRegistry(registry)

    const result1 = findCounterexamples(ev, tc, {
        numRuns: 50,
        seed: 123,
        generator: fastOpts,
    })
    const result2 = findCounterexamples(ev, tc, {
        numRuns: 50,
        seed: 123,
        generator: fastOpts,
    })

    assertEquals(result1.passed, result2.passed)
    assertEquals(result1.counterexamples, result2.counterexamples)
})

// ── Larger search (gated) ─────────────────────────────────────────────────────

// The stress test uses heavier generation budgets and more runs. It is gated
// behind the `SLOW_TESTS` environment variable so it does not slow down regular
// CI builds. Run locally with:
//   SLOW_TESTS=1 deno test --allow-env test/counterexamples.test.ts
const slowTestsEnabled = (() => {
    try {
        return Deno.env.get("SLOW_TESTS") === "1"
    } catch {
        // No env permission — skip the stress test.
        return false
    }
})()

Deno.test({
    name: "counterexamples: Progress + Preservation hold for 500 runs (slow)",
    ignore: !slowTestsEnabled,
}, () => {
    const { registry } = createTestFixtures()
    const ev = new LCEval().setRegistry(registry)
    const tc = new LCTypeCheck().setRegistry(registry)

    const result = findCounterexamples(ev, tc, {
        numRuns: 500,
        seed: 0,
        generator: heavyOpts,
    })

    assertNoCounterexamples(result)
    assert(result.passed)
})
