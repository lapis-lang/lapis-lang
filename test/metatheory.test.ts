/**
 * Metatheory verification tests — verify Progress and Preservation hold
 * for the LC core calculus via lang-forma's metatheory engine.
 *
 * This is the mechanized counterpart to the hand-argued soundness proofs:
 *   - Progress: every well-typed term is either a value or can take a step.
 *   - Preservation: if a well-typed term steps, the result is well-typed
 *     at the same type.
 *
 * The engine works on the first-class InferenceRule model collected from
 * @requires/@ensures contract metadata on LCEval (dynamic-semantics rules)
 * and LCTypeCheck (static-semantics rules).
 */

import {
    checkPreservation,
    checkProgress,
    classifyRules,
    collectRules,
    LCEval,
    LCTypeCheck,
    verifyMetatheory,
} from "../src/index.ts"

import { assertEquals, assertNotEquals } from "@std/assert"

// ── Rule collection ───────────────────────────────────────────────────────────

Deno.test("metatheory: LCEval produces evaluation rules from contract metadata", () => {
    const rules = collectRules(LCEval)
    const names = rules.map((r) => r.name).sort()
    assertEquals(names, [
        "E-App",
        "E-Cofold",
        "E-Fold",
        "E-Lam",
        "E-Let",
        "E-Obs",
        "E-TAbs",
        "E-TApp",
        "E-Unfold",
    ])
})

Deno.test("metatheory: every LCEval rule has a production linkage", () => {
    const rules = collectRules(LCEval)
    for (const rule of rules) {
        assertNotEquals(
            rule.production,
            undefined,
            `rule ${rule.name} has no production linkage`,
        )
    }
})

Deno.test("metatheory: collectRules standalone agrees with Grammar.rules", () => {
    assertEquals(
        collectRules(LCEval).map((r) => r.name).sort(),
        LCEval.rules.map((r) => r.name).sort(),
    )
})

// ── Rule classification ───────────────────────────────────────────────────────

Deno.test("metatheory: rules are classified as value-rules or step-rules", () => {
    const rules = collectRules(LCEval)
    const classified = classifyRules(rules)

    const valueRules = classified
        .filter((c) => c.kind === "value")
        .map((c) => c.rule.name)
        .sort()
    const stepRules = classified
        .filter((c) => c.kind === "step")
        .map((c) => c.rule.name)
        .sort()

    // Value-rules (no premises): lambda, unfold, type abstraction
    assertEquals(valueRules, ["E-Lam", "E-TAbs", "E-Unfold"])

    // Step-rules (with premises): application, let, fold, obs, cofold, typeApp
    assertEquals(stepRules, ["E-App", "E-Cofold", "E-Fold", "E-Let", "E-Obs", "E-TApp"])
})

// ── Progress ──────────────────────────────────────────────────────────────────

Deno.test("metatheory: Progress holds — no gaps in step-rule coverage", () => {
    const rules = collectRules(LCEval)
    const result = checkProgress(rules, LCEval)

    assertEquals(result.holds, true)
    assertEquals(result.gaps.length, 0)
})

Deno.test("metatheory: Progress constructor coverage — every semantic production is value or step", () => {
    const rules = collectRules(LCEval)
    const result = checkProgress(rules, LCEval)

    // Every production linked to a dynamic-semantics rule must be either
    // a value-rule or covered by a step-rule. If holds is true, there are
    // no stuck productions.
    assertEquals(result.holds, true)
})

// ── Preservation ──────────────────────────────────────────────────────────────

Deno.test("metatheory: Preservation holds — step-rules preserve types (static)", () => {
    const rules = collectRules(LCEval)
    const staticRules = collectRules(LCTypeCheck)
    const result = checkPreservation(rules, staticRules)

    assertEquals(result.holds, true)
    // Every step-rule should preserve types.
    for (const check of result.checks) {
        assertEquals(
            check.preserves,
            true,
            `${check.rule}: ${check.explanation}`,
        )
    }
})

Deno.test("metatheory: Preservation — all 6 step-rules checked", () => {
    const rules = collectRules(LCEval)
    const staticRules = collectRules(LCTypeCheck)
    const result = checkPreservation(rules, staticRules)

    const checkedRules = result.checks.map((c) => c.rule).sort()
    assertEquals(checkedRules, ["E-App", "E-Cofold", "E-Fold", "E-Let", "E-Obs", "E-TApp"])
})

// ── Combined verification ─────────────────────────────────────────────────────

Deno.test("metatheory: verifyMetatheory — Progress + Preservation both hold", () => {
    const report = verifyMetatheory(LCEval, LCTypeCheck)

    assertEquals(report.holds, true)
    assertEquals(report.progress.holds, true)
    assertEquals(report.preservation.holds, true)
})

Deno.test("metatheory: verifyMetatheory — unification strengthening also holds", () => {
    const report = verifyMetatheory(LCEval, LCTypeCheck)

    // The unification layer strengthens the static Preservation check.
    // It is optional — if present, each check should pass (conclusion type τ
    // unifies with premise type τ). If absent, the static check is sufficient.
    const unification = report.preservation.unification
    if (unification) {
        for (const check of unification) {
            assertEquals(
                check.preserves,
                true,
                `unification ${check.rule}: ${check.explanation}`,
            )
        }
    }
})

// ── Rule formatting ───────────────────────────────────────────────────────────

Deno.test("metatheory: every LCEval rule formats as proof-tree notation", () => {
    const rules = collectRules(LCEval)
    for (const rule of rules) {
        const text = rule.format()
        const text2 = rule.format()
        assertEquals(text2, text) // format() is deterministic

        const lines = text.split("\n")
        // Value-rules (no premises): [bar, conclusion] — 2 lines
        // Step-rules (with premises): [premises, bar, conclusion] — 3 lines
        const expectedLines = rule.premises.length > 0 ? 3 : 2
        assertEquals(lines.length, expectedLines)

        // The bar labels the rule name.
        const bar = lines[lines.length - 2]!
        assertEquals(bar.includes(rule.name), true)

        // The conclusion sits below the bar.
        const conclusion = lines[lines.length - 1]!
        const conclusionFormula = rule.conclusion[0]?.formula
        assertEquals(
            conclusionFormula !== undefined && conclusion.includes(conclusionFormula),
            true,
        )
    }
})

// ── Typing rules are unaffected ───────────────────────────────────────────────

Deno.test("metatheory: LCTypeCheck rules are still collected correctly", () => {
    const rules = collectRules(LCTypeCheck)
    const names = rules.map((r) => r.name).sort()
    assertEquals(names, [
        "T-Abs",
        "T-App",
        "T-Cofold",
        "T-Fold",
        "T-Let",
        "T-Obs",
        "T-TAbs",
        "T-TApp",
        "T-Unfold",
        "T-Var",
        "T-Variant",
    ])
})
