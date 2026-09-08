/**
 * Inference rule tests — verify the lang-forma first-class rule model
 * (`Grammar.rules` / `collectRules`) collects the declared typing rules
 * from `@requires`/`@ensures` contract metadata.
 */

import { collectRules, formatRule, type FormattedInferenceRule, LCTypeCheck } from "../src/index.ts"

import { assertEquals } from "@std/assert"

const expected = [
    ["T-Abs", ["lam"], [], ["result : σ → τ"]],
    ["T-App", ["app"], ["fn : σ → τ  ∧  arg <: σ"], ["result : τ"]],
    ["T-Cofold", ["cofold"], [], ["result : σ"]],
    ["T-Fold", ["fold"], [], ["result : σ (join of handler body types)"]],
    ["T-Let", ["let_"], [], ["result : τ"]],
    ["T-Obs", ["obs"], [], ["result : Gₖ(T)[α:=T]"]],
    ["T-TAbs", ["typeAbs"], [], ["result : ∀α<:σ.τ"]],
    ["T-TApp", ["typeApp"], ["body : ∀α<:σ.τ  ∧  T₂ <: σ"], ["result : τ[α:=T₂]"]],
    ["T-Unfold", ["unfold"], [], ["result : T"]],
    ["T-Var", ["varRef"], ["x : σ ∈ Γ"], ["result : σ"]],
    ["T-Variant", ["variantCon"], [], ["result : T"]],
] as const

/** Project a FormattedInferenceRule onto the compared shape. */
function shape(rule: FormattedInferenceRule) {
    return {
        name: rule.name,
        methods: rule.methods.map(String),
        premises: rule.premises.map((c) => c.formula),
        conclusion: rule.conclusion.map((c) => c.formula),
        sideConditions: rule.sideConditions.map((c) => c.formula),
        frameConditions: rule.frameConditions.map((c) => c.formula),
    }
}

Deno.test("rules: generated rules match the declared typing rules", () => {
    const actual = LCTypeCheck.rules.map((rule) => JSON.stringify(shape(rule))).sort()
    const sortedExpected = expected.map(([name, methods, premises, conclusion]) =>
        JSON.stringify({
            name,
            methods: [...methods],
            premises: [...premises],
            conclusion: [...conclusion],
            sideConditions: [],
            frameConditions: [],
        })
    ).sort()
    assertEquals(actual, sortedExpected)
})

Deno.test("collectRules: standalone form agrees with Grammar.rules", () => {
    assertEquals(
        collectRules(LCTypeCheck).map((rule) => JSON.stringify(shape(rule))).sort(),
        LCTypeCheck.rules.map((rule) => JSON.stringify(shape(rule))).sort(),
    )
})

Deno.test("formatRule: renders every rule in proof-tree notation", () => {
    for (const rule of LCTypeCheck.rules) {
        const text = formatRule(rule)
        // The rule name labels the bar; the conclusion sits below it.
        assertEquals(text.includes(rule.name), true)
        assertEquals(rule.format(), text) // format() is always attached
    }
})
