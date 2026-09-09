/**
 * Inference rule tests — verify the lang-forma first-class rule model
 * (`Grammar.rules` / `collectRules`) collects the declared typing and
 * evaluation rules from `@requires`/`@ensures` contract metadata.
 */

import {
    collectRules,
    formatRule,
    type FormattedInferenceRule,
    LCEval,
    LCTypeCheck,
} from "../src/index.ts"

import { assertEquals } from "@std/assert"

const expectedTyping = [
    ["T-Abs", ["lam"], [], ["result : σ → τ"]],
    ["T-App", ["app"], ["fn : σ → τ  ∧  arg <: σ"], ["result : τ"]],
    ["T-Cofold", ["cofold"], [], ["result : σ"]],
    ["T-Fold", ["fold"], [], ["result : σ (join of handler body types)"]],
    ["T-Let", ["let_"], ["def : σ  ∧  σ <: τ"], ["result : τ'"]],
    ["T-Obs", ["obs"], [], ["result : Gₖ(T)[α:=T]"]],
    ["T-TAbs", ["typeAbs"], [], ["result : ∀α<:σ.τ"]],
    ["T-TApp", ["typeApp"], ["body : ∀α<:σ.τ  ∧  T₂ <: σ"], ["result : τ[α:=T₂]"]],
    ["T-Unfold", ["unfold"], [], ["result : T"]],
    ["T-Var", ["varRef"], ["x : σ ∈ Γ"], ["result : σ"]],
    ["T-Variant", ["variantCon"], [], ["result : T"]],
] as const

const expectedEval = [
    ["E-App", ["app"], ["fn : ⟨x, σ, span, ρ⟩"], ["result : w"]],
    ["E-Cofold", ["cofold"], ["scrutinee : codataVal"], ["result : w"]],
    ["E-Fold", ["fold"], ["scrutinee : Cₖ(vⱼ)"], ["result : w"]],
    ["E-Lam", ["lam"], [], ["result : ⟨x, σ, span, ρ⟩"]],
    ["E-Let", ["let_"], ["def : v"], ["result : w"]],
    ["E-Obs", ["obs"], ["scrutinee : codataVal"], ["result : w"]],
    ["E-TAbs", ["typeAbs"], [], ["result : Λα<:σ. t"]],
    ["E-TApp", ["typeApp"], ["body : Λα<:σ. t"], ["result : t[α:=τ]"]],
    ["E-Unfold", ["unfold"], [], ["result : codataVal"]],
] as const

/**
 * Project a FormattedInferenceRule onto the compared shape.
 *
 * `production` is omitted from the shape: `LCTypeCheck` contracts don't carry
 * a `production` key, so it is `undefined` for all typing rules. `LCEval`
 * contracts do carry `production` (via `@rule({ rule, production })` on
 * overridden productions or `production` in `@ensures` metadata), but it is
 * verified separately in `metatheory.test.ts`. The method linkage is
 * asserted via `methods` instead.
 */
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

function expectedShape(
    name: string,
    methods: readonly string[],
    premises: readonly string[],
    conclusion: readonly string[],
) {
    return JSON.stringify({
        name,
        methods: [...methods],
        premises: [...premises],
        conclusion: [...conclusion],
        sideConditions: [],
        frameConditions: [],
    })
}

Deno.test("rules: generated typing rules match the declared typing rules", () => {
    const actual = LCTypeCheck.rules.map((rule) => JSON.stringify(shape(rule))).sort()
    const sortedExpected = expectedTyping.map(([name, methods, premises, conclusion]) =>
        expectedShape(name, methods, premises, conclusion)
    ).sort()
    assertEquals(actual, sortedExpected)
})

Deno.test("rules: generated eval rules match the declared eval rules", () => {
    const actual = LCEval.rules.map((rule) => JSON.stringify(shape(rule))).sort()
    const sortedExpected = expectedEval.map(([name, methods, premises, conclusion]) =>
        expectedShape(name, methods, premises, conclusion)
    ).sort()
    assertEquals(actual, sortedExpected)
})

Deno.test("collectRules: standalone form agrees with Grammar.rules", () => {
    assertEquals(
        collectRules(LCTypeCheck).map((rule) => JSON.stringify(shape(rule))).sort(),
        LCTypeCheck.rules.map((rule) => JSON.stringify(shape(rule))).sort(),
    )
    assertEquals(
        collectRules(LCEval).map((rule) => JSON.stringify(shape(rule))).sort(),
        LCEval.rules.map((rule) => JSON.stringify(shape(rule))).sort(),
    )
})

Deno.test("formatRule: renders every rule in proof-tree notation", () => {
    for (const rule of [...LCTypeCheck.rules, ...LCEval.rules]) {
        const text = formatRule(rule)
        assertEquals(rule.format(), text) // format() is always attached

        // Structure: [premises, bar, conclusion] — or [bar, conclusion]
        // for axioms (no premises; the empty premises line is omitted).
        const lines = text.split("\n")
        assertEquals(lines.length, rule.premises.length > 0 ? 3 : 2)

        // The bar labels the rule name; the conclusion sits below it.
        const bar = lines[lines.length - 2]!
        const conclusion = lines[lines.length - 1]!
        assertEquals(bar.includes(rule.name), true)
        const conclusionFormula = rule.conclusion[0]?.formula
        assertEquals(
            conclusionFormula !== undefined && conclusion.includes(conclusionFormula),
            true,
        )

        // Premises sit above the bar, split on ∧ and spaced across the line.
        if (rule.premises.length > 0) {
            const premises = lines[0]!
            for (const p of rule.premises) {
                for (const part of p.formula?.split(/\s*∧\s*/) ?? []) {
                    assertEquals(premises.includes(part), true)
                }
            }
        }
    }
})
