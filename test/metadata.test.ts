/**
 * Inference rule generation tests — verify toInference() produces correct
 * rules from contract metadata.
 */

import { LCTypeCheck } from "../src/index.ts"

import { assertEquals } from "@std/assert"

const expected = [
    ["T-Abs", "lam", [], "result : σ → τ"],
    ["T-App", "app", ["fn : σ → τ  ∧  arg <: σ"], "result : τ"],
    ["T-Cofold", "cofold", [], "result : σ"],
    ["T-Fold", "fold", [], "result : σ (join of handler body types)"],
    ["T-Let", "let_", [], "result : τ"],
    ["T-Obs", "obs", [], "result : Gₖ(T)[α:=T]"],
    ["T-TAbs", "typeAbs", [], "result : ∀α<:σ.τ"],
    ["T-TApp", "typeApp", ["body : ∀α<:σ.τ  ∧  T₂ <: σ"], "result : τ[α:=T₂]"],
    ["T-Unfold", "unfold", [], "result : T"],
    ["T-Var", "varRef", ["x : σ ∈ Γ"], "result : σ"],
    ["T-Variant", "variantCon", [], "result : T"],
] as const

Deno.test("toInference: generated rules match the declared typing rules", () => {
    const actual = new LCTypeCheck().toInference().map((rule) =>
        JSON.stringify({
            name: rule.name,
            production: rule.production,
            premises: rule.premises,
            conclusion: rule.conclusion,
        })
    ).sort()
    const sortedExpected = expected.map(([name, production, premises, conclusion]) =>
        JSON.stringify({ name, production, premises, conclusion })
    ).sort()
    assertEquals(actual, sortedExpected)
})
