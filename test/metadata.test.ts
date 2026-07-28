/**
 * Inference rule generation tests — verify toInference() produces correct
 * rules from contract metadata.
 */

import { LCTypeCheck } from "../src/index.ts"

import { assert, assertEquals } from "@std/assert"

Deno.test("toInference: generates T-Var rule", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    const tVar = rules.find((r) => r.name === "T-Var")
    assert(tVar !== undefined, "T-Var rule should exist")
    assertEquals(tVar.production, "varRef")
    assert(tVar.premises.includes("x : σ ∈ Γ"))
    assertEquals(tVar.conclusion, "result : σ")
})

Deno.test("toInference: generates T-Abs rule", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    const tAbs = rules.find((r) => r.name === "T-Abs")
    assert(tAbs !== undefined, "T-Abs rule should exist")
    assertEquals(tAbs.production, "lam")
    assertEquals(tAbs.conclusion, "result : σ → τ")
})

Deno.test("toInference: generates T-App rule", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    const tApp = rules.find((r) => r.name === "T-App")
    assert(tApp !== undefined, "T-App rule should exist")
    assertEquals(tApp.production, "app")
    assert(tApp.premises.includes("fn : σ → τ  ∧  arg <: σ"))
    assertEquals(tApp.conclusion, "result : τ")
})

Deno.test("toInference: generates T-Let rule", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    const tLet = rules.find((r) => r.name === "T-Let")
    assert(tLet !== undefined, "T-Let rule should exist")
    assertEquals(tLet.production, "let_")
    assertEquals(tLet.conclusion, "result : τ")
})

Deno.test("toInference: generates T-Variant rule", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    const tVariant = rules.find((r) => r.name === "T-Variant")
    assert(tVariant !== undefined, "T-Variant rule should exist")
    assertEquals(tVariant.production, "variantCon")
    assertEquals(tVariant.conclusion, "result : T")
})

Deno.test("toInference: generates T-Obs rule", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    const tObs = rules.find((r) => r.name === "T-Obs")
    assert(tObs !== undefined, "T-Obs rule should exist")
    assertEquals(tObs.production, "obs")
    assertEquals(tObs.conclusion, "result : Gₖ(T)[α:=T]")
})

Deno.test("toInference: generates T-Fold rule", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    const tFold = rules.find((r) => r.name === "T-Fold")
    assert(tFold !== undefined, "T-Fold rule should exist")
    assertEquals(tFold.production, "fold")
    assertEquals(tFold.conclusion, "result : σ (join of handler body types)")
})

Deno.test("toInference: generates T-Unfold rule", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    const tUnfold = rules.find((r) => r.name === "T-Unfold")
    assert(tUnfold !== undefined, "T-Unfold rule should exist")
    assertEquals(tUnfold.production, "unfold")
    assertEquals(tUnfold.conclusion, "result : T")
})

Deno.test("toInference: all rules have non-empty conclusions", () => {
    const tc = new LCTypeCheck()
    const rules = tc.toInference()
    assert(rules.length >= 8, "should have at least 8 rules")
    for (const rule of rules) {
        assert(rule.conclusion !== "", `rule ${rule.name} should have a conclusion`)
        assert(rule.production !== "", `rule ${rule.name} should have a production`)
    }
})
