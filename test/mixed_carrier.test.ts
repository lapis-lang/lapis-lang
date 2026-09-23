/**
 * Mixed-carrier tests — a `DataType` declaring BOTH named variants and
 * pattern members (the Stage-1 additive form). The member gates widened
 * additively: a mixed carrier's pattern member's bare atom reads as its
 * token (the same reading `PatternDataType`'s atoms took), its `match("…")`
 * form introduces through the pattern route, and `fold [T] …` over it routes
 * to the pattern fold (the pattern branch is ordered first). The variant
 * routes keep working on the same carrier — both member kinds are reachable
 * from one declaration.
 */

import { assert, assertEquals } from "@std/assert"

import {
    EvalErrorValue,
    LCEval,
    LCTypeCheck,
    OpRegistry,
    TokenVal,
    TypeRegistry,
    ValueEnv,
    VariantVal,
} from "../src/index.ts"

import { DataType, FunType, TokenType, TypeEnv, Variant } from "../src/core/types.ts"

import { parsePattern } from "../src/core/pattern_lang.ts"

import { createMixedType, createPatternType } from "./fixtures.ts"

// ── Fixtures ────────────────────────────────────────────────────────────────

/**
 * The hex-color pattern: `#` + six hex digits. The counted-repetition
 * spelling (`#[A-F0-9]{6}`) is NOT in the supported fragment (Stage-4
 * scope); the same LANGUAGE spells as an explicit six-fold class concat,
 * so the motivating declaration is exercisable today.
 */
const HEX6 = "#[A-F0-9][A-F0-9][A-F0-9][A-F0-9][A-F0-9][A-F0-9]"

/** The short two-digit form — a distinct pattern for exhaustiveness tests. */
const HEX2 = "#[0-9][0-9]"

/**
 * A mixed harness: the carrier is a `DataType` with variants AND patterns —
 * `data Color { Red, Green, Hex }` with a hex-color pattern is the
 * motivating mixed declaration.
 */
function mixedHarness(
    patterns: readonly string[] = [HEX6],
) {
    const registry = new TypeRegistry()
    const color = createMixedType(
        "Color",
        [
            new Variant("Red", []),
            new Variant("Green", []),
            new Variant("Hex", []),
        ],
        patterns,
    )
    registry.register(color)
    const opRegistry = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ev = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
    return { registry, opRegistry, tc, ev, color }
}

/** Type-check a source string; the single type or `undefined` (empty forest). */
function typeOfOne(
    h: ReturnType<typeof mixedHarness>,
    source: string,
    gamma: TypeEnv = new TypeEnv(),
) {
    const results = [...h.tc.parseWith(source, gamma)]
    return results.length === 1 ? results[0] : undefined
}

/** Evaluate a source string; the single value or `undefined` (empty forest). */
function evalOne(
    h: ReturnType<typeof mixedHarness>,
    source: string,
    rho: ValueEnv = new ValueEnv(),
) {
    const results = [...h.ev.parseWith(source, rho)]
    return results.length === 1 ? results[0] : undefined
}

// ── Registry: the mixed carrier's patterns are indexed ───────────────────────

Deno.test("mixed carrier: the registry indexes a DataType's patterns (reverse lookup)", () => {
    const h = mixedHarness()
    // The declared pattern resolves through the reverse index to the
    // mixed carrier — the same index `PatternDataType` registration filled.
    assertEquals(h.registry.lookupPatternSource(HEX6), h.color)
})

Deno.test("mixed carrier: a parent-declared pattern indexes on the child (comb inheritance)", () => {
    // The pattern walk mirrors the variant walk's parent-chain read: a comb
    // child whose PARENT declared the pattern is equally a declaring carrier,
    // so registering only the child leaves the parent-declared pattern
    // constructible through the child (the same semantics the variant index
    // applies to inherited variants — `lookupVariant` resolves the child for
    // a parent-declared variant name).
    const parent = DataType.define("BaseColor")
        .addPattern(parsePattern(HEX6))
        .build()
    const child = DataType.define("ChildColor", parent)
        .addVariant(new Variant("Red", []))
        .build()
    const registry = new TypeRegistry()
    const opRegistry = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ev = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
    registry.register(child)
    // The parent-declared pattern indexes under the CHILD (its registrar).
    assertEquals(registry.lookupPatternSource(HEX6), child)
    // And both introduction routes reach it end-to-end.
    assertEquals(
        [...tc.parseWith(`match("${HEX6}")`, new TypeEnv())].length,
        1,
        "the match form resolves the parent-declared pattern",
    )
    assert(
        [...ev.parseWith(`match("${HEX6}")`, new ValueEnv())][0] instanceof
            TokenVal,
        "the match form evaluates",
    )
})

Deno.test("mixed carrier: a variant-only carrier's name is not a pattern language", () => {
    // A `DataType` with NO pattern members must NOT gate the pattern routes:
    // its name is an ordinary variant carrier. The anchoring walk's typeref
    // arm (`isResolvableAndAnchored`) rejects a `<NatM>` reference naming a
    // variant-only carrier — the language is unknowable (the constructor
    // would be accepted with a language the registry cannot enumerate).
    const registry = new TypeRegistry()
    registry.register(createMixedType("NatM", [], []))
    const opRegistry = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    // A pattern referencing the variant-only carrier is unresolvable.
    const results = [...tc.parseWith('match("<NatM>[0-9]")', new TypeEnv())]
    assertEquals(results.length, 0)
})

// ── Token route: the bare atom reads as the carrier's token ─────────────────

Deno.test("mixed carrier: the bare carrier name introduces a token (T-Token over a DataType)", () => {
    const h = mixedHarness()
    // The bare atom's shape: the CARRIER name (the same reading a
    // PatternDataType's bare atom took — the token's text is the name). The
    // variant names (`Red`, `Green`, `Hex`) are constructor calls, not
    // tokens.
    const t = typeOfOne(h, "Color")
    assertEquals(t, h.color, "the bare carrier atom types as the carrier")
    const v = evalOne(h, "Color")
    assert(v instanceof TokenVal, "the bare atom evaluates to a TokenVal")
    if (v instanceof TokenVal) {
        assertEquals(v.dataTypeName, "Color")
        assertEquals(v.text, "Color")
    }
})

Deno.test("mixed carrier: a variant name constructs the variant (branch order)", () => {
    // Branch order: `variantProd` (Ident(args)) runs before
    // `patternTokenProd`, so a mixed carrier's variant construction keeps the
    // variant route even though the carrier also gates the token branch.
    const h = mixedHarness()
    const v = evalOne(h, "Red()")
    assert(v instanceof VariantVal, "the variant constructs")
    if (v instanceof VariantVal) {
        assertEquals(v.dataType.name, "Color")
    }
    // And the CARRIER name takes the token route.
    const tok = evalOne(h, "Color")
    assert(tok instanceof TokenVal, "the carrier's bare name is the token")
})

// ── match("…") route: the explicit introduction over a mixed carrier ────────

Deno.test('mixed carrier: match("…") introduces through the pattern route (T-Pattern)', () => {
    const h = mixedHarness()
    const t = typeOfOne(h, `match("${HEX6}")`)
    assertEquals(t, h.color, "the match form types as the declaring carrier")
    const v = evalOne(h, `match("${HEX6}")`)
    assert(v instanceof TokenVal, "the match form evaluates to a TokenVal")
    if (v instanceof TokenVal) {
        assertEquals(v.dataTypeName, "Color")
        // The token's text is the CANONICAL source (the gate's resolution).
        assertEquals(v.text, HEX6)
    }
})

Deno.test("mixed carrier: an undeclared pattern rejects the match route", () => {
    const h = mixedHarness()
    // A five-digit hex concat is a DIFFERENT AST (and canonical source) from
    // the declared six-fold concat — no type declares it.
    const undeclared = "#[A-F0-9][A-F0-9][A-F0-9][A-F0-9][A-F0-9]"
    assertEquals(
        typeOfOne(h, `match("${undeclared}")`),
        undefined,
        "a distinct pattern is not the carrier's declaration",
    )
})

// ── The mixed fold: pattern arms route to the pattern fold ──────────────────

Deno.test("mixed carrier: fold over the pattern arm routes to the pattern fold", () => {
    const h = mixedHarness()
    // The annotation carries patterns — the ordered-first pattern branch owns
    // the source; the single handler returns its token, so σ = Token.
    const t = typeOfOne(
        h,
        `fold [Color] match("${HEX6}") { match("${HEX6}") → match }`,
    )
    assert(t instanceof TokenType, "the fold's result is the handler body's type")
})

Deno.test("mixed carrier: fold dispatches the token to its handler", () => {
    const h = mixedHarness()
    const v = evalOne(
        h,
        `fold [Color] match("${HEX6}") { match("${HEX6}") → match }`,
    )
    assert(v instanceof TokenVal, "the fired body returned the bound token")
})

Deno.test("mixed carrier: exhaustiveness covers the pattern members", () => {
    const h = mixedHarness([HEX6, HEX2])
    // One handler for a two-pattern carrier: exhaustiveness fails.
    assertEquals(
        typeOfOne(
            h,
            `fold [Color] match("${HEX6}") { match("${HEX6}") → match }`,
        ),
        undefined,
        "the second declared pattern has no handler",
    )
    // Both handlers: the fold accepts and types as the common σ.
    const t = typeOfOne(
        h,
        `fold [Color] match("${HEX6}") { match("${HEX6}") → match, match("${HEX2}") → match }`,
    )
    assert(t instanceof TokenType, "complete handlers type the fold")
})

// ── Variant routes keep working on the same carrier ─────────────────────────

Deno.test("mixed carrier: variant fold still parses (the same carrier, variant route)", () => {
    const h = mixedHarness()
    const src = "\\c:Color. fold [Color] c { Red() → c, Green() → c, Hex() → c }"
    const t = [...h.tc.parseWith(src, new TypeEnv())]
    assertEquals(t.length, 1, "the variant fold over the mixed carrier parses")
    assert(t[0] instanceof FunType)
})

Deno.test("mixed carrier: a variant scrutinee takes no pattern handler", () => {
    const h = mixedHarness()
    // A variant scrutinee is NOT a token: the pattern fold declines it (the
    // two routes never mix within one step) — the evaluator reports the
    // failure as an `EvalErrorValue` sentinel, never a crash and never a
    // successful handler dispatch.
    //
    // PINNED STAGE-1 BOUNDARY: the checker cannot per-arm-enforce the token
    // shape — premise 1 (`isSubtype(scrutineeType, T)`) passes because
    // `Red() : Color` on a mixed carrier, and only the evaluator's dispatch
    // catches the shape mismatch. On a pure PatternDataType the tension cannot
    // arise (no variants exist), so this is a surface the mixed form opens;
    // the merged fold's per-arm premises close it. Until then, this sentinel
    // (not a parse rejection) IS the pinned contract — do not mistake it for
    // a final typing rule.
    const folded = evalOne(
        h,
        `fold [Color] Red() { match("${HEX6}") → match }`,
    )
    assert(
        folded instanceof EvalErrorValue,
        "a variant scrutinee takes no pattern handler (the error sentinel)",
    )
})

// ── Cross-carrier isolation ─────────────────────────────────────────────────

Deno.test("mixed carrier: a foreign pattern head rejects the handler", () => {
    // A mixed carrier's handler for a pattern declared on a DIFFERENT type
    // rejects (the handler gate's `resolved.typeName !== dataType.name`) —
    // a pattern owned by another registered type would be unmatchable and
    // would corrupt the exhaustiveness accounting.
    const h = mixedHarness()
    const pat = createPatternType("Pat", ["[0-9]+"])
    h.registry.register(pat)
    assertEquals(
        typeOfOne(
            h,
            `fold [Color] match("${HEX6}") { match("[0-9]+") → match }`,
        ),
        undefined,
        "a foreign pattern head rejects the handler",
    )
})
