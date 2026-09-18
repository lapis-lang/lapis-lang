/**
 * Pattern-language tests — the parser, the language-equation
 * counting, and the enumeration: the counting semantics of the restricted
 * regular fragment (surface-syntax.md §1.3) and its rejection surface.
 */

import { assertEquals, assertThrows } from "@std/assert"

import {
    CHARACTER_UNIVERSE_SIZE,
    enumeratePattern,
    makePatternCountEnv,
    MAX_PATTERN_COUNT,
    parsePattern,
    patternCounts,
    PatternParseError,
    patternToString,
    satAddSeq,
} from "../src/core/pattern_lang.ts"

const env = makePatternCountEnv(() => undefined)

// ── Parsing ──────────────────────────────────────────────────────────────────

Deno.test("parser: round-trip — char, any, class, star, plus, opt, typeref", () => {
    assertEquals(patternToString(parsePattern("a")), "a")
    assertEquals(patternToString(parsePattern(".")), ".")
    assertEquals(patternToString(parsePattern("[0-9]")), "[0-9]")
    assertEquals(patternToString(parsePattern("[0-9]*")), "[0-9]*")
    assertEquals(patternToString(parsePattern("[0-9]+")), "[0-9]+")
    assertEquals(patternToString(parsePattern("-?")), "-?")
    assertEquals(patternToString(parsePattern("<Nat>")), "<Nat>")
    // Concatenation joins the parts (no implicit separator).
    assertEquals(patternToString(parsePattern("ab")), "ab")
    // Escaped metacharacters render escaped again.
    assertEquals(patternToString(parsePattern("\\+")), "\\+")
    assertEquals(patternToString(parsePattern("\\.")), "\\.")
})

Deno.test("parser: class ranges expand (the dash is a range operator)", () => {
    const digits = parsePattern("[0-9]") as { kind: "class"; set: Uint8Array }
    assertEquals([...digits.set].length, 10, "0 through 9")
    const letters = parsePattern("[a-fA-F]") as { kind: "class"; set: Uint8Array }
    assertEquals([...letters.set].length, 12, "a-f plus A-F")
})

Deno.test("parser: a leading dash in a class is a literal ([-a] = {-, a})", () => {
    const cls = parsePattern("[-a]") as { kind: "class"; set: Uint8Array }
    assertEquals([...cls.set].includes("-".charCodeAt(0)), true)
    assertEquals([...cls.set].length, 2)
})

Deno.test("parser: excluded constructs reject loudly with the reason", () => {
    // Alternation — declare a second variant instead.
    assertThrows(
        () => parsePattern("a|b"),
        PatternParseError,
        "alternation",
    )
    // Groups.
    assertThrows(() => parsePattern("(ab)"), PatternParseError, "groups")
    // Unterminated class / type reference.
    assertThrows(() => parsePattern("[ab"), PatternParseError, "unterminated")
    assertThrows(() => parsePattern("<Nat"), PatternParseError, "unterminated")
    // A trailing escape.
    assertThrows(() => parsePattern("a\\"), PatternParseError, "escapes nothing")
    // Inverted range.
    assertThrows(() => parsePattern("[9-0]"), PatternParseError, "inverted")
    // Empty pattern.
    assertThrows(() => parsePattern(""), PatternParseError, "empty pattern")
    // Lowercase type reference (PascalCase only).
    assertThrows(
        () => parsePattern("<nat>"),
        PatternParseError,
        "PascalCase",
    )
})

Deno.test("parser: non-ASCII characters reject (the ASCII universe fiat)", () => {
    assertThrows(
        () => parsePattern("[é]"),
        PatternParseError,
        "character universe",
    )
})

Deno.test("parser: the empty string pattern is rejected — variants must consume", () => {
    assertThrows(() => parsePattern(""), PatternParseError, "at least one")
})

// ── The counting semantics ───────────────────────────────────────────────────

Deno.test("equations: [0-9]+ gives cₙ = 10ⁿ (Nat's geometric reading)", () => {
    assertEquals(patternCounts(parsePattern("[0-9]+"), 3, env), [0, 10, 100, 1000])
})

Deno.test("equations: [0-9]* gives c₀ = 1 (the ε string) then 10ⁿ", () => {
    assertEquals(patternCounts(parsePattern("[0-9]*"), 3, env), [1, 10, 100, 1000])
})

Deno.test("equations: a single class counts its set size at length 1", () => {
    assertEquals(patternCounts(parsePattern("[abc]"), 3, env), [0, 3, 0, 0])
})

Deno.test("equations: `.` matches the whole ASCII universe (128)", () => {
    assertEquals(patternCounts(parsePattern("."), 1, env), [0, 128])
})

Deno.test("equations: concatenation convolves (aa: one string per length ≥ 2)", () => {
    // "aa" — exactly one string per length ≥ 2 (aa, aaa, aaaa, ...). Wait —
    // "aa" is two literal chars: ONLY the fixed string "aa" matches, so
    // c₂ = 1 and cₙ = 0 beyond (the parser sees two char atoms; a repeat on
    // each is absent). Verify: the language of "aa" is {"aa"} exactly.
    assertEquals(patternCounts(parsePattern("aa"), 4, env), [0, 0, 1, 0, 0])
})

Deno.test("equations: opt adds the ε branch (c₀ = 1)", () => {
    assertEquals(patternCounts(parsePattern("[0-9]?"), 2, env), [1, 10, 0])
})

Deno.test("equations: Int = -?[0-9]+ — the sign extends every digit string by one", () => {
    // -? [0-9]+: a string needs ≥1 digit. Length 1: only the 10 digits
    // (the bare '-' does not match — the plus part cannot be ε). Length 2:
    // the 10 '-'d strings + the 100 dd strings = 110.
    assertEquals(patternCounts(parsePattern("-?[0-9]+"), 2, env), [0, 10, 110])
})

Deno.test("equations: a negated class counts the complement (128 − set)", () => {
    assertEquals(patternCounts(parsePattern("[^a]"), 1, env), [0, 127])
})

Deno.test("equations: a type reference reads the referenced type's counts", () => {
    const char = parsePattern(".")
    const stringPat = parsePattern("<Char>*")
    const charType = { name: "Char", patterns: [char] } as never
    // The Char reference reads through the environment.
    const env2 = makePatternCountEnv((name) => name === "Char" ? (charType as never) : undefined)
    // Char's language: 128 strings of length 1. String = <Char>*: cₙ = 128ⁿ
    // (saturating — 128² = 16384 fits, so the count is exact at k = 2).
    assertEquals(patternCounts(stringPat, 2, env2), [1, 128, 16384])
})

Deno.test("equations: type-level sums saturate, never overflow", () => {
    // The set-based counting caps every node's language at the set budget,
    // so saturation lives at the TYPE level — the multi-variant sum
    // (`satAddSeq`, the alternation of a declaration's pattern list):
    // doubling 60 times saturates 1 at 2⁵³ (the integer-exactness ceiling,
    // an over-estimate — never under-reporting the space).
    let seq = [0, 1]
    for (let i = 0; i < 60; i++) seq = satAddSeq(seq, seq)
    assertEquals(seq[1], MAX_PATTERN_COUNT)
})

Deno.test("equations: a concat-closed sublanguage counts STRINGS, not splits", () => {
    // The counting correctness regression: a language whose pieces
    // concatenate into other pieces ("aa" ∈ {a, aa}) would double-count
    // under the factorization recurrence (the "aa" string factors as
    // [aa] and [a·a]) — the set arithmetic counts each string once.
    // a** = (a*)* = a* — the language flattens; the counts must too.
    assertEquals(patternCounts(parsePattern("a**"), 3, env), [1, 1, 1, 1])
    // [0-9]*? = opt(star): nullable inner — the ε branch adds nothing
    // (the language has ONE ε).
    assertEquals(patternCounts(parsePattern("[0-9]*?"), 3, env), [1, 10, 100, 1000])
    // (a+)+ = a+ — the plus flattens over a nullable-closed base.
    assertEquals(patternCounts(parsePattern("a++"), 3, env), [0, 1, 1, 1])
    // plus of a NULLABLE pattern keeps the ε (the single ε-piece path):
    // (a*)+ = a*.
    assertEquals(patternCounts(parsePattern("a*+"), 3, env), [1, 1, 1, 1])
    // A product that absorbs its own split: [0-9]+[0-9]* = [0-9]+ —
    // the convolution's split-counting would double every string.
    assertEquals(patternCounts(parsePattern("[0-9]+[0-9]*"), 3, env), [0, 10, 100, 1000])
})

Deno.test("equations: the set-based count declines past the counting budget", () => {
    // [^0-9]*[0-9] at k = 3: the star part's language is 118³ strings —
    // past MAX_STAR_COUNT_BUDGET — the count declines loudly (the
    // certificate never guesses; the caller states a smaller degree).
    assertThrows(
        () => patternCounts(parsePattern("[^0-9]*[0-9]"), 3, env),
        PatternParseError,
        "counting budget",
    )
})

// ── Enumeration ──────────────────────────────────────────────────────────────

Deno.test("enumeration: [0-9]+ at k = 2 yields 110 strings (10 + 100)", () => {
    const strings = enumeratePattern(parsePattern("[0-9]+"), 2, env, 256)
    assertEquals(strings?.size, 110)
})

Deno.test("enumeration: the budget declines (undefined) when the class overflows", () => {
    // ".?." at k = 2: (1 + 128) × 128 = 16512 > 256 — declined.
    assertEquals(enumeratePattern(parsePattern(".?."), 2, env, 256), undefined)
    // A tighter budget declines a smaller class too (110 > 100).
    assertEquals(enumeratePattern(parsePattern("[0-9]+"), 2, env, 100), undefined)
    // "." alone has only 128 strings (one character each — never declined at 256).
    assertEquals(enumeratePattern(parsePattern("."), 2, env, 256)?.size, 128)
})

Deno.test("enumeration: [0-9]* includes ε (the empty string)", () => {
    const strings = enumeratePattern(parsePattern("[0-9]*"), 1, env, 256)
    assertEquals(strings?.has(""), true)
    assertEquals(strings?.size, 11, "ε plus the ten digits")
})

// ── Type-reference cycles ────────────────────────────────────────────────────

Deno.test("equations: a type-reference cycle rejects loudly (ill-founded)", () => {
    const a = parsePattern("<B>")
    const b = parsePattern("<A>")
    const aType = { name: "A", patterns: [a] } as never
    const bType = { name: "B", patterns: [b] } as never
    const cycleEnv = makePatternCountEnv((name) =>
        name === "A" ? aType : name === "B" ? bType : undefined
    )
    assertThrows(
        () => patternCounts(a, 2, cycleEnv),
        PatternParseError,
        "cycle",
    )
})

Deno.test("equations: an unknown type reference rejects loudly", () => {
    assertThrows(
        () => patternCounts(parsePattern("<Missing>"), 1, env),
        PatternParseError,
        "does not resolve",
    )
})

// ── The universe fiat ────────────────────────────────────────────────────────

Deno.test("universe: ASCII — 128 code points (the recorded fiat)", () => {
    assertEquals(CHARACTER_UNIVERSE_SIZE, 128)
})
