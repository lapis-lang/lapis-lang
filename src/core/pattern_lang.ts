/**
 * LC Pattern Language — the AST, parser, and counting semantics of pattern
 * constructors (the `pᵢ` of `μ α. Σᵢ pᵢ`).
 *
 * See _docs/theory/surface-syntax.md §1.3 (the restricted regular fragment)
 * and type-algebra.md §2.3 (pattern types are regular languages — rational
 * generating functions by Chomsky–Schützenberger).
 *
 * The pattern language is a restricted regular fragment over the lexer's
 * character universe (ASCII — code points 0–127 — a language-definition fiat;
 * widening to Unicode is a later, separate decision):
 *
 *   p ::= c          character literal (non-special chars; `\c` escapes)
 *       | .          any character (the universe)
 *       | [...]      character class (ranges `a-z`); `[^...]` negates
 *       | p p        concatenation
 *       | p +        one or more
 *       | p *        zero or more
 *       | p ?        zero or one
 *       | <TypeName> the pattern of another registered data type
 *
 * Excluded (loud parse rejections): alternation `|` (use multiple variants —
 * a declaration's pattern list is the alternation), groups `()`, anchors
 * (`^`/`$`), backreferences. Flat patterns compile to a DFA-equivalent AST;
 * type references make the language context-free-ish but the COUNTING here is
 * over lengths only, which stays well-defined.
 *
 * The counting semantics — the language-equation reading, evaluated over
 * finite SETS (type-algebra.md §2.3/§3): each node's language is
 * materialized as the set of its strings of length ≤ k, the equation's
 * operations — product (concat), closure (star/plus), union (opt) — run
 * over those sets, and the per-length count sequence $c_n$ is the set's
 * size profile. The set arithmetic is the exact route: factorization
 * recurrences (convolution, geometric series) count SPLITS, not strings —
 * a concat-closed sublanguage ("aa" ∈ {a, aa}) factors two ways and the
 * rounds double-count — while a set holds each string once, so the counts
 * agree with `enumeratePattern` by construction (the certificate's theorem:
 * one count, two derivations).
 *
 *   char/class/`.  →  c₁ = 1 or the matched-set size
 *   concatenation PQ  →  the product of the parts' sets, deduped
 *   star P*           →  the set closure (ε once, whatever the nesting)
 *   plus P+           →  the positive closure (≥1 piece; ε iff P nullable)
 *   opt P?            →  ε ∪ P (c₀ = max(1, c₀(P)); cₙ = cₙ(P))
 *   type ref <T>      →  the referenced type's coefficients (recursion
 *                        through registered types — memoized; cycles reject
 *                        loudly: an ill-founded equation has no reading)
 *
 * Saturating arithmetic: counts saturate at MAX_PATTERN_COUNT (2⁵³ — the
 * integer-exactness ceiling). A saturated count is still "≥ the true count",
 * which is the direction certificates need (a certificate never under-counts
 * the space it claims).
 */

import { type PatternDataType } from "./types.ts"

// ── The character universe ───────────────────────────────────────────────────

/**
 * The character universe: ASCII, code points 0–127 (the language-definition
 * fiat). `.` and character classes range over this universe; a character
 * outside it cannot be matched by any pattern, so a Unicode lexeme has no
 * pattern variant and no token can carry it until a later language-definition
 * change widens the universe.
 */
export const CHARACTER_UNIVERSE_SIZE = 128

/** A character in the universe: a code point in [0, 127]. */
export type UniverseChar = string

/** The universe as a sorted array of code points — the `.` vocabulary. */
export const UNIVERSE: readonly number[] = Array.from(
    { length: CHARACTER_UNIVERSE_SIZE },
    (_, i) => i,
)

// ── Saturating counting ──────────────────────────────────────────────────────

/**
 * The count ceiling: beyond this, counts saturate (integer-exactness ceiling;
 * a saturated count never under-reports the space).
 */
export const MAX_PATTERN_COUNT = 2 ** 53

function satAdd(a: number, b: number): number {
    const sum = a + b
    return sum > MAX_PATTERN_COUNT ? MAX_PATTERN_COUNT : sum
}

/**
 * Saturating SUM of two count sequences: the type-level alternation reading
 * — a pattern TYPE's language is the union of its variants', and the
 * variant counts are summed per length (the union's count is the sum MINUS
 * the overlap; the sum is an OVER-estimate — saturating keeps it
 * integer-exact, and over-estimation is the safe direction: a certificate
 * never under-reports its space). Used by `typeCoefficients` (the
 * multi-variant sum) and by `type_algebra`'s field arm.
 */
export function satAddSeq(a: readonly number[], b: readonly number[]): number[] {
    const out: number[] = []
    const n = Math.max(a.length, b.length)
    for (let i = 0; i < n; i++) {
        out.push(satAdd(a[i] ?? 0, b[i] ?? 0))
    }
    return out
}

/** Truncate a count sequence to exactly k+1 entries (the degree-k prefix). */
export function truncateTo(seq: readonly number[], k: number): number[] {
    const out: number[] = []
    for (let i = 0; i <= k; i++) out.push(satAdd(seq[i] ?? 0, 0))
    return out
}

// ── The AST ──────────────────────────────────────────────────────────────────

/** A pattern AST node — one of the restricted-regular constructs. */
export type PatternAST =
    /** A single literal character. */
    | { readonly kind: "char"; readonly char: string }
    /** `.` — any character in the universe. */
    | { readonly kind: "any" }
    /** `[...]` / `[^...]` — a (possibly negated) character class. */
    | { readonly kind: "class"; readonly set: Uint8Array; readonly negated: boolean }
    /** `p₁p₂...pₙ` — concatenation (n ≥ 2 in source; 1 is a passthrough). */
    | { readonly kind: "concat"; readonly parts: readonly PatternAST[] }
    /** `p*` — Kleene star. */
    | { readonly kind: "star"; readonly inner: PatternAST }
    /** `p+` — one or more. */
    | { readonly kind: "plus"; readonly inner: PatternAST }
    /** `p?` — zero or one. */
    | { readonly kind: "opt"; readonly inner: PatternAST }
    /** `<TypeName>` — the pattern of another registered data type. */
    | { readonly kind: "typeref"; readonly name: string }

/** Render a pattern AST back to its source form (the round-trip contract). */
export function patternToString(ast: PatternAST): string {
    switch (ast.kind) {
        case "char":
            return escapeSpecial(ast.char)
        case "any":
            return "."
        case "class": {
            // Collapse contiguous runs into ranges (the round-trip contract:
            // `[0-9]` renders as `[0-9]`, not `[0123456789]`).
            const spans = classSpans(ast.set)
            if (ast.negated) {
                const complement = new Uint8Array(
                    UNIVERSE.filter((cp) => !ast.set.includes(cp)),
                )
                const negatedSpans = classSpans(complement)
                return `[^${spansToSource(negatedSpans)}]`
            }
            return `[${spansToSource(spans)}]`
        }
        case "concat":
            return ast.parts.map(patternToString).join("")
        case "star":
            return `${patternToString(ast.inner)}*`
        case "plus":
            return `${patternToString(ast.inner)}+`
        case "opt":
            return `${patternToString(ast.inner)}?`
        case "typeref":
            return `<${ast.name}>`
    }
}

/** The metacharacters that must be escaped in source (surface-syntax.md §1.3). */
const METACHARACTERS = "+*?[]\\.<>"

function escapeSpecial(ch: string): string {
    return METACHARACTERS.includes(ch) ? `\\${ch}` : ch
}

/** A contiguous run of code points: [lo, hi] inclusive. */
interface ClassSpan {
    lo: number
    hi: number
}

/** Collapse a sorted code-point array into contiguous spans. */
function classSpans(set: Uint8Array): ClassSpan[] {
    const spans: ClassSpan[] = []
    for (const cp of set) {
        const last = spans[spans.length - 1]
        if (last && last.hi === cp - 1) {
            last.hi = cp
        } else {
            spans.push({ lo: cp, hi: cp })
        }
    }
    return spans
}

/** Render class spans as source (ranges `a-b` collapse; singles stay plain). */
function spansToSource(spans: ClassSpan[]): string {
    const out: string[] = []
    for (const span of spans) {
        if (span.lo === span.hi) {
            out.push(escapeSpecial(String.fromCharCode(span.lo)))
        } else if (span.hi === span.lo + 1) {
            // Two adjacent chars: keep them separate (a 2-char range like
            // `a-b` is fine, but a dash range of 2 reads clearer as `ab`).
            out.push(
                escapeSpecial(String.fromCharCode(span.lo)) +
                    escapeSpecial(String.fromCharCode(span.hi)),
            )
        } else {
            out.push(
                escapeSpecial(String.fromCharCode(span.lo)) + "-" +
                    escapeSpecial(String.fromCharCode(span.hi)),
            )
        }
    }
    return out.join("")
}

// ── The parser ───────────────────────────────────────────────────────────────

/** A pattern parse failure: the offending source and the reason. */
export class PatternParseError extends Error {
    constructor(
        readonly source: string,
        reason: string,
    ) {
        super(`pattern ${JSON.stringify(source)}: ${reason}`)
        this.name = "PatternParseError"
    }
}

/** The pattern AST of one source pattern — the parse is total or throws. */
export function parsePattern(source: string): PatternAST {
    if (source.length === 0) {
        throw new PatternParseError(
            source,
            "an empty pattern matches nothing — a variant must consume at least one character",
        )
    }
    const parser = new PatternParser(source)
    const ast = parser.parseWhole()
    return ast
}

/**
 * Recursive-descent parser over the restricted fragment. The grammar is
 * concatenation of postfix-repeated atoms:
 *
 *   pattern := repeat (repeat)*
 *   repeat  := atom ('*' | '+' | '?')?
 *   atom    := '.' | '\' char | '[' class ']' | '<' ident '>' | char
 *
 * The excluded constructs fail by construction: `|` and `()` are not atom
 * starters (they parse as literal chars ONLY when escaped; a bare `|` is a
 * parse error naming the excluded construct), `^` only negates INSIDE a
 * class (a leading `^` in source position is a literal — `^` is not a
 * metacharacter in this fragment, consistent with surface-syntax.md's
 * metacharacter list), and backreferences have no syntax.
 */
class PatternParser {
    private pos = 0

    constructor(private readonly source: string) {}

    parseWhole(): PatternAST {
        const ast = this.parse()
        if (this.pos < this.source.length) {
            throw new PatternParseError(
                this.source,
                `unexpected ${JSON.stringify(this.source[this.pos])} at position ${this.pos}`,
            )
        }
        return ast
    }

    private parse(): PatternAST {
        const parts: PatternAST[] = []
        while (this.pos < this.source.length) {
            parts.push(this.parseRepeat())
        }
        return parts.length === 1 ? parts[0] : { kind: "concat", parts }
    }

    private parseRepeat(): PatternAST {
        let atom = this.parseAtom()
        while (this.pos < this.source.length) {
            const ch = this.source[this.pos]
            if (ch === "*") {
                this.pos++
                atom = { kind: "star", inner: atom }
            } else if (ch === "+") {
                this.pos++
                atom = { kind: "plus", inner: atom }
            } else if (ch === "?") {
                this.pos++
                atom = { kind: "opt", inner: atom }
            } else {
                break
            }
        }
        return atom
    }

    private parseAtom(): PatternAST {
        const ch = this.source[this.pos]!
        if (ch === "|") {
            throw new PatternParseError(
                this.source,
                "alternation | is excluded — declare a second pattern variant instead (surface-syntax.md §1.3)",
            )
        }
        if (ch === "(" || ch === ")") {
            throw new PatternParseError(
                this.source,
                "groups () are excluded — flat patterns only (surface-syntax.md §1.3)",
            )
        }
        if (ch === "\\") {
            if (this.pos + 1 >= this.source.length) {
                throw new PatternParseError(this.source, "a trailing \\ escapes nothing")
            }
            const escaped = this.source[this.pos + 1]!
            this.pos += 2
            if (escaped === "<" || escaped === ">") {
                throw new PatternParseError(
                    this.source,
                    `\\${escaped} is not a valid escape — type references are <Ident>, never escaped literals`,
                )
            }
            return { kind: "char", char: escaped }
        }
        if (ch === ".") {
            this.pos++
            return { kind: "any" }
        }
        if (ch === "[") {
            this.pos++
            return this.parseClass()
        }
        if (ch === "<") {
            this.pos++
            return this.parseTypeRef()
        }
        this.pos++
        return { kind: "char", char: ch }
    }

    private parseClass(): PatternAST {
        const negated = this.source[this.pos] === "^"
        if (negated) this.pos++
        const set = new Set<number>()
        let first = true
        while (true) {
            if (this.pos >= this.source.length) {
                throw new PatternParseError(this.source, "an unterminated character class")
            }
            const ch = this.source[this.pos]!
            if (ch === "]" && !first) {
                this.pos++
                break
            }
            if (ch === "\\" && this.pos + 1 < this.source.length) {
                this.pos++
                const escaped = this.source[this.pos]!
                set.add(escaped.charCodeAt(0))
                this.pos++
                first = false
                continue
            }
            // Range: a-b — the dash is a RANGE OPERATOR when it sits between
            // two class members (the CURRENT char and the next); a dash in
            // the LEADING position (the current char itself, first=true) is
            // a literal: the standard lexer convention (`[-a]` is the set
            // {-, a}).
            if (
                this.source[this.pos + 1] === "-" && this.source[this.pos + 2] !== undefined &&
                this.source[this.pos + 2] !== "]"
            ) {
                const lo = ch.charCodeAt(0)
                let hiPos = this.pos + 2
                let hiChar = this.source[hiPos]!
                if (hiChar === "\\" && this.source[hiPos + 1] !== undefined) {
                    hiPos++
                    hiChar = this.source[hiPos]!
                }
                const hi = hiChar.charCodeAt(0)
                if (lo > hi) {
                    throw new PatternParseError(
                        this.source,
                        `a character class range [${ch}-${hiChar}] is inverted`,
                    )
                }
                for (let cp = lo; cp <= hi; cp++) set.add(cp)
                this.pos = hiPos + 1
                first = false
                continue
            }
            const plain = this.source[this.pos]!
            if (plain.charCodeAt(0) > 127) {
                throw new PatternParseError(
                    this.source,
                    `${
                        JSON.stringify(plain)
                    } is outside the character universe — ASCII (code points 0–127) only`,
                )
            }
            set.add(plain.charCodeAt(0))
            this.pos++
            first = false
        }
        const arr = new Uint8Array(set)
        return { kind: "class", set: arr, negated }
    }

    private parseTypeRef(): PatternAST {
        const end = this.source.indexOf(">", this.pos)
        if (end < 0) {
            throw new PatternParseError(this.source, "an unterminated type reference <")
        }
        const name = this.source.slice(this.pos, end)
        if (!/^[A-Z][A-Za-z0-9]*$/.test(name)) {
            throw new PatternParseError(
                this.source,
                `a type reference must be a PascalCase identifier, got ${JSON.stringify(name)}`,
            )
        }
        this.pos = end + 1
        return { kind: "typeref", name }
    }
}

// ── The counting environment ─────────────────────────────────────────────────

/**
 * The counting environment: resolves type references to pattern types, with
 * memoization and cycle rejection. `coefficientsOf` is the referenced type's
 * own full counting (the recursion point); `enumerateOf` its constructive
 * dual.
 */
export interface PatternCountEnv {
    /** Look up a referenced type by name (returns undefined for unknown names). */
    lookupPattern(name: string): PatternDataType | undefined
    /** The referenced type's coefficients — the recursion point (memoized by the caller). */
    coefficientsOf(name: string, k: number, stack: readonly string[]): readonly number[]
    /** The referenced type's full size-≤ k token set (the enumeration recursion point). */
    enumerateOf(
        name: string,
        k: number,
        maxCount: number,
        refChain: readonly string[],
    ): Set<string> | undefined
}

/**
 * The per-length count sequence of a pattern AST: c₀..c_k — the number of
 * strings of EXACTLY length n the pattern's language contains (saturating).
 *
 * This is the language-equation reading, evaluated over finite SETS: each
 * node's language is materialized as the set of its strings of length ≤ k
 * (the same sets `enumerateNode` produces), and the equation's operations —
 * union (opt), product (concat), closure (star/plus) — run over those sets.
 * The per-length counts are then the set's size profile. This is the ONLY
 * exact route for the general fragment: the classic factorization recurrences
 * (convolution, geometric series) count SPLITS, not strings — a
 * concat-closed sublanguage ("aa" ∈ {a, aa}) factors two ways, and the
 * rounds double-count it — while a set can only hold each string once, so
 * the count agrees with the enumeration by construction (the certificate's
 * theorem: one count, two derivations — here literally the same set walk,
 * read twice).
 *
 * Set-reading budget: a node whose language's size-≤ k class exceeds
 * MAX_STAR_COUNT_BUDGET declines loudly (the count cannot be certified
 * through a saturating recurrence for closed sublanguages; the decline is
 * the honest bound). Simple atoms never approach it (char/class ≤ 128);
 * a starred/ref'd pattern enumerates up to the budget.
 *
 * @param ast the pattern AST
 * @param k   the degree (returns exactly k+1 entries)
 * @param env the counting environment (type-reference resolution)
 * @param refChain the type-reference chain so far (cycle detection — a
 *                 reference cycle makes the equation ill-founded and rejects
 *                 loudly)
 */
export function patternCounts(
    ast: PatternAST,
    k: number,
    env: PatternCountEnv,
    refChain: readonly string[] = [],
): number[] {
    switch (ast.kind) {
        case "char":
            return ones(1, k)
        case "any":
            // `.` matches the whole universe — 128 characters at length 1
            // (the ASCII fiat; the count that String's cₙ = 128ⁿ rides on).
            return truncateTo([0, CHARACTER_UNIVERSE_SIZE], k)
        case "class": {
            // The class's per-length count is (matched count) at length 1:
            // the SIZES of the matched set matter for the convolution; the
            // sequence itself is 0 at n=0 and matched at n=1.
            const matched = classSize(ast)
            return truncateTo([0, matched], k)
        }
        case "concat": {
            // The PRODUCT of the parts' languages: a string of length ≤ k
            // factors as a left part followed by a right part; the set
            // arithmetic takes the product and DEDUPS (a closed part can
            // absorb the split — "10" = "1"·"0" and "10"·"ε" are the same
            // string; the convolution's split-counting would double it).
            let acc: Set<string> = new Set([""])
            for (const part of ast.parts) {
                const right = enumerateNode(part, k, env, MAX_STAR_COUNT_BUDGET, refChain)
                if (right === undefined) {
                    throw new PatternParseError(
                        patternToString(part),
                        `the concatenated pattern's enumeration exceeds the counting budget (${MAX_STAR_COUNT_BUDGET} strings) — the count declines loudly (the set arithmetic is required)`,
                    )
                }
                const next = new Set<string>()
                for (const left of acc) {
                    for (const piece of right) {
                        const joined = left + piece
                        if (joined.length <= k) next.add(joined)
                        if (next.size > MAX_STAR_COUNT_BUDGET) {
                            throw new PatternParseError(
                                patternToString(ast),
                                `the concatenation's product exceeds the counting budget — the count declines loudly`,
                            )
                        }
                    }
                }
                acc = next
            }
            return countStringsPerLength(acc, k)
        }
        case "star": {
            // L = the KLEENE closure of P's SET — the counts count DISTINCT
            // strings: for a concat-closed sublanguage ("aa" ∈ {a, aa}),
            // the round recurrence counts FACTORIZATIONS ("aa" factors as
            // [aa] and [a·a]) and double-counts. The set arithmetic is the
            // only exact route; it makes the counts agree with the
            // enumeration BY CONSTRUCTION (the certificate's theorem).
            const strings = enumerateNode(ast.inner, k, env, MAX_STAR_COUNT_BUDGET, refChain)
            if (strings === undefined) {
                throw new PatternParseError(
                    patternToString(ast),
                    `the starred pattern's enumeration exceeds the counting budget (${MAX_STAR_COUNT_BUDGET} strings) — the count declines loudly`,
                )
            }
            const counted = starCountsFromStrings(strings, k)
            return truncateTo(counted, k)
        }
        case "plus": {
            // P+ = the positive closure of P's SET — at least one P-piece,
            // concatenated. The counts count DISTINCT strings (the same
            // discipline the star arm runs — a concat-closed base factors
            // two ways and the round arithmetic double-counts). The
            // closure runs over P's NON-EMPTY strings: a nullable P's ε
            // piece contributes nothing, so the closure of the non-empty
            // part is P+ minus whatever ε-membership P's own nullable
            // pieces re-create — the ε is then re-added exactly when a
            // single piece can be ε (P nullable): P+ = P · P*.
            const strings = enumerateNode(ast.inner, k, env, MAX_STAR_COUNT_BUDGET, refChain)
            if (strings === undefined) {
                throw new PatternParseError(
                    patternToString(ast),
                    `the closed pattern's enumeration exceeds the counting budget (${MAX_STAR_COUNT_BUDGET} strings) — the count declines loudly`,
                )
            }
            const nullable = strings.has("")
            const nonEmpty = new Set([...strings].filter((s) => s.length > 0))
            const closed = starStringsOf(nonEmpty, k, MAX_STAR_COUNT_BUDGET)
            if (closed === undefined) {
                throw new PatternParseError(
                    patternToString(ast),
                    `the positive closure's enumeration exceeds the counting budget — the count declines loudly`,
                )
            }
            // The star closure seeds ε; P+ holds ε exactly when P does (the
            // single ε-piece path) — drop the seed unless P is nullable.
            if (!nullable) closed.delete("")
            return countStringsPerLength(closed, k)
        }
        case "opt": {
            const inner = patternCounts(ast.inner, k, env, refChain)
            // L = ε ∪ P — a UNION, so the ε overlap must not double-count:
            // a nullable P already holds ε (c₀(P) = 1) and the ε branch
            // adds nothing. At length n ≥ 1 the branches are disjoint (the
            // ε-only branch contributes nothing), so cₙ = cₙ(P); at n = 0
            // both branches hold exactly {ε}, so c₀ = max(1, c₀(P)) — and
            // c₀(P) ≤ 1 always (a length-0 language holds at most ε).
            const out: number[] = []
            for (let n = 0; n <= k; n++) {
                out.push(n === 0 ? Math.max(1, inner[0] ?? 0) : inner[n] ?? 0)
            }
            return out
        }
        case "typeref": {
            if (refChain.includes(ast.name)) {
                throw new PatternParseError(
                    patternToString(ast),
                    `the type-reference chain ${
                        [...refChain, ast.name].join(" → ")
                    } is a cycle — the language equation is ill-founded`,
                )
            }
            return [...env.coefficientsOf(ast.name, k, [...refChain, ast.name])]
        }
    }
}

/**
 * The per-length counts of a STRING SET (saturating): the honest count of
 * distinct strings per length — the arithmetic the set-based star/plus
 * arms reduce to (counting a closed sublanguage needs the set, not the
 * factorization rounds).
 */
function countStringsPerLength(strings: Set<string>, k: number): number[] {
    const out: number[] = []
    for (let n = 0; n <= k; n++) {
        let c = 0
        for (const s of strings) {
            if (s.length === n) c = satAdd(c, 1)
        }
        out.push(c)
    }
    return out
}

/**
 * P*'s counts given P's enumerated string set: the per-length sizes of the
 * SET closure — the count the certificate needs (distinct strings, per
 * length). The set arithmetic dedups exactly as the enumeration's does,
 * so the two readings agree BY CONSTRUCTION (the certificate's theorem:
 * one count, two derivations — the recurrence's round arithmetic cannot
 * be trusted for closed sublanguages, where a piece concatenates into
 * another piece and the round-based sum double-counts).
 */
function starCountsFromStrings(
    strings: Set<string>,
    k: number,
): number[] {
    const closed = starStringsOf(strings, k, MAX_STAR_COUNT_BUDGET)
    if (closed === undefined) {
        throw new PatternParseError(
            [...strings].join(" | "),
            `the star closure's enumeration exceeds the counting budget — the count declines loudly`,
        )
    }
    return countStringsPerLength(closed, k)
}

/** The enumeration budget the counting's set-based star arm runs under. */
const MAX_STAR_COUNT_BUDGET = 2 ** 16

function ones(nonzeroAt: number, k: number): number[] {
    const out: number[] = []
    for (let n = 0; n <= k; n++) out.push(n === nonzeroAt ? 1 : 0)
    return out
}

/** The number of universe characters a class matches (saturating). */
function classSize(ast: Extract<PatternAST, { kind: "class" }>): number {
    if (ast.negated) return UNIVERSE.length - ast.set.length
    return ast.set.length
}

/**
 * The coefficients of a pattern AST truncated to the degree-k prefix
 * (c₀..cₖ) — the exact size-≤ k inhabitant count is the SUM of the sequence.
 *
 * @throws PatternParseError on an ill-founded type-reference cycle
 */
export function patternCoefficients(
    ast: PatternAST,
    k: number,
    env: PatternCountEnv,
): readonly number[] {
    return truncateTo(patternCounts(ast, k, env, []), k)
}

/**
 * P*'s string set given P's string set (the geometric enumeration, isolated
 * for `plus`): L = ε + P·L, iterated to the length bound.
 */
function starStringsOf(
    inner: Set<string>,
    k: number,
    maxCount: number,
): Set<string> | undefined {
    let acc: Set<string> = new Set([""])
    for (let round = 0; round <= k; round++) {
        const next = new Set<string>(acc)
        for (const left of acc) {
            for (const piece of inner) {
                const joined = left + piece
                if (joined.length <= k) next.add(joined)
                if (next.size > maxCount) return undefined
            }
        }
        if (next.size === acc.size) break // fixpoint
        acc = next
    }
    return acc
}

// ── Enumeration ──────────────────────────────────────────────────────────────

/**
 * Enumerate all strings of length ≤ k in a pattern's language — the true
 * size-≤ k token set (each string is a potential `TokenVal.text`).
 *
 * The enumeration is the convolution reading's constructive dual: each node
 * contributes its matched strings per length, concatenation takes the
 * product of the parts' string sets per length pair, star accumulates
 * repetition counts. Budget: the returned set is capped at `maxCount` —
 * a pattern whose size-≤ k class exceeds the cap returns `undefined` (the
 * caller declines loudly; the certificate never guesses).
 *
 * @param ast the pattern AST
 * @param k   the size bound (strings of length ≤ k)
 * @param env the counting environment (type references enumerate through it)
 * @param maxCount the enumeration budget
 * @returns the sorted string set (deduped), or `undefined` when the class
 *          exceeds the budget
 */
export function enumeratePattern(
    ast: PatternAST,
    k: number,
    env: PatternCountEnv,
    maxCount: number,
    refChain: readonly string[] = [],
): Set<string> | undefined {
    const results = enumerateNode(ast, k, env, maxCount, refChain)
    if (results === undefined) return undefined
    if (results.size > maxCount) return undefined
    return results
}

function enumerateNode(
    ast: PatternAST,
    k: number,
    env: PatternCountEnv,
    maxCount: number,
    refChain: readonly string[],
): Set<string> | undefined {
    switch (ast.kind) {
        case "char":
            return new Set([ast.char])
        case "any":
            // `.` matches the whole universe — its size-≤ k class holds 0
            // strings at k = 0 and 128 at k ≥ 1: past the budget, decline
            // (the enumeration never truncates — a partial set would
            // masquerade as the full class).
            if (k === 0) return new Set()
            if (UNIVERSE.length > maxCount) return undefined
            return new Set(UNIVERSE.map((cp) => String.fromCharCode(cp)))
        case "class": {
            // Same contract: k = 0 holds nothing; the matched set is all-
            // or-nothing against the budget (the class's language has no
            // prefix to enumerate — truncation would lie about coverage).
            const out = new Set<string>()
            if (k === 0) return out
            for (const cp of ast.set) {
                if (!ast.negated) {
                    out.add(String.fromCharCode(cp))
                    if (out.size > maxCount) return undefined
                }
            }
            if (ast.negated) {
                const present = new Set<number>(ast.set)
                for (const cp of UNIVERSE) {
                    if (!present.has(cp)) {
                        out.add(String.fromCharCode(cp))
                        if (out.size > maxCount) return undefined
                    }
                }
            }
            return out
        }
        case "concat": {
            let acc: Set<string> = new Set([""])
            for (const part of ast.parts) {
                const right = enumerateNode(part, k, env, maxCount, refChain)
                if (right === undefined) return undefined
                const next = new Set<string>()
                for (const left of acc) {
                    if (left.length > k) continue
                    for (const rightStr of right) {
                        const joined = left + rightStr
                        if (joined.length <= k) next.add(joined)
                        if (next.size > maxCount) return undefined
                    }
                }
                acc = next
            }
            return acc
        }
        case "star": {
            // L = ε + P·L — iterate to the length bound.
            let acc: Set<string> = new Set([""])
            for (let round = 0; round <= k; round++) {
                const inner = enumerateNode(ast.inner, k, env, maxCount, refChain)
                if (inner === undefined) return undefined
                const next = new Set<string>(acc)
                for (const left of acc) {
                    for (const piece of inner) {
                        const joined = left + piece
                        if (joined.length <= k) next.add(joined)
                        if (next.size > maxCount) return undefined
                    }
                }
                if (next.size === acc.size) break // fixpoint
                acc = next
            }
            return acc
        }
        case "plus": {
            // P+ = P · P* — enumerate the star's strings, drop ε. The star
            // loop over `ast` itself is INFINITE (P+ = P* by that reading);
            // the constructive dual of P+ is: enumerate P (the inner), then
            // extend with star's fixpoint over it.
            const inner = enumerateNode(ast.inner, k, env, maxCount, refChain)
            if (inner === undefined) return undefined
            const star = starStringsOf(inner, k, maxCount)
            if (star === undefined) return undefined
            const out = new Set<string>()
            for (const left of inner) {
                for (const right of star) {
                    const joined = left + right
                    if (joined.length <= k) out.add(joined)
                    if (out.size > maxCount) return undefined
                }
            }
            return out
        }
        case "opt": {
            const inner = enumerateNode(ast.inner, k, env, maxCount, refChain)
            if (inner === undefined) return undefined
            return new Set(["", ...inner])
        }
        case "typeref": {
            if (refChain.includes(ast.name)) {
                throw new PatternParseError(
                    patternToString(ast),
                    `the type-reference chain ${
                        [...refChain, ast.name].join(" → ")
                    } is a cycle — the language equation is ill-founded`,
                )
            }
            return env.enumerateOf(ast.name, k, maxCount, [...refChain, ast.name])
        }
    }
}

// ── The registry-facing environment ─────────────────────────────────────────

/**
 * Build the counting environment from the type registry: a type reference
 * `<T>` resolves to the registered pattern type `T` and reads ITS coefficients
 * (or enumerates ITS space) — recursion through the registry, memoized, with
 * cycle rejection at the recursion point.
 */
export function makePatternCountEnv(
    lookupPattern: (name: string) => PatternDataType | undefined,
): PatternCountEnv {
    const coeffMemo = new Map<string, readonly number[]>()
    return {
        lookupPattern,
        coefficientsOf(name: string, k: number, refChain: readonly string[]): readonly number[] {
            const memoKey = `${name}#${k}`
            const memoed = coeffMemo.get(memoKey)
            if (memoed !== undefined) return memoed
            const resolved = lookupPattern(name)
            if (!resolved) {
                throw new PatternParseError(
                    name,
                    `the type reference <${name}> does not resolve to a registered pattern type`,
                )
            }
            const out = typeCoefficients(resolved, k, lookupPattern, refChain, coeffMemo)
            coeffMemo.set(memoKey, out)
            return out
        },
        enumerateOf(
            name: string,
            k: number,
            maxCount: number,
            refChain: readonly string[],
        ): Set<string> | undefined {
            const resolved = lookupPattern(name)
            if (!resolved) {
                throw new PatternParseError(
                    name,
                    `the type reference <${name}> does not resolve to a registered pattern type`,
                )
            }
            return typeEnumeration(resolved, k, maxCount, lookupPattern, refChain, new Map())
        },
    }
}

/**
 * A pattern TYPE's counts: the UNION of its variants' languages — a
 * declaration's pattern list is the sum type's language, and the union
 * may OVERLAP (variants `a` and `a?` both hold the string "a"; the sum
 * would double-count it). The union's count is computed from the union's
 * STRING SET (each variant enumerates, the sets merge, the per-length
 * profile reads off the merged set) — the same dedup the enumeration
 * runs, so the counts agree with `inhabitantsUpToSize` by construction.
 * Memoized per (type, k); the refChain carries the recursion for cycle
 * rejection.
 */
function typeCoefficients(
    type: PatternDataType,
    k: number,
    lookupPattern: (name: string) => PatternDataType | undefined,
    refChain: readonly string[],
    memo: Map<string, readonly number[]>,
): readonly number[] {
    const memoKey = `${type.name}#${k}`
    const memoed = memo.get(memoKey)
    if (memoed !== undefined) return memoed
    const union = new Set<string>()
    const env = makeEnv(lookupPattern, memo)
    for (const ast of type.patterns) {
        const part = enumerateNode(ast, k, env, MAX_STAR_COUNT_BUDGET, refChain)
        if (part === undefined) {
            memo.set(memoKey, zeroSeq(k))
            throw new PatternParseError(
                type.name,
                `the variant enumeration exceeds the counting budget (${MAX_STAR_COUNT_BUDGET} strings) — the coefficients decline loudly (the union's count needs the set arithmetic, and the set is too large to materialize)`,
            )
        }
        for (const s of part) union.add(s)
        if (union.size > MAX_STAR_COUNT_BUDGET) {
            memo.set(memoKey, zeroSeq(k))
            throw new PatternParseError(
                type.name,
                `the union of ${type.name}'s variants exceeds the counting budget — the coefficients decline loudly`,
            )
        }
    }
    const out = countStringsPerLength(union, k)
    memo.set(memoKey, out)
    return out
}

/** The zero count sequence up to degree k. */
function zeroSeq(k: number): number[] {
    return new Array<number>(k + 1).fill(0)
}

/**
 * A pattern TYPE's full size-≤ k enumeration: the union of its variants'
 * matched strings. Memoized per (type, k); the refChain carries the recursion.
 */
function typeEnumeration(
    type: PatternDataType,
    k: number,
    maxCount: number,
    lookupPattern: (name: string) => PatternDataType | undefined,
    refChain: readonly string[],
    enumMemo: Map<string, Set<string> | undefined>,
): Set<string> | undefined {
    const memoKey = `${type.name}#${k}`
    if (enumMemo.has(memoKey)) return enumMemo.get(memoKey)
    const out = new Set<string>()
    for (const ast of type.patterns) {
        const part = enumerateNode(ast, k, makeEnv(lookupPattern, new Map()), maxCount, refChain)
        if (part === undefined) {
            enumMemo.set(memoKey, undefined)
            return undefined
        }
        for (const s of part) {
            out.add(s)
            if (out.size > maxCount) {
                enumMemo.set(memoKey, undefined)
                return undefined
            }
        }
    }
    enumMemo.set(memoKey, out)
    return out
}

/**
 * A pattern TYPE's union coefficients, through the type-registry hook the
 * caller installed (`setPatternLookup` in type_algebra.ts wires the law
 * checker's registry): the entry point the type-algebra module's pattern
 * arms share (the carrier arm and the field arm read the same union).
 *
 * @throws PatternParseError on a counting-budget decline or an
 *         ill-founded type-reference cycle.
 */
export function typeUnionCounts(type: PatternDataType, k: number): readonly number[] {
    const lookup = (name: string): PatternDataType | undefined => {
        const resolved = patternLookupHook(name)
        return resolved
    }
    return typeCoefficients(type, k, lookup, [type.name], new Map())
}

/**
 * A pattern TYPE's union enumeration (size-≤ k, budget-capped) — the
 * constructive dual of `typeUnionCounts`: the merged string set the
 * counts profile. Returns `undefined` past the budget (the caller
 * declines loudly — the certificate never truncates).
 *
 * @throws PatternParseError on an ill-founded type-reference cycle.
 */
export function typeUnionStrings(
    type: PatternDataType,
    k: number,
    maxCount: number,
): Set<string> | undefined {
    const lookup = (name: string): PatternDataType | undefined => patternLookupHook(name)
    return typeEnumeration(type, k, maxCount, lookup, [type.name], new Map())
}

/** The installed registry hook (wired by `setPatternLookup` in type_algebra). */
function patternLookupHook(name: string): PatternDataType | undefined {
    return registryHook(name)
}

/**
 * The registry hook `type_algebra.ts` installs. Kept as a module variable
 * here to avoid a static import cycle (type_algebra imports this module
 * for the counting; this module must not import type_algebra back) — the
 * setter is re-exported wiring, and the default THROWS (a type reference
 * with no installed registry is a typed rejection).
 */
let registryHook: (name: string) => PatternDataType | undefined = () => {
    throw new TypeError(
        "a pattern language type reference <T> requires the registry hook — " +
            "install it via setPatternLookup (the law checker wires the type registry)",
    )
}

/**
 * Install the type-reference lookup hook (called by type_algebra.ts at
 * module setup — its own hook delegates here). The prior hook is returned
 * for restoration in tests.
 */
export function setRegistryHook(
    lookup: (name: string) => PatternDataType | undefined,
): (name: string) => PatternDataType | undefined {
    const prior = registryHook
    registryHook = lookup
    return prior
}

/** The full environment over a lookup function (coefficients + enumeration). */
function makeEnv(
    lookupPattern: (name: string) => PatternDataType | undefined,
    memo: Map<string, readonly number[]>,
): PatternCountEnv {
    return {
        lookupPattern,
        coefficientsOf(name: string, k: number, refChain: readonly string[]): readonly number[] {
            const memoKey = `${name}#${k}`
            const memoed = memo.get(memoKey)
            if (memoed !== undefined) return memoed
            const resolved = lookupPattern(name)
            if (!resolved) {
                throw new PatternParseError(
                    name,
                    `the type reference <${name}> does not resolve to a registered pattern type`,
                )
            }
            return typeCoefficients(resolved, k, lookupPattern, refChain, memo)
        },
        enumerateOf(
            name: string,
            k: number,
            maxCount: number,
            refChain: readonly string[],
        ): Set<string> | undefined {
            const resolved = lookupPattern(name)
            if (!resolved) {
                throw new PatternParseError(
                    name,
                    `the type reference <${name}> does not resolve to a registered pattern type`,
                )
            }
            return typeEnumeration(resolved, k, maxCount, lookupPattern, refChain, new Map())
        },
    }
}
