/**
 * Lexical productions for the surface language — `surface-grammar.md` §2.
 *
 * Kept separate from the grammar class so the character-level rules live in one
 * place: identifiers, PascalCase names, keywords and their guard, symbolic
 * operation names, and the literal spellings.
 */

import { char, empty, epsilon, literal, or, type Parser, pred } from "@lapis-lang/lang-forma"

/**
 * The keywords of §2.5.
 *
 * A keyword may not be an identifier, and a keyword must be followed by a
 * non-`alnum` character (`dataFoo` is an identifier, `data` is a keyword).
 */
export const SURFACE_KEYWORDS: readonly string[] = [
    "data",
    "behavior",
    "protocol",
    "relation",
    "query",
    "io",
    "fold",
    "unfold",
    "map",
    "merge",
    "scan",
    "satisfies",
    "not",
    "self",
    "old",
    "prev",
    "aux",
    "Family",
    "Self",
] as const

/** `alnum ::= alpha | digit` (§2.1). */
export const isAlnum = (c: string): boolean => /[A-Za-z0-9_]/.test(c)

/** `alphaLower ::= "a" … "z" | "_"` (§2.1). */
export const isLowerStart = (c: string): boolean => /[a-z_]/.test(c)

/** `alphaUpper ::= "A" … "Z"` (§2.1). */
export const isUpperStart = (c: string): boolean => /[A-Z]/.test(c)

/** The characters a symbolic operation name may be built from (§2.3). */
export const isSymbolicOpChar = (c: string): boolean => "+-*/<>=!?&|,.".includes(c)

/**
 * Follow an identifier-continuation character, greedily, into a string.
 *
 * The engine's `pred` matches exactly one character, so a run is built by
 * `many()` and joined here — the one place that shape is written.
 */
export function charsWhere(p: (c: string) => boolean, label: string): Parser<string> {
    return pred(p, label).many().map((cs: string[]) => cs.join(""))
}

/**
 * A keyword (§2.5), guarded: the match must not be continued by an `alnum`
 * character, so `dataFoo` is an identifier rather than `data` + `Foo`.
 */
export function keyword(word: string): Parser<string> {
    return literal(word).bind(() =>
        pred(isAlnum, "<keyword-guard>").opt().bind((next) =>
            next === undefined ? epsilon(word) : empty<string>()
        )
    )
}

/**
 * A named identifier: a lower-case start, then a run of `alnum` characters,
 * rejecting keywords (§2.2).
 */
export const ident: Parser<string> = pred(isLowerStart, "<ident-start>")
    .bind((first) =>
        charsWhere(isAlnum, "<ident-rest>").bind((rest) => {
            const name = first + rest
            return SURFACE_KEYWORDS.includes(name) ? empty<string>() : epsilon(name)
        })
    )

/**
 * A PascalCase identifier: an upper-case start, then `alnum` (§2.2).
 *
 * `Family` and `Self` are keywords (§2.5) and so are excluded here — they are
 * references (§3.5), not names.
 */
export const pascalIdent: Parser<string> = pred(isUpperStart, "<pascal-start>")
    .bind((first) =>
        charsWhere(isAlnum, "<pascal-rest>").bind((rest) => {
            const name = first + rest
            return SURFACE_KEYWORDS.includes(name) ? empty<string>() : epsilon(name)
        })
    )

/**
 * A symbolic operation name (§2.3): a contiguous run of operator characters,
 * recognised by longest match among *declared* operators.
 *
 * The longest-match refinement needs the declaration table and so belongs to
 * name resolution; this production accepts any run. Resolution does **not** yet
 * report an undeclared operator, so an unknown symbol is currently passed
 * through into the emitted core text, where the core's own parse fails. See
 * `surface-grammar.md` §5.
 */
export const symbolicOp: Parser<string> = charsWhere(isSymbolicOpChar, "<symbolic-op>")
    .bind((op) => op === "" ? empty<string>() : epsilon(op))

/**
 * `true` / `false` / `nil` (§2.5's special values).
 *
 * These are **not** keywords — they are ordinary values. `true` and `false` are
 * `Bool`'s variants and `nil` is the null reference, so they are parsed as
 * literals rather than references.
 */
export const specialValue: Parser<string> = or(
    literal("true"),
    literal("false"),
    literal("nil"),
)

/**
 * A quoted string literal — `'"' ( char | escape )* '"'` (§2.4).
 *
 * The delimiter escapes are pinned; the fuller escape vocabulary is open (§9.1).
 */
export const stringLiteral: Parser<string> = char('"').bind(() =>
    quotedBody('"').map((body) => `"${body}"`)
)

/** A quoted character literal — `"'" ( char | escape ) "'"` (§2.4). */
export const charLiteral: Parser<string> = char("'").bind(() =>
    quotedBody("'").map((body) => `'${body}'`)
)

/** The body of a quoted literal up to its (unescaped) closing delimiter. */
function quotedBody(delimiter: string): Parser<string> {
    return or(
        // An escaped delimiter is content: the backslash consumes the next char.
        char("\\").bind(() =>
            pred((c: string) => c !== "\n", "<escape-char>").bind((c) =>
                quotedBody(delimiter).map((rest) => `\\${c}${rest}`)
            )
        ),
        // The closing delimiter ends the body.
        char(delimiter).map(() => ""),
        // Anything else is content.
        pred((c: string) => c !== delimiter && c !== "\\" && c !== "\n", "<string-char>")
            .bind((c) => quotedBody(delimiter).map((rest) => c + rest)),
    )
}

/**
 * `literal` from §2.4: whatever text a declared pattern matched.
 *
 * A pattern-driven lexer needs the declaration table, which the pipeline does
 * not yet thread into the lexer. The digits-only form below is the subset the
 * `examples/` fixtures need; the general form arrives with the lexer work.
 */
export const patternLiteral: Parser<string> = pred(
    (c: string) => /[0-9-]/.test(c),
    "<pattern-literal>",
).many().bind((cs: string[]) => {
    const text = cs.join("")
    // A lone `-` with no digits is not a literal — it is the subtraction
    // operator, which the expression grammar reads.
    return /^-?[0-9]+$/.test(text) ? epsilon(text) : empty<string>()
})
