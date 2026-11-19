/**
 * Surface layout primitives — `surface-grammar.md` §7's L1/L2 rules.
 *
 * Layout is a grammar-level concern in Lapis, not a post-pass. Two rules:
 *
 * - **L1 — Indentation.** A block's contents are indented exactly one indent
 *   unit (4 spaces) more than the line that introduces it. Continuation lines
 *   within a body line are indented further.
 * - **L2 — Newline.** A newline separates body lines. Blank lines and comments
 *   are consumed between them.
 *
 * **Whitespace is spaces, never tabs.** A tab is not a whitespace character in
 * this grammar, so a file that mixes the two is rejected rather than silently
 * re-indented — the indent unit is four spaces, and a tab would make the column
 * a matter of the reader's tab width. Comments are the one exception: their
 * content is free text and may contain anything but an unbalanced `*\/`.
 *
 * The implementation is P4P-style: every block-introducing production takes the
 * child column as a parameter and `spaces(n)` matches exactly `n` spaces. There
 * is no pre-pass and no token rewriting — the column is threaded through
 * `@rule` method parameters, which the engine memoizes per `(instance, method,
 * arguments)`.
 *
 * The engine's own whitespace primitives (`ws`, `ws1`, `wsChar`) are unusable
 * here for two reasons: they are newline-inclusive, so `ws` would let a line
 * swallow the newline that terminates it; and they admit tabs. This module
 * supplies the newline-excluding, spaces-only counterparts.
 */

import { empty, epsilon, literal, or, type Parser, pred } from "@lapis-lang/lang-forma"

/** The indent unit — `surface-grammar.md` §7 L1. */
export const INDENT_UNIT = 4

/** The body column of a top-level declaration's contents (§7's table). */
export const DECL_BODY_COLUMN = INDENT_UNIT

/** The column of case arms and contracts inside a fold body (§7's table). */
export const ARM_COLUMN = INDENT_UNIT * 2

/** The column of a multi-line case arm body (§7's table). */
export const ARM_BODY_COLUMN = INDENT_UNIT * 3

/**
 * Match exactly `n` spaces.
 *
 * `n === 0` yields the empty match — a top-level declaration starts at column 0
 * and therefore consumes no padding. Kept as `literal("")` rather than a
 * special case at each call site so block productions read uniformly.
 */
export function spaces(n: number): Parser<string> {
    return literal(" ".repeat(n))
}

/**
 * A newline: `\r\n` or `\n` (L2 accepts both). Ordered longest-first so the
 * two-character form is not shadowed by the one-character form.
 */
export const newline: Parser<string> = or(literal("\r\n"), literal("\n"))

/**
 * One horizontal whitespace character.
 *
 * **Spaces only — never a tab.** A source file cannot mix the two, and the
 * indent unit is four spaces (§7 L1), so a tab is not whitespace here at all:
 * it is a rejected character wherever code appears. Comments are the sole
 * exception, because their content is free text (§2.4).
 */
export const hwsChar: Parser<string> = pred(
    (c: string) => c === " ",
    "<space>",
)

/**
 * Zero or more horizontal whitespace characters.
 *
 * This is the separator *within* a line. A line's end is `newline`'s job, so a
 * production that ends a line must not expect this to reach it.
 */
export const hws: Parser<string> = hwsChar.many().map((cs: string[]) => cs.join(""))

/**
 * One or more horizontal whitespace characters — a required in-line gap.
 *
 * A zero-length match is rejected via `empty()`, so `Push value` and
 * `Pushvalue` are distinguished rather than both accepted.
 */
export const hws1: Parser<string> = hwsChar.many().bind(
    (cs: string[]) => cs.length === 0 ? empty<string>() : epsilon(cs.join("")),
)

/**
 * A block comment — `/* … *\/`, delimited and **nestable**.
 *
 * Nesting is counted rather than matched by a non-greedy pattern because the
 * delimiters are not distinguishable from content otherwise: a comment may not
 * contain an unbalanced `*\/`.
 */
export const comment: Parser<string> = literal("/*").bind(() => commentBody(1))

/** The body of a block comment, `depth` delimiters deep. */
function commentBody(depth: number): Parser<string> {
    const content = pred(
        (c: string) => c !== "/" && c !== "*",
        "<comment-char>",
    )
    return or(
        // A nested opener deepens the count.
        literal("/*").bind(() => commentBody(depth + 1)),
        // A closer shallows it; at depth 1 the comment ends.
        literal("*/").bind(() => depth === 1 ? epsilon("") : commentBody(depth - 1)),
        // Any other character is content.
        content.bind((c) => commentBody(depth).map((rest) => c + rest)),
        // A lone `/` or `*` that begins no delimiter is content too.
        or(literal("/"), literal("*")).bind((c) => commentBody(depth).map((rest) => c + rest)),
    ).map((body: string) => body)
}

/**
 * A line's trailing horizontal space, an optional comment, then its newline.
 *
 * Every block line ends this way, so a trailing comment needs no special
 * handling at the call site. The whitespace and comment are interleaved rather
 * than ordered — `expr /* note *\/` and `expr/* note *\/` are both a trailing
 * comment (`surface-syntax.md` §1.4's result annotation, whose own example is
 * `Color Red toHex            /* "#FF0000" *\/`).
 *
 * Returns the newline so the caller can tell a line end from end-of-input.
 */
export const lineEnd: Parser<string> = hws
    .then(comment.opt())
    .then(hws)
    .then(newline)
    .map((pairs) => pairs[1] as string)

/** A blank line: optional horizontal space, then a newline. */
const blankLine: Parser<string> = hws.then(newline).map(() => "")

/**
 * Zero or more blank lines and comment-only lines — what L2 consumes between
 * body items.
 *
 * Indentation is deliberately not consumed here: a blank line's leading spaces
 * belong to no block, so the next item's own `spaces(column)` still matches it.
 */
export const trivia: Parser<string> = or(
    blankLine,
    hws.then(comment).then(hws).then(newline).map(() => ""),
).many().map((xs: string[]) => xs.join(""))
