/**
 * Surface layout primitives.
 *
 * L1: a block's contents sit at exactly the introducing line's column + 4.
 * L2: a newline separates body lines; blank lines and comments are eaten
 * between them.
 *
 * Spaces only, never tabs — the indent unit is four spaces, so a tab would make
 * a column a matter of the reader's tab width. Comments are the exception: their
 * content is free text. The engine's own `ws` family is unusable here because it
 * is newline-inclusive (a line would swallow its terminator) and admits tabs;
 * this module supplies the newline-excluding, spaces-only counterparts.
 *
 * The column is threaded through `@rule` method parameters, which the engine
 * memoizes per `(instance, method, arguments)` — no pre-pass, no token rewriting.
 */

import { empty, epsilon, literal, or, type Parser, pred } from "@lapis-lang/lang-forma"

/** The indent unit. */
export const INDENT_UNIT = 4

/** A top-level declaration's body column. */
export const DECL_BODY_COLUMN = INDENT_UNIT

/** Case arms and contracts inside a fold body. */
export const ARM_COLUMN = INDENT_UNIT * 2

/** A multi-line case arm body. */
export const ARM_BODY_COLUMN = INDENT_UNIT * 3

/** Match exactly `n` spaces; `n === 0` is the empty match (a column-0 line). */
export function spaces(n: number): Parser<string> {
    return literal(" ".repeat(n))
}

/** `\r\n` or `\n` — longest-first so the two-character form is not shadowed. */
export const newline: Parser<string> = or(literal("\r\n"), literal("\n"))

/** One horizontal whitespace character: a space, never a tab. */
export const hwsChar: Parser<string> = pred(
    (c: string) => c === " ",
    "<space>",
)

/**
 * Zero or more spaces — the separator *within* a line. A line's end is
 * `newline`'s job, so a line-ending production must not expect this to reach it.
 */
export const hws: Parser<string> = hwsChar.many().map((cs: string[]) => cs.join(""))

/** One or more spaces — a required in-line gap, so `Push value` ≠ `Pushvalue`. */
export const hws1: Parser<string> = hwsChar.many().bind(
    (cs: string[]) => cs.length === 0 ? empty<string>() : epsilon(cs.join("")),
)

/**
 * A nestable block comment. Nesting is counted rather than pattern-matched:
 * the delimiters are otherwise indistinguishable from content.
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
 * A line's trailing spaces, an optional comment, then its newline — every block
 * line ends this way, so a trailing comment needs no per-site handling. The
 * whitespace and comment interleave, so both `expr /* note *\/` and
 * `expr/* note *\/` are trailing comments. Returns the newline, so a caller can
 * tell a line end from end-of-input.
 */
export const lineEnd: Parser<string> = hws
    .then(comment.opt())
    .then(hws)
    .then(newline)
    .map((pairs) => pairs[1] as string)

/** A blank line: optional horizontal space, then a newline. */
const blankLine: Parser<string> = hws.then(newline).map(() => "")

/**
 * Zero or more blank and comment-only lines — what L2 consumes between items.
 * Indentation is not consumed: a blank line's spaces belong to no block, so the
 * next item's own `spaces(column)` still matches.
 */
export const trivia: Parser<string> = or(
    blankLine,
    hws.then(comment).then(hws).then(newline).map(() => ""),
).many().map((xs: string[]) => xs.join(""))
