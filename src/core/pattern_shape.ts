/**
 * The pattern-language's structural carrier shape — the ONE dependency edge
 * between the type universe and the pattern language (type-only, erased at
 * runtime, so `types.ts`'s value import of `patternToString` from
 * `pattern_lang.ts` closes no cycle).
 *
 * The pattern language reads only a carrier's NAME (memo keys, reference
 * identity) and its DECLARED PATTERNS (the union language) — it never
 * dispatches on the carrier's class or walks its variants. Declaring that
 * structural contract here lets `DataType` (whose members ARE pattern
 * constructors — the one carrier shape since the absorption sweep) satisfy
 * the language's entry points without a class edge in either direction.
 */
import type { PatternAST } from "./pattern_lang.ts"

export interface PatternTypeShape {
    /** The carrier's name — memo keys and `<T>` reference identity. */
    readonly name: string
    /** The carrier's declared patterns — the union language. */
    readonly patterns: readonly PatternAST[]
}
