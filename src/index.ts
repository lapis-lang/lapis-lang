/**
 * Lapis — public exports.
 *
 * The Lapis Core Calculus (F_{<:μν}) lives under `src/core/`; the surface
 * language's pipeline lives under `src/surface/`. The two are deliberately
 * different shapes — a one-pass executable grammar for the core, parse-to-AST
 * plus tree-consuming passes for the surface — and `src/surface/index.ts`
 * explains why.
 *
 * See `_docs/theory/lc.md` for the core calculus and
 * `_docs/theory/surface-grammar.md` for the surface grammar.
 */

// Lapis Core Calculus (F_{<:μν}) — the executable spec
export * from "./core/index.ts"

// The surface language: grammar, name resolution, elaboration
export * from "./surface/index.ts"
