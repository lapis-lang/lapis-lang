/**
 * LC Law Testing — the property-based law harness (forAll over a grammar),
 * with ∂T-based structural shrinking.
 *
 * See _docs/theory/law-testing.md (the specification) and _docs/theory/
 * type-algebra.md §4 (one-hole contexts). The harness pattern: a law is a
 * universally-quantified claim over an operand space; checking it generatively
 * means `forAll` over a grammar-rooted value generator whose samples are the
 * law's intended domain.
 *
 * The rejection-quality contract is unchanged from the test-local harness
 * this module promotes: passing runs are **evidence, never proof** (the
 * `asserted` tier at best); a failing run throws `PropertyFailure` with the
 * shrunk minimal counterexample. What this module adds is the SHRINKER:
 *
 * lang-forma's `GrammarGenerator` shrinks by re-generating at shallower
 * depths — structurally smaller, but derived from the GENERATOR, never from
 * the failing value. The ∂T shrinker derives candidates from the failing
 * VALUE's own structure (McBride 2001): the contexts of a value are its
 * holes — positions where a smaller filler can be plugged — so the
 * counterexample shrinks along the actual value's structure, monotone
 * toward a minimal falsifier. Fallback: a counterexample that does not
 * evaluate to a structured value (a token, a closure, a parse hole)
 * delegates to the regeneration strategy — the ∂T path is a strict
 * upgrade, never a regression of coverage.
 */

import {
    type GeneratorOptions,
    type Grammar,
    GrammarGenerator,
    type GrammarShape,
} from "@lapis-lang/lang-forma"

import { typeAlgebra } from "./type_algebra.ts"
import { type EvalTerm, samplesFor } from "./law_checking.ts"
import { type Value, ValueEnv, VariantVal } from "./values.ts"
import { DataType, type Type } from "./types.ts"

// ── Context paths ─────────────────────────────────────────────────────────────

/**
 * A one-hole context of a CONCRETE value: the path of
 * `(variantName, fieldName)` steps from the root to a punched field.
 *
 * The type-level derivative (`ContextSpec`) enumerates which steps are
 * admissible at each node; a path is valid iff every step descends through
 * a spec's hole. For a single-recursive-field carrier (Nat, List), a value of
 * depth n admits exactly n paths — each level's recursive field is one
 * context; leaf-shaped nodes (no fields, no hole) contribute none. Branching
 * carriers (two recursive fields in one variant) have one path per recursive
 * FIELD occurrence, so a 5-node binary tree of 3 leaves has 4 paths.
 */
export type ContextPath = readonly (readonly [string, string])[]

/**
 * Enumerate every admissible context path of a structured value.
 *
 * A path is admissible when each step lands on a field the carrier's
 * derivative marks as a hole position — the walk follows the same rules the
 * type-level derivative states, but over the actual value tree. The walk is
 * the value-level mirror of the derivative's structural recursion: at each
 * node, the specs name the punchable fields; a hole type that is itself a
 * data type opens the chain rule (descent continues inside the field's
 * subtree, per its own derivative).
 */
export function contextPaths(value: VariantVal): ContextPath[] {
    const paths: ContextPath[] = []

    const walk = (node: VariantVal, carrier: DataType, prefix: ContextPath): void => {
        const index = typeAlgebra.specFor(carrier)
        for (const [fieldName, fieldValue] of node.fields) {
            const spec = index.get(node.variantName)?.get(fieldName)
            if (spec === undefined) continue
            // This field is a punchable position: the path here (prefix +
            // this step) is itself a context — replace the whole field.
            const here: ContextPath = [...prefix, [node.variantName, fieldName] as const]
            paths.push(here)
            // The chain rule, one level — driven by the spec's data edge
            // (the algebra's derivative for the hole's own structure, the
            // rule as DATA): the descent continues INSIDE the field's
            // subtree exactly when the edge is defined AND the subtree's
            // carrier is the edge's hole carrier. The edge IS the hole
            // type's derivative (memoized on the spec), so the walk consults
            // the same spec objects the algebra serves — no independent
            // re-derivation. Identity comparison: the evaluator stamps every
            // value's `dataType` from the same registry the carrier came
            // from, so reference equality is exact and cheaper than name
            // matching (two distinct DataType instances can share a name).
            // Rose-shaped recursion (a Family under a list-like field)
            // differentiates through here only one level deep — the
            // expressiveness boundary type-algebra.md §4.3 states.
            const edge = spec.derivative()
            if (
                fieldValue instanceof VariantVal && edge !== undefined &&
                fieldValue.dataType === spec.holeType
            ) {
                walk(fieldValue, fieldValue.dataType, here)
            }
        }
    }

    // The carrier the value inhabits is recorded on the value itself.
    walk(value, value.dataType, [])
    return paths
}

/**
 * Plug a filler into a context path: rebuild the spine from the root with
 * the filler substituted at the punched position. Pure tree surgery — no
 * evaluation: values are eager `VariantVal`s, so reconstruction is direct
 * field-map rebuilding.
 *
 * Returns `undefined` when the path does not match the value's shape (a
 * caller bug surfaced honestly, not a silent wrong-value).
 */
export function plug(
    value: VariantVal,
    path: ContextPath,
    filler: VariantVal,
): VariantVal | undefined {
    if (path.length === 0) return filler
    const [[variantName, fieldName], ...rest] = path
    if (value.variantName !== variantName) return undefined
    const fieldValue = value.fields.get(fieldName!)
    if (fieldValue === undefined || !(fieldValue instanceof VariantVal)) return undefined
    const patched = plug(fieldValue, rest, filler)
    if (patched === undefined) return undefined
    const fields = new Map(value.fields)
    fields.set(fieldName!, patched)
    return new VariantVal(value.variantName, value.dataType, fields)
}

/**
 * Render a value as LC source — the virtual `Value.renderSource` (the
 * per-kind arms live on the subclasses). Free-function surface: the harness's
 * domain is source strings, so plugged candidates render back to the concrete
 * syntax the evaluator parses; `undefined` when the value has no valid
 * source form (the result must always re-parse).
 */
export function renderValue(value: Value): string | undefined {
    return value.renderSource()
}

// ── The ∂T shrinker ───────────────────────────────────────────────────────────

/**
 * The shrinker's sample depth for filler generation (the screen's residual
 * budget — small bounded spaces keep shrink candidate enumeration cheap;
 * a filler needs only to be a valid, strictly smaller inhabitant).
 */
const SHRINK_SAMPLE_DEPTH = 2

/** Options for `DerivativeGenerator`. */
export interface DerivativeGeneratorOptions {
    /** The evaluation primitive (parse + evaluate LC source). */
    evalOf: EvalTerm
    /** The operand carrier the generator's samples inhabit. */
    carrier: DataType
    /** How deep the carrier's sample vocabulary reaches (the fillers' budget). */
    sampleDepth?: number
}

/**
 * A grammar-aware generator with ∂T-based structural shrinking.
 *
 * `sample` and `forAll` are inherited from `GrammarGenerator` untouched;
 * only `shrink` changes strategy. On a counterexample:
 *
 * 1. Parse/evaluate the counterexample source to a structured value (a
 *    `VariantVal` of the carrier's family). Anything else — a token, a
 *    closure, a hole — delegates to `super.shrink` (the regeneration
 *    fallback): the ∂T path strictly upgrades, never regresses.
 * 2. Enumerate the value's context paths (the value-level ∂T).
 * 3. For each path × each strictly-smaller filler, render the plugged
 *    candidate. The list is ordered: shallower paths first (a spine shrink
 *    is the strongest single reduction), fillers smallest first.
 *
 * The result stays within the `ValueGenerator<string>` contract —
 * lang-forma's property runner consumes `shrink` exactly as before, so
 * `forAll`/`PropertyFailure`/seed-reproducibility semantics are unchanged.
 */
export class DerivativeGenerator<S extends GrammarShape = GrammarShape>
    extends GrammarGenerator<string, S> {
    private readonly evalOf: EvalTerm
    private readonly carrier: DataType
    private readonly sampleDepth: number
    /**
     * Cross-call cache of the SAMPLED vocabulary per hole type. `samplesFor`
     * is a pure function of (holeType, depth, evalOf) — the evaluator-driven
     * sampling re-parses and re-constructs the same bounded space every call
     * (~1.2ms per call, once per shrink before caching; the property runner
     * calls `shrink` many times per counterexample). Only the REUSE part of
     * a filler pool varies per counterexample, so that part stays per-call
     * (see `fillers`). Bounded: one entry per distinct hole type seen.
     */
    private readonly sampleCache = new Map<DataType, readonly VariantVal[]>()

    constructor(
        grammar: Grammar<S>,
        options: GeneratorOptions,
        deps: DerivativeGeneratorOptions,
    ) {
        super(grammar, () => grammar.start(), options)
        this.evalOf = deps.evalOf
        this.carrier = deps.carrier
        this.sampleDepth = deps.sampleDepth ?? SHRINK_SAMPLE_DEPTH
    }

    override shrink(source: string): string[] {
        // Parse the counterexample into a structured value. Failure shapes:
        // an empty forest (did not parse), an error sentinel (evaluation
        // broke), a non-structured value (token/closure), or a value whose
        // carrier differs from the generator's — all fall back to
        // regeneration.
        const value = this.evalOf(source, new ValueEnv())[0]
        if (!(value instanceof VariantVal)) return super.shrink(source)
        // The value's carrier must be the generator's carrier: contextPaths
        // walks with the VALUE's stamped type while `holeTypeAt` resolves
        // from this.carrier — a value evaluated under a different registry
        // or family would produce paths resolved against the wrong type
        // (fillers of the wrong space, plugs of the wrong shape). Identity
        // check: same registry, same instance, or no ∂T path is trusted.
        if (value.dataType !== this.carrier) return super.shrink(source)
        const paths = contextPaths(value)

        // Prefetch the reuse pool once: the failing value's own subvalues
        // (same-type values already paid for — no generation needed).
        const pool: VariantVal[] = []
        const visit = (node: VariantVal): void => {
            pool.push(node)
            for (const field of node.fields.values()) {
                if (field instanceof VariantVal) visit(field)
            }
        }
        visit(value)

        const candidates: string[] = []
        const seen = new Set<string>()
        // Filler pools are assembled per hole type ONCE per shrink call: every
        // path through the same carrier resolves to the same holeType, and
        // re-sampling per path would re-run the evaluator-driven sampler once
        // per path (measured: ~55× the regeneration baseline on a depth-20
        // Nat — the dominant cost). The sampled vocabulary itself is cached
        // across calls (`sampleCache`); only the reuse pool differs per
        // counterexample, so the per-call work is pool assembly + plug.
        const fillersByHoleType = new Map<DataType, readonly VariantVal[]>()
        // Shallower paths first: a context closer to the root replaces a
        // LARGER subtree, so its fillers are the strongest reductions. Within
        // a path, fillers ascend by size (smallest first).
        const orderedPaths = [...paths].sort((a, b) => a.length - b.length)
        for (const path of orderedPaths) {
            const subtree = subtreeAt(value, path)
            if (subtree === undefined) continue
            // The hole's type: consult the carrier's spec index at the LAST
            // step (the walk into nested fields needs the nested carrier's
            // derivative — the chain rule's value-level reading).
            const holeType = this.holeTypeAt(path)
            if (!(holeType instanceof DataType)) continue
            const size = subtree.size()
            let holeFillers = fillersByHoleType.get(holeType)
            if (holeFillers === undefined) {
                holeFillers = this.fillers(holeType, pool)
                fillersByHoleType.set(holeType, holeFillers)
            }
            for (const filler of holeFillers) {
                // Strictly smaller than the subtree at THIS hole — the
                // monotone filter is per-path (the pool itself is not).
                if (filler.size() >= size) continue
                const patched = plug(value, path, filler)
                if (patched === undefined) continue
                // Round-trip-checked render: a candidate whose subtree is
                // not renderable (a closure- or codata-valued field, a
                // deviant token) declines — NEVER emitted as malformed
                // source the evaluator would fail on (an unparseable
                // candidate would surface as a non-evaluation, i.e. a fake
                // falsification the runner reports).
                const rendered = patched.renderSource()
                if (rendered === undefined) continue
                if (rendered === source) continue
                if (seen.has(rendered)) continue
                seen.add(rendered)
                candidates.push(rendered)
            }
        }
        // A counterexample with no admissible (path, filler) pair — an
        // already-minimal value, or holes with no vocabulary — falls back to
        // regeneration so the runner still gets candidates to try.
        if (candidates.length === 0) return super.shrink(source)
        return candidates
    }

    /**
     * The hole's type at a context path: resolved by walking the carrier's
     * spec index — step i consults the spec for the CURRENT carrier (the
     * carrier the walk has descended into), and a spec whose holeType is a
     * data type different from the current carrier opens the chain rule
     * (the next carrier is the hole's type). The indexes come from the
     * algebra's memoized `specFor` (identity-keyed per carrier): the walk
     * consults the SAME spec objects `contextPaths` descended, not a
     * per-step rebuild.
     */
    private holeTypeAt(path: ContextPath): Type | undefined {
        let carrier: DataType = this.carrier
        for (const [variantName, fieldName] of path) {
            const spec = typeAlgebra.specFor(carrier).get(variantName)?.get(fieldName)
            if (spec === undefined) return undefined
            // The data edge IS the gate: it is defined exactly when the hole
            // type has punchable structure (a DataType), so consulting it
            // (memoized on the spec) is what licenses the descent — the walk
            // and the edge cannot diverge (the edge is computed from the
            // hole type by the algebra, the single derivation both walkers
            // read).
            const edge = spec.derivative()
            if (edge === undefined) return undefined
            const next = spec.holeType
            if (!(next instanceof DataType)) return undefined
            carrier = next
        }
        return carrier
    }

    /**
     * The filler pool for a hole type: the hole type's cached sampled
     * vocabulary (shallower samples first) plus the reuse pool (the failing
     * value's own same-typed subvalues), deduped. NOT filtered by the
     * subtree size — that filter is applied per hole (the pool serves every
     * path of a given hole type, and each hole's subtree size differs).
     */
    private fillers(holeType: Type, pool: readonly VariantVal[]): readonly VariantVal[] {
        if (!(holeType instanceof DataType)) return []
        let samples = this.sampleCache.get(holeType)
        if (samples === undefined) {
            samples = samplesFor(holeType, this.sampleDepth, this.evalOf)
            this.sampleCache.set(holeType, samples)
        }
        const out: VariantVal[] = []
        const seen = new Set<string>()
        const push = (v: VariantVal): void => {
            // Unrenderable fillers (a closure- or codata-valued subvalue) are
            // excluded HERE: a filler that cannot render can never produce a
            // valid candidate, so keeping it would only waste plug+render
            // work per path.
            const key = v.renderSource()
            if (key === undefined) return
            if (seen.has(key)) return
            seen.add(key)
            out.push(v)
        }
        for (const sample of samples) push(sample)
        for (const reused of pool) {
            if (reuseAdmissible(reused, holeType)) push(reused)
        }
        return out
    }
}

/**
 * Whether a pooled value may serve as a filler for a hole of the given
 * type: same data type identity (the plugged candidate must stay
 * well-typed — subtyping is NOT admitted here; the law instances are
 * well-typed by construction and the shrinker must not widen that).
 */
function reuseAdmissible(candidate: VariantVal, holeType: Type): boolean {
    return holeType instanceof DataType && candidate.dataType === holeType
}

/**
 * The subtree at a context path (the value the hole would replace).
 * `undefined` when the path does not match the value's shape.
 */
function subtreeAt(value: VariantVal, path: ContextPath): VariantVal | undefined {
    let node: VariantVal = value
    for (const [variantName, fieldName] of path) {
        if (node.variantName !== variantName) return undefined
        const field = node.fields.get(fieldName!)
        if (field === undefined || !(field instanceof VariantVal)) return undefined
        node = field
    }
    return node
}
