/**
 * LC Values — the value forms of the Lapis Core Calculus.
 *
 * See _docs/theory/lc.md §2.3 for the formal specification.
 *
 *   v ::= λx:σ. t                           closure
 *       | Cᵢ(v₁, ..., vₙ)                   constructed variant (eager: fields are values)
 *       | match(pₖ)                         matched token (a value of pattern-matched type)
 *       | unfold [T] s {oⱼ → gⱼ}            codata value (lazy: seed stored, generators deferred)
 */

import type { DataType, Type } from "./types.ts"
import type { Span } from "@lapis-lang/lang-forma"

// ── Value ─────────────────────────────────────────────────────────────────────

/**
 * The free-function surface for the virtuals (compatibility exports): the
 * ladders live on the subclasses as `Value.equals`/`Value.size` — these are
 * the same-signature delegates the original API carried, so existing
 * consumers keep importing them. New code calls the methods directly.
 */

/**
 * Structural equality on data values — the virtual `Value.equals` (the
 * per-kind contracts live on the subclasses). Free-function surface.
 */
export function valueEquals(a: Value, b: Value): boolean {
    return a.equals(b)
}

/**
 * The structural size of a value — the virtual `Value.size`. Free-function
 * surface.
 */
export function valueSize(value: Value): number {
    return value.size()
}

/**
 * The root of the LC value hierarchy.
 *
 * Equality, size, and source rendering are intrinsic representation concerns
 * (the same tier as `Type.equals` and `toString` in `types.ts`), so they live
 * here as virtual methods, owned by the subclasses.
 */
export abstract class Value {
    abstract readonly kind: string

    /**
     * Structural equality on data values — the runtime `=` primitive's
     * equality on data (semantics.md §7): two values are equal when they
     * have the same constructor and equal fields, recursively.
     *
     * Scope (first cut): finite data values. Function values (closures) and
     * codata values have no structural equality: closures are code, codata
     * equality is bisimulation, and both are outside the first cut —
     * comparing a value containing one returns `false` unless it is
     * literally the same reference (identical closures ARE equal, which
     * keeps `idempotent` on a closure-valued argument well-defined at the
     * reference level). Law checking (law_checking.ts) restricts itself to
     * operations whose parameter types are data or pattern types, so its
     * comparisons observe the `VariantVal` and `TokenVal` parts.
     *
     * The base implementation is the REFERENCE rule every subclass shares
     * unless it overrides: two distinct values of kinds without structural
     * equality are unequal.
     */
    equals(other: Value): boolean {
        return this === other
    }

    /**
     * The structural size of a value: its node count (one per variant
     * constructor; tokens count as their TEXT LENGTH — the language-equation
     * reading counts per-length strings, so a token's size is the length of
     * its raw matched text).
     *
     * This is the monotone measure the ∂T shrinker minimizes (a filler is a
     * candidate only when STRICTLY smaller than the subtree it replaces) and
     * the size the certified screen's prefix is stated in (size-≤ k classes).
     * One definition keeps the two mechanisms agreeing on what "smaller" and
     * "the prefix" mean.
     *
     * The token arm: a token's size is `text.length`. The language
     * equation counts strings of exactly length n (`Nat = [0-9]+` gives
     * cₙ = 10ⁿ — 10 strings of length 1), so the certificate's c₁ counts
     * single-CHARACTER tokens; the size measure must agree or the enumeration
     * and the coefficients disagree. (The empty string matches `[^"]*`-style
     * patterns — size 0, honest.) The shrinker's contract is unaffected: a
     * shorter token is still strictly smaller than a longer one.
     *
     * The base implementation is the conservative fallback (1 — the
     * atomic-node measure); the data subclasses override with their own
     * structure's measure.
     */
    size(): number {
        return 1
    }

    /**
     * Render this value as LC source — the concrete syntax an evaluator
     * parses — or `undefined` when the value has NO valid source form.
     * The result must always re-parse (a malformed candidate would be
     * reported as a falsification the evaluator cannot even run), so a
     * value whose source form cannot be reconstructed declines rather than
     * emitting a partial render.
     *
     * This is the ROUND-TRIP judgment: the property harness's domain is
     * source strings, so plugged shrink candidates render back to source
     * and re-parse to the same value. The law checker's display renderer
     * (`law_checking.ts`) is a SEPARATE judgment — quoting tokens
     * (`Type"text"`) for readable counterexamples — and stays there.
     *
     * The base implementation declines: kinds without an LC source form
     * (closures are code, codata values are lazy generators, error
     * sentinels are not terms) return `undefined` — the caller either
     * skips this candidate or falls back to regeneration.
     */
    renderSource(): string | undefined {
        return undefined
    }

    /**
     * Render this value for DISPLAY — the law checker's counterexample
     * text: a variant renders as `Name(field, …)` recursively, a token
     * renders as `Type"text"` (quoted — the type name disambiguates two
     * pattern types whose tokens carry the same text, and the quotes make
     * whitespace/boundary characters visible), and kinds without a term
     * reading fall back to `<kind>` — a display NEVER declines where the
     * source form would.
     *
     * This is the DISPLAY judgment (the counterpart of `renderSource`'s
     * round-trip judgment): its output is human-readable LawError text
     * AND the dedup key the exhaustion sweep uses (each distinct value
     * seen once — the quoted-token form keeps two same-named pattern
     * types' tokens distinct, mirroring `TokenVal.equals`'s identity).
     * The base implementation is the `<kind>` fallback (closures are
     * code, codata values are lazy generators, error sentinels are not
     * terms — none has a term reading, all have a kind tag).
     */
    renderDisplay(): string {
        return `<${this.kind}>`
    }
}

// ── SpanClosure ───────────────────────────────────────────────────────────────

/**
 * A closure that captures the body's **input span** (not a pre-evaluated body
 * term). Used by the grammar-based evaluator (`LCEval`): the body is
 * re-evaluated on demand by re-parsing its source substring under the
 * extended environment via `_forward` — the higher-order attribute mechanism.
 *
 * `input` is the source text the span indexes into. For closures captured
 * during the main parse it is the parse input; for closures captured while
 * evaluating an operation definition (E-Op — the definition lives in the
 * `OpRegistry`, not the parse input) it is the definition source. Carrying
 * it on the closure keeps an escaping closure (e.g. an op returning a
 * function) applicable after the definition-evaluation window closes.
 */
export class SpanClosure extends Value {
    readonly kind = "closure"
    constructor(
        readonly param: string,
        readonly paramType: Type,
        readonly bodySpan: Span,
        readonly env: ValueEnv,
        /** The source text that `bodySpan` indexes into. */
        readonly input: string = "",
    ) {
        super()
    }

    /** Alias for `paramType`, for duck-typing compatibility with lang-forma's `inferValueType`. */
    get type(): Type {
        return this.paramType
    }
}

// ── Variant value ─────────────────────────────────────────────────────────────

/**
 * `Cᵢ(v₁, ..., vₙ)` — a constructed variant. Eager: fields are already values.
 */
export class VariantVal extends Value {
    readonly kind = "variantVal"
    constructor(
        readonly variantName: string,
        readonly dataType: DataType,
        readonly fields: Map<string, Value>,
    ) {
        super()
    }
    /**
     * Structural equality: same constructor, same carrier NAME, equal fields
     * (same key sets, recursively equal values). The carrier's NAME — not
     * its instance identity — is the comparison: values evaluated under
     * distinct registries that declare the same-named type shape are
     * structurally equal (the law checker renders and compares rendered
     * source; the name is the structural identity the evaluator's instances
     * are checked against).
     */
    override equals(other: Value): boolean {
        if (this === other) return true
        return other instanceof VariantVal &&
            this.variantName === other.variantName &&
            this.dataType.name === other.dataType.name &&
            fieldsEqual(this.fields, other.fields)
    }

    /** The node count: 1 (this constructor) + each field's size. */
    override size(): number {
        let size = 1
        for (const field of this.fields.values()) size += field.size()
        return size
    }

    /**
     * LC source form: `Name(field, …)` — recursively through the fields;
     * a field subtree with no source form declines the WHOLE candidate
     * (decline propagates: a partial render is never emitted). Field order
     * follows the value's construction order (`fields` is insertion-ordered
     * by field declaration).
     */
    override renderSource(): string | undefined {
        const fields: string[] = []
        for (const field of this.fields.values()) {
            const rendered = field.renderSource()
            if (rendered === undefined) return undefined
            fields.push(rendered)
        }
        return fields.length > 0
            ? `${this.variantName}(${fields.join(", ")})`
            : `${this.variantName}()`
    }

    /**
     * Display form: `Name(field, …)` recursively (fields in construction
     * order). A non-displayable field falls back to its `<kind>` tag —
     * display never declines (the LawError text must always be readable).
     */
    override renderDisplay(): string {
        const fields = [...this.fields.values()].map((f) => f.renderDisplay())
        return fields.length > 0
            ? `${this.variantName}(${fields.join(", ")})`
            : `${this.variantName}()`
    }
}

// ── Token value ───────────────────────────────────────────────────────────────

/**
 * `match(pₖ)` — a matched token: the sole inhabitant of a pattern-matched
 * data type (`PatternDataType`). The raw matched text IS the value — there is
 * no structure beneath it (lc.md §2.1: the token is introduced by the lexer,
 * an axiom of the operational semantics, with no evaluation rule producing
 * it). In this grammar-based evaluator the "lexer" is the term grammar
 * itself: an atom whose name resolves to a registered `PatternDataType`
 * parses the matched text and yields the token as a value.
 *
 * Two tokens are equal (structurally, like `equals`) iff they inhabit
 * the SAME pattern type AND their raw text is equal. The type name is part
 * of the identity because cross-type token collisions are plausible (two
 * pattern types can share the token atom's name-lexed form) and a law's
 * schema operands range over a typed carrier — a `PatA` token and a `PatB`
 * token with identical text are distinct values, as distinct as two variants
 * of different data types with the same constructor shape.
 */
export class TokenVal extends Value {
    readonly kind = "tokenVal"
    constructor(
        /** The pattern-matched type this token inhabits. */
        readonly dataTypeName: string,
        /** The raw matched text — the token's entire content. */
        readonly text: string,
    ) {
        super()
    }

    /**
     * Two tokens are equal (structurally, like `equals`) iff they
     * inhabit the SAME pattern type AND their raw text is equal. The type
     * name is part of the identity because cross-type token collisions are
     * plausible (two pattern types can share the token atom's name-lexed
     * form) and a law's schema operands range over a typed carrier — a
     * `PatA` token and a `PatB` token with identical text are distinct
     * values, as distinct as two variants of different data types with the
     * same constructor shape.
     */
    override equals(other: Value): boolean {
        if (this === other) return true
        return other instanceof TokenVal &&
            this.dataTypeName === other.dataTypeName &&
            this.text === other.text
    }

    /** A token's size is its TEXT LENGTH (the per-length-class reading). */
    override size(): number {
        return this.text.length
    }

    /**
     * LC source form: the bare pattern-type name — the evaluator's
     * `patternTokenProd` emits `matchedToken(name, name)`, so the text IS
     * the name-lexed source. `Pat("x")` is NOT LC syntax; a token whose
     * text deviates from its type name (possible only by direct
     * construction, never by evaluation) has no source form and declines.
     */
    override renderSource(): string | undefined {
        return this.text === this.dataTypeName ? this.dataTypeName : undefined
    }

    /**
     * Display form: `Type"text"` (quoted). The type name disambiguates
     * two pattern types whose tokens carry the same text, and the quotes
     * make whitespace/boundary characters visible — a counterexample must
     * be readable unambiguously (mirrors `equals`'s type+text identity).
     */
    override renderDisplay(): string {
        return `${this.dataTypeName}(${JSON.stringify(this.text)})`
    }
}

// ── Value environment ─────────────────────────────────────────────────────────

/**
 * The value environment `ρ` — maps names to values.
 * Used during evaluation (the inherited attribute for the evaluator).
 */
export class ValueEnv {
    private readonly bindings: Map<string, Value>

    constructor(entries?: Map<string, Value>) {
        this.bindings = entries ?? new Map()
    }

    lookup(name: string): Value | undefined {
        return this.bindings.get(name)
    }

    extend(name: string, value: Value): ValueEnv {
        const next = new Map(this.bindings)
        next.set(name, value)
        return new ValueEnv(next)
    }

    /** Create a ValueEnv from a raw Map. */
    static from(map: Map<string, Value>): ValueEnv {
        return new ValueEnv(map)
    }

    /** Export to a raw Map. */
    toMap(): Map<string, Value> {
        return new Map(this.bindings)
    }
}

// ── Structural value equality ─────────────────────────────────────────────────

/**
 * Equality is the virtual `Value.equals` (documented there — the closure
 * reference rule, the token type+text identity, the VariantVal contract
 * all live on the subclasses). Field-wise equality on a variant's fields
 * (same key sets, recursively equal values).
 */
function fieldsEqual(a: Map<string, Value>, b: Map<string, Value>): boolean {
    if (a.size !== b.size) return false
    for (const [name, value] of a) {
        const other = b.get(name)
        if (other === undefined || !value.equals(other)) return false
    }
    return true
}
