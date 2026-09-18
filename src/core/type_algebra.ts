/**
 * LC Type Algebra — derivatives (one-hole contexts) and coefficients
 * (certified screen coverage) of regular types.
 *
 * See _docs/theory/type-algebra.md §4 (McBride 2001: the formal derivative
 * of a regular type is its type of one-hole contexts) and §3 (coefficients:
 * certified screen coverage).
 *
 * Two readings of the SAME type equation share this module — the "one
 * module, three readings" consolidation (counting lives in law_checking.ts
 * as `finiteInhabitants`, contexts and coefficients here):
 *
 * - **∂T (§4)** — `derivative(type)`: the one-hole contexts of T's values,
 *   by implicit differentiation. Lapis's `Type` AST already spells the
 *   μ-bound — a recursive field (`Field.isRecursive`) IS an occurrence of
 *   the recursion variable — so differentiating the μ-equation directly
 *   reduces to ordinary structural recursion over `Type` that never follows
 *   recursive fields (that occurrence is the hole). No equation solving, no
 *   quotient rule:
 *
 *     ∂a const = 0                        (no a inside → no contexts)
 *     ∂a (F + G) = ∂a F + ∂a G            (sum rule — the variant set)
 *     ∂a (F · G) = ∂a F · G + F · ∂a G    (Leibniz — the variant's fields)
 *     ∂a a = 1                            (the hole itself)
 *
 * - **Coefficients (§3)** — `coefficients(type, k)`: the truncated GF
 *   reading of the same equations. Size = node count (constructor nodes;
 *   the same measure `valueSize` uses), so the certificate and the ∂T
 *   shrinker agree on what "smaller" means. Each type contributes one
 *   equation, each recursive field is one occurrence of the recursion
 *   variable, and the system is solved by truncated fixpoint iteration —
 *   never by solving for a closed form. The GF taxonomy falls out of the
 *   same equations: chain types (Nat, List) satisfy linear recurrences
 *   (their GFs are rational — Chomsky–Schützenberger's territory for
 *   pattern types, once encodings are declared); branching μ-types satisfy
 *   quadratic recurrences (Tree = Leaf + Node(T,T) is the Catalan series
 *   $T = 1 + x T^2$). One mechanism covers both: no closed forms, no
 *   per-type case analysis.
 *
 * The derivative never diverges: the only potentially-infinite unfolding of
 * a μ-type is through its recursive fields, and those are exactly the
 * positions the traversal stops at. The coefficient fixpoint converges:
 * each iteration round the minimal nonzero degree of a productive system
 * advances, so at most k+1 rounds; cycles that never become productive
 * converge to zero vectors (honest: those variants contribute no
 * inhabitants).
 *
 * Boundaries (type-algebra.md §4.3):
 * - **Chain rule, depth ≤ 1**: a field of another data type `B` yields a
 *   context whose hole sits *inside* that field's subtree — punching it
 *   consults `derivative(B)` at the next path step (the chain rule
 *   $\partial_a F(G(a)) = \partial_a G \cdot \partial_G F$, read one level
 *   at a time). Recursion under a *list-like* field (rose trees,
 *   $R = a \cdot L(R)$) is only partially covered: each type's derivative
 *   is taken w.r.t. its own μ-bound, so a hole in R nested through L is
 *   beyond this first cut — `Field.isRecursive` marks direct Family
 *   positions only, and extending nested-recursion expressiveness is a
 *   separate decision.
 * - **Intersections** are not a semiring operation: an intersection-headed
 *   carrier is a typed rejection (the screen treats intersected carriers as
 *   unscreenable too — consistent), and an intersection-typed FIELD
 *   contributes no context (the same unsampleable rule as functions).
 * - **Function-typed fields** have exponential generating functions; they
 *   contribute no context (the screen's existing rule, not weakened).
 * - **Codata (ν)** is the coalgebraic dual — untouched; bounded observation
 *   stays bounded. The same holds for coefficients: a ν-typed carrier or
 *   field is a typed rejection (codata's generating function is not a
 *   counting object — bounded observation, not bounded construction).
 */

import { CodataType, DataType, IntersectionType, PatternDataType, type Type } from "./types.ts"
import { setRegistryHook, typeUnionCounts } from "./pattern_lang.ts"

/**
 * The type-reference environment's lookup hook, set by the caller (the law
 * checker wires it to the type registry). `coefficients` is pure w.r.t. this
 * module — the hook is process-global because the counting needs the FULL
 * registry (a `<T>` reference may name any declared pattern type, not just
 * the carrier), and threading the registry through every `coefficients` call
 * site would change their signatures for one consumer (the pattern arm).
 *
 * The DEFAULT hook reads the pattern arm self-consistently: a type reference
 * `<T>` with no installed registry is a typed rejection — but a pattern
 * FIELD inside a data carrier needs its own type's counting, which requires
 * NO registry (the field's pattern ASTs are on the field type itself). The
 * hook only matters for type REFERENCES inside patterns (`<T>`); a pattern
 * language without references works without any hook.
 */
let patternLookup: (name: string) => PatternDataType | undefined = () => {
    throw new TypeError(
        "a pattern language type reference <T> requires the registry hook — " +
            "install it via setPatternLookup (the law checker wires the type registry)",
    )
}

/**
 * Install the type-reference lookup hook (called once at law-checking setup).
 * The prior hook is returned for restoration in tests.
 */
export function setPatternLookup(
    lookup: (name: string) => PatternDataType | undefined,
): (name: string) => PatternDataType | undefined {
    const prior = patternLookup
    patternLookup = lookup
    setRegistryHook(lookup)
    return prior
}

// ── Context specifications ───────────────────────────────────────────────────

/**
 * A one-hole context shape: the specification of a position in `T`'s
 * structure that can be punched, together with the surroundings the hole
 * leaves behind (Leibniz's "everything except the hole").
 *
 * This is a *description*, not a synthesized context type: every consumer —
 * structural shrinking now; `old`/paramorphism typing and live-observation
 * evidence typing later — needs which positions are punchable and what
 * surrounds them. The closed forms the literature names for specific shapes
 * (the list zipper ∂L = L², the tree context $T^2 \cdot L(2aT)$) are
 * derivable from these specs; they are a rendering choice, not the
 * representation.
 */
export interface ContextSpec {
    /** The variant whose field is punched. */
    variantName: string
    /** The punched field's name. */
    fieldName: string
    /**
     * The hole's type — what plugs into it. For a direct recursive field
     * this is the carrier itself; for a field of another data type this is
     * that field's type (the chain rule's one-level reading: punching the
     * hole descends into the field's own structure).
     */
    holeType: Type
    /** The other fields' types forming the surroundings, in field order. */
    surroundTypes: Type[]
}

// ── The derivative ───────────────────────────────────────────────────────────

/**
 * The derivative of a regular μ-type: the shapes of all one-hole contexts
 * of its values.
 *
 * For each variant, each field is a potential hole position:
 *
 * - A **recursive field** is the μ-bound spelled in the AST — punching it
 *   is the classic zipper step (the hole takes a value of the carrier
 *   itself; the surroundings are the variant's other fields).
 * - A **field of another data type** opens the chain rule: the hole may sit
 *   deeper, inside that field's own structure, so the spec's `holeType` is
 *   the field's type and the punch is resolved by consulting that type's
 *   derivative at the next path step.
 * - **Function-typed, `Any`-typed, `Nothing`-typed, token, and
 *   pattern-typed fields** contribute nothing: no hole vocabulary (the same
 *   unsampleable rule the residual screen applies).
 *
 * Parent-chain variants are covered via `allVariants()` (comb inheritance),
 * matching how values are constructed and how the sampler sweeps.
 *
 * The result is ordered variant-by-variant, field-by-field; the order is
 * deterministic (it follows the declaration order) so callers can rely on
 * reproducible shrink candidate orderings.
 *
 * @throws TypeError when the carrier is headed by an intersection type
 * (intersections are not a semiring operation — type-algebra.md §4.3).
 */
export function derivative(type: DataType): ContextSpec[] {
    if (type instanceof IntersectionType) {
        throw new TypeError(
            `derivative(${type.name}): intersection types are not a semiring ` +
                `operation — no derivative is defined (type-algebra.md §4.3)`,
        )
    }
    const specs: ContextSpec[] = []
    for (const variant of type.allVariants()) {
        for (const field of variant.fields) {
            const fieldType = field.type
            if (field.isRecursive) {
                // The μ-bound occurrence: the hole takes a carrier value
                // (the classic zipper step at this variant).
                specs.push({
                    variantName: variant.name,
                    fieldName: field.name,
                    holeType: type,
                    surroundTypes: variant.fields
                        .filter((f) => f !== field)
                        .map((f) => f.type),
                })
            } else if (fieldType instanceof DataType) {
                // Chain rule, one level: the hole may sit inside the field's
                // own structure — `holeType` names where the descent goes.
                // (The field itself can also BE the hole when the punch
                // replaces the whole field value; that whole-field case is
                // covered by this same spec — a context whose hole type is
                // the field's type admits both replace-whole and
                // descend-inside fillers at the value layer.)
                specs.push({
                    variantName: variant.name,
                    fieldName: field.name,
                    holeType: fieldType,
                    surroundTypes: variant.fields
                        .filter((f) => f !== field)
                        .map((f) => f.type),
                })
            } // Function-typed, Any-typed, Nothing-typed, Token-typed, and
            // pattern-typed fields: no finite sample vocabulary or no
            // structure to punch — no context (type-algebra.md §4.3).
        }
    }
    return specs
}

// ── Coefficients: certified screen coverage (type-algebra.md §3) ─────────────

/**
 * The saturating coefficient ceiling. A count at or past this ceiling is
 * reported AS the ceiling: the arithmetic stays within the exact-integer
 * range, callers compare `>=`, never `===`, and a prefix is certified only
 * up to where the ceiling cuts it. Declared encodings (fixed encoding
 * families like binary64) bring counts like 2⁶⁴ — far past the exact
 * range — so saturation is the arithmetic's contract, not an edge case.
 */
export const MAX_COEFFICIENT = 2 ** 53

/**
 * A type's truncated generating function: the coefficient list
 * `[c₀, c₁, ..., cₖ]` where `cₙ` counts the inhabitants of size n
 * (size = constructor-node count — the same measure `valueSize` uses).
 * Counts are saturated at `MAX_COEFFICIENT`.
 */
export type Coefficients = readonly number[]

/** Saturating addition: past the ceiling the exact value no longer matters. */
function satAdd(a: number, b: number): number {
    const sum = a + b
    return sum > MAX_COEFFICIENT ? MAX_COEFFICIENT : sum
}

/** Saturating multiplication: 0 annihilates; the ceiling caps the product. */
function satMul(a: number, b: number): number {
    if (a === 0 || b === 0) return 0
    if (a >= MAX_COEFFICIENT || b >= MAX_COEFFICIENT) return MAX_COEFFICIENT
    const product = a * b
    return product > MAX_COEFFICIENT ? MAX_COEFFICIENT : product
}

/**
 * Convolve two saturated coefficient lists, truncating to degree `k`:
 * the generating-function PRODUCT (a field's contribution multiplies the
 * surroundings'). Degrees past either input's own truncation read as 0.
 */
function convolve(f: Coefficients, g: Coefficients, k: number): number[] {
    const out = new Array<number>(k + 1).fill(0)
    for (let n = 0; n <= k; n++) {
        let sum = 0
        for (let i = 0; i <= n; i++) {
            const fi = f[i] ?? 0
            const gi = g[n - i] ?? 0
            sum = satAdd(sum, satMul(fi, gi))
        }
        out[n] = sum
    }
    return out
}

/**
 * The `x · G(x)` shift: one constructor node multiplies the GF by x —
 * the coefficient list shifts up one degree (cₙ ↦ cₙ₋₁). Degrees past the
 * input's own truncate read as 0 (a short list — e.g. a nullary variant's
 * unit — is implicitly zero-padded to the full degree).
 */
function shiftByX(coeffs: Coefficients, k: number): number[] {
    const out = new Array<number>(k + 1).fill(0)
    for (let n = 1; n <= k; n++) out[n] = coeffs[n - 1] ?? 0
    return out
}

/** The zero polynomial up to degree k. */
function zeroUpTo(k: number): number[] {
    return new Array<number>(k + 1).fill(0)
}

/**
 * The coefficient reading of ONE field's generating function, against the
 * current iteration state.
 *
 * - A **recursive field** is the μ-bound occurrence — its GF is the
 *   CARRIER's current approximation (the fixpoint's self-reference, never
 *   unfolded). This holds for inherited variants too: a parent-chain
 *   variant's recursive field is declared with the PARENT's type, but the
 *   sampler draws its fillers from the carrier's own space
 *   (`samplesFor(type, depth − 1)`), so the comb's algebra is the subtype
 *   carrier — the same reading `derivative` applies (a comb's hole type is
 *   the carrier it was taken of).
 * - A **data field** reads the field type's current approximation (mutual
 *   systems advance together).
 * - A **pattern field** is the declared fallback (the singleton token —
 *   one size-1 inhabitant).
 * - Every other field type contributes the zero polynomial (the same
 *   unsampleable rule the screen's `construct` and `screenableDomain`
 *   apply — function/`Any`/`Nothing`/token/intersection-typed fields have
 *   no finite vocabulary).
 */
function fieldGF(
    field: { type: Type; isRecursive: boolean },
    k: number,
    current: GFState,
    carrier: DataType,
): Coefficients {
    if (field.isRecursive) return current.currentFor(carrier, k)
    const fieldType = field.type
    if (fieldType instanceof DataType) return current.currentFor(fieldType, k)
    if (fieldType instanceof PatternDataType) {
        // The language-equation reading: the field's GF is the
        // pattern type's own counting — the UNION of its variants'
        // languages (variants may overlap — `a` and `a?` both hold "a" —
        // so the counts read off the merged string set, not the per-
        // variant sum). With tokens sized by TEXT LENGTH (`valueSize`'s
        // token arm), this matches the enumeration's per-length classes
        // exactly.
        return typeUnionCounts(fieldType, k)
    }
    return zeroUpTo(k)
}

/**
 * The iteration state: every type's current coefficient approximation,
 * iterated in lockstep. All equations of the (possibly mutually recursive)
 * system are solved to the same degree together — a round recomputes each
 * type's coefficients from the others' CURRENT approximations (recursive
 * fields read the carrier's previous round, never unfolded, so recursion
 * terminates by construction), so the minimal nonzero degree of a
 * productive system advances every round. At most k+1 productive rounds
 * exist (inhabitants have positive size); unproductive cycles converge to
 * zero vectors within the same bound.
 */
class GFState {
    private readonly memo = new Map<DataType, number[]>()

    constructor(private readonly system: Set<DataType>) {}

    /** A system member's CURRENT approximation (never triggers a solve). */
    currentFor(type: DataType, k: number): Coefficients {
        return this.memo.get(type) ?? zeroUpTo(k)
    }

    getFor(type: DataType, k: number): Coefficients {
        const cached = this.memo.get(type)
        if (cached && cached.length - 1 >= k) return cached
        // Every member starts at the zero vector: the equations read each
        // other's PREVIOUS round through `currentFor`, so a round never
        // re-enters the solver (the fixpoint's self-reference is the memo,
        // not the call stack).
        for (const member of this.system) {
            if (!this.memo.has(member)) this.memo.set(member, zeroUpTo(k))
        }
        // At most k+1 productive rounds (inhabitants have positive size);
        // one extra round lets an unproductive cycle settle.
        for (let round = 0; round <= k + 1; round++) {
            let changed = false
            const updates = new Map<DataType, number[]>()
            for (const member of this.system) {
                const next = this.equationFor(member, k)
                updates.set(member, next)
            }
            for (const [member, next] of updates) {
                const prev = this.memo.get(member)!
                if (!coefficientsEqual(prev, next)) {
                    this.memo.set(member, next)
                    changed = true
                }
            }
            if (!changed) break
        }
        return this.memo.get(type) ?? zeroUpTo(k)
    }

    /** The GF equation for one type: Σ over variants ( x · Π over fields GF(field) ). */
    private equationFor(
        carrier: DataType,
        k: number,
    ): number[] {
        const sum = zeroUpTo(k)
        for (const variant of carrier.allVariants()) {
            let product: number[] = [1] // the multiplicative unit (constant 1)
            for (const field of variant.fields) {
                const gf = fieldGF(field, k, this, carrier)
                product = convolve(product, gf, k)
            }
            // The constructor node itself: multiply by x (shift up one).
            product = shiftByX(product, k)
            for (let n = 0; n <= k; n++) sum[n] = satAdd(sum[n]!, product[n]!)
        }
        return sum
    }
}

function coefficientsEqual(a: Coefficients, b: Coefficients): boolean {
    if (a.length !== b.length) return false
    for (let i = 0; i < a.length; i++) {
        if (a[i] !== b[i]) return false
    }
    return true
}

/**
 * The coefficients c₀..cₖ of a type's generating function, from the TYPE
 * EQUATION — never from any enumeration. This is the certificate's
 * independence: the coefficients are computed by a different method than
 * the screen's sweep, so agreement between the two is evidence about the
 * type, not about the sampler.
 *
 * The equation, per data type (size = constructor-node count):
 *
 *   T(x) = Σ over variants Cᵢ ( x · Π over fields j GFᵢⱼ(x) )
 *
 * where a field's GF is: recursive → x·T(x) (the carrier's current
 * approximation — the fixpoint, never unfolded); another data type B →
 * B(x); a pattern type → x (the declared singleton-token fallback — the
 * language-equation reading needs the declared-encoding machinery, a
 * follow-up);
 * function/`Any`/`Nothing`/token/intersection-typed → 0 (the same
 * unsampleable rule `construct`/`screenableDomain` apply).
 *
 * The system is solved by TRUNCATED FIXPOINT ITERATION at degree k — all
 * equations of the (possibly mutually recursive) system iterate from zero
 * vectors until no coefficient changes. Termination: each round the
 * minimal nonzero degree of a productive system advances (inhabitants have
 * positive size), so at most k+1 rounds; cycles that never become
 * productive converge to zero vectors — honest zeros (an unproductive
 * variant has no inhabitants, consistent with the sampler's drop).
 *
 * The GF taxonomy (type-algebra.md §3) falls out of these same equations:
 * chain types (Nat: T = 1 + x·T; List) satisfy LINEAR recurrences — their
 * GFs are rational, Chomsky–Schützenberger's territory for pattern types
 * once encodings are declared — while branching μ-types (Tree = Leaf +
 * Node(T,T): T = 1 + x·T², the Catalan series) satisfy quadratic
 * recurrences. One mechanism, no closed forms, no per-type case analysis.
 *
 * Parent-chain variants are summed in via `allVariants()` (comb
 * inheritance), matching how values are constructed and how the sampler
 * sweeps.
 *
 * @param type the carrier (μ data type, or a pattern type for the declared
 *             fallback)
 * @param k    the certified size bound (the returned array is c₀..cₖ)
 * @returns the saturated coefficient array, length k+1
 *
 * @throws TypeError when the carrier is an intersection (not a semiring
 * operation — the same typed rejection `derivative` applies) or codata
 * (a ν-type's generating function is not a counting object).
 */
export function coefficients(
    type: DataType | PatternDataType,
    k: number,
): Coefficients {
    if (k < 0) {
        throw new RangeError(`coefficients(${type.name}): the degree k must be ≥ 0`)
    }
    if (type instanceof IntersectionType) {
        throw new TypeError(
            `coefficients(${type.name}): intersection types are not a semiring ` +
                `operation — no coefficient reading is defined (type-algebra.md §3)`,
        )
    }
    if (type instanceof PatternDataType) {
        // The language-equation reading: a pattern type's language
        // is the UNION of its variants' languages — variants may overlap
        // (`a` and `a?` both hold "a"), so the counts read off the merged
        // STRING SET (the same dedup the certified enumerator runs), not
        // the per-variant sum. Cycles through type references reject
        // loudly inside the environment (an ill-founded equation has no
        // reading).
        return typeUnionCounts(type, k)
    }
    if (type instanceof CodataType) {
        throw new TypeError(
            `coefficients(${type.name}): codata types are the coalgebraic dual — ` +
                `their generating function is not a counting object ` +
                `(type-algebra.md §4.3)`,
        )
    }
    // Collect the system: the carrier plus every data type reachable
    // through non-recursive data fields (mutual recursion arrives that way).
    const system = new Set<DataType>()
    const collect = (t: Type): void => {
        if (t instanceof DataType && !system.has(t)) {
            system.add(t)
            for (const variant of t.allVariants()) {
                for (const field of variant.fields) {
                    if (!field.isRecursive && field.type instanceof DataType) {
                        collect(field.type)
                    }
                }
            }
        }
    }
    collect(type)
    const state = new GFState(system)
    return state.getFor(type, k)
}
