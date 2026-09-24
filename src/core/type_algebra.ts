/**
 * LC Type Algebra — the judgment class over `Type` syntax: derivatives
 * (one-hole contexts), coefficients (certified screen coverage), and
 * inhabitant counting of regular types, as readings of one equation system.
 *
 * See _docs/theory/type-algebra.md §4 (McBride 2001: the formal derivative
 * of a regular type is its type of one-hole contexts) and §3 (coefficients:
 * certified screen coverage).
 *
 * ## The judgment class
 *
 * The type-level judgments over the `Type` AST are the SAME structural
 * recursion over the SAME syntax, with the same termination argument (a
 * `Family`-typed field spells the μ-bound; the walk never follows it), and
 * the same unsampleable-field rules. `TypeAlgebra` hosts them as methods of
 * one class — the judgment-class pattern (`grammar-as-semantics.md` §7.3)
 * applied to type-level syntax: the types are the syntax, the algebra's
 * readings are the judgments. The class is deliberately NOT a `Grammar`
 * subclass (types are not a parse — the boundary condition below): its
 * memoization is the "@rule-style" seam of per-instance identity-keyed
 * caches (the treeKey v3.0.1 keying scheme) without the decorator's
 * `Grammar`-hierarchy precondition.
 *
 * Instance state is limited to caches and the injected lookup hook — the
 * readings are pure functions of their arguments, testable without fixture
 * setup (the module-level default instance backs the free-function
 * delegates).
 *
 * Three readings of the SAME type equation share this class (contexts,
 * coefficients, and counting):
 *
 * - **∂T (§4)** — `derivative(type)`: the one-hole contexts of T's values,
 *   by implicit differentiation. Lapis's `Type` AST already spells the
 *   μ-bound — a `Family`-typed field IS an occurrence of the binder —
 *   so differentiating the μ-equation directly reduces to ordinary
 *   structural recursion over `Type` that never follows recursive fields
 *   (that occurrence is the hole). No equation solving, no quotient rule:
 *
 *     ∂a const = 0                        (no a inside → no contexts)
 *     ∂a (F + G) = ∂a F + ∂a G            (sum rule — the variant set)
 *     ∂a (F · G) = ∂a F · G + F · ∂a G    (Leibniz — the variant's fields)
 *     ∂a a = 1                            (the hole itself)
 *
 * - **Coefficients (§3)** — `coefficients(type, k)`: the truncated GF
 *   reading of the same equations. Size = node count (constructor nodes;
 *   the same measure `Value.size` uses), so the certificate and the ∂T
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
 * - **Counting (§2)** — `inhabitants(type)`: the total |T| classifier that
 *   decides the `finite` regime (a recursive, function-typed, or
 *   `Any`-typed field ⇒ unbounded; otherwise the product/sum recursion,
 *   saturated past the exhaustion ceiling). The same field-kind case table,
 *   the third reading of the same equations.
 *
 * The derivative never diverges: the only potentially-infinite unfolding of
 * a μ-type is through its recursive fields, and those are exactly the
 * positions the traversal stops at. The coefficient fixpoint converges:
 * each iteration round the minimal nonzero degree of a productive system
 * advances, so at most k+1 rounds; cycles that never become productive
 * converge to zero vectors (honest: those variants contribute no
 * inhabitants).
 *
 * ## Boundaries (type-algebra.md §4.3)
 *
 * - **Chain rule, depth ≤ 1**: a field of another data type `B` yields a
 *   context whose hole sits *inside* that field's subtree — punching it
 *   consults `derivative(B)` at the next path step (the chain rule
 *   $\partial_a F(G(a)) = \partial_a G \cdot \partial_G F$, read one level
 *   at a time). The `ContextSpec` carries that next step as the data edge
 *   `derivative()` — the chain rule is data, not a second synchronized
 *   walker. Recursion under a *list-like* field (rose trees,
 *   $R = a \cdot L(R)$) is only partially covered: each type's derivative
 *   is taken w.r.t. its own μ-bound, so a hole in R nested through L is
 *   beyond this first cut — `FamilyType` marks direct Family positions
 *   only, and extending nested-recursion expressiveness is a separate
 *   decision.
 * - **Intersections** are not a semiring operation: an intersection-headed
 *   carrier is a typed rejection (the screen treats intersected carriers as
 *   unscreenable too — consistent), and an intersection-typed FIELD
 *   contributes no context (the same unsampleable rule as functions).
 * - **Function-typed fields** have exponential generating functions; they
 *   contribute no context (the screen's existing rule, not weakened).
 * - **Codata (ν)** is the coalgebraic dual — untouched; bounded
 *   observation stays bounded. The same holds for coefficients: a ν-typed
 *   carrier or field is a typed rejection (codata's generating function is
 *   not a counting object — bounded observation, not bounded construction).
 *   Both typed rejections (intersection and codata) apply to BOTH readings
 *   through one `requireSemiringCarrier` boundary — a ν-carrier reaching
 *   either judgment rejects with a typed error naming it, never a crash
 *   deeper inside the traversal.
 */

import { CodataType, DataType, Field, IntersectionType, type Type, Variant } from "./types.ts"
import { satAddSeq, setRegistryHook, typeUnionCountsWith } from "./pattern_lang.ts"

// ── The lookup hook (instance state; the module global is the facade) ────────

/**
 * The type-reference environment's lookup hook. `coefficients` is pure
 * w.r.t. this module — the hook is carried per instance because the counting
 * needs the FULL registry (a `<T>` reference may name any declared pattern
 * type, not just the carrier), and threading the registry through every
 * `coefficients` call site would change their signatures for one consumer
 * (the pattern arm).
 *
 * The DEFAULT hook reads the pattern arm self-consistently: a type reference
 * `<T>` with no installed registry is a typed rejection — but a pattern
 * FIELD inside a data carrier needs its own type's counting, which requires
 * NO registry (the field's pattern ASTs are on the field type itself). The
 * hook only matters for type REFERENCES inside patterns (`<T>`); a pattern
 * language without references works without any hook.
 */
export type PatternLookup = (name: string) => DataType | undefined

const rejectingLookup: PatternLookup = () => {
    throw new TypeError(
        "a pattern language type reference <T> requires the registry hook — " +
            "install it via setPatternLookup (the law checker wires the type registry)",
    )
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
 *
 * The CHAIN RULE IS DATA: a spec whose hole type is itself a data type
 * carries the next step of the punch as a lazily memoized `derivative()` —
 * the contexts of the hole's own structure. A hole type that contributes no
 * structure (token, function, `Any`, `Nothing`, pattern, intersection) has
 * no edge (the same unsampleable rule the readings apply).
 */
export class ContextSpec {
    /** The variant whose field is punched. */
    readonly variantName: string
    /** The punched field's name. */
    readonly fieldName: string
    /**
     * The hole's type — what plugs into it. For a direct recursive field
     * this is the carrier itself; for a field of another data type this is
     * that field's type (the chain rule's one-level reading: punching the
     * hole descends into the field's own structure).
     */
    readonly holeType: Type
    /** The other fields' types forming the surroundings, in field order. */
    readonly surroundTypes: readonly Type[]

    /**
     * The memoized chain-rule edge (lazily computed on first `derivative()`
     * consultation; `undefined` before that — a spec is constructed once per
     * carrier and lives in the algebra's identity-keyed memo, so the edge is
     * computed at most once per spec).
     */
    private edge: ContextSpec[] | undefined | false = false

    /**
     * The spec constructor — the STABLE construction surface for shape-level
     * consumers (the structural tests build specs directly to assert their
     * fields; the algebra itself constructs them inside `derivative`). The
     * 4-argument call shape of the former interface is preserved (the
     * algebra reference is the 5th, injectable argument); direct construction
     * is supported but should prefer `derivative`/`specFor` for production
     * reads (those serve the memoized, identity-consistent specs).
     */
    constructor(
        variantName: string,
        fieldName: string,
        holeType: Type,
        surroundTypes: readonly Type[],
        private readonly algebra: TypeAlgebra,
    ) {
        this.variantName = variantName
        this.fieldName = fieldName
        this.holeType = holeType
        this.surroundTypes = surroundTypes
    }

    /**
     * The contexts INSIDE the hole's own structure (the chain rule as
     * data): consult the hole type's derivative at the next path step —
     * punching INSIDE the field's subtree. `undefined` when the hole type
     * has no punchable structure (a token, function, `Any`, `Nothing`,
     * pattern, or intersection field).
     */
    derivative(): ContextSpec[] | undefined {
        if (this.edge === false) {
            this.edge = this.holeType instanceof DataType
                ? this.algebra.derivative(this.holeType)
                : undefined
        }
        return this.edge
    }
}

// ── The judgment class ───────────────────────────────────────────────────────

/**
 * The type-level judgments over the `Type` AST, hosted as one class: the
 * shared traversal scaffolding (variant iteration, field-kind dispatch,
 * mutual-system collection, memoization) once, and each reading as an
 * instance method.
 *
 * Instance state is caches and the lookup hook ONLY — the readings are
 * pure functions of their arguments (a `derivative` call on a fresh
 * instance needs no fixture setup; the module default instance backs the
 * free-function delegates).
 *
 * Memoization is identity-keyed (`WeakMap` per carrier): types are immutable
 * by construction (persistent builders — types.ts), so instance identity is
 * a valid cache key with no precondition and no invalidation path — the same
 * keying scheme `treeKey` v3.0.1 applies to class
 * instances. Cache growth is bounded by the number of distinct carrier
 * instances seen (registries are finite); no eviction.
 */
export class TypeAlgebra {
    private readonly derivativeMemo = new WeakMap<DataType, ContextSpec[]>()
    private readonly specIndexMemo = new WeakMap<
        DataType,
        Map<string, Map<string, ContextSpec>>
    >()
    private readonly inhabitantsMemo = new WeakMap<DataType, number | undefined>()
    /**
     * The coefficients memo (identity-keyed per carrier, degree-keyed per
     * entry): the truncated series is INTRINSIC to the immutable carrier, so a
     * repeat call at the same (or smaller) degree reads the cache; a LARGER
     * degree re-solves (the previous array is a prefix — the fixpoint's
     * memoized state seeds the new degree). The pattern arm is memoized
     * through the language equation's own environment memo (pattern_lang.ts).
     */
    private coefficientsMemo = new WeakMap<
        DataType,
        { degree: number; coeffs: Coefficients }
    >()

    /** The pattern-language type-reference lookup (constructor-injected). */
    private lookup: PatternLookup

    constructor(lookup: PatternLookup = rejectingLookup) {
        this.lookup = lookup
    }

    /**
     * Install the type-reference lookup hook on this instance; the prior
     * hook is returned for restoration.
     *
     * The coefficients memo is INVALIDATED here: a pattern carrier's counts
     * resolve `<T>` references through the lookup, so entries computed under
     * one registry are not valid under another (the law checker swaps and
     * restores hooks per `declareCheckedLawWithRegistry` call — a restored
     * hook must never read entries computed under the swapped one).
     */
    setLookup(lookup: PatternLookup): PatternLookup {
        const prior = this.lookup
        if (lookup !== prior) {
            this.coefficientsMemo = new WeakMap()
        }
        this.lookup = lookup
        return prior
    }

    // ── The derivative (type-algebra.md §4) ──────────────────────────────────

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
     *   the field's type and the punch is resolved through the spec's data
     *   edge (`ContextSpec.derivative()`) at the next path step.
     * - **Function-typed, `Any`-typed, `Nothing`-typed, token, and
     *   pattern-typed fields** contribute nothing: no hole vocabulary (the same
     *   unsampleable rule the residual screen applies).
     *
     * Parent-chain variants are covered via `allVariants()` (comb inheritance),
     * matching how values are constructed and how the sampler sweeps.
     *
     * The result is ordered variant-by-variant, field-by-field; the order is
     * deterministic (it follows the declaration order) so callers can rely on
     * reproducible shrink candidate orderings. The array is memoized per
     * carrier instance (identity-keyed — a carrier's derivative is
     * intrinsic); callers must not mutate the returned array.
     *
     * @throws TypeError when the carrier is headed by an intersection type
     * (intersections are not a semiring operation — type-algebra.md §4.3).
     */
    derivative(type: DataType): ContextSpec[] {
        this.requireSemiringCarrier(type, "derivative")
        const cached = this.derivativeMemo.get(type)
        if (cached !== undefined) return cached
        const specs: ContextSpec[] = []
        for (const variant of type.allVariants()) {
            for (const field of variant.fields) {
                // The field's kind classification — routed through
                // `field.type.dispatch` (the Type universe's required-case
                // collection read). The hole's type: Family (the μ-bound)
                // reads as the carrier the derivative was taken OF (a comb's
                // hole type is the carrier — the subtype's algebra, not the
                // parent's); a data field names where the descent goes (the
                // chain rule's one-level reading — the field itself can also
                // BE the hole when the punch replaces the whole field value).
                // Function/`Any`/`Nothing`/Token/pattern/intersection-typed
                // fields contribute no context (no finite sample vocabulary
                // or no structure to punch — type-algebra.md §4.3).
                const spec = field.type.dispatch<ContextSpec | undefined>({
                    family: (): ContextSpec | undefined =>
                        new ContextSpec(
                            variant.name,
                            field.name,
                            type,
                            this.surroundingsOf(variant, field, type),
                            this,
                        ),
                    data: (fieldCarrier): ContextSpec | undefined =>
                        // A pattern-BEARING field carrier contributes no
                        // context: its values are tokens (atomic — nothing
                        // to punch), the same no-structure rule the token
                        // field applies. A pattern FIELD still joins the
                        // recursive field's surroundings (Leibniz: every
                        // non-hole field, in field order). Stage 5's
                        // member-shape derivative decides whether a pattern
                        // carrier's token values gain structure.
                        fieldCarrier.patterns.length > 0 ? undefined : new ContextSpec(
                            variant.name,
                            field.name,
                            fieldCarrier,
                            this.surroundingsOf(variant, field, type),
                            this,
                        ),
                    fun: () => undefined,
                    intersection: () => undefined,
                    polymorphic: () => undefined,
                    typeVar: () => undefined,
                    codata: () => undefined,
                    token: () => undefined,
                    any: () => undefined,
                    nothing: () => undefined,
                })
                if (spec !== undefined) specs.push(spec)
            }
        }
        this.derivativeMemo.set(type, specs)
        return specs
    }

    /**
     * The specs admissible at a node of the given carrier, indexed for
     * path-walking: variant name → field name → spec. Memoized per carrier
     * (identity-keyed — the same spec objects `derivative` builds, indexed
     * once per carrier; value-level walkers consult this instead of
     * rebuilding a fresh index per node).
     */
    specFor(carrier: DataType): Map<string, Map<string, ContextSpec>> {
        let index = this.specIndexMemo.get(carrier)
        if (index === undefined) {
            index = new Map()
            for (const spec of this.derivative(carrier)) {
                let byField = index.get(spec.variantName)
                if (!byField) {
                    byField = new Map()
                    index.set(spec.variantName, byField)
                }
                byField.set(spec.fieldName, spec)
            }
            this.specIndexMemo.set(carrier, index)
        }
        return index
    }

    /**
     * The Leibniz surroundings for one punched field: the other fields' types,
     * with any Family field reading as the carrier the derivative was taken OF
     * (the hole type's translation — a comb's hole is the carrier, not the
     * parent).
     */
    private surroundingsOf(
        variant: Variant,
        punched: Field,
        carrier: DataType,
    ): Type[] {
        return variant.fields
            .filter((f) => f !== punched)
            .map((f) => f.type.resolveFamily(carrier))
    }

    // ── Counting (type-algebra.md §2 — the third reading) ────────────────────

    /**
     * Count the inhabitants of a data type, or `undefined` when the type is not
     * finitely inhabitable.
     *
     * The space of a μ-type is finite exactly when every variant field is:
     * a recursive field makes the type unbounded (a value may nest arbitrarily
     * deep), a function-typed field has no finite vocabulary, and `Any`-typed
     * fields are equally unbounded (the top type subsumes every type). A field
     * referencing another data type contributes that type's count (the product
     * through the variant's fields); parent-chain variants are summed in via
     * comb inheritance.
     *
     * Counts are saturated: any component exceeding the ceiling returns one
     * past it, so deep record chains cannot overflow the number range while the
     * caller's comparison against the ceiling still decides enumerability — a
     * value past the ceiling means "finite but not exhaustible here".
     *
     * The verdict is memoized per carrier instance (identity-keyed): a type's
     * finiteness is intrinsic to the immutable carrier, so the memo is sound
     * across calls. The memo stores `null` for the undefined verdict
     * (a WeakMap value cannot be `undefined` without losing the
     * absent-or-computed distinction); `null` reads back as `undefined`.
     */
    inhabitants(type: DataType): number | undefined {
        const cached = this.inhabitantsMemo.get(type)
        if (this.inhabitantsMemo.has(type)) {
            // The null sentinel IS the undefined verdict (a count is always
            // a positive number — 0 is a real count for a variant-less
            // carrier, so null is unambiguous).
            return cached === null ? undefined : cached
        }
        return this.count(type, new Set())
    }

    /**
     * The counting recursion: the product over a variant's fields, the sum
     * over the variant set, `undefined` when any component is unbounded —
     * a Family field (the μ-bound), a function-typed or `Any`-typed field,
     * or a field type whose own count is undefined — saturated past the
     * exhaustion ceiling. The field-kind classification routes through
     * `field.type.dispatch` (the same dispatcher the other readings read).
     *
     * `inProgress` marks the CURRENT traversal path — a field type already
     * on the path is a data-field cycle (a type nesting itself through a
     * data field: the re-entrancy shape `Self = Base | Wrap(inner: Self)`),
     * hence unbounded. The memo is consulted at EVERY recursion level
     * (a verdict computed in an earlier call — or earlier in this walk —
     * short-circuits), and every completed verdict is cached, including the
     * cycle-derived `undefined` (a type on a data-field cycle is genuinely
     * unbounded, so the verdict is sound to persist).
     *
     * The verdict's states are tracked explicitly (`undefined` is a real
     * outcome, not the "not yet computed" default — a naive optional breaks
     * exactly here): `unset` = the loop ran to completion, the sum `total`
     * is the verdict; `unbounded` = a component was unbounded (⇒ undefined);
     * `saturated` = the ceiling was crossed (⇒ ceiling + 1).
     */
    private count(type: DataType, inProgress: Set<DataType>): number | undefined {
        const cached = this.inhabitantsMemo.get(type)
        if (this.inhabitantsMemo.has(type)) return cached === null ? undefined : cached
        if (inProgress.has(type)) return undefined
        inProgress.add(type)
        let total = 0
        let state: "unset" | "unbounded" | "saturated" = "unset"
        loop: for (const variant of type.allVariants()) {
            let product = 1
            for (const field of variant.fields) {
                // The field's kind: Family (the μ-bound) and Any (the top —
                // it subsumes every type) are unbounded; data fields thread
                // the product through their own count; every other kind has
                // no finite sample vocabulary (functions, tokens, patterns,
                // intersections, `Nothing`-typed fields).
                const UNBOUNDED = "unbounded" as const
                const kind = field.type.dispatch<DataType | typeof UNBOUNDED | undefined>(
                    {
                        family: () => UNBOUNDED,
                        any: () => UNBOUNDED,
                        data: (t) =>
                            // A pattern-BEARING field carrier: its token
                            // language's finiteness decides. A FINITE
                            // pattern language (bounded lengths, no star
                            // over an open class — `ab`, `[ab]{2,3}`) keeps
                            // the carrier finitely inhabitable: the count
                            // threads through the union's total (the
                            // per-length counts, saturated at the ceiling).
                            // An UNBOUNDED language (`[0-9]+`, `.`) routes
                            // unbounded — the generating function is
                            // rational, never polynomial. The test is the
                            // union's truncated count: a saturated (ceiling
                            // +1) or budget-declined reading routes
                            // unbounded; a bounded total is the finite
                            // member count the product multiplies.
                            t.patterns.length > 0 ? this.patternLanguageCount(t) : t,
                        fun: () => undefined,
                        intersection: () => undefined,
                        polymorphic: () => undefined,
                        typeVar: () => undefined,
                        codata: () => undefined,
                        token: () => undefined,
                        nothing: () => undefined,
                    },
                )
                if (kind === UNBOUNDED || !(kind instanceof DataType)) {
                    // The μ-bound, the top type, and every non-data kind:
                    // unbounded (function types — and any other non-data
                    // type — have no finite sample vocabulary).
                    state = "unbounded"
                    break loop
                }
                const sub = this.count(kind, inProgress)
                if (sub === undefined) {
                    state = "unbounded"
                    break loop
                }
                product *= sub
                if (product > MAX_FINITE_INHABITANTS) {
                    state = "saturated"
                    break loop
                }
            }
            total += product
            if (total > MAX_FINITE_INHABITANTS) {
                state = "saturated"
                break loop
            }
        }
        inProgress.delete(type)
        // The three states → the verdict: the completed loop's sum; the
        // unbounded `undefined`; the saturated ceiling + 1. The memo stores
        // `null` for the undefined verdict (WeakMap values cannot be
        // `undefined` without losing the "absent" distinction).
        // The MIXED composition (the counting side): the carrier's OWN
        // pattern members contribute their token-language count to the sum
        // (kind-disjoint universes — VariantVal sizes and token text
        // lengths add without double-counting). A finite token language
        // keeps the carrier finite (its count joins the variant sum); an
        // unbounded one poisons the verdict (the rational GF).
        let verdict: number | undefined
        if (state === "unbounded") {
            verdict = undefined
        } else if (state === "saturated") {
            verdict = MAX_FINITE_INHABITANTS + 1
        } else {
            verdict = total
        }
        if (verdict !== undefined && type.patterns.length > 0) {
            const tokenCount = this.patternLanguageCount(type)
            if (tokenCount === undefined) return undefined
            verdict = Math.min(verdict + tokenCount, MAX_FINITE_INHABITANTS + 1)
        }
        this.inhabitantsMemo.set(type, verdict ?? null as unknown as number)
        return verdict
    }

    /**
     * The token-language count of a pattern-bearing carrier — the
     * finiteness test's reading. `typeUnionCounts`' truncated profile sums
     * to the language's total size; a SATURATED profile (the ceiling + 1)
     * or one that would exceed the exhaustion ceiling routes unbounded (the
     * rational GF), while a bounded total IS the finite member count.
     * Memoized through the same inhabitants memo (identity-keyed — the
     * carrier is frozen, so the verdict is stable).
     */
    private patternLanguageCount(type: DataType): number | undefined {
        const cached = this.inhabitantsMemo.get(type)
        if (this.inhabitantsMemo.has(type)) return cached === null ? undefined : cached
        if (this.patternCountMemo.has(type)) return this.patternCountMemo.get(type)
        // A budget DECLINE is the unbounded reading (the language's set is
        // too large to materialize — the rational GF): undefined, not a
        // throw — the counting classifier's contract is verdict-or-undefined,
        // and the decline is the honest "no finite verdict" shape.
        let verdict: number | undefined
        try {
            const profile = typeUnionCountsWith(type, MAX_FINITE_INHABITANTS, this.lookup)
            const total = profile.reduce((sum, c) => sum + c, 0)
            verdict = total >= MAX_COEFFICIENT ? undefined : total
        } catch {
            verdict = undefined
        }
        this.patternCountMemo.set(type, verdict)
        return verdict
    }

    private patternCountMemo = new WeakMap<DataType, number | undefined>()

    // ── The typed-rejection boundary ─────────────────────────────────────────

    /**
     * A carrier must be a semiring object to enter the algebra: an
     * intersection-headed carrier is a typed rejection (intersections are
     * not a semiring operation — type-algebra.md §4.3), and a ν-typed
     * carrier is the coalgebraic dual (its generating function is not a
     * counting object). The thrown message names the calling judgment —
     * the same diagnostic discipline `subtyping.ts`'s `requireType` applies
     * to the lattice. On return, the carrier is asserted a `DataType`
     * (the pattern arm is dispatched by the callers BEFORE this boundary —
     * a mis-typed intersection reaching through an unsound cast rejects
     * here).
     */
    private requireSemiringCarrier(
        type: DataType | CodataType,
        caller: string,
    ): asserts type is DataType {
        if (type instanceof IntersectionType) {
            throw new TypeError(
                `${caller}(${type.name}): intersection types are not a semiring ` +
                    `operation — no ${
                        caller === "derivative"
                            ? "derivative is defined (type-algebra.md §4.3)"
                            : "coefficient reading is defined (type-algebra.md §3)"
                    }`,
            )
        }
        if (type instanceof CodataType) {
            throw new TypeError(
                `${caller}(${type.name}): codata types are the coalgebraic dual — ` +
                    `their generating function is not a counting object ` +
                    `(type-algebra.md §4.3)`,
            )
        }
    }

    // ── Coefficients: certified screen coverage (type-algebra.md §3) ─────────

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
     *             fallback; a CodataType is accepted in the signature and
     *             rejected with a typed error — the declared boundary below)
     * @param k    the certified size bound (the returned array is c₀..cₖ)
     * @returns the saturated coefficient array, length k+1
     *
     * @throws TypeError when the carrier is an intersection (not a semiring
     * operation — the same typed rejection `derivative` applies) or codata
     * (a ν-type's generating function is not a counting object).
     */
    coefficients(
        type: DataType | CodataType,
        k: number,
    ): Coefficients {
        if (k < 0) {
            throw new RangeError(`coefficients(${type.name}): the degree k must be ≥ 0`)
        }
        if (type instanceof DataType && type.patterns.length > 0 && type.variants.length === 0) {
            // The language-equation reading: a PATTERNS-ONLY carrier's
            // language is the UNION of the declared patterns — variants may
            // overlap (`a` and `a?` both hold "a"), so the counts read off
            // the merged STRING SET (the same dedup the certified enumerator
            // runs), not the per-variant sum. Cycles through type references
            // reject loudly inside the environment (an ill-founded equation
            // has no reading).
            return typeUnionCountsWith(type, k, this.lookup)
        }
        this.requireSemiringCarrier(type, "coefficients")
        // Collect the system: the carrier plus every data type reachable
        // through non-Family data fields (mutual recursion arrives that way).
        // The field classification routes through `dispatch` — the same
        // dispatcher `fieldGF` reads, so the two stay one case table.
        const system = new Set<DataType>()
        const collect = (t: Type): void => {
            if (t instanceof DataType && !system.has(t)) {
                system.add(t)
                for (const variant of t.allVariants()) {
                    for (const field of variant.fields) {
                        field.type.dispatch<undefined>({
                            family: () => undefined, // the μ-bound — never collected
                            data: (inner) => {
                                collect(inner)
                                return undefined
                            },
                            codata: () => undefined,
                            fun: () => undefined,
                            intersection: () => undefined,
                            polymorphic: () => undefined,
                            typeVar: () => undefined,
                            token: () => undefined,
                            any: () => undefined,
                            nothing: () => undefined,
                        })
                    }
                }
            }
        }
        collect(type)
        // The identity/degree-keyed memo: a repeat call at the same (or a
        // smaller) degree reads the cached truncated series — the fixpoint
        // does not re-run. A larger degree re-runs the fixpoint over the
        // collected system (the previous result is a prefix of the new one,
        // but the fixpoint's zero-vector seeding makes a straight prefix
        // extension wrong — recompute; the system set is derived cheaply).
        const memoed = this.coefficientsMemo.get(type)
        if (memoed !== undefined && memoed.degree >= k) {
            // The cached vector is a truncated series at a ≥ degree: the
            // requested c₀..cₖ prefix is its first k+1 entries — return the
            // EXACT requested shape (a caller comparing the returned array
            // against its requested degree would otherwise see extra entries).
            return memoed.coeffs.slice(0, k + 1)
        }
        const state = new GFState(system, this.lookup)
        let coeffs = state.getFor(type, k)
        // The MIXED composition: a carrier with BOTH member kinds reads
        // the per-length SUM of (the variant-system fixpoint) plus (the
        // token-language counts). Soundness: variant inhabitants are
        // `VariantVal`s (size = constructor-node count), pattern inhabitants
        // are tokens (size = text length) — KIND-DISJOINT universes, so the
        // sequences add without double-counting. The token side reads the
        // union with the same saturation arithmetic the union arm applies.
        if (type.patterns.length > 0) {
            const tokenCounts = typeUnionCountsWith(type, k, this.lookup)
            coeffs = coeffs.map((c, i) => Math.min(c + (tokenCounts[i] ?? 0), MAX_COEFFICIENT))
        }
        this.coefficientsMemo.set(type, { degree: k, coeffs })
        return coeffs
    }
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
 * The inhabitant ceiling for the counting classifier (semantics.md §5.4:
 * "Bool, enums, records of finites (< ~2²⁰ inhabitants)" — the ceiling is set
 * below the doc's upper edge: exhaustion MEMOIZES each distinct type's
 * deduped space as real `VariantVal`s, and the memory cost is the honest
 * price of full enumeration. 2¹⁷ × ~1.5KB/value ≈ 200MB per distinct
 * carrier — the practical bound measured on the default heap; a 2²⁰-space
 * record type exhausts it (OOM, measured ~1.8GB).) A data type whose
 * inhabitant count is at or below this bound is exhaustible: the entire
 * input space is checked, making a passing check a proof. Bumping this
 * ceiling requires a heap headroom check or an external-memory sweep.
 * Declared HERE so the classifier and its consumers (law_checking.ts) read
 * ONE constant.
 */
export const MAX_FINITE_INHABITANTS = 2 ** 17

/**
 * A type's truncated generating function: the coefficient list
 * `[c₀, c₁, ..., cₖ]` where `cₙ` counts the inhabitants of size n
 * (size = constructor-node count — the same measure `Value.size` uses).
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
    field: { type: Type },
    k: number,
    current: GFState,
    carrier: DataType,
): Coefficients {
    // The field's kind classification — routed through `dispatch` (the Type
    // universe's one dispatcher; a new kind must answer here). Family reads
    // the CARRIER's current approximation (the μ-bound's self-reference —
    // the fixpoint, never unfolded; the comb's algebra is the subtype
    // carrier); a data field reads its own type's; a pattern field reads the
    // language-equation counting (the union of its variants' languages —
    // variants may overlap, so the counts read off the merged string set,
    // not the per-variant sum; tokens sized by TEXT LENGTH match the
    // enumeration's per-length classes exactly); every other kind
    // contributes the zero polynomial (the same unsampleable rule the
    // screen's `construct` and `screenableDomain` apply).
    return field.type.dispatch<Coefficients>({
        family: () => current.currentFor(carrier, k),
        data: (t) =>
            // A pattern-BEARING data field reads the language-equation
            // counting: its members are pattern constructors, so its
            // per-length classes are the UNION's token counts (tokens
            // sized by TEXT LENGTH — matching the enumeration's per-length
            // classes exactly). The variant-system path below (collect +
            // fixpoint) only sees carriers WITH variants; a patterns-only
            // field carrier's GF is its token language, never a zero
            // polynomial — routing it through the system would report zero
            // inhabitants for a With(p) variant (the enumeration hole the
            // certificate's mismatch check rejects).
            //
            // The MIXED composition: a field carrier with BOTH member
            // kinds sums (its variant-system approximation, read through
            // the fixpoint memo) plus (its token-language counts) — the
            // same kind-disjoint sum the top-level coefficients arm runs.
            // Omitting either kind would under-count the field's space and
            // the enumeration's class filter would then mismatch the
            // certificate.
            t.patterns.length > 0 && t.variants.length === 0
                ? typeUnionCountsWith(t, k, current.lookup)
                : t.patterns.length > 0
                ? satAddSeq(
                    current.currentFor(t, k),
                    [...typeUnionCountsWith(t, k, current.lookup)],
                )
                : current.currentFor(t, k),
        fun: () => zeroUpTo(k),
        intersection: () => zeroUpTo(k),
        polymorphic: () => zeroUpTo(k),
        typeVar: () => zeroUpTo(k),
        codata: () => zeroUpTo(k),
        token: () => zeroUpTo(k),
        any: () => zeroUpTo(k),
        nothing: () => zeroUpTo(k),
    })
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

    constructor(
        private readonly system: Set<DataType>,
        /** The algebra instance's pattern-type lookup (the per-instance seam). */
        readonly lookup: (name: string) => DataType | undefined,
    ) {}

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

// ── The module default instance and its delegates ───────────────────

/**
 * The module-level default `TypeAlgebra`. The free-function delegates below
 * (`derivative`, `coefficients`, `finiteInhabitants`, `setPatternLookup`)
 * route through it: the pure, zero-fixture call surface. Fresh instances
 * (tests, or a consumer isolating its lookup hook and memos) carry their
 * own state.
 */
export const typeAlgebra = new TypeAlgebra()

/**
 * The derivative of a regular μ-type: the shapes of all one-hole contexts
 * of its values (the module default instance's reading — see
 * `TypeAlgebra.derivative` for the contract).
 *
 * @throws TypeError when the carrier is headed by an intersection type
 * (intersections are not a semiring operation — type-algebra.md §4.3).
 */
export function derivative(type: DataType): ContextSpec[] {
    return typeAlgebra.derivative(type)
}

/**
 * The coefficients c₀..cₖ of a type's generating function (the module
 * default instance's reading — see `TypeAlgebra.coefficients` for the
 * contract).
 *
 * @throws TypeError when the carrier is an intersection (not a semiring
 * operation — the same typed rejection `derivative` applies) or codata
 * (a ν-type's generating function is not a counting object).
 */
export function coefficients(
    type: DataType | CodataType,
    k: number,
): Coefficients {
    return typeAlgebra.coefficients(type, k)
}

/**
 * Count the inhabitants of a data type, or `undefined` when the type is not
 * finitely inhabitable (the module default instance's reading — see
 * `TypeAlgebra.inhabitants` for the contract).
 */
export function finiteInhabitants(type: DataType): number | undefined {
    return typeAlgebra.inhabitants(type)
}

/**
 * Install the type-reference lookup hook on the module default instance
 * (called once at law-checking setup). The prior hook is returned for
 * restoration in tests.
 */
export function setPatternLookup(
    lookup: PatternLookup,
): PatternLookup {
    const prior = typeAlgebra.setLookup(lookup)
    setRegistryHook(lookup)
    return prior
}
