/**
 * LC Type Algebra — derivatives of regular types (one-hole contexts).
 *
 * See _docs/theory/type-algebra.md §4 (McBride 2001: the formal derivative
 * of a regular type is its type of one-hole contexts) and
 * _docs/issue64-plan.md (the PBI plan).
 *
 * The module implements **implicit differentiation**: Lapis's `Type` AST
 * already spells the μ-bound — a recursive field (`Field.isRecursive`) IS an
 * occurrence of the recursion variable — so differentiating the μ-equation
 * directly reduces to ordinary structural recursion over `Type` that never
 * follows recursive fields (that occurrence is the hole). No equation
 * solving, no quotient rule:
 *
 *   ∂a const = 0                        (no a inside → no contexts)
 *   ∂a (F + G) = ∂a F + ∂a G            (sum rule — the variant set)
 *   ∂a (F · G) = ∂a F · G + F · ∂a G    (Leibniz — the variant's fields)
 *   ∂a a = 1                            (the hole itself)
 *
 * The derivative never diverges: the only potentially-infinite unfolding of
 * a μ-type is through its recursive fields, and those are exactly the
 * positions the traversal stops at.
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
 *   stays bounded.
 */

import { DataType, IntersectionType, type Type } from "./types.ts"

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
