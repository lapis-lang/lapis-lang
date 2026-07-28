/**
 * LC Subtyping — the decision procedure for the subtyping relation `<:`.
 *
 * See _docs/theory/lc.md §4 for the formal specification.
 *
 * Implements:
 *   S-Refl, S-Top, S-Bot, S-Trans, S-Var (§4)
 *   S-Fun (§4.1)
 *   S-Data-Width, S-Data-Depth (§4.2)
 *   S-Codata-Width, S-Codata-Depth (§4.3)
 *   S-And-Intro, S-And-Elim (§4.4)
 */

import {
    Any,
    AnyType,
    CodataType,
    DataType,
    FunType,
    IntersectionType,
    Nothing,
    NothingType,
    PatternDataType,
    PolymorphicType,
    TokenType,
    type Type,
    TypeVar,
    TypeVarEnv,
} from "./types.ts"

/**
 * Check if `sub <: super_` in type variable context `delta`.
 *
 * This is the core operation of the type system. It implements the subtyping
 * rules from lc.md §4. The `delta` context provides bounds for type variables
 * (F<:). For closed types (no type variables), pass an empty TypeVarEnv.
 */
export function isSubtype(
    sub: Type,
    super_: Type,
    delta: TypeVarEnv = new TypeVarEnv(),
): boolean {
    // S-Bot: Nothing <: σ (for any σ)
    if (sub instanceof NothingType) return true

    // S-Top: σ <: Any (for any σ)
    if (super_ instanceof AnyType) return true

    // S-Refl: σ <: σ
    if (sub.equals(super_)) return true

    // S-Var: α <: σ (where σ is α's bound in Δ)
    if (sub instanceof TypeVar) {
        const bound = delta.lookup(sub.name)
        if (bound && isSubtype(bound, super_, delta)) return true
        // Also check if super_ is the same type variable
        if (super_ instanceof TypeVar && sub.name === super_.name) return true
    }

    // S-Fun: τ₁ <: σ₁ ∧ σ₂ <: τ₂ ⟹ σ₁→σ₂ <: τ₁→τ₂
    if (sub instanceof FunType && super_ instanceof FunType) {
        return isSubtype(super_.param, sub.param, delta) && // contravariant domain
            isSubtype(sub.result, super_.result, delta) // covariant codomain
    }

    // S-All: ∀α<:σ₁.τ₁ <: ∀α<:σ₂.τ₂  iff  σ₁ <: σ₂ ∧ σ₂ <: σ₁ ∧ τ₁ <: τ₂
    // (bounds must be equal, body is covariant under the bound)
    if (sub instanceof PolymorphicType && super_ instanceof PolymorphicType) {
        // Bounds must be equivalent (both directions)
        if (!isSubtype(sub.bound, super_.bound, delta)) return false
        if (!isSubtype(super_.bound, sub.bound, delta)) return false
        // Body is covariant, with α bound to super_'s bound in both contexts
        const delta1 = delta.extend(super_.typeVarName, super_.bound)
        return isSubtype(sub.body, super_.body, delta1)
    }

    // S-Data-Width + S-Data-Depth: μ-type subtyping
    if (sub instanceof DataType && super_ instanceof DataType) {
        return isDataTypeSubtype(sub, super_, delta)
    }

    // Pattern-matched data types: only reflexive (same name)
    if (sub instanceof PatternDataType && super_ instanceof PatternDataType) {
        return sub.equals(super_)
    }

    // S-Codata-Width + S-Codata-Depth: ν-type subtyping
    if (sub instanceof CodataType && super_ instanceof CodataType) {
        return isCodataTypeSubtype(sub, super_, delta)
    }

    // Token: only reflexive and <: Any (already handled by S-Top)
    if (sub instanceof TokenType && super_ instanceof TokenType) return true

    // S-And-Intro / S-And-Elim: intersection subtyping
    if (sub instanceof IntersectionType) {
        // S-And-Elim: σ ∧ τ <: σ (and σ ∧ τ <: τ)
        if (isSubtype(sub.left, super_, delta)) return true
        if (isSubtype(sub.right, super_, delta)) return true
    }
    if (super_ instanceof IntersectionType) {
        // S-And-Intro: σ <: τ₁ ∧ σ <: τ₂ ⟹ σ <: τ₁ ∧ τ₂
        if (
            isSubtype(sub, super_.left, delta) &&
            isSubtype(sub, super_.right, delta)
        ) {
            return true
        }
    }

    return false
}

/**
 * S-Data-Width + S-Data-Depth combined.
 *
 * Width: more variants = subtype (T has all of T's variants, possibly more).
 * Depth: field narrowing = subtype (T's field types <: T's field types).
 *
 * The guarded assumption `α <: T'` is handled by checking field types
 * recursively with the assumption that the recursive position is already
 * a subtype. In practice, we check field types structurally, which is
 * correct for non-mutually-recursive types. For deeply recursive types,
 * a coinductive check would be needed (future work).
 */
function isDataTypeSubtype(
    sub: DataType,
    super_: DataType,
    delta: TypeVarEnv,
): boolean {
    const subVariants = sub.allVariants()
    const superVariants = super_.allVariants()

    // S-Data-Width: every variant in super_ must be in sub
    for (const sv of superVariants) {
        const subVariant = subVariants.find((v) => v.name === sv.name)
        if (!subVariant) return false

        // S-Data-Depth: field types must be subtypes (covariant)
        if (subVariant.fields.length !== sv.fields.length) return false
        for (let i = 0; i < subVariant.fields.length; i++) {
            const subField = subVariant.fields[i]!
            const superField = sv.fields[i]!
            if (!isSubtype(subField.type, superField.type, delta)) {
                return false
            }
        }
    }

    return true
}

/**
 * S-Codata-Width + S-Codata-Depth combined.
 *
 * Width: more observers = subtype (T has all of T's observers, possibly more).
 * Depth: observer type narrowing = subtype (T's observer types <: T's,
 * contravariant).
 */
function isCodataTypeSubtype(
    sub: CodataType,
    super_: CodataType,
    delta: TypeVarEnv,
): boolean {
    const subObservers = sub.allObservers()
    const superObservers = super_.allObservers()

    // S-Codata-Width: every observer in super_ must be in sub
    for (const so of superObservers) {
        const subObs = subObservers.find((o) => o.name === so.name)
        if (!subObs) return false

        // S-Codata-Depth: observer types contravariant
        // T's observer type <: T's observer type means:
        // super_'s type <: sub's type (contravariant)
        if (!isSubtype(so.type, subObs.type, delta)) {
            return false
        }
    }

    return true
}

// ── Type equality ─────────────────────────────────────────────────────────────

/** Check if two types are structurally equal. */
export function typeEquals(a: Type, b: Type): boolean {
    return a.equals(b)
}

// ── Join and Meet: lattice operations ────────────────────────────────────────
//
// Adapted from TAPL §16.4 (fullfsub). These compute the least upper bound
// (join) and greatest lower bound (meet) of two types in the subtyping
// lattice. Used for:
//   - Fold result type inference (join of handler body types)
//   - Conditional branch type checking (join of both arms)
//   - Nothing propagation (meet with Nothing = Nothing)

/**
 * Compute the **join** (least upper bound) of `s` and `t` — the smallest
 * type that both `s` and `t` are subtypes of.
 *
 *   join(s, t) = t          if s <: t
 *   join(s, t) = s          if t <: s
 *   join(σ₁→σ₂, τ₁→τ₂) = (meet(σ₁, τ₁)) → (join(σ₂, τ₂))
 *   join(s, t) = Any        otherwise (no common supertype)
 */
export function join(
    s: Type,
    t: Type,
    delta: TypeVarEnv = new TypeVarEnv(),
): Type {
    if (isSubtype(s, t, delta)) return t
    if (isSubtype(t, s, delta)) return s

    // Nothing <: everything, so the above handles Nothing cases.
    // Any is handled: if either is Any, isSubtype(s, Any) = true → return Any.

    if (s instanceof FunType && t instanceof FunType) {
        const dom = meet(s.param, t.param, delta)
        return new FunType(dom, join(s.result, t.result, delta))
    }

    if (s instanceof PolymorphicType && t instanceof PolymorphicType) {
        // join of ∀α<:σ₁.τ₁ and ∀α<:σ₂.τ₂ = ∀α<:meet(σ₁,σ₂).join(τ₁,τ₂)
        // (if bounds are compatible)
        if (isSubtype(s.bound, t.bound, delta) && isSubtype(t.bound, s.bound, delta)) {
            const delta1 = delta.extend(s.typeVarName, s.bound)
            return new PolymorphicType(
                s.typeVarName,
                meet(s.bound, t.bound, delta),
                join(s.body, t.body, delta1),
            )
        }
    }

    // No common supertype found
    return Any
}

/**
 * Compute the **meet** (greatest lower bound) of `s` and `t` — the largest
 * type that is a subtype of both `s` and `t`.
 *
 *   meet(s, t) = s          if s <: t
 *   meet(s, t) = t          if t <: s
 *   meet(σ₁→σ₂, τ₁→τ₂) = (join(σ₁, τ₁)) → (meet(σ₂, τ₂))
 *   meet(s, t) = Nothing    otherwise (no common subtype)
 */
export function meet(
    s: Type,
    t: Type,
    delta: TypeVarEnv = new TypeVarEnv(),
): Type {
    if (isSubtype(s, t, delta)) return s
    if (isSubtype(t, s, delta)) return t

    if (s instanceof FunType && t instanceof FunType) {
        const dom = join(s.param, t.param, delta)
        return new FunType(dom, meet(s.result, t.result, delta))
    }

    if (s instanceof PolymorphicType && t instanceof PolymorphicType) {
        // meet of ∀α<:σ₁.τ₁ and ∀α<:σ₂.τ₂ = ∀α<:join(σ₁,σ₂).meet(τ₁,τ₂)
        if (isSubtype(s.bound, t.bound, delta) && isSubtype(t.bound, s.bound, delta)) {
            const delta1 = delta.extend(s.typeVarName, s.bound)
            return new PolymorphicType(
                s.typeVarName,
                join(s.bound, t.bound, delta),
                meet(s.body, t.body, delta1),
            )
        }
    }

    // No common subtype found
    return Nothing
}
