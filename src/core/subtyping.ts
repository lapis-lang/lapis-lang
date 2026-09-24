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
    isDeclaredTypeKind,
    Nothing,
    NothingType,
    PolymorphicType,
    TokenType,
    type Type,
    TypeVar,
    TypeVarEnv,
} from "./types.ts"

import { patternToString } from "./pattern_lang.ts"

/**
 * The Type-universe membership test: is this value actually a declared
 * kind? This is the lattice module's boundary — ONE validation at the
 * module's entry: the invariant is enforced at its construction point, not
 * scattered in prose.
 *
 * The grammar edge already enforces the deeper invariant (every
 * production-path override rejects a failed premise with `empty<Type>()`
 * BEFORE a contracted action runs, so the failure sentinel cannot flow into
 * a Type-typed channel); this check is what makes a BYPASSED edge crash
 * loudly instead of silently satisfying a rule — `requireType` throws a
 * TypeError naming the non-type operand, so a leaked sentinel can never
 * satisfy a premise.
 *
 * Routed through `t.dispatch` — a new Type subclass must answer here or the
 * boundary refuses it (the closed-universe assumption is checked, not
 * assumed).
 *
 * This is the ONE definition of "member of the closed universe" — the
 * typing grammar's `isWellFormedType` check reuses it, so a new subclass
 * cannot satisfy one consumer while being refused by the other.
 */
export function isTypeValue(t: unknown): t is Type {
    if (t === undefined || t === null) return false
    // Nominal brand check FIRST — through `isDeclaredTypeKind` (types.ts),
    // which consults the module-private brand symbol: a plain object with a
    // compatible `dispatch` method (or any forged duck-type) is refused
    // before the protocol is ever consulted — the dispatch result is data,
    // not identity, and the brand cannot be forged without the private
    // symbol.
    if (!isDeclaredTypeKind(t)) return false
    try {
        ;(t as Type).dispatch<boolean>({
            fun: () => true,
            intersection: () => true,
            polymorphic: () => true,
            typeVar: () => true,
            family: () => true,
            data: () => true,
            codata: () => true,
            token: () => true,
            any: () => true,
            nothing: () => true,
        })
        return true
    } catch {
        return false
    }
}

/**
 * Validate a lattice operand; a non-type throws (loud, never absorbed).
 * `caller` names the public API performing the validation, so the thrown
 * message points at the failing function (`isSubtype: sub operand …`) —
 * misattributed diagnostics would send a debugger to the wrong call site.
 */
function requireType(operand: Type, side: string, caller: string): Type {
    if (!isTypeValue(operand)) {
        throw new TypeError(
            `${caller}: ${side} operand is not a Type (the failure sentinel ` +
                `and foreign values cannot enter the lattice — the grammar edge ` +
                `rejects a failed premise with empty<Type>(), never undefined)`,
        )
    }
    return operand
}

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
    // The parameters are typed `Type` (strict null checks forbid undefined)
    // and the grammar edge enforces the invariant: every production-path
    // override rejects a failed premise with `empty<Type>()` BEFORE any
    // contracted action runs, so `undefined` (the contract-failure sentinel)
    // cannot reach the lattice as an operand. A bypassed edge is a caller
    // bug — `requireType` throws loudly, never silently satisfying a
    // premise via S-Top.
    requireType(sub, "sub", "isSubtype")
    requireType(super_, "super", "isSubtype")

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
        // Same-name variables in the same Δ slot are THE binder: name identity
        // is the promotion rule, not S-Refl's structural equality. This is
        // deliberately name-only, unlike `TypeVar.equals` (which includes the
        // bound): here both operands are being read against the SAME Δ
        // context, so equal names are guaranteed equal bounds by the context —
        // the context, not the type, is what makes them the same binder. A
        // free-standing TypeVar (no Δ) that reaches S-Var falls to the
        // conservative name-only recovery below, which is the F<: treatment
        // the calculus's bounded quantification requires (lc.md §4).
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
    if (sub instanceof DataType && super_ instanceof DataType) {
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

    // S-Data-Width (pattern members): every pattern member the SUPER's
    // lineage declares must be declared in the SUB's lineage by canonical
    // source — a pattern member's width contribution is its declared
    // CONSTRUCTOR identity (a pattern the sub's lineage lacks is an
    // inhabitant the sub cannot produce). Depth does not apply: patterns
    // bind no fields.
    for (const superPattern of super_.allPatterns()) {
        const source = patternToString(superPattern)
        if (sub.findPattern(source) === undefined) return false
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

/**
 * Check if two types are structurally equal — a delegate over the Type
 * hierarchy's own `.equals`. Kept as a named export because the lattice's
 * consumers read it as "the equality operator on σ"; the grammar-edge
 * invariant makes a leaked sentinel a caller bug, not a case to guard.
 */
export function typeEquals(a: Type, b: Type): boolean {
    requireType(a, "a", "typeEquals")
    requireType(b, "b", "typeEquals")
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
    // `Type`-typed operands (strict null checks) + the grammar-edge invariant
    // (a failed premise is `empty<Type>()`, never a leaked sentinel) keep the
    // lattice's operands types; `requireType` (via `isSubtype`) throws on a
    // bypassed edge.
    requireType(s, "s", "join")
    requireType(t, "t", "join")

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
    // `requireType` validates both operands once at the entry — the
    // invariant is enforced here, not per-guard downstream.
    requireType(s, "s", "meet")
    requireType(t, "t", "meet")

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
