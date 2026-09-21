/**
 * LC Types — the type system of the Lapis Core Calculus (F_{<:μν}).
 *
 * See _docs/theory/lc.md §2.1 for the formal specification.
 *
 *   σ, τ ::= α                  type variable
 *          | σ → τ              function type
 *          | μ α. Σᵢ Cᵢ(σᵢ)      recursive data type (sum of named variants)
 *          | μ α. Σᵢ pᵢ          pattern-matched data type (sum of pattern constructors)
 *          | ν α. Πⱼ oⱼ(σⱼ)      corecursive codata type (product of named observers)
 *          | Token               raw matched text
 *          | Any                 top
 *          | Nothing             bottom
 *          | σ ∧ τ              intersection type
 *
 * The μ-bound α occurring at a field's recursive position is spelled as the
 * `Family` singleton (`FamilyType`) — the same bound-variable mechanism as
 * ∀-quantification: a binder (the μ) and an occurrence (the field type). A
 * field whose type is `Family` IS the recursion; there is no parallel flag.
 */

// The pattern AST type — pattern_lang.ts owns the language; this import is
// type-only (a cycle-free edge: pattern_lang.ts imports the pattern TYPE here).
import type { PatternAST } from "./pattern_lang.ts"

// ── Type ──────────────────────────────────────────────────────────────────────

/** The root of the LC type hierarchy. Every type is a subtype of this. */
export abstract class Type {
    /** Structural equality (not subtyping — use `isSubtype` for that). */
    abstract equals(other: Type): boolean

    /** Human-readable representation for debugging. */
    abstract toString(): string
}

// ── Type variable ─────────────────────────────────────────────────────────────

/** `α` — a type variable, used for bounded quantification (F<:). */
export class TypeVar extends Type {
    constructor(
        readonly name: string,
        readonly bound: Type,
    ) {
        super()
    }

    /** The bound is part of the binder: two same-named variables with
     * different bounds are different binders. */
    equals(other: Type): boolean {
        return other instanceof TypeVar &&
            this.name === other.name &&
            this.bound.equals(other.bound)
    }

    toString(): string {
        return this.name
    }
}

// ── Family (the μ-bound reference) ───────────────────────────────────────────

/**
 * `α` at a recursive position — the μ-bound self-reference (surface: Family).
 *
 * A field typed `Family` inside a `DataType`'s variant is an occurrence of
 * the μ-bound: the same mechanism as a ∀-bound variable occurring in a
 * polymorphic type's body. The singleton carries no carrier reference — the
 * μ it belongs to is resolved by the traversal consuming it (the carrier
 * under analysis), exactly as a bound variable is resolved by the context.
 *
 * A field typed as the carrier's DataType instance (without `Family`) is a
 * genuine data field that happens to name the same type — a distinct,
 * non-recursive position (the re-entrancy case the enumerators handle). The
 * two are no longer confusable: the type says which one it is.
 */
export class FamilyType extends Type {
    equals(other: Type): boolean {
        return other instanceof FamilyType
    }

    toString(): string {
        return "Family"
    }
}

/** Singleton instance of the μ-bound reference. */
export const Family = new FamilyType()

// ── Function type ─────────────────────────────────────────────────────────────

/** `σ → τ` — function type (blocks, predicates, transforms). */
export class FunType extends Type {
    constructor(
        readonly param: Type,
        readonly result: Type,
    ) {
        super()
    }

    equals(other: Type): boolean {
        return other instanceof FunType &&
            this.param.equals(other.param) &&
            this.result.equals(other.result)
    }

    toString(): string {
        return `(${this.param} → ${this.result})`
    }
}

// ── Data type (μ) ─────────────────────────────────────────────────────────────

/**
 * A variant constructor: `Cᵢ(field₁: σ₁, field₂: σ₂, ...)`.
 *
 * A field's type may be `Family` at the recursive position (the μ-bound α).
 */
export class Variant {
    constructor(
        readonly name: string,
        readonly fields: Field[],
    ) {}
    /**
     * Close this variant: the fields array is frozen in place, so a
     * retained alias cannot mutate a sealed definition. `DataType.seal()`
     * seals every variant it carries; a direct call is idempotent.
     */
    seal(): this {
        Object.freeze(this.fields)
        return this
    }
    findField(name: string): Field | undefined {
        return this.fields.find((f) => f.name === name)
    }
}

/** A field within a variant: `fieldName: Type`. */
export class Field {
    constructor(
        readonly name: string,
        readonly type: Type,
    ) {}
}

/**
 * `μ α. Σᵢ Cᵢ(σᵢ)` — a recursive data type (initial algebra).
 *
 * The bound `α` is the recursive self-reference (`Family` in the surface syntax).
 * `variants` is the sum (tagged union). `parent` is the supertype for comb
 * inheritance (null for base types).
 */
export class DataType extends Type {
    /** The construction-phase array (private — mutation flows through
     * `addVariant` only, which rejects a post-`seal()` call). */
    private readonly _variants: Variant[]
    parent: DataType | null

    private sealed = false

    constructor(
        readonly name: string,
        variants: Variant[] = [],
        parent: DataType | null = null,
    ) {
        super()
        this._variants = variants
        this.parent = parent
    }

    /**
     * The variants — readonly in the type: mutation happens only through
     * `addVariant` during the construction phase, so a post-construction
     * mutation attempt is a COMPILE error, not a runtime failure. After
     * `seal()` the array is also frozen at runtime (an alias-retaining
     * caller cannot mutate it either).
     */
    get variants(): readonly Variant[] {
        return this._variants
    }

    /**
     * Add variants during the construction phase (before `seal()`).
     * A post-`seal()` call is a caller bug — it throws, never a silent
     * corruption. Re-using a variant (from another type) is rejected: a
     * sealed variant cannot re-enter construction.
     */
    addVariant(...variants: Variant[]): this {
        if (this.sealed) {
            throw new TypeError(
                `addVariant: ${this.name} is sealed — the definition is closed`,
            )
        }
        for (const variant of variants) {
            if (Object.isFrozen(variant.fields)) {
                throw new TypeError(
                    `addVariant: ${variant.name} is already sealed — ` +
                        `a variant cannot be re-used across type definitions`,
                )
            }
        }
        this._variants.push(...variants)
        return this
    }

    /**
     * Close the definition: the variants array AND every variant's fields
     * array are frozen in place, so a retained alias (the type's own array,
     * a variant, a fields array) cannot mutate the sealed definition.
     * Further construction is rejected loudly. Types are values.
     */
    seal(): this {
        if (this.sealed) return this
        this.sealed = true
        for (const variant of this._variants) variant.seal()
        Object.freeze(this._variants)
        return this
    }

    equals(other: Type): boolean {
        return other instanceof DataType && this.name === other.name
    }

    toString(): string {
        return this.name
    }

    /** All variants from this type and its parent chain (comb inheritance). */
    allVariants(): Variant[] {
        const result = [...this.variants]
        if (this.parent) result.push(...this.parent.allVariants())
        return result
    }

    /** Find a variant by name, searching the parent chain. */
    findVariant(name: string): Variant | undefined {
        return this.allVariants().find((v) => v.name === name)
    }
}

// ── Pattern-matched data type (μ with patterns) ───────────────────────────────

/**
 * `μ α. Σᵢ pᵢ` — a pattern-matched data type.
 *
 * Each `pᵢ` is a parsed pattern (a restricted regular expression — see
 * `pattern_lang.ts`) specifying an infinite set of constructors. There are
 * no fields (no Family); the sole inhabitant of a matched constructor is the
 * `Token` — the raw matched text. The AST is stored (not the source string):
 * the language-equation reading (`pattern_lang.ts` — concatenation multiplies,
 * alternation sums, Kleene star inverts (1−P)) reads the structure, and
 * rendering back to source is the AST's `toString`.
 */
export class PatternDataType extends Type {
    constructor(
        readonly name: string,
        readonly patterns: PatternAST[],
    ) {
        super()
    }

    equals(other: Type): boolean {
        return other instanceof PatternDataType && this.name === other.name
    }

    toString(): string {
        return this.name
    }
}

// ── Codata type (ν) ───────────────────────────────────────────────────────────

/**
 * `ν α. Πⱼ oⱼ(σⱼ)` — a corecursive codata type (final coalgebra).
 *
 * The bound `α` is the corecursive self-reference (`Self` in the surface syntax).
 * `observers` is the product (record of observations). `parent` is the supertype.
 */
export class CodataType extends Type {
    /** The construction-phase array (private — mutate through `addObserver`); see `DataType`. */
    private readonly _observers: Observer[]
    parent: CodataType | null

    private sealed = false

    constructor(
        readonly name: string,
        observers: Observer[] = [],
        parent: CodataType | null = null,
    ) {
        super()
        this._observers = observers
        this.parent = parent
    }

    /**
     * The observers — readonly in the type (see `DataType.variants`); after
     * `seal()` the array is also frozen at runtime.
     */
    get observers(): readonly Observer[] {
        return this._observers
    }

    /** Add observers during the construction phase (before `seal()`); a
     * post-`seal()` call throws (see `DataType.addVariant`). */
    addObserver(...observers: Observer[]): this {
        if (this.sealed) {
            throw new TypeError(
                `addObserver: ${this.name} is sealed — the definition is closed`,
            )
        }
        this._observers.push(...observers)
        return this
    }

    /** Close the definition (see `DataType.seal`). */
    seal(): this {
        if (this.sealed) return this
        this.sealed = true
        Object.freeze(this._observers)
        return this
    }

    equals(other: Type): boolean {
        return other instanceof CodataType && this.name === other.name
    }

    toString(): string {
        return this.name
    }

    /** All observers from this type and its parent chain. */
    allObservers(): Observer[] {
        const result = [...this.observers]
        if (this.parent) result.push(...this.parent.allObservers())
        return result
    }

    /** Find an observer by name, searching the parent chain. */
    findObserver(name: string): Observer | undefined {
        return this.allObservers().find((o) => o.name === name)
    }
}

/** An observer declaration: `oⱼ: σⱼ`. A continuation observer's type names
 * the codata type itself (the ν-side self-reference — a data field, not a
 * flag; `allObservers` reads it like any other observer type). */
export class Observer {
    constructor(
        readonly name: string,
        readonly type: Type,
        readonly isContinuation: boolean = false,
    ) {}
}

// ── Token type ────────────────────────────────────────────────────────────────

/** `Token` — raw matched text from the lexer. The one non-μ/ν primitive. */
export class TokenType extends Type {
    equals(other: Type): boolean {
        return other instanceof TokenType
    }

    toString(): string {
        return "Token"
    }
}

/** Singleton instance of the Token type. */
export const Token = new TokenType()

// ── Lattice bounds ────────────────────────────────────────────────────────────

/** `Any` — the top of the subtyping lattice. Every type is a subtype of Any. */
export class AnyType extends Type {
    equals(other: Type): boolean {
        return other instanceof AnyType
    }

    toString(): string {
        return "Any"
    }
}

/** `Nothing` — the bottom of the subtyping lattice. Subtype of every type. */
export class NothingType extends Type {
    equals(other: Type): boolean {
        return other instanceof NothingType
    }

    toString(): string {
        return "Nothing"
    }
}

/** Singleton instances of the lattice bounds. */
export const Any = new AnyType()
export const Nothing = new NothingType()

// ── Intersection type ─────────────────────────────────────────────────────────

/** `σ ∧ τ` — intersection type. A value of type `σ ∧ τ` satisfies both. */
export class IntersectionType extends Type {
    constructor(
        readonly left: Type,
        readonly right: Type,
    ) {
        super()
    }

    equals(other: Type): boolean {
        return other instanceof IntersectionType &&
            this.left.equals(other.left) &&
            this.right.equals(other.right)
    }

    toString(): string {
        return `(${this.left} ∧ ${this.right})`
    }
}

// ── Polymorphic type (F<:) ────────────────────────────────────────────────────

/**
 * `∀α <: σ. τ` — a bounded polymorphic type (universal quantification).
 *
 * The bound `σ` constrains the type variable `α`. The body `τ` may reference `α`.
 * This is distinct from `FunType(σ, τ)` — a function type `σ → τ` is not
 * polymorphic. `T-TApp` requires a `PolymorphicType`, not a `FunType`.
 */
export class PolymorphicType extends Type {
    constructor(
        readonly typeVarName: string,
        readonly bound: Type,
        readonly body: Type,
    ) {
        super()
    }

    equals(other: Type): boolean {
        return other instanceof PolymorphicType &&
            this.typeVarName === other.typeVarName &&
            this.bound.equals(other.bound) &&
            this.body.equals(other.body)
    }

    toString(): string {
        return `∀${this.typeVarName} <: ${this.bound}. ${this.body}`
    }
}

// ── Type context (Δ) ──────────────────────────────────────────────────────────

/**
 * `Δ` — the type variable context, mapping type variable names to their bounds.
 * Used for bounded quantification (F<:).
 */
export class TypeVarEnv {
    private readonly bindings: Map<string, Type>

    constructor(entries?: Map<string, Type>) {
        this.bindings = entries ?? new Map()
    }

    lookup(name: string): Type | undefined {
        return this.bindings.get(name)
    }

    extend(name: string, bound: Type): TypeVarEnv {
        const next = new Map(this.bindings)
        next.set(name, bound)
        return new TypeVarEnv(next)
    }
}

// ── Term variable context (Γ) ─────────────────────────────────────────────────

/**
 * `Γ` — the term variable context, mapping term names to their types.
 * This is the inherited attribute threaded through the typing rules.
 */
export class TypeEnv {
    private readonly bindings: Map<string, Type>

    constructor(entries?: Map<string, Type>) {
        this.bindings = entries ?? new Map()
    }

    lookup(name: string): Type | undefined {
        return this.bindings.get(name)
    }

    extend(name: string, type: Type): TypeEnv {
        const next = new Map(this.bindings)
        next.set(name, type)
        return new TypeEnv(next)
    }

    /** Check if a name is bound. */
    has(name: string): boolean {
        return this.bindings.has(name)
    }
}

// ── Structural dispatch (foldType) ───────────────────────────────────────────

/**
 * The generic structural recursion over the Type universe — the one
 * traversal every pass shares.
 *
 * Each case handler receives the type (narrowed) and, for the composite
 * kinds, its recursive sub-types. A case returning `undefined` delegates to
 * the structural default (recurse into sub-types, rebuild composites);
 * otherwise the returned `Type` replaces the node. Leaf kinds with no
 * handler and no sub-types return themselves.
 *
 * This is the shape `substituteTypeVar` (typing), the cost algebra's kind
 * classification, and the coefficient machinery's dispatch all walk — one
 * case table instead of N hand-rolled `instanceof` ladders.
 */
export interface TypeCases<T> {
    typeVar?: (t: TypeVar) => T | undefined
    family?: (t: FamilyType) => T | undefined
    fun?: (t: FunType, param: T, result: T) => T | undefined
    data?: (t: DataType) => T | undefined
    patternData?: (t: PatternDataType) => T | undefined
    codata?: (t: CodataType) => T | undefined
    token?: (t: TokenType) => T | undefined
    any?: (t: AnyType) => T | undefined
    nothing?: (t: NothingType) => T | undefined
    intersection?: (t: IntersectionType, left: T, right: T) => T | undefined
    polymorphic?: (t: PolymorphicType, bound: T, body: T) => T | undefined
}

/**
 * Dispatch on the type's shape, with the structural default for unhandled
 * cases: recurse into sub-types via `map` and rebuild composite kinds. The
 * `undefined` protocol lets a case handler bail out to the default (see
 * `mapType`).
 *
 * Internally untyped (the handler return types vary per kind — a generic
 * signature would force every caller through the same cast); the typed
 * entries are `mapType` and `foldType`.
 */
// deno-lint-ignore no-explicit-any
function dispatchType(t: Type, cases: TypeCases<any>): unknown {
    if (t instanceof TypeVar) {
        return cases.typeVar?.(t) ?? t
    }
    if (t instanceof FamilyType) {
        return cases.family?.(t) ?? t
    }
    if (t instanceof FunType) {
        // Unreachable via `mapType` (its FunType arm runs first); this default
        // exists only for a direct `dispatchType` call with no handler.
        return cases.fun?.(t, t.param, t.result) ?? new FunType(t.param, t.result)
    }
    if (t instanceof DataType) {
        return cases.data?.(t) ?? t
    }
    if (t instanceof PatternDataType) {
        return cases.patternData?.(t) ?? t
    }
    if (t instanceof CodataType) {
        return cases.codata?.(t) ?? t
    }
    if (t instanceof TokenType) {
        return cases.token?.(t) ?? t
    }
    if (t instanceof AnyType) {
        return cases.any?.(t) ?? t
    }
    if (t instanceof NothingType) {
        return cases.nothing?.(t) ?? t
    }
    if (t instanceof IntersectionType) {
        return cases.intersection?.(t, t.left, t.right) ?? new IntersectionType(t.left, t.right)
    }
    if (t instanceof PolymorphicType) {
        return cases.polymorphic?.(t, t.bound, t.body) ??
            new PolymorphicType(t.typeVarName, t.bound, t.body)
    }
    // Unreachable for every declared kind — an unknown subclass reaches
    // here only if someone extends Type outside this module. Loud, not
    // silent.
    throw new TypeError(`foldType: unknown Type subclass ${t.constructor.name}`)
}

/**
 * Map a type bottom-up: every sub-type is mapped first, then the node's
 * case handler sees the mapped children. A handler returning `undefined`
 * keeps the structurally-defaulted node (children substituted, shape
 * rebuilt, unchanged when no child moved) — so a substitution only spells
 * the kinds it transforms.
 *
 * `FamilyType`, `DataType`, `PatternDataType`, `CodataType`, and the
 * lattice/token leaves are atoms (no traversable sub-types); their default
 * returns the node unchanged.
 *
 * Shadowing note: at a `PolymorphicType` node the handler runs AFTER the
 * children are mapped; a shadowing handler returns the ORIGINAL node
 * (discarding the mapped children), so a substitution's no-descend rule is
 * expressed by returning the original binder.
 */
export function mapType(t: Type, cases: TypeCases<Type>): Type {
    if (t instanceof FunType) {
        const p = mapType(t.param, cases)
        const r = mapType(t.result, cases)
        return cases.fun?.(t, p, r) ?? (p === t.param && r === t.result ? t : new FunType(p, r))
    }
    if (t instanceof IntersectionType) {
        const l = mapType(t.left, cases)
        const r = mapType(t.right, cases)
        return cases.intersection?.(t, l, r) ??
            (l === t.left && r === t.right ? t : new IntersectionType(l, r))
    }
    if (t instanceof PolymorphicType) {
        const b = mapType(t.bound, cases)
        const body = mapType(t.body, cases)
        return cases.polymorphic?.(t, b, body) ??
            (b === t.bound && body === t.body ? t : new PolymorphicType(t.typeVarName, b, body))
    }
    // Atoms: dispatch (a handler may still transform the leaf).
    return dispatchType(t, cases) as Type
}

/**
 * Dispatch a type's shape to a case table WITHOUT structural recursion —
 * the classification-style fold: each case receives the narrowed type and,
 * for composite kinds, its immediate sub-types, and returns whatever the
 * analysis computes (a tag, a summary, a count). Every case is REQUIRED —
 * a table that omits a kind is a compile error, which is the point: a new
 * Type subclass forces every case table to answer for it.
 *
 * Contrast with `mapType` (bottom-up, defaultable cases, rebuilds types):
 * `foldType` is for consumers that reduce a type to a value; `mapType` is
 * for consumers that transform it.
 */
// deno-lint-ignore no-explicit-any
export function foldType<T>(t: Type, cases: TypeCases<T> & Record<keyof TypeCases<never>, any>): T {
    if (t instanceof FunType) {
        return cases.fun!(t, t.param, t.result)
    }
    if (t instanceof IntersectionType) {
        return cases.intersection!(t, t.left, t.right)
    }
    if (t instanceof PolymorphicType) {
        return cases.polymorphic!(t, t.bound, t.body)
    }
    if (t instanceof TypeVar) {
        return cases.typeVar!(t)
    }
    if (t instanceof FamilyType) {
        return cases.family!(t)
    }
    if (t instanceof DataType) {
        return cases.data!(t)
    }
    if (t instanceof PatternDataType) {
        return cases.patternData!(t)
    }
    if (t instanceof CodataType) {
        return cases.codata!(t)
    }
    if (t instanceof TokenType) {
        return cases.token!(t)
    }
    if (t instanceof AnyType) {
        return cases.any!(t)
    }
    if (t instanceof NothingType) {
        return cases.nothing!(t)
    }
    // Unreachable for every declared kind — an unknown subclass reaches
    // here only if someone extends Type outside this module. Loud, not
    // silent.
    throw new TypeError(`foldType: unknown Type subclass ${t.constructor.name}`)
}
