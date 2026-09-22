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
 *
 * ## Construction protocol (persistent builders)
 *
 * `DataType`/`CodataType` are immutable VALUES built through persistent
 * builders: `define(name, parent?)` returns a builder handle;
 * `addVariant`/`addObserver` return a NEW builder (the receiver is
 * unchanged); `build()` publishes a fresh frozen instance. A field may
 * reference the builder to name the type being built — the direct
 * self-reference knot (`Self = Base | Wrap(inner: Self)`), resolved at
 * `build()` time. The knot was chosen over a lazy type reference because a
 * thunk cannot be initialized before `build()` consumes it without a
 * post-build fixup pass; the builder handle is inert until publication, so
 * one resolution walk suffices and no construction-phase mutator survives
 * on the type. Identity tracks shape by construction — every `addVariant`
 * and every `build()` produces a distinct object — so instance-keyed
 * caches are sound with no precondition and no invalidation path. Mutually
 * referencing definitions build as a group (`DataType.buildAll`);
 * `Variant`/`Field`/`Observer` are frozen at their own construction; the
 * `Family` μ-bound singleton is orthogonal to the protocol. */

// The pattern AST type — pattern_lang.ts owns the language; this import is
// type-only (a cycle-free edge: pattern_lang.ts imports the pattern TYPE here).
import type { PatternAST } from "./pattern_lang.ts"

/**
 * The nominal brand symbol for the Type universe — MODULE-PRIVATE. An outside
 * module can neither create an equal symbol (Symbol equality is by reference)
 * nor copy the property onto a forged object, so the membership check is a
 * genuine identity test, not a forgeable tag. Exposed only through
 * `isDeclaredTypeKind` (below), which consults the private symbol.
 */
const TYPE_BRAND = Symbol("lapis-lang/Type")

/**
 * Nominal membership in the Type universe: consults the module-private brand
 * symbol. The property lives on `Type.prototype` (an instance field on the
 * abstract root), so only declared subclasses' instances carry it — and a
 * caller cannot COPY it onto a plain object without possessing the private
 * symbol, which this module does not export. This is the boundary
 * `isTypeValue` (subtyping.ts) validates before the `dispatch` protocol.
 */
export function isDeclaredTypeKind(t: unknown): boolean {
    return t !== null && typeof t === "object" &&
        (t as { [TYPE_BRAND]?: true })[TYPE_BRAND] === true
}

// ── Type ──────────────────────────────────────────────────────────────────────
/** The root of the LC type hierarchy. Every type is a subtype of this. */
export abstract class Type {
    /**
     * The closed-universe brand: every instance of a declared Type subclass
     * carries this marker through the prototype chain, so nominal membership
     * is checkable WITHOUT relying on the structural `dispatch` protocol (any
     * object with a compatible `dispatch` method would otherwise pass a
     * duck-typed test). The brand is a module-private symbol — outside
     * modules cannot forge it.
     */
    readonly [TYPE_BRAND]: true = true

    /** Structural equality (not subtyping — use `isSubtype` for that). */
    abstract equals(other: Type): boolean

    /** Human-readable representation for debugging. */
    abstract toString(): string

    /**
     * Dispatch this type's shape to a case table WITHOUT structural
     * recursion — the classification-style fold: the narrowed `this` and,
     * for composite kinds, the immediate sub-types are handed to the
     * matching case, and whatever the analysis computes (a tag, a summary,
     * a count) comes back.
     *
     * Implemented per subclass (each kind knows its own arm — the same
     * polymorphism `equals`/`toString` already exercise); the closed
     * universe is the class hierarchy itself, so an undeclared subclass
     * reaching a generic consumer throws loudly from the root default.
     *
     * The REQUIRED-case form: a table that omits a kind is a compile error
     * (`RequiredCases<T>`), and an omitted arm reaching the root default
     * throws at runtime — a caller bug surfaced loudly, never a silent
     * `undefined`.
     *
     * Contrast with `map` (bottom-up, defaultable cases, rebuilds types):
     * `dispatch` is for consumers that reduce a type to a value; `map` is
     * for consumers that transform it.
     */
    abstract dispatch<T>(cases: RequiredCases<T>): T

    /**
     * Map this type bottom-up: every sub-type is mapped first, then the
     * node's case handler sees the mapped children. A handler returning
     * `undefined` keeps the structurally-defaulted node (children
     * substituted, shape rebuilt, unchanged when no child moved) — so a
     * substitution only spells the kinds it transforms.
     *
     * Implemented per subclass, like `dispatch`: atom kinds have no
     * traversable sub-types (their arm runs the optional handler, keeping
     * the node unchanged when it yields `undefined`); the composite kinds
     * (`FunType`, `IntersectionType`, `PolymorphicType`) override to map
     * their children first. A pass-local marker outside the universe
     * throws from both virtuals — there is no structural reading of it.
     *
     * Shadowing note: at a `PolymorphicType` node the handler runs AFTER
     * the children are mapped; a shadowing handler returns the ORIGINAL
     * node (discarding the mapped children), so a substitution's
     * no-descend rule is expressed by returning the original binder.
     */
    abstract map(cases: TypeCases<Type>): Type

    /**
     * Resolve the μ-bound occurrence against a carrier: a `Family`-typed
     * field IS the recursion, so its type is the carrier it recurses
     * through; every other kind is itself.
     *
     * The μ-bound is a TYPE (the same binder/occurrence mechanism as a
     * ∀-bound variable), so the resolution is intrinsic and lives on the
     * subclasses, the same tier `equals`/`toString` exercise. Each pass
     * resolves the binder against the carrier it is analyzing (the
     * context, not the singleton, makes it that carrier) — exactly as a
     * bound variable resolves against its context.
     */
    /**
     * Resolve the μ-bound occurrence against a carrier: a `Family`-typed
     * field IS the recursion, so its type is the carrier it recurses
     * through; every other kind is itself.
     *
     * The base implementation is the identity — only the μ-bound occurrence
     * itself resolves differently, so only `FamilyType` overrides. The
     * μ-bound is a TYPE (the same binder/occurrence mechanism as a
     * ∀-bound variable), so the resolution is intrinsic and lives on the
     * subclasses, the same tier `equals`/`toString` exercise. Each pass
     * resolves the binder against the carrier it is analyzing (the
     * context, not the singleton, makes it that carrier) — exactly as a
     * bound variable resolves against its context. A pass-local marker
     * outside the universe throws (no μ-bound to resolve).
     */
    resolveFamily(_carrier: DataType): Type {
        return this
    }
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

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.typeVar(this)
    }

    /** An atom: no traversable sub-types; the base `map` default applies. */
    override map(cases: TypeCases<Type>): Type {
        return cases.typeVar?.(this) ?? this
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
 * non-recursive position (the re-entrancy case the enumerators handle): the
 * type says which one it is.
 */
export class FamilyType extends Type {
    equals(other: Type): boolean {
        return other instanceof FamilyType
    }

    toString(): string {
        return "Family"
    }

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.family(this)
    }

    /** An atom: no traversable sub-types; the base `map` default applies. */
    override map(cases: TypeCases<Type>): Type {
        return cases.family?.(this) ?? this
    }

    /**
     * THE μ-bound occurrence: resolved against the analyzing carrier —
     * the context (the traversal consuming this singleton) supplies the
     * carrier, exactly as a bound variable resolves against its context.
     */
    override resolveFamily(carrier: DataType): Type {
        return carrier
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

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.fun(this, this.param, this.result)
    }

    /**
     * Bottom-up: both children mapped first, then the handler sees the
     * mapped param/result. `undefined` keeps the structurally-defaulted
     * node — the ORIGINAL when neither child moved (no allocation), a
     * rebuilt `FunType` when one did.
     */
    override map(cases: TypeCases<Type>): Type {
        const p = this.param.map(cases)
        const r = this.result.map(cases)
        return cases.fun?.(this, p, r) ??
            (p === this.param && r === this.result ? this : new FunType(p, r))
    }
}

// ── Data type (μ) ─────────────────────────────────────────────────────────────

/**
 * A variant constructor: `Cᵢ(field₁: σ₁, field₂: σ₂, ...)`.
 *
 * A field's type may be `Family` at the recursive position (the μ-bound α).
 * The fields array is frozen AT CONSTRUCTION: a variant is an immutable
 * value from the moment it exists, so a retained alias cannot mutate any
 * definition that carries it.
 */
export class Variant {
    readonly fields: readonly Field[]

    constructor(
        readonly name: string,
        fields: Field[],
    ) {
        this.fields = Object.freeze(fields)
        Object.freeze(this)
    }

    findField(name: string): Field | undefined {
        return this.fields.find((f) => f.name === name)
    }
}

/**
 * The type slot during construction: a resolved `Type`, or an unresolved
 * builder reference — the self-reference knot (a field may name the type
 * being built through its builder, resolved by `build()`).
 *
 * The union exists at CONSTRUCTION time only: `build()` rewrites builder
 * slots to the built instances, so every published `Field`/`Observer`
 * carries a genuine `Type` behind its getter. Reading the type of a
 * retained pre-build field throws loudly — nothing unresolved can leak
 * into the closed `Type` universe.
 */
export type TypeSlot = Type | DataTypeBuilder | CodataBuilder

/**
 * The read side of a type slot: a builder reference reaching a consumer is
 * a caller bug (a field that never went through `build()`) — rejected
 * loudly, never silently read as a type.
 */
function resolvedSlotType(slot: TypeSlot, what: string): Type {
    if (slot instanceof DataTypeBuilder || slot instanceof CodataBuilder) {
        throw new TypeError(
            `${what} is unresolved — its builder reference was never resolved by build()`,
        )
    }
    return slot
}

/** A field within a variant: `fieldName: Type` — frozen AT CONSTRUCTION. */
export class Field {
    #slot: TypeSlot

    constructor(
        readonly name: string,
        type: TypeSlot,
    ) {
        this.#slot = type
        Object.freeze(this)
    }

    /** The field's type — always a resolved `Type` on a published definition. */
    get type(): Type {
        return resolvedSlotType(this.#slot, `field "${this.name}"`)
    }

    /**
     * Resolve an unresolved builder slot against a build group: the original
     * field when the slot is already a resolved type, a NEW field carrying
     * the built instance when the slot's lineage is in the group, a loud
     * rejection when the reference cannot resolve (a foreign lineage, or the
     * other construction kind — mixed data/codata groups are not supported).
     */
    resolveBuild(group: BuildGroup): Field | undefined {
        if (this.#slot instanceof DataTypeBuilder || this.#slot instanceof CodataBuilder) {
            const resolved = group.get(this.#slot.lineage)
            if (resolved === undefined) {
                throw new TypeError(
                    `field "${this.name}" references a builder outside the build group — ` +
                        `every unresolved reference must resolve within the same build call`,
                )
            }
            return new Field(this.name, resolved)
        }
        return undefined
    }
}

/**
 * The build-time resolution map: a lineage token (shared by every builder
 * derived from one `define()` call) → the instance publishing for it.
 */
export type BuildGroup = Map<object, DataType | CodataType>

/**
 * `μ α. Σᵢ Cᵢ(σᵢ)` — a recursive data type (initial algebra).
 *
 * The bound `α` is the recursive self-reference (`Family` in the surface syntax).
 * `variants` is the sum (tagged union). `parent` is the supertype for comb
 * inheritance (null for base types).
 *
 * Persistent construction (see the module doc): instances are immutable on
 * publication — the constructor is private, `define(name, parent?)` returns
 * a builder, and `build()` publishes a fresh frozen instance. Identity
 * tracks shape: two builds (or two builder derivations) are distinct
 * objects, which is what makes instance-keyed caches sound with no
 * precondition.
 */
export class DataType extends Type {
    // The variants array is swapped exactly once, inside `buildAll` (before
    // publication): instances are constructed with the raw variants, then
    // the resolved (knotted) variants replace them. A published instance
    // never changes again — `private` keeps the swap module-internal.
    private _variants: readonly Variant[]
    readonly parent: DataType | null

    private constructor(
        readonly name: string,
        variants: readonly Variant[],
        parent: DataType | null,
    ) {
        super()
        this._variants = Object.freeze(variants)
        this.parent = parent
    }

    /** Begin construction: a builder handle for a data type definition. */
    static define(name: string, parent: DataType | null = null): DataTypeBuilder {
        return DataTypeBuilder.initial(name, parent)
    }

    /**
     * Build a mutually referencing group in one pass: every builder in the
     * group may reference every other (through the builder handle), and all
     * references resolve simultaneously at publication. Duplicate lineages
     * in one group reject.
     */
    static buildAll(...builders: DataTypeBuilder[]): DataType[] {
        if (builders.length === 0) return []
        const group: BuildGroup = new Map<object, DataType | CodataType>()
        for (const b of builders) {
            if (group.has(b.lineage)) {
                throw new TypeError(
                    `buildAll: the builder for ${b.name} appears twice — one lineage, one slot`,
                )
            }
            group.set(b.lineage, undefined as unknown as DataType | CodataType)
        }
        // Construction order: the instances exist first (nothing reads their
        // fields yet), the group fills with THOSE instances, then each
        // definition's variants resolve against the completed map and are
        // installed — the returned instances ARE the map's values, so a
        // knotted field names the final instance of its lineage. A mixed-kind
        // group (a data builder reaching a codata publication) rejects with a
        // message naming both kinds — the group is single-kind, never mixed.
        const instances = builders.map((b) => new DataType(b.name, b.variants, b.parent))
        builders.forEach((b, i) => group.set(b.lineage, instances[i]!))
        builders.forEach((b, i) => {
            instances[i]!._variants = Object.freeze(resolveVariantFields(b.variants, group))
        })
        return instances
    }

    /**
     * The variants — a frozen array: the definition is immutable from the
     * moment it exists (post-construction mutation is impossible, not
     * merely rejected).
     */
    get variants(): readonly Variant[] {
        return this._variants
    }

    equals(other: Type): boolean {
        return other instanceof DataType && this.name === other.name
    }

    toString(): string {
        return this.name
    }

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.data(this)
    }

    /** An atom: the base `map` default applies (no traversable sub-types). */
    override map(cases: TypeCases<Type>): Type {
        return cases.data?.(this) ?? this
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

/**
 * The persistent builder for a `DataType`: `define` starts one, every
 * `addVariant` derives a NEW builder (the receiver's lineage is unchanged),
 * and `build()` publishes a fresh frozen instance carrying the accumulated
 * variants — the self-reference knot resolving on the way.
 */
export class DataTypeBuilder {
    /** The lineage token shared by every builder derived from one `define()`. */
    readonly lineage: object

    private constructor(
        readonly name: string,
        readonly parent: DataType | null,
        readonly variants: readonly Variant[],
        lineage: object,
    ) {
        this.lineage = lineage
    }

    static initial(name: string, parent: DataType | null): DataTypeBuilder {
        return new DataTypeBuilder(name, parent, [], {})
    }

    /** Derive a builder carrying these variants in addition to the current ones. */
    addVariant(...variants: Variant[]): DataTypeBuilder {
        return new DataTypeBuilder(
            this.name,
            this.parent,
            [...this.variants, ...variants],
            this.lineage,
        )
    }

    /** Publish a fresh immutable instance (two builds are distinct objects). */
    build(): DataType {
        return DataType.buildAll(this)[0]!
    }
}

/**
 * A group's variants with the knot resolved: fields whose slots are already
 * resolved types keep their ORIGINAL objects (no allocation); unresolved
 * builder references produce NEW fields carrying the built instance.
 */
function resolveVariantFields(
    variants: readonly Variant[],
    group: BuildGroup,
): Variant[] {
    return variants.map((variant) => {
        const mapped = variant.fields.map((f) => f.resolveBuild(group))
        return mapped.some((f) => f !== undefined)
            ? new Variant(variant.name, mapped.map((f, i) => f ?? variant.fields[i]!))
            : variant
    })
}

/** The observers' counterpart of `resolveVariantFields` (one slot per observer). */
function resolveObserverFields(
    observers: readonly Observer[],
    group: BuildGroup,
): Observer[] {
    return observers.map((observer) => observer.resolveBuild(group) ?? observer)
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

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.patternData(this)
    }

    /** An atom: the base `map` default applies (no traversable sub-types). */
    override map(cases: TypeCases<Type>): Type {
        return cases.patternData?.(this) ?? this
    }
}

// ── Codata type (ν) ───────────────────────────────────────────────────────────

/**
 * `ν α. Πⱼ oⱼ(σⱼ)` — a corecursive codata type (final coalgebra).
 *
 * The bound `α` is the corecursive self-reference (`Self` in the surface syntax).
 * `observers` is the product (record of observations). `parent` is the supertype.
 *
 * Persistent construction mirrors `DataType` exactly: `define` returns a
 * builder, `addObserver` derives a new builder, `build()` publishes a fresh
 * frozen instance — immutable on publication, identity tracking shape.
 */
export class CodataType extends Type {
    // The observers array's pre-publication swap (see `DataType._variants`).
    private _observers: readonly Observer[]
    readonly parent: CodataType | null

    private constructor(
        readonly name: string,
        observers: readonly Observer[],
        parent: CodataType | null,
    ) {
        super()
        this._observers = Object.freeze(observers)
        this.parent = parent
    }

    /** Begin construction: a builder handle for a codata type definition. */
    static define(name: string, parent: CodataType | null = null): CodataBuilder {
        return CodataBuilder.initial(name, parent)
    }

    /**
     * Build a mutually referencing group in one pass (see
     * `DataType.buildAll`): the ν-side of a mutual knot — an observer may
     * name the codata type being built through any builder of the group.
     */
    static buildAll(...builders: CodataBuilder[]): CodataType[] {
        if (builders.length === 0) return []
        const group: BuildGroup = new Map<object, DataType | CodataType>()
        for (const b of builders) {
            if (group.has(b.lineage)) {
                throw new TypeError(
                    `buildAll: the builder for ${b.name} appears twice — one lineage, one slot`,
                )
            }
            group.set(b.lineage, undefined as unknown as DataType | CodataType)
        }
        const instances = builders.map((b) => new CodataType(b.name, b.observers, b.parent))
        builders.forEach((b, i) => group.set(b.lineage, instances[i]!))
        builders.forEach((b, i) => {
            instances[i]!._observers = Object.freeze(resolveObserverFields(b.observers, group))
        })
        return instances
    }

    /**
     * The observers — a frozen array (see `DataType.variants`): immutable
     * from the moment the definition exists.
     */
    get observers(): readonly Observer[] {
        return this._observers
    }

    equals(other: Type): boolean {
        return other instanceof CodataType && this.name === other.name
    }

    toString(): string {
        return this.name
    }

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.codata(this)
    }

    /** An atom: the base `map` default applies (no traversable sub-types). */
    override map(cases: TypeCases<Type>): Type {
        return cases.codata?.(this) ?? this
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

/**
 * The persistent builder for a `CodataType` (see `DataTypeBuilder`):
 * `define` starts one, `addObserver` derives a new builder, `build()`
 * publishes a fresh frozen instance with the knot resolved.
 */
export class CodataBuilder {
    /** The lineage token shared by every builder derived from one `define()`. */
    readonly lineage: object

    private constructor(
        readonly name: string,
        readonly parent: CodataType | null,
        readonly observers: readonly Observer[],
        lineage: object,
    ) {
        this.lineage = lineage
    }

    static initial(name: string, parent: CodataType | null): CodataBuilder {
        return new CodataBuilder(name, parent, [], {})
    }

    /** Derive a builder carrying these observers in addition to the current ones. */
    addObserver(...observers: Observer[]): CodataBuilder {
        return new CodataBuilder(
            this.name,
            this.parent,
            [...this.observers, ...observers],
            this.lineage,
        )
    }

    /** Publish a fresh immutable instance (two builds are distinct objects). */
    build(): CodataType {
        return CodataType.buildAll(this)[0]!
    }
}

/**
 * An observer declaration: `oⱼ: σⱼ`. A continuation observer's type names
 * the codata type itself (the ν-side self-reference — a data field, not a
 * flag; `allObservers` reads it like any other observer type).
 *
 * The type slot follows `Field`'s discipline: a builder reference is
 * accepted at construction (the self-reference knot) and resolved by
 * `build()`; the public `type` getter always hands back a genuine `Type`.
 */
export class Observer {
    private readonly slot: TypeSlot

    constructor(
        readonly name: string,
        type: TypeSlot,
        readonly isContinuation: boolean = false,
    ) {
        this.slot = type
    }

    /** The observer's type — always a resolved `Type` on a published definition. */
    get type(): Type {
        return resolvedSlotType(this.slot, `observer "${this.name}"`)
    }

    /**
     * Resolve an unresolved builder slot against a build group (see
     * `Field.resolveBuild`): the original observer when already resolved, a
     * NEW observer carrying the built instance when the reference resolves,
     * a loud rejection otherwise.
     */
    resolveBuild(group: BuildGroup): Observer | undefined {
        if (this.slot instanceof DataTypeBuilder || this.slot instanceof CodataBuilder) {
            const resolved = group.get(this.slot.lineage)
            if (resolved === undefined) {
                throw new TypeError(
                    `observer "${this.name}" references a builder outside the build group — ` +
                        `every unresolved reference must resolve within the same build call`,
                )
            }
            return new Observer(this.name, resolved, this.isContinuation)
        }
        return undefined
    }
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

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.token(this)
    }

    /** An atom: the base `map` default applies (no traversable sub-types). */
    override map(cases: TypeCases<Type>): Type {
        return cases.token?.(this) ?? this
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

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.any(this)
    }

    /** An atom: the base `map` default applies (no traversable sub-types). */
    override map(cases: TypeCases<Type>): Type {
        return cases.any?.(this) ?? this
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

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.nothing(this)
    }

    /** An atom: the base `map` default applies (no traversable sub-types). */
    override map(cases: TypeCases<Type>): Type {
        return cases.nothing?.(this) ?? this
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

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.intersection(this, this.left, this.right)
    }

    /**
     * Bottom-up: both children mapped first, then the handler sees the
     * mapped left/right. `undefined` keeps the structurally-defaulted
     * node — the ORIGINAL when neither child moved, rebuilt otherwise.
     */
    override map(cases: TypeCases<Type>): Type {
        const l = this.left.map(cases)
        const r = this.right.map(cases)
        return cases.intersection?.(this, l, r) ??
            (l === this.left && r === this.right ? this : new IntersectionType(l, r))
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

    override dispatch<T>(cases: RequiredCases<T>): T {
        return cases.polymorphic(this, this.bound, this.body)
    }

    /**
     * Bottom-up: the bound and body mapped first, then the handler sees
     * the mapped children. `undefined` keeps the structurally-defaulted
     * node — the ORIGINAL when neither child moved, rebuilt otherwise.
     *
     * Shadowing note: the handler runs AFTER the children are mapped; a
     * shadowing handler returns the ORIGINAL node (discarding the mapped
     * children), so a substitution's no-descend rule is expressed by
     * returning the original binder.
     */
    override map(cases: TypeCases<Type>): Type {
        const b = this.bound.map(cases)
        const body = this.body.map(cases)
        return cases.polymorphic?.(this, b, body) ??
            (b === this.bound && body === this.body
                ? this
                : new PolymorphicType(this.typeVarName, b, body))
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

// ── Structural dispatch (the TypeCases protocol) ─────────────────────────────

/**
 * The case protocol over the Type universe — the one dispatch every pass
 * shares. Each case handler receives the type (narrowed) and, for the
 * composite kinds, its recursive sub-types.
 *
 * Consumers invoke the dispatch polymorphically: `t.dispatch(cases)` (the
 * required-case classification fold) and `t.map(cases)` (the bottom-up
 * transformation) are virtual methods on `Type`, implemented per subclass —
 * a new Type subclass implements its own dispatch arm, so the closed
 * universe is enforced by the class hierarchy itself. The case tables stay
 * external: per-judgment actions are supplied per call.
 *
 * The handler returns are deliberately optional-result (`T | undefined`):
 * `map` reads `undefined` as "keep the structural default" (the node
 * unchanged for atoms, rebuilt from mapped children for composites), and
 * `dispatch` treats it as an omitted arm (the required-case compile
 * contract `RequiredCases<T>` makes omission a caller bug — the runtime
 * then surfaces a missing arm as a loud TypeError from the caller's `!`).
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
 * The case protocol, REQUIRED-case form: a table that omits a kind is a
 * compile error — the classification-style fold's contract (a new Type
 * subclass forces every case table to answer for it). `dispatch` requires
 * this form; an arm that yields `undefined` is a caller bug, not a case to
 * default (the classification fold must never silently produce one). The
 * `-?` strips the optionality the `TypeCases` mapping would otherwise
 * preserve. The parameter types stay loose (`any` + rest) because the
 * per-kind signatures vary — `dispatch`'s implementors narrow internally.
 */
export type RequiredCases<T> = {
    // deno-lint-ignore no-explicit-any
    [K in keyof TypeCases<T>]-?: (t: any, ...rest: any[]) => T
}

/**
 * The free-function surface for the virtuals (compatibility exports): the
 * dispatch itself lives on the subclasses as `Type.dispatch`/`Type.map` —
 * these are the same-signature entry points the original API carried, so
 * existing consumers keep importing them. New code calls the methods
 * directly.
 */

/**
 * The classification-style fold — the virtual `Type.dispatch`. Free-function
 * surface.
 */
// deno-lint-ignore no-explicit-any
export function foldType<T>(t: Type, cases: TypeCases<T> & Record<keyof TypeCases<never>, any>): T {
    return t.dispatch(cases)
}

/**
 * The bottom-up transformation — the virtual `Type.map`. Free-function
 * surface.
 */
export function mapType(t: Type, cases: TypeCases<Type>): Type {
    return t.map(cases)
}
