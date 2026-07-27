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
 */

// ── Type ──────────────────────────────────────────────────────────────────────

/** The root of the LC type hierarchy. Every type is a subtype of this. */
export abstract class Type {
    /** Structural equality (not subtyping — use `isSubtype` for that). */
    abstract equals(other: Type): boolean;

    /** Human-readable representation for debugging. */
    abstract toString(): string;
}

// ── Type variable ─────────────────────────────────────────────────────────────

/** `α` — a type variable, used for bounded quantification (F<:). */
export class TypeVar extends Type {
    constructor(
        readonly name: string,
        readonly bound: Type,
    ) {
        super();
    }

    equals(other: Type): boolean {
        return other instanceof TypeVar && this.name === other.name;
    }

    toString(): string {
        return this.name;
    }
}

// ── Function type ─────────────────────────────────────────────────────────────

/** `σ → τ` — function type (blocks, predicates, transforms). */
export class FunType extends Type {
    constructor(
        readonly param: Type,
        readonly result: Type,
    ) {
        super();
    }

    equals(other: Type): boolean {
        return other instanceof FunType
            && this.param.equals(other.param)
            && this.result.equals(other.result);
    }

    toString(): string {
        return `(${this.param} → ${this.result})`;
    }
}

// ── Data type (μ) ─────────────────────────────────────────────────────────────

/**
 * A variant constructor: `Cᵢ(field₁: σ₁, field₂: σ₂, ...)`.
 *
 * Fields may contain `FamilyRef` at the recursive position (the μ-bound α).
 * `isRecursive` marks whether a field is a Family (recursive) position.
 */
export class Variant {
    constructor(
        readonly name: string,
        readonly fields: Field[],
    ) {}

    findField(name: string): Field | undefined {
        return this.fields.find((f) => f.name === name);
    }
}

/** A field within a variant: `fieldName: Type`. */
export class Field {
    constructor(
        readonly name: string,
        readonly type: Type,
        readonly isRecursive: boolean = false,
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
    /** Mutable to allow self-referential μ-type construction (create empty, then push variants). */
    variants: Variant[];
    parent: DataType | null;

    constructor(
        readonly name: string,
        variants: Variant[],
        parent: DataType | null = null,
    ) {
        super();
        this.variants = variants;
        this.parent = parent;
    }

    equals(other: Type): boolean {
        return other instanceof DataType && this.name === other.name;
    }

    toString(): string {
        return this.name;
    }

    /** All variants from this type and its parent chain (comb inheritance). */
    allVariants(): Variant[] {
        const result = [...this.variants];
        if (this.parent) result.push(...this.parent.allVariants());
        return result;
    }

    /** Find a variant by name, searching the parent chain. */
    findVariant(name: string): Variant | undefined {
        return this.allVariants().find((v) => v.name === name);
    }
}

// ── Pattern-matched data type (μ with patterns) ───────────────────────────────

/**
 * `μ α. Σᵢ pᵢ` — a pattern-matched data type.
 *
 * Each `pᵢ` is a pattern (a restricted regular expression) specifying an
 * infinite set of constructors. There are no fields (no Family); the sole
 * inhabitant of a matched constructor is the `Token` — the raw matched text.
 */
export class PatternDataType extends Type {
    constructor(
        readonly name: string,
        readonly patterns: string[],
    ) {
        super();
    }

    equals(other: Type): boolean {
        return other instanceof PatternDataType && this.name === other.name;
    }

    toString(): string {
        return this.name;
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
    constructor(
        readonly name: string,
        readonly observers: Observer[],
        readonly parent: CodataType | null = null,
    ) {
        super();
    }

    equals(other: Type): boolean {
        return other instanceof CodataType && this.name === other.name;
    }

    toString(): string {
        return this.name;
    }

    /** All observers from this type and its parent chain. */
    allObservers(): Observer[] {
        const result = [...this.observers];
        if (this.parent) result.push(...this.parent.allObservers());
        return result;
    }

    /** Find an observer by name, searching the parent chain. */
    findObserver(name: string): Observer | undefined {
        return this.allObservers().find((o) => o.name === name);
    }
}

/** An observer declaration: `oⱼ: σⱼ`. May contain `SelfRef` at the corecursive position. */
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
        return other instanceof TokenType;
    }

    toString(): string {
        return "Token";
    }
}

/** Singleton instance of the Token type. */
export const Token = new TokenType();

// ── Lattice bounds ────────────────────────────────────────────────────────────

/** `Any` — the top of the subtyping lattice. Every type is a subtype of Any. */
export class AnyType extends Type {
    equals(other: Type): boolean {
        return other instanceof AnyType;
    }

    toString(): string {
        return "Any";
    }
}

/** `Nothing` — the bottom of the subtyping lattice. Subtype of every type. */
export class NothingType extends Type {
    equals(other: Type): boolean {
        return other instanceof NothingType;
    }

    toString(): string {
        return "Nothing";
    }
}

/** Singleton instances of the lattice bounds. */
export const Any = new AnyType();
export const Nothing = new NothingType();

// ── Intersection type ─────────────────────────────────────────────────────────

/** `σ ∧ τ` — intersection type. A value of type `σ ∧ τ` satisfies both. */
export class IntersectionType extends Type {
    constructor(
        readonly left: Type,
        readonly right: Type,
    ) {
        super();
    }

    equals(other: Type): boolean {
        return other instanceof IntersectionType
            && this.left.equals(other.left)
            && this.right.equals(other.right);
    }

    toString(): string {
        return `(${this.left} ∧ ${this.right})`;
    }
}

// ── Type context (Δ) ──────────────────────────────────────────────────────────

/**
 * `Δ` — the type variable context, mapping type variable names to their bounds.
 * Used for bounded quantification (F<:).
 */
export class TypeVarEnv {
    private readonly bindings: Map<string, Type>;

    constructor(entries?: Map<string, Type>) {
        this.bindings = entries ?? new Map();
    }

    lookup(name: string): Type | undefined {
        return this.bindings.get(name);
    }

    extend(name: string, bound: Type): TypeVarEnv {
        const next = new Map(this.bindings);
        next.set(name, bound);
        return new TypeVarEnv(next);
    }
}

// ── Term variable context (Γ) ─────────────────────────────────────────────────

/**
 * `Γ` — the term variable context, mapping term names to their types.
 * This is the inherited attribute threaded through the typing rules.
 */
let typeEnvCounter = 0;

export class TypeEnv {
    private readonly bindings: Map<string, Type>;
    /** Unique ID for treeKey distinction (@rule caching in zipper-grammar). */
    readonly _id: number;

    constructor(entries?: Map<string, Type>) {
        this.bindings = entries ?? new Map();
        this._id = ++typeEnvCounter;
    }

    lookup(name: string): Type | undefined {
        return this.bindings.get(name);
    }

    extend(name: string, type: Type): TypeEnv {
        const next = new Map(this.bindings);
        next.set(name, type);
        return new TypeEnv(next);
    }

    /** Check if a name is bound. */
    has(name: string): boolean {
        return this.bindings.has(name);
    }
}