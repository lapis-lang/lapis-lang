/**
 * Lapis semantic types — the type system for the Lapis Core (LC).
 *
 * This file defines the types used by the semantic analysis passes
 * (name resolution, type checking, law checking). The type structure mirrors
 * the core calculus (see _docs/theory/lc.md §2.1):
 *
 *   σ, τ ::= α              type variable
 *          | σ → τ          function type (blocks, predicates, transforms)
 *          | μ α. Σᵢ Cᵢ(σᵢ)  recursive data type (sum of named variants)
 *          | μ α. Σᵢ pᵢ      pattern-matched data type (sum of pattern constructors)
 *          | ν α. Πⱼ oⱼ(σⱼ)  corecursive codata type (product of named observers)
 *          | Token           raw matched text
 *          | Any            top of the lattice
 *          | Nothing        bottom of the lattice
 *          | σ ∧ τ          intersection type (protocol conformance)
 *
 * NOTE: BaseType and the convenience constructors (Int, String_, Bool, etc.)
 * below are legacy from the pre-redesign skeleton. They will be replaced by
 * pattern-matched μ types during Stage 1 implementation (see
 * _docs/design-decisions.md §"No base types").
 *
 * The subtyping relation (<:) is the core of the type system — it subsumes
 * generics (see _docs/theory/lc.md §4). Subtyping rules:
 *   - S-Refl, S-Top, S-Bot, S-Trans, S-Var (basic)
 *   - S-Fun (contravariant domain, covariant codomain)
 *   - S-Data-Width (more variants = subtype; the `extend` mechanism)
 *   - S-Data-Depth (field narrowing = subtype)
 *   - S-Codata-Width (more observers = subtype)
 *   - S-Codata-Depth (observer type narrowing = subtype)
 *   - S-And-Intro, S-And-Elim (intersection / protocol conformance)
 *
 * Design note: Lapis avoids parametric polymorphism (generics) in favor of
 * subtyping. Following Meyer (OOSC) and Bracha (Pluggable Type Systems),
 * bounded quantification over a subtyping lattice recovers most of what
 * generics buy you. The cost — loss of parametricity — is recovered *by
 * declaration* via `properties` annotations (see _docs/theory/language-design.md §2.1).
 */

import type { Node } from './ast.ts';

// ── Base type class ───────────────────────────────────────────────────────────

/**
 * Base class for all Lapis types.
 *
 * Types form a subtyping lattice with `Any` at the top and `Nothing` at the
 * bottom. The subtyping relation is decidable and structural (see `isSubtypeOf`).
 */
export abstract class LapisType {
    /** Structural equality (not subtyping — use `isSubtypeOf` for that). */
    abstract equals(other: LapisType): boolean;

    /**
     * Subtyping check: is `this <: other`?
     *
     * This is the core operation of the type system. It implements the rules
     * from _docs/core-calculus.md §3:
     *   - S-Refl:  σ <: σ
     *   - S-Top:   σ <: Any
     *   - S-Bot:   Nothing <: σ
     *   - S-Trans: σ <: τ ∧ τ <: υ ⟹ σ <: υ
     *   - S-Fun:   τ₁ <: σ₁ ∧ σ₂ <: τ₂ ⟹ σ₁→σ₂ <: τ₁→τ₂
     *   - S-Data-Width:  more variants = subtype
     *   - S-Data-Depth:  field narrowing = subtype
     *   - S-Codata-Width: more observers = subtype
     *   - S-And-Intro/Elim: intersection types
     */
    abstract isSubtypeOf(other: LapisType): boolean;
}

// ── Base types ────────────────────────────────────────────────────────────────

/** Base (primitive) types: Int, String, Bool, Number, Object, Array, ... */
export class BaseType extends LapisType {
    constructor(readonly name: string) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof BaseType && this.name === other.name;
    }

    isSubtypeOf(other: LapisType): boolean {
        // S-Refl
        if (this.equals(other)) return true;
        // S-Top
        if (other instanceof AnyType) return true;
        // S-Bot (Nothing is a subtype of everything, but a base type isn't Nothing)
        // Base types have no structural subtyping among themselves (no Int <: Number
        // unless explicitly declared — future work: a numeric tower)
        return false;
    }
}

// ── Lattice bounds ───────────────────────────────────────────────────────────

/** `Any` — the top of the subtyping lattice. Every type is a subtype of Any. */
export class AnyType extends LapisType {
    equals(other: LapisType): boolean { return other instanceof AnyType; }
    isSubtypeOf(other: LapisType): boolean { return other instanceof AnyType; }
}

/** `Nothing` — the bottom of the subtyping lattice. Subtype of every type. */
export class NothingType extends LapisType {
    equals(other: LapisType): boolean { return other instanceof NothingType; }
    isSubtypeOf(_other: LapisType): boolean { return true; } // S-Bot
}

// ── Type variables ────────────────────────────────────────────────────────────

/** A type variable (used for bounded quantification — F<:). */
export class TypeVar extends LapisType {
    constructor(readonly name: string, readonly bound: LapisType) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof TypeVar && this.name === other.name;
    }

    isSubtypeOf(other: LapisType): boolean {
        // S-Refl
        if (this.equals(other)) return true;
        // S-Top
        if (other instanceof AnyType) return true;
        // A type variable is a subtype of its bound (S-Var)
        if (other.equals(this.bound)) return true;
        // Transitively, check the bound
        return this.bound.isSubtypeOf(other);
    }
}

// ── Function types ────────────────────────────────────────────────────────────

/** `σ → τ` — function type (blocks, predicates, transforms). */
export class FunType extends LapisType {
    constructor(readonly param: LapisType, readonly result: LapisType) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof FunType
            && this.param.equals(other.param)
            && this.result.equals(other.result);
    }

    isSubtypeOf(other: LapisType): boolean {
        // S-Refl
        if (this.equals(other)) return true;
        // S-Top
        if (other instanceof AnyType) return true;
        // S-Fun: contravariant in domain, covariant in codomain
        //   τ₁ <: σ₁  ∧  σ₂ <: τ₂  ⟹  σ₁→σ₂ <: τ₁→τ₂
        if (other instanceof FunType) {
            return other.param.isSubtypeOf(this.param)   // contravariant
                && this.result.isSubtypeOf(other.result); // covariant
        }
        return false;
    }
}

// ── Data types (μ-types — initial algebras) ───────────────────────────────────

/**
 * A variant constructor declaration: `Cᵢ(field₁: σ₁, field₂: σ₂, ...)`.
 *
 * The field types may contain `FamilyRef` positions (the recursive self-reference
 * `α`), which are replaced by the fold result type σ during fold type checking
 * (see _docs/core-calculus.md §4.3, T-Fold).
 */
export class VariantType {
    constructor(
        readonly name: string,           // PascalCase variant name
        readonly fields: FieldDecl[],    // field declarations
    ) {}
}

/** A field declaration within a variant: `fieldName: TypeName`. */
export class FieldDecl {
    constructor(
        readonly name: string,           // camelCase field name
        readonly type: LapisType,         // field type (may be FamilyRefType)
    ) {}
}

/**
 * `μ α. Σᵢ Cᵢ(Fᵢ(α))` — a recursive data type (initial algebra).
 *
 * The bound `α` is the recursive self-reference (`Family` in the surface syntax).
 * Subtyping:
 *   - S-Data-Width: more variants = subtype (the `extend` mechanism)
 *   - S-Data-Depth: field narrowing = subtype
 */
export class DataType extends LapisType {
    constructor(
        readonly name: string,            // type name
        readonly variants: VariantType[], // variant constructors
        readonly parent: DataType | null, // parent type (for comb inheritance)
    ) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof DataType && this.name === other.name;
    }

    isSubtypeOf(other: LapisType): boolean {
        // S-Refl
        if (this.equals(other)) return true;
        // S-Top
        if (other instanceof AnyType) return true;
        // S-Data-Width: check if all of `other`'s variants are in `this`'s variants
        // (this has more variants → subtype). Walk the parent chain for inherited
        // variants (comb inheritance).
        if (other instanceof DataType) {
            // Collect all variants from this type and its ancestors
            const myVariants = this.allVariants();
            const otherVariants = other.allVariants();

            // S-Data-Width: other's variants must be a subset of mine
            for (const ov of otherVariants) {
                const myVariant = myVariants.find(v => v.name === ov.name);
                if (!myVariant) return false; // missing variant → not a subtype

                // S-Data-Depth: each shared variant's fields must be subtypes
                // (field narrowing: NumList.Cons head:Number <: List.Cons head:Object)
                if (myVariant.fields.length !== ov.fields.length) return false;
                for (let i = 0; i < myVariant.fields.length; i++) {
                    if (!myVariant.fields[i]!.type.isSubtypeOf(ov.fields[i]!.type)) {
                        return false;
                    }
                }
            }
            return true;
        }
        return false;
    }

    /** All variants from this type and its parent chain (comb inheritance). */
    allVariants(): VariantType[] {
        const result = [...this.variants];
        if (this.parent) result.push(...this.parent.allVariants());
        return result;
    }

    /** Find a variant by name, searching the parent chain. */
    findVariant(name: string): VariantType | undefined {
        return this.allVariants().find(v => v.name === name);
    }
}

// ── Codata types (ν-types — final coalgebras) ─────────────────────────────────

/**
 * `ν α. Πⱼ oⱼ(Gⱼ(α))` — a corecursive codata type (final coalgebra).
 *
 * The bound `α` is the corecursive self-reference (`Self` in the surface syntax).
 * Subtyping:
 *   - S-Codata-Width: more observers = subtype (dual of data width)
 */
export class CodataType extends LapisType {
    constructor(
        readonly name: string,             // type name
        readonly observers: FieldDecl[],   // observer signatures
        readonly parent: CodataType | null, // parent type (for inheritance)
    ) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof CodataType && this.name === other.name;
    }

    isSubtypeOf(other: LapisType): boolean {
        // S-Refl
        if (this.equals(other)) return true;
        // S-Top
        if (other instanceof AnyType) return true;
        // S-Codata-Width: this has more observers → subtype
        // (a type that promises more observations can be used where fewer are expected)
        if (other instanceof CodataType) {
            const myObservers = this.allObservers();
            const otherObservers = other.allObservers();

            // other's observers must be a subset of mine
            for (const oo of otherObservers) {
                const myObs = myObservers.find(o => o.name === oo.name);
                if (!myObs) return false;
                // Contravariant in observer types (dual of covariant fields)
                if (!oo.type.isSubtypeOf(myObs.type)) return false;
            }
            return true;
        }
        return false;
    }

    /** All observers from this type and its parent chain. */
    allObservers(): FieldDecl[] {
        const result = [...this.observers];
        if (this.parent) result.push(...this.parent.allObservers());
        return result;
    }

    /** Find an observer by name, searching the parent chain. */
    findObserver(name: string): FieldDecl | undefined {
        return this.allObservers().find(o => o.name === name);
    }
}

// ── Intersection types (protocol conformance) ────────────────────────────────

/**
 * `σ ∧ τ` — intersection type. A value of type `σ ∧ τ` satisfies both.
 *
 * Used to express protocol conformance: `τ ∧ P` means "a τ that also satisfies
 * protocol P." See _docs/core-calculus.md §3.5.
 */
export class IntersectionType extends LapisType {
    constructor(readonly left: LapisType, readonly right: LapisType) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof IntersectionType
            && this.left.equals(other.left)
            && this.right.equals(other.right);
    }

    isSubtypeOf(other: LapisType): boolean {
        // S-Refl
        if (this.equals(other)) return true;
        // S-Top
        if (other instanceof AnyType) return true;
        // S-And-Elim: σ <: τ₁ ∧ τ₂ ⟹ σ <: τ₁ (and σ <: τ₂)
        // An intersection is a subtype of either component
        if (this.left.isSubtypeOf(other) || this.right.isSubtypeOf(other)) return true;
        // An intersection is a subtype of another intersection if both components match
        if (other instanceof IntersectionType) {
            return this.left.isSubtypeOf(other.left) && this.right.isSubtypeOf(other.right);
        }
        return false;
    }
}

// ── Protocol types ───────────────────────────────────────────────────────────

/**
 * A protocol type — a set of operation signatures that a type must satisfy.
 *
 * Protocol conformance `τ satisfies P` is modeled as `τ <: P` (intersection:
 * `τ ∧ P`). See _docs/core-calculus.md §3.5 and _docs/elaboration.md §3.3.
 *
 * Conformance is checked structurally: a type satisfies a protocol if it
 * declares all the protocol's required operations with compatible signatures.
 */
export class ProtocolType extends LapisType {
    constructor(
        readonly name: string,
        readonly requiredOps: Map<string, LapisType>,  // operation name → signature
        readonly parent: ProtocolType | null,
    ) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof ProtocolType && this.name === other.name;
    }

    isSubtypeOf(other: LapisType): boolean {
        // S-Refl
        if (this.equals(other)) return true;
        // S-Top
        if (other instanceof AnyType) return true;
        // A protocol is a subtype of another protocol if it requires at least
        // the same operations (more requirements = subtype, dual of data width)
        if (other instanceof ProtocolType) {
            const myOps = this.allRequiredOps();
            const otherOps = other.allRequiredOps();
            for (const [name, sig] of otherOps) {
                const mySig = myOps.get(name);
                if (!mySig) return false;
                if (!mySig.isSubtypeOf(sig)) return false;
            }
            return true;
        }
        return false;
    }

    /** All required operations from this protocol and its parent chain. */
    allRequiredOps(): Map<string, LapisType> {
        const result = new Map(this.requiredOps);
        if (this.parent) {
            for (const [k, v] of this.parent.allRequiredOps()) result.set(k, v);
        }
        return result;
    }
}

// ── Recursive self-references ─────────────────────────────────────────────────

/**
 * `Family` — the recursive self-reference in a data type (the μ-bound α).
 *
 * In a fold handler, `Family`-typed fields arrive as the *already-folded* result
 * (of type σ), not as the raw sub-structure. See T-Fold in
 * _docs/core-calculus.md §4.3.
 */
export class FamilyRefType extends LapisType {
    constructor(readonly targetType: DataType) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof FamilyRefType
            && this.targetType.name === other.targetType.name;
    }

    isSubtypeOf(other: LapisType): boolean {
        // Family is a subtype of its target type (and Any)
        if (other instanceof AnyType) return true;
        return this.targetType.isSubtypeOf(other);
    }
}

/**
 * `Self` — the corecursive self-reference in a codata type (the ν-bound α).
 *
 * In an unfold generator, `Self`-typed observers produce the next codata value
 * (lazily). See T-Unfold in _docs/core-calculus.md §4.5.
 */
export class SelfRefType extends LapisType {
    constructor(readonly targetType: CodataType) { super(); }

    equals(other: LapisType): boolean {
        return other instanceof SelfRefType
            && this.targetType.name === other.targetType.name;
    }

    isSubtypeOf(other: LapisType): boolean {
        if (other instanceof AnyType) return true;
        return this.targetType.isSubtypeOf(other);
    }
}

// ── Typed AST nodes ───────────────────────────────────────────────────────────

/**
 * A typed expression — an AST node annotated with its type.
 *
 * This is the output of the type-checking pass. Each expression carries its
 * inferred/checked type, so downstream passes (law checking, evaluation) don't
 * need to re-derive it.
 */
export class TypedExpr {
    constructor(
        readonly node: Node,       // the original AST node
        readonly type: LapisType,   // the type of this expression
    ) {}
}

// ── Type environment ───────────────────────────────────────────────────────────

/**
 * The type environment Γ — maps names to types.
 *
 * This is the inherited attribute threaded through the type-checking grammar
 * subclass (see _docs/semantics.md §5.3). It flows top-down: each production
 * that binds a name extends Γ for its sub-terms.
 */
export class TypeEnv {
    private readonly bindings: Map<string, LapisType>;

    constructor(entries?: Map<string, LapisType>) {
        this.bindings = entries ?? new Map();
    }

    /** Look up a name's type. Returns undefined if not bound. */
    lookup(name: string): LapisType | undefined {
        return this.bindings.get(name);
    }

    /** Extend the environment with a new binding. Returns a new env (immutable). */
    extend(name: string, type: LapisType): TypeEnv {
        const next = new Map(this.bindings);
        next.set(name, type);
        return new TypeEnv(next);
    }

    /** Extend with multiple bindings. */
    extendAll(entries: [string, LapisType][]): TypeEnv {
        const next = new Map(this.bindings);
        for (const [name, type] of entries) next.set(name, type);
        return new TypeEnv(next);
    }
}

// ── Name environment (for name resolution) ───────────────────────────────────

/**
 * The name environment — maps names to their declarations.
 *
 * Used by the name-resolution pass (the first semantic layer above the base
 * grammar). Resolves variant references, type references, and operation names.
 */
export class NameEnv {
    private readonly types: Map<string, DataType | CodataType | ProtocolType>;
    private readonly variants: Map<string, { type: string; variant: VariantType }>;
    private readonly operations: Map<string, { type: string; op: string }>;

    constructor(
        types?: Map<string, DataType | CodataType | ProtocolType>,
        variants?: Map<string, { type: string; variant: VariantType }>,
        operations?: Map<string, { type: string; op: string }>,
    ) {
        this.types = types ?? new Map();
        this.variants = variants ?? new Map();
        this.operations = operations ?? new Map();
    }

    lookupType(name: string): DataType | CodataType | ProtocolType | undefined {
        return this.types.get(name);
    }

    lookupVariant(name: string): { type: string; variant: VariantType } | undefined {
        return this.variants.get(name);
    }

    lookupOperation(name: string): { type: string; op: string } | undefined {
        return this.operations.get(name);
    }

    extendType(name: string, type: DataType | CodataType | ProtocolType): NameEnv {
        const types = new Map(this.types);
        types.set(name, type);
        return new NameEnv(types, this.variants, this.operations);
    }

    extendVariant(variantName: string, typeName: string, variant: VariantType): NameEnv {
        const variants = new Map(this.variants);
        variants.set(variantName, { type: typeName, variant });
        return new NameEnv(this.types, variants, this.operations);
    }

    extendOperation(opName: string, typeName: string, op: string): NameEnv {
        const operations = new Map(this.operations);
        operations.set(opName, { type: typeName, op });
        return new NameEnv(this.types, this.variants, operations);
    }
}

// ── Convenience constructors ──────────────────────────────────────────────────

export const Any = new AnyType();
export const Nothing = new NothingType();
export const Int = new BaseType('Int');
export const String_ = new BaseType('String');
export const Bool = new BaseType('Bool');
export const Number_ = new BaseType('Number');
export const Object_ = new BaseType('Object');
export const Array_ = new BaseType('Array');