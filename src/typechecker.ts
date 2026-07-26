/**
 * Lapis type checker — the second semantic layer above the base grammar.
 *
 * Architecture (see _docs/semantics.md §5 and _docs/grammar-as-semantics.md):
 *
 *   LapisGrammar              (characters → AST)           — src/grammar.ts
 *     → LapisNameResolver     (AST → resolved AST)         — src/nameresolver.ts
 *       → LapisTypeChecker    (resolved AST → typed AST)  — this file
 *         → LapisLawChecker   (typed AST → verified AST)  — src/lawchecker.ts (planned)
 *           → LapisEvaluator   (verified AST → Values)     — src/evaluator.ts (planned)
 *
 * The type checker threads a `TypeEnv` (Γ) top-down as an inherited attribute
 * and synthesizes types bottom-up as return values. It implements the typing
 * rules from _docs/core-calculus.md §4:
 *
 *   T-Var:     Γ(x) = σ  ⟹  Γ ⊢ x : σ
 *   T-Abs:     Γ, x:σ ⊢ t : τ  ⟹  Γ ⊢ λx:σ.t : σ → τ
 *   T-App:     Γ ⊢ t : σ→τ  ∧  Γ ⊢ u : σ  ⟹  Γ ⊢ t u : τ
 *   T-Variant: Γ ⊢ tⱼ : Fₖ(σ)[α:=T]  ⟹  Γ ⊢ Cₖ(tⱼ) : T
 *   T-Fold:    Γ ⊢ e : T  ∧  Γ ⊢ hᵢ : Fᵢ(σ)[α:=σ]→σ  ⟹  Γ ⊢ fold_T e {...} : σ
 *   T-Obs:     Γ ⊢ e : T  ⟹  Γ ⊢ e.oₖ : Gₖ(T)[α:=T]
 *   T-Unfold:  Γ ⊢ s : Σ  ∧  Γ ⊢ gⱼ : Σ→Gⱼ(Σ)[α:=Σ]  ⟹  Γ ⊢ unfold_T s {...} : T
 *   T-Cofold:  Γ ⊢ e : T  ∧  Γ ⊢ h : Πⱼ(Gⱼ(σ)[α:=σ])→σ  ⟹  Γ ⊢ cofold_T e {...} : σ
 *   T-TAbs:    Δ, α<:σ ⊢ t : τ  ⟹  Δ ⊢ Λα<:σ.t : ∀α<:σ.τ
 *   T-TApp:    Γ ⊢ t : ∀α<:σ.τ  ∧  Δ ⊢ υ<:σ  ⟹  Γ ⊢ t[υ] : τ[α:=υ]
 *   T-Let:     Γ ⊢ t : σ  ∧  Γ,x:σ ⊢ u : τ  ⟹  Γ ⊢ let x:σ=t in u : τ
 *   T-Sub:     Γ ⊢ t : σ  ∧  σ <: τ  ⟹  Γ ⊢ t : τ
 *
 * Why the hard cases from general type theory don't arise in Lapis:
 *   - No polymorphic recursion: no general recursion; fold result types are
 *     declared in the spec, not inferred.
 *   - No let-generalization: subtyping, not parametric polymorphism.
 *   - `super` gives the complete AST node, so cross-reference checking has
 *     full knowledge (no bidirectional flow needed).
 *
 * The `super` pattern: this pass calls the name resolver's output (the resolved
 * AST) and checks types against it. In a single-pass implementation, this would
 * be a grammar subclass overriding productions; in the current two-pass
 * implementation, it's a tree walk over the resolved AST.
 */

import {
    type Node,
    type TopLevelDecl,
    IntLit,
    StringLit,
    SymbolLit,
    Ident,
    VariantRef,
    SelfRef,
    FamilyRef,
    CoSelfRef,
    OldRef,
    PrevRef,
    AuxRef,
    BinarySend,
    UnarySend,
    KeywordSend,
    PrefixSend,
    Block,
    Record,
    RecordEntry,
    ArrayLit,
    Spec,
    SpecEntry,
    ContractClause,
    Field,
    Variant,
    CaseArm,
    Satisfies,
    FoldDecl,
    UnfoldDecl,
    MapDecl,
    MergeDecl,
    DataDecl,
    BehaviorDecl,
    ProtocolDecl,
    RelationDecl,
    QueryDecl,
    IoDecl,
    Module,
} from './ast.ts';
import {
    LapisType,
    BaseType,
    AnyType,
    NothingType,
    TypeVar,
    FunType,
    DataType,
    CodataType,
    VariantType,
    FieldDecl,
    IntersectionType,
    ProtocolType,
    FamilyRefType,
    SelfRefType,
    TypedExpr,
    TypeEnv,
    Any,
    Nothing,
    Int,
    String_ as StrType,
    Bool,
    Number_ as NumType,
    Object_ as ObjType,
    Array_ as ArrType,
} from './types.ts';
import { resolveModule, NameResolutionError } from './nameresolver.ts';
import { NameEnv } from './types.ts';

// ── Type checking errors ──────────────────────────────────────────────────────

/** Error thrown when a type check fails. */
export class TypeError_ extends Error {
    constructor(
        message: string,
        readonly expected: LapisType | null,
        readonly actual: LapisType | null,
        readonly span: { start: number; end: number } | null,
    ) {
        const exp = expected ? `expected ${formatType(expected)}` : '';
        const act = actual ? `got ${formatType(actual)}` : '';
        const detail = [exp, act].filter(Boolean).join(', ');
        super(`${message}${detail ? ' (' + detail + ')' : ''}`);
        this.name = 'TypeError';
    }
}

/** Format a type for error messages. */
function formatType(t: LapisType): string {
    if (t instanceof BaseType) return t.name;
    if (t instanceof AnyType) return 'Any';
    if (t instanceof NothingType) return 'Nothing';
    if (t instanceof FunType) return `${formatType(t.param)} → ${formatType(t.result)}`;
    if (t instanceof DataType) return t.name;
    if (t instanceof CodataType) return t.name;
    if (t instanceof ProtocolType) return t.name;
    if (t instanceof IntersectionType) return `${formatType(t.left)} ∧ ${formatType(t.right)}`;
    if (t instanceof FamilyRefType) return `Family<${t.targetType.name}>`;
    if (t instanceof SelfRefType) return `Self<${t.targetType.name}>`;
    return '?';
}

// ── Type checking pass ────────────────────────────────────────────────────────

/**
 * Type-check a module.
 *
 * Entry point for the type checker. Resolves names first (via the name
 * resolver), then checks types.
 *
 * Returns the module with all expressions annotated with their types
 * (as TypedExpr wrappers, in a full implementation).
 */
export function typeCheckModule(mod: Module): Module {
    // Step 1: resolve names
    const resolved = resolveModule(mod);

    // Step 2: build the initial type environment from all declarations
    let typeEnv = new TypeEnv();
    const nameEnv = collectNameEnv(resolved);
    for (const decl of resolved.declarations) {
        typeEnv = registerType(decl, typeEnv, nameEnv);
    }

    // Step 3: check each declaration
    for (const decl of resolved.declarations) {
        checkDeclaration(decl, typeEnv, nameEnv);
    }

    return resolved;
}

// ── Name environment collection ───────────────────────────────────────────────

/**
 * Build a NameEnv from a module's declarations.
 * This is a simplified version of the name resolver's collection pass,
 * used to look up type declarations during type checking.
 */
function collectNameEnv(mod: Module): NameEnv {
    let env = new NameEnv();
    for (const decl of mod.declarations) {
        if (decl instanceof DataDecl) {
            const variants = decl.body
                .filter((item): item is Variant => item instanceof Variant)
                .map(v => new VariantType(v.name, v.fields.map(f => new FieldDecl(f.name, new BaseType(f.typeName ?? 'Any')))));
            const dataType = new DataType(decl.name, variants, null);
            env = env.extendType(decl.name, dataType);
            for (const v of variants) {
                env = env.extendVariant(v.name, decl.name, v);
            }
        } else if (decl instanceof BehaviorDecl) {
            const observers = decl.observers.map(o => new FieldDecl(o.name, new BaseType(o.typeName ?? 'Any')));
            env = env.extendType(decl.name, new CodataType(decl.name, observers, null));
        } else if (decl instanceof ProtocolDecl) {
            const requiredOps = new Map<string, LapisType>();
            for (const method of decl.methods) {
                requiredOps.set(method.name, Any);
            }
            env = env.extendType(decl.name, new ProtocolType(decl.name, requiredOps, null));
        }
    }
    return env;
}

// ── Type registration ─────────────────────────────────────────────────────────

/** Register a top-level declaration's type in the type environment. */
function registerType(decl: TopLevelDecl, env: TypeEnv, nameEnv: NameEnv): TypeEnv {
    if (decl instanceof DataDecl) {
        const type = nameEnv.lookupType(decl.name);
        if (type) return env.extend(decl.name, type);
    } else if (decl instanceof BehaviorDecl) {
        const type = nameEnv.lookupType(decl.name);
        if (type) return env.extend(decl.name, type);
    } else if (decl instanceof ProtocolDecl) {
        const type = nameEnv.lookupType(decl.name);
        if (type) return env.extend(decl.name, type);
    }
    return env;
}

// ── Declaration checking ──────────────────────────────────────────────────────

/** Type-check a top-level declaration. */
function checkDeclaration(decl: TopLevelDecl, env: TypeEnv, nameEnv: NameEnv): void {
    if (decl instanceof DataDecl) {
        checkDataDecl(decl, env, nameEnv);
    } else if (decl instanceof BehaviorDecl) {
        checkBehaviorDecl(decl, env, nameEnv);
    } else if (decl instanceof ProtocolDecl) {
        checkProtocolDecl(decl, env, nameEnv);
    } else if (decl instanceof RelationDecl) {
        checkRelationDecl(decl, env, nameEnv);
    } else if (decl instanceof QueryDecl) {
        checkQueryDecl(decl, env, nameEnv);
    }
    // IoDecl doesn't need type checking (it's a Mealy machine data value)
}

/** Type-check a data declaration. */
function checkDataDecl(decl: DataDecl, env: TypeEnv, nameEnv: NameEnv): void {
    const dataType = nameEnv.lookupType(decl.name);
    if (!dataType || !(dataType instanceof DataType)) return;

    // Check each fold/unfold/map/merge in the body
    for (const item of decl.body) {
        if (item instanceof FoldDecl) {
            checkFoldDecl(item, dataType, env, nameEnv);
        } else if (item instanceof UnfoldDecl) {
            checkUnfoldDecl(item, dataType, env, nameEnv);
        } else if (item instanceof Satisfies) {
            checkSatisfies(item, dataType, nameEnv);
        }
        // Variants and maps are checked structurally
    }
}

/** Type-check a behavior declaration. */
function checkBehaviorDecl(decl: BehaviorDecl, env: TypeEnv, nameEnv: NameEnv): void {
    const codataType = nameEnv.lookupType(decl.name);
    if (!codataType || !(codataType instanceof CodataType)) return;

    for (const item of decl.body) {
        if (item instanceof FoldDecl) {
            // Behavior fold = cofold (codata elimination)
            checkCofoldDecl(item, codataType, env, nameEnv);
        } else if (item instanceof UnfoldDecl) {
            checkUnfoldDecl(item, codataType, env, nameEnv);
        }
    }
}

/** Type-check a protocol declaration. */
function checkProtocolDecl(decl: ProtocolDecl, env: TypeEnv, nameEnv: NameEnv): void {
    // Check that each method is a valid fold declaration
    for (const method of decl.methods) {
        // Protocol methods are fold declarations with optional default bodies
        // The spec defines the operation's signature
        // TODO: verify the method signature matches the protocol's required shape
    }
}

/** Type-check a relation declaration. */
function checkRelationDecl(decl: RelationDecl, env: TypeEnv, nameEnv: NameEnv): void {
    // Verify origin and destination folds exist and have the right signature
    const originFold = decl.folds.find(f => f.name === 'origin');
    const destFold = decl.folds.find(f => f.name === 'destination');
    if (!originFold) {
        throw new TypeError_('Relation missing required fold: origin', null, null, decl.span);
    }
    if (!destFold) {
        throw new TypeError_('Relation missing required fold: destination', null, null, decl.span);
    }
    // TODO: verify origin and destination return the endpoint types
}

/** Type-check a query declaration. */
function checkQueryDecl(decl: QueryDecl, env: TypeEnv, nameEnv: NameEnv): void {
    // Verify cospan projections (output, done, accept) reference valid observers
    // TODO: verify cospan projections
}

// ── Fold checking (T-Fold) ────────────────────────────────────────────────────

/**
 * Type-check a fold declaration against its data type.
 *
 * Implements T-Fold from _docs/core-calculus.md §4.3:
 *
 *   T = μ α. Σᵢ Cᵢ(Fᵢ(α))
 *   Γ ⊢ e : T
 *   Γ ⊢ hᵢ : Fᵢ(σ)[α := σ] → σ   (for each variant Cᵢ)
 *   ────────────────────────────────────────────────────────────────  (T-Fold)
 *   Γ ⊢ fold_T e {Cᵢ(xⱼ) → tᵢ} : σ
 *
 * The result type σ comes from the spec's `out` entry (declared, not inferred).
 * Each handler must:
 *   1. Match a variant of T (exhaustiveness)
 *   2. Bind the variant's fields, with recursive (Family) fields typed as σ
 *      (the already-folded result), and non-recursive fields typed as declared
 *   3. Produce a body of type σ
 */
function checkFoldDecl(
    fold: FoldDecl,
    dataType: DataType,
    env: TypeEnv,
    nameEnv: NameEnv,
): void {
    // 1. Resolve the result type σ from the spec
    const σ = resolveResultType(fold.spec, dataType);
    if (!σ) {
        throw new TypeError_(
            `Fold '${fold.name}' missing result type (spec must have 'out')`,
            null, null, fold.span,
        );
    }

    // 2. Check exhaustiveness: every variant of T must have a handler
    //    (or a wildcard handler must be present)
    const allVariants = dataType.allVariants();
    const handledVariants = new Set(fold.arms.map(a => a.pattern));
    const hasWildcard = handledVariants.has('_');

    if (!hasWildcard) {
        for (const variant of allVariants) {
            if (!handledVariants.has(variant.name)) {
                throw new TypeError_(
                    `Fold '${fold.name}' is not exhaustive: missing handler for variant '${variant.name}'`,
                    null, null, fold.span,
                );
            }
        }
    }

    // 3. Check each handler's body type matches σ
    for (const arm of fold.arms) {
        if (arm.pattern === '_') continue; // wildcard — type checked when invoked

        const variant = dataType.findVariant(arm.pattern);
        if (!variant) {
            throw new TypeError_(
                `Fold '${fold.name}' has handler for unknown variant '${arm.pattern}'`,
                null, null, arm.span,
            );
        }

        // Build the handler's environment: bind field names to their types
        // Recursive (Family) fields get type σ (the already-folded result)
        // Non-recursive fields get their declared types
        let armEnv = env.extend('self', dataType); // self is in scope
        for (let i = 0; i < variant.fields.length; i++) {
            const field = variant.fields[i]!;
            const binding = arm.bindings[i] ?? field.name;
            if (binding === '_') continue; // wildcard binding

            // If the field type is FamilyRefType, it's a recursive field → type σ
            // Otherwise, use the declared field type
            const fieldType = field.type instanceof FamilyRefType ? σ : field.type;
            armEnv = armEnv.extend(binding, fieldType);
        }

        // Check the handler body produces type σ
        const bodyType = checkExpr(arm.body, armEnv, nameEnv);
        if (!bodyType.isSubtypeOf(σ)) {
            throw new TypeError_(
                `Fold '${fold.name}' handler for '${arm.pattern}' produces wrong type`,
                σ, bodyType, arm.span,
            );
        }
    }
}

// ── Unfold checking (T-Unfold) ─────────────────────────────────────────────────

/**
 * Type-check an unfold declaration against its codata type.
 *
 * Implements T-Unfold from _docs/core-calculus.md §4.5:
 *
 *   T = ν α. Πⱼ oⱼ(Gⱼ(α))
 *   Γ ⊢ s : Σ
 *   Γ ⊢ gⱼ : Σ → Gⱼ(Σ)[α := Σ]   (for each observer oⱼ)
 *   ────────────────────────────────────────────────────────────────  (T-Unfold)
 *   Γ ⊢ unfold_T s {oⱼ → gⱼ} : T
 *
 * Each generator must produce a value of the observer's type, with Self
 * positions replaced by the seed type Σ.
 */
function checkUnfoldDecl(
    unfold: UnfoldDecl,
    targetType: DataType | CodataType,
    env: TypeEnv,
    nameEnv: NameEnv,
): void {
    // Resolve the seed type Σ from the spec's `in` entry
    const Σ = resolveInputType(unfold.spec);
    if (!Σ) {
        // Parameterless unfold — seed type is Unit
        // TODO: handle parameterless unfolds
    }

    // For data unfolds (constructors), check each arm matches a variant
    // For codata unfolds (generators), check each arm matches an observer
    if (targetType instanceof CodataType) {
        const allObservers = targetType.allObservers();
        for (const arm of unfold.arms) {
            const observer = allObservers.find(o => o.name === arm.pattern);
            if (!observer) {
                throw new TypeError_(
                    `Unfold '${unfold.name}' has generator for unknown observer '${arm.pattern}'`,
                    null, null, arm.span,
                );
            }
            // TODO: check the generator body type matches the observer's type
            // with Self replaced by Σ
        }
    } else if (targetType instanceof DataType) {
        // Data unfold (constructor from seed) — check arms match variants
        const allVariants = targetType.allVariants();
        for (const arm of unfold.arms) {
            const variant = allVariants.find(v => v.name === arm.pattern);
            if (!variant) {
                throw new TypeError_(
                    `Unfold '${unfold.name}' has generator for unknown variant '${arm.pattern}'`,
                    null, null, arm.span,
                );
            }
        }
    }
}

// ── Cofold checking (T-Cofold — behavior fold) ────────────────────────────────

/**
 * Type-check a behavior fold (cofold) against its codata type.
 *
 * Implements T-Cofold from _docs/core-calculus.md §4.6:
 *
 *   T = ν α. Πⱼ oⱼ(Gⱼ(α))
 *   Γ ⊢ e : T
 *   Γ ⊢ h : Πⱼ(Gⱼ(σ)[α := σ]) → σ   (single handler for the observation product)
 *   ────────────────────────────────────────────────────────────────  (T-Cofold)
 *   Γ ⊢ cofold_T e {oⱼ(xⱼ) → t} : σ
 *
 * The handler receives all observations simultaneously (the product), with
 * continuation (Self) fields exposed as fold functions.
 */
function checkCofoldDecl(
    fold: FoldDecl,
    codataType: CodataType,
    env: TypeEnv,
    nameEnv: NameEnv,
): void {
    // Resolve the result type σ from the spec
    const σ = resolveResultType(fold.spec, codataType);
    if (!σ) {
        throw new TypeError_(
            `Behavior fold '${fold.name}' missing result type (spec must have 'out')`,
            null, null, fold.span,
        );
    }

    // Behavior folds have a single `_` handler that receives the observation product
    const handler = fold.arms.find(a => a.pattern === '_');
    if (!handler) {
        // Could also have per-observer handlers in a future extension
        throw new TypeError_(
            `Behavior fold '${fold.name}' must have a '_' handler`,
            null, null, fold.span,
        );
    }

    // Build the handler environment: bind observer names to their types
    // Continuation (Self) observers get type σ → σ (fold functions)
    // Simple observers get their declared types
    let handlerEnv = env.extend('self', codataType);
    for (const observer of codataType.allObservers()) {
        if (observer.type instanceof SelfRefType) {
            // Continuation: a fold function σ → σ
            handlerEnv = handlerEnv.extend(observer.name, new FunType(σ, σ));
        } else {
            handlerEnv = handlerEnv.extend(observer.name, observer.type);
        }
    }

    // Check the handler body produces type σ
    const bodyType = checkExpr(handler.body, handlerEnv, nameEnv);
    if (!bodyType.isSubtypeOf(σ)) {
        throw new TypeError_(
            `Behavior fold '${fold.name}' handler produces wrong type`,
            σ, bodyType, handler.span,
        );
    }
}

// ── Satisfies checking ─────────────────────────────────────────────────────────

/**
 * Check protocol conformance (satisfies clause).
 *
 * Verifies that the type declares all operations required by the protocol,
 * with compatible signatures. This is structural conformance — the type
 * satisfies the protocol if it has the right operations, regardless of
 * explicit declaration.
 *
 * See _docs/core-calculus.md §3.5 and _docs/elaboration.md §3.3.
 */
function checkSatisfies(satisfies: Satisfies, type: DataType | CodataType, nameEnv: NameEnv): void {
    const protocol = nameEnv.lookupType(satisfies.protocolName);
    if (!protocol || !(protocol instanceof ProtocolType)) {
        throw new TypeError_(
            `Unknown protocol '${satisfies.protocolName}'`,
            null, null, satisfies.span,
        );
    }

    // Check that the type has all required operations
    // (In a full implementation, this would check the fold/unfold declarations
    // on the type against the protocol's required operations)
    // TODO: verify each required operation exists with a compatible signature
}

// ── Expression checking ───────────────────────────────────────────────────────

/**
 * Type-check an expression and return its type.
 *
 * This is the core expression type-checking function. It implements the
 * typing rules for each expression form (T-Var, T-Abs, T-App, T-Variant, etc.)
 * by case analysis on the AST node.
 *
 * The environment Γ (TypeEnv) is the inherited attribute, threaded top-down.
 * The returned type is the synthesized attribute, flowing bottom-up.
 */
function checkExpr(node: Node, env: TypeEnv, nameEnv: NameEnv): LapisType {
    // Literals
    if (node instanceof IntLit)    return Int;
    if (node instanceof StringLit) return StrType;
    if (node instanceof SymbolLit) return new BaseType('Symbol');

    // References
    if (node instanceof Ident) {
        const type = env.lookup(node.name);
        if (!type) {
            throw new TypeError_(`Unbound variable '${node.name}'`, null, null, node.span);
        }
        return type;  // T-Var
    }

    if (node instanceof VariantRef) {
        // A variant reference — look up the variant and return its type
        const variantInfo = nameEnv.lookupVariant(node.name);
        if (!variantInfo) {
            throw new TypeError_(`Unknown variant '${node.name}'`, null, null, node.span);
        }
        const type = nameEnv.lookupType(variantInfo.type);
        if (!type) {
            throw new TypeError_(`Unknown type '${variantInfo.type}'`, null, null, node.span);
        }
        return type;  // T-Variant (simplified — full version checks field types)
    }

    if (node instanceof SelfRef) {
        // `self` — the current instance. Should be in Γ.
        const type = env.lookup('self');
        if (!type) {
            throw new TypeError_("'self' not in scope", null, null, node.span);
        }
        return type;
    }

    if (node instanceof FamilyRef) {
        // `Family` — the recursive self-reference. Resolved to the data type.
        // In a fold handler, Family-typed fields arrive as the fold result type σ.
        const type = env.lookup('Family');
        return type ?? Any;
    }

    if (node instanceof CoSelfRef) {
        // `Self` — the corecursive self-reference. Resolved to the codata type.
        const type = env.lookup('Self');
        return type ?? Any;
    }

    if (node instanceof OldRef) {
        // `old field` — raw pre-fold sub-node (paramorphism). Same type as the
        // field's declared type (the raw sub-structure, not the folded result).
        const type = env.lookup(node.fieldName);
        return type ?? Any;
    }

    if (node instanceof PrevRef) {
        // `prev field` — previous fold result (histomorphism). Same type as the
        // field's fold result.
        const type = env.lookup(node.fieldName);
        return type ?? Any;
    }

    if (node instanceof AuxRef) {
        // `aux foldName` — auxiliary fold result (zygomorphism).
        const type = env.lookup(node.foldName);
        return type ?? Any;
    }

    // Composite expressions
    if (node instanceof BinarySend) {
        // Binary operator: a op b → check both operands and return result type
        // The operator resolves to a fold on the operand type
        const leftType = checkExpr(node.receiver, env, nameEnv);
        const rightType = checkExpr(node.arg, env, nameEnv);
        // TODO: resolve the operator to a fold and check the result type
        // For now, return the left type (common for arithmetic)
        return leftType;
    }

    if (node instanceof UnarySend) {
        // Unary message: recv selector → check receiver, return result type
        const recvType = checkExpr(node.receiver, env, nameEnv);
        // TODO: resolve the selector to a fold and check the result type
        return recvType;  // simplified
    }

    if (node instanceof KeywordSend) {
        // Keyword message: recv k1: a1 k2: a2 → check receiver and args
        const recvType = checkExpr(node.receiver, env, nameEnv);
        for (const arg of node.args) {
            checkExpr(arg, env, nameEnv);
        }
        // TODO: resolve the keyword selector to a fold and check the result type
        return recvType;  // simplified
    }

    if (node instanceof PrefixSend) {
        // Prefix operator: - expr or not expr
        const operandType = checkExpr(node.operand, env, nameEnv);
        if (node.op === 'not') return Bool;
        return operandType;  // negation preserves type (simplified)
    }

    if (node instanceof Block) {
        // Lambda: [params | body] → function type
        // Build the parameter type (from context or Any) and check the body
        let bodyEnv = env;
        for (const param of node.params) {
            bodyEnv = bodyEnv.extend(param.name, Any);  // param type from context
        }
        const bodyType = checkExpr(node.body, bodyEnv, nameEnv);
        // Simplified: single-param block → FunType(Any, bodyType)
        if (node.params.length === 0) {
            return new FunType(new BaseType('Unit'), bodyType);
        }
        return new FunType(Any, bodyType);  // T-Abs (simplified)
    }

    if (node instanceof ArrayLit) {
        // Array literal: {a, b, c} → Array type
        for (const item of node.items) {
            checkExpr(item, env, nameEnv);
        }
        return ArrType;
    }

    if (node instanceof Record) {
        // Record: (k1: v1, k2: v2) → record type (simplified to Any)
        for (const entry of node.entries) {
            checkExpr(entry.value, env, nameEnv);
        }
        return Any;
    }

    // Fallback: unknown expression type
    return Any;
}

// ── Spec resolution ──────────────────────────────────────────────────────────

/**
 * Resolve the result type (σ) from a fold/unfold spec's `out` entry.
 *
 * The `out` entry declares the operation's return type. For folds, this is the
 * type that recursive (Family) fields are replaced with. See T-Fold in
 * _docs/core-calculus.md §4.3.
 */
function resolveResultType(spec: Spec | null, targetType: DataType | CodataType): LapisType | null {
    if (!spec) return null;
    for (const entry of spec.entries) {
        if (entry.key === 'out') {
            // The `out` value is a type name (VariantRef or Ident)
            // TODO: resolve it to a LapisType properly
            return Any;  // simplified
        }
    }
    return null;
}

/**
 * Resolve the input/seed type (Σ) from a fold/unfold spec's `in` entry.
 */
function resolveInputType(spec: Spec | null): LapisType | null {
    if (!spec) return null;
    for (const entry of spec.entries) {
        if (entry.key === 'in') {
            return Any;  // simplified
        }
    }
    return null;
}