/**
 * Lapis name resolution — the first semantic layer above the base grammar.
 *
 * Architecture (see _docs/semantics.md §5 and _docs/grammar-as-semantics.md):
 *
 * The semantic analysis passes are structured as grammar subclasses, following
 * Bracha's executable-grammar model. Each layer calls `super` to get the
 * previous layer's complete output, threads its own context as method arguments
 * (inherited attributes), and returns a richer result (synthesized attributes).
 *
 *   LapisGrammar              (characters → AST)           — src/grammar.ts
 *     → LapisNameResolver     (AST → resolved AST)         — this file
 *       → LapisTypeChecker     (resolved AST → typed AST) — src/typechecker.ts
 *         → LapisLawChecker    (typed AST → verified AST) — src/lawchecker.ts (planned)
 *           → LapisEvaluator   (verified AST → Values)     — src/evaluator.ts (planned)
 *
 * Name resolution threads a `NameEnv` (the inherited attribute) top-down. The
 * environment maps type names, variant names, and operation names to their
 * declarations. Each production that declares a name extends the environment for
 * its sub-terms; productions that don't bind names inherit unchanged from the
 * base grammar.
 *
 * The `super` pattern: this subclass overrides only the productions that bind or
 * reference names. For all other productions, the base grammar's parsing runs
 * unchanged, and the resolved AST is the same as the raw AST. This is the
 * "grammar subclassing = semantic pass" model — each pass only spells out what
 * it changes.
 *
 * Why this works for Lapis specifically (see discussion in
 * _docs/grammar-as-semantics.md):
 *   - No polymorphic recursion (no general recursion; declared result types)
 *   - No let-generalization (subtyping, not parametric polymorphism)
 *   - `super` gives the complete AST node, not a streaming view, so
     cross-reference checking has full knowledge
 */

import { Grammar, rule } from 'jsr:@lapis-lang/zipper-grammar';
import type { Parser, Span } from 'jsr:@lapis-lang/zipper-grammar';
import {
    LapisGrammar,
    type LapisShape,
} from './grammar.ts';
import {
    type Node,
    type TopLevelDecl,
    type DataBodyItem,
    Ident,
    VariantRef,
    DataDecl,
    BehaviorDecl,
    ProtocolDecl,
    RelationDecl,
    QueryDecl,
    FoldDecl,
    UnfoldDecl,
    Variant,
    Field,
    CaseArm,
    Satisfies,
    Module,
} from './ast.ts';
import {
    NameEnv,
    DataType,
    CodataType,
    ProtocolType,
    VariantType,
    FieldDecl,
    AnyType,
    NothingType,
    BaseType,
    Any,
    type LapisType,
} from './types.ts';

// ── Resolved AST nodes ────────────────────────────────────────────────────────

/**
 * A resolved reference — an identifier that has been linked to its declaration.
 *
 * The `resolvedName` is the canonical name (e.g., the fully-qualified type name),
 * and `resolvedDecl` is a reference to the declaration it points to.
 */
export class ResolvedIdent extends Ident {
    constructor(
        readonly originalName: string,
        readonly resolvedName: string,
        span: Span,
    ) { super(resolvedName, span); }
}

/**
 * A resolved variant reference — a PascalCase name linked to its variant
 * declaration.
 */
export class ResolvedVariantRef extends VariantRef {
    constructor(
        readonly originalName: string,
        readonly resolvedName: string,
        readonly typeName: string | null,  // the type this variant belongs to
        span: Span,
    ) { super(resolvedName, span); }
}

// ── Name resolution errors ────────────────────────────────────────────────────

/** Error thrown when a name cannot be resolved. */
export class NameResolutionError extends Error {
    override readonly name = 'NameResolutionError';
    constructor(
        message: string,
        readonly nameRef: string,
        readonly span: Span | null,
    ) { super(`${message}: ${nameRef}`); }
}

// ── Name resolution shape ─────────────────────────────────────────────────────

/**
 * The shape for the name-resolution grammar. Most productions return the same
 * type as the base grammar (the AST is unchanged for productions that don't
 * reference names). The productions that *do* reference names return resolved
 * nodes.
 *
 * In a full implementation, this shape would extend LapisShape with resolved
 * variants. For now, we use the base shape and resolve names in a post-parse
 * walk, which is simpler and avoids re-running the parser.
 *
 * Design decision: single-pass vs. multi-pass
 *   The `super` pattern allows single-pass (parse + resolve simultaneously),
 *   but for the first implementation we use a two-pass approach:
 *     1. Parse to AST (base grammar)
 *     2. Walk the AST and resolve names (this file's `resolveModule` function)
 *   This is simpler to implement and test. The single-pass version can be
 *   achieved later by overriding productions in a subclass.
 */

// ── Name resolution pass ───────────────────────────────────────────────────────

/**
 * Resolve all names in a module.
 *
 * This is the entry point for name resolution. It walks the AST and builds a
 * `NameEnv` incrementally:
 *   1. First pass: collect all type declarations (data, behavior, protocol,
 *      relation, query) into the environment. This handles forward references
 *      (mutual recursion, deferred materialization — see _docs/elaboration.md
 *      §9.4).
 *   2. Second pass: resolve all references (variant refs, type refs, operation
 *      refs) against the complete environment.
 *
 * This two-pass structure within name resolution mirrors the deferred-
 * materialization strategy from lapis-js: declare all types first, then
 * materialize (resolve references) once every binding is in scope.
 */
export function resolveModule(mod: Module): Module {
    // Pass 1: collect all type declarations
    let env = new NameEnv();
    for (const decl of mod.declarations) {
        env = collectDeclaration(decl, env);
    }

    // Pass 2: resolve all references
    const resolvedDecls = mod.declarations.map(decl => resolveDeclaration(decl, env));
    return new Module(resolvedDecls, mod.source, mod.span);
}

// ── Pass 1: collect declarations ──────────────────────────────────────────────

/** Register a top-level declaration's types and variants in the environment. */
function collectDeclaration(decl: TopLevelDecl, env: NameEnv): NameEnv {
    if (decl instanceof DataDecl) {
        return collectDataDecl(decl, env);
    } else if (decl instanceof BehaviorDecl) {
        return collectBehaviorDecl(decl, env);
    } else if (decl instanceof ProtocolDecl) {
        return collectProtocolDecl(decl, env);
    } else if (decl instanceof RelationDecl) {
        return collectRelationDecl(decl, env);
    } else if (decl instanceof QueryDecl) {
        return collectQueryDecl(decl, env);
    }
    return env;
}

/** Collect a data declaration's type and variants into the environment. */
function collectDataDecl(decl: DataDecl, env: NameEnv): NameEnv {
    // Build the DataType (without resolving parent yet — parent is resolved in pass 2)
    const variants = decl.body
        .filter((item): item is Variant => item instanceof Variant)
        .map(v => new VariantType(v.name, v.fields.map(f => new FieldDecl(f.name, parseTypeRef(f.typeName)))));

    const dataType = new DataType(decl.name, variants, null); // parent resolved later
    let env_ = env.extendType(decl.name, dataType);

    // Register each variant name
    for (const v of variants) {
        env_ = env_.extendVariant(v.name, decl.name, v);
    }

    // Register each fold/unfold/map/merge operation
    for (const item of decl.body) {
        if (item instanceof FoldDecl) {
            env_ = env_.extendOperation(item.name, decl.name, 'fold');
        } else if (item instanceof UnfoldDecl) {
            env_ = env_.extendOperation(item.name, decl.name, 'unfold');
        }
    }

    return env_;
}

/** Collect a behavior declaration's type and observers into the environment. */
function collectBehaviorDecl(decl: BehaviorDecl, env: NameEnv): NameEnv {
    const observers = decl.observers.map(o => new FieldDecl(o.name, parseTypeRef(o.typeName)));
    const codataType = new CodataType(decl.name, observers, null);
    let env_ = env.extendType(decl.name, codataType);

    // Register unfold operations (PascalCase constructors)
    for (const item of decl.body) {
        if (item instanceof UnfoldDecl) {
            env_ = env_.extendOperation(item.name, decl.name, 'unfold');
        }
    }

    return env_;
}

/** Collect a protocol declaration into the environment. */
function collectProtocolDecl(decl: ProtocolDecl, env: NameEnv): NameEnv {
    // Build the ProtocolType with required operations from its fold declarations
    const requiredOps = new Map<string, LapisType>();
    for (const method of decl.methods) {
        // The operation signature is derived from the fold's spec
        // (full type resolution happens in the type checker)
        requiredOps.set(method.name, parseSpecToType(method.spec));
    }
    const protocolType = new ProtocolType(decl.name, requiredOps, null);
    return env.extendType(decl.name, protocolType);
}

/** Collect a relation declaration (it's a data type with span projections). */
function collectRelationDecl(decl: RelationDecl, env: NameEnv): NameEnv {
    const variants = decl.variants.map(v => new VariantType(v.name, v.fields.map(f => new FieldDecl(f.name, parseTypeRef(f.typeName)))));
    const dataType = new DataType(decl.name, variants, null);
    let env_ = env.extendType(decl.name, dataType);

    for (const v of variants) {
        env_ = env_.extendVariant(v.name, decl.name, v);
    }
    for (const fold of decl.folds) {
        env_ = env_.extendOperation(fold.name, decl.name, 'fold');
    }

    return env_;
}

/** Collect a query declaration (it's a behavior type with cospan projections). */
function collectQueryDecl(decl: QueryDecl, env: NameEnv): NameEnv {
    const observers = decl.observers.map(o => new FieldDecl(o.name, parseTypeRef(o.typeName)));
    const codataType = new CodataType(decl.name, observers, null);
    let env_ = env.extendType(decl.name, codataType);

    for (const unfold of decl.unfolds) {
        env_ = env_.extendOperation(unfold.name, decl.name, 'unfold');
    }

    return env_;
}

// ── Pass 2: resolve references ────────────────────────────────────────────────

/** Resolve all references in a top-level declaration. */
function resolveDeclaration(decl: TopLevelDecl, env: NameEnv): TopLevelDecl {
    if (decl instanceof DataDecl) {
        return resolveDataDecl(decl, env);
    } else if (decl instanceof BehaviorDecl) {
        return resolveBehaviorDecl(decl, env);
    } else if (decl instanceof ProtocolDecl) {
        return resolveProtocolDecl(decl, env);
    } else if (decl instanceof RelationDecl) {
        return resolveRelationDecl(decl, env);
    } else if (decl instanceof QueryDecl) {
        return resolveQueryDecl(decl, env);
    }
    return decl;
}

/** Resolve references in a data declaration. */
function resolveDataDecl(decl: DataDecl, env: NameEnv): DataDecl {
    // Resolve parent type if present
    if (decl.parent) {
        const parentType = env.lookupType(decl.parent);
        if (!parentType) {
            throw new NameResolutionError('Unknown parent type', decl.parent, decl.span);
        }
        // TODO: wire the parent into the DataType for comb inheritance
    }

    // Resolve variant references and field types in fold arms
    const resolvedBody = decl.body.map(item => resolveDataBodyItem(item, env, decl.name));
    return new DataDecl(decl.name, decl.parent, resolvedBody, decl.span);
}

/** Resolve references in a data body item (variant, fold, unfold, etc.). */
function resolveDataBodyItem(item: DataBodyItem, env: NameEnv, typeName: string): DataBodyItem {
    if (item instanceof FoldDecl) {
        const resolvedArms = item.arms.map(arm => resolveCaseArm(arm, env, typeName));
        return new FoldDecl(item.name, item.spec, item.contractClauses, resolvedArms, item.span);
    } else if (item instanceof UnfoldDecl) {
        const resolvedArms = item.arms.map(arm => resolveCaseArm(arm, env, typeName));
        return new UnfoldDecl(item.name, item.spec, resolvedArms, item.span);
    } else if (item instanceof Variant) {
        // Variants don't have references to resolve (their fields are type names,
        // resolved in the type checker)
        return item;
    } else if (item instanceof Satisfies) {
        // Verify the protocol exists
        const proto = env.lookupType(item.protocolName);
        if (!proto) {
            throw new NameResolutionError('Unknown protocol', item.protocolName, item.span);
        }
        return item;
    }
    return item;
}

/** Resolve references in a case arm. */
function resolveCaseArm(arm: CaseArm, env: NameEnv, typeName: string): CaseArm {
    // Verify the variant exists in this type (or its ancestors)
    const typeDecl = env.lookupType(typeName);
    if (typeDecl instanceof DataType) {
        const variant = typeDecl.findVariant(arm.pattern);
        if (!variant) {
            throw new NameResolutionError(
                `Unknown variant in type ${typeName}`,
                arm.pattern,
                arm.span,
            );
        }
    }

    // The body expression may contain references (self, Family, old, prev, aux,
    // variant refs, operation names) — these are resolved recursively in a
    // full implementation. For now, we return the arm unchanged.
    // TODO: walk arm.body and resolve all references
    return arm;
}

/** Resolve references in a behavior declaration. */
function resolveBehaviorDecl(decl: BehaviorDecl, env: NameEnv): BehaviorDecl {
    if (decl.parent) {
        const parentType = env.lookupType(decl.parent);
        if (!parentType) {
            throw new NameResolutionError('Unknown parent type', decl.parent, decl.span);
        }
    }
    // TODO: resolve references in body items
    return decl;
}

/** Resolve references in a protocol declaration. */
function resolveProtocolDecl(decl: ProtocolDecl, env: NameEnv): ProtocolDecl {
    if (decl.parent) {
        const parentType = env.lookupType(decl.parent);
        if (!parentType || !(parentType instanceof ProtocolType)) {
            throw new NameResolutionError('Unknown parent protocol', decl.parent, decl.span);
        }
    }
    return decl;
}

/** Resolve references in a relation declaration. */
function resolveRelationDecl(decl: RelationDecl, env: NameEnv): RelationDecl {
    // Verify origin and destination folds exist
    const hasOrigin = decl.folds.some(f => f.name === 'origin');
    const hasDestination = decl.folds.some(f => f.name === 'destination');
    if (!hasOrigin) {
        throw new NameResolutionError('Relation missing required fold', 'origin', decl.span);
    }
    if (!hasDestination) {
        throw new NameResolutionError('Relation missing required fold', 'destination', decl.span);
    }
    return decl;
}

/** Resolve references in a query declaration. */
function resolveQueryDecl(decl: QueryDecl, env: NameEnv): QueryDecl {
    // Verify cospan projections (output, done, accept) are present as observers
    // TODO: verify cospan projections
    return decl;
}

// ── Type reference parsing ────────────────────────────────────────────────────

/**
 * Parse a type name string into a LapisType.
 *
 * This is a simplified version for the name-resolution pass. Full type
 * resolution (with subtyping checks) happens in the type checker.
 *
 * Recognized names:
 *   - `Family` → FamilyRefType (placeholder; target resolved later)
 *   - `Self`  → SelfRefType (placeholder; target resolved later)
 *   - `Any`   → AnyType
 *   - `Nothing` → NothingType
 *   - `Int`, `String`, `Bool`, `Number`, `Object`, `Array` → BaseType
 *   - Other PascalCase names → BaseType (to be resolved in type checker)
 */
function parseTypeRef(typeName: string | null): LapisType {
    if (typeName === null) return Any;  // untyped field = Any
    switch (typeName) {
        case 'Any':     return new AnyType();
        case 'Nothing': return new NothingType();
        case 'Family':  return new BaseType('Family');  // placeholder — resolved to FamilyRefType in type checker
        case 'Self':    return new BaseType('Self');      // placeholder — resolved to SelfRefType in type checker
        default:        return new BaseType(typeName);
    }
}

/**
 * Parse a fold/unfold spec into a LapisType (the operation's signature).
 *
 * This is a placeholder — full spec-to-type resolution happens in the type
 * checker, where the spec's `in` and `out` entries are mapped to parameter
 * and result types.
 */
function parseSpecToType(_spec: unknown): LapisType {
    // TODO: resolve spec entries to a function type
    return Any;
}
