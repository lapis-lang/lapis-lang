/**
 * Name resolution for the surface language — the first tree-consuming pass.
 *
 * The pass walks the surface AST and answers the three questions elaboration
 * cannot answer locally:
 *
 * 1. **Which declarations exist**, and what each contributes — declared type
 *    names, their variants and fields, and their operations. This is the
 *    declaration table, and it is what makes the bare-vs-qualified rule (#84)
 *    decidable: a bare name resolves iff it is unique in scope.
 * 2. **Whether every type name resolves.** The surface has no type variables
 *    and no type parameters, permanently (`surface-grammar.md` §3.8), so a name
 *    that is neither built in nor declared has no legitimate meaning. It is an
 *    error at the annotation, not an opaque variable minted for later — that
 *    permissiveness is #116's defect, and the surface must not inherit it.
 * 3. **Whether a reserved reference was taken as a declaration name.**
 *    `Family` and `Self` are the language-defined recursive references; a user
 *    declaration may not shadow them (#101), or the same spelling would flip
 *    the recursion discipline by what else happens to be in scope.
 *
 * Resolution is a separate pass rather than grammar gates because every one of
 * these questions is *whole-program*: `data List` may declare `Cons` before
 * `data Nat` refers to it, and the surface has no ordering rule.
 */

import type {
    AtomType,
    DataBodyItem,
    DataDecl,
    Declaration,
    FoldDecl,
    SpecRecord,
    SurfaceProgram,
} from "./ast.ts"
// ── Diagnostics ──────────────────────────────────────────────────────────────

/**
 * A resolution failure: a rule, the offending name, and a message that names
 * the remedy.
 *
 * The message *text* is provisional — #99 owns the pinned diagnostic vocabulary.
 * This pass fixes the *reasons*, so #99 has one place per rejection to pin.
 */
export interface ResolutionError {
    readonly reason:
        | "reserved-declaration-name"
        | "duplicate-declaration"
        | "unknown-type"
        | "unknown-variant"
        | "duplicate-variant"
        | "arity-mismatch"
        | "wildcard-arm"
    readonly message: string
}

// ── The declaration table ────────────────────────────────────────────────────

/** One declared variant: its name and its fields in declaration order. */
export interface ResolvedVariant {
    readonly name: string
    readonly fields: readonly { readonly name: string; readonly type: AtomType }[]
}

/** One declared `data` type, as the rest of the pipeline sees it. */
export interface ResolvedData {
    readonly name: string
    readonly parent?: string
    readonly variants: readonly ResolvedVariant[]
    readonly folds: readonly FoldDecl[]
}

/** What a program declares, indexed for resolution. */
export interface DeclarationTable {
    /** The declared types, in source order. */
    readonly types: ReadonlyMap<string, ResolvedData>
    /**
     * Variant name → declaring type's name, for bare resolution.
     *
     * A name mapping to more than one type is stored under
     * `ambiguousVariants` instead: bare use is then an error and the qualified
     * form is required (#84).
     */
    readonly variants: ReadonlyMap<string, string>
    /** Variant names declared by more than one type — bare use is ambiguous. */
    readonly ambiguousVariants: ReadonlySet<string>
}

/** A resolution outcome: the table, the errors, or both. */
export interface ResolutionResult {
    readonly table: DeclarationTable
    readonly errors: readonly ResolutionError[]
    /** Whether the program resolved without errors. */
    readonly ok: boolean
}

/**
 * The names the language defines and no declaration may take (§3.5, §12.16).
 *
 * `Family` and `Self` are references, not types: `Family` is the μ-bound α of
 * the carrier being analyzed and `Self` is the declaring type itself.
 */
export const RESERVED_DECLARATION_NAMES: readonly string[] = ["Family", "Self"] as const

/**
 * The type names that resolve without a declaration (§3.8).
 *
 * `Any` and `Nothing` are the lattice bounds; `Family` and `Self` are the
 * recursive references. There are no others: a name not in this set must be
 * declared by the program.
 */
export const BUILTIN_TYPE_NAMES: readonly string[] = [
    "Any",
    "Nothing",
    "Family",
    "Self",
] as const

// ── The pass ─────────────────────────────────────────────────────────────────

/**
 * Resolve a program's names.
 *
 * Two phases, because a program's declarations are unordered: collect the table
 * from every declaration first, then validate every reference against it. A
 * single walk would reject a forward reference (`Cons` used by a type declared
 * above the one that declares it) — legal in the surface, which has no
 * declaration ordering rule.
 */
export function resolveProgram(program: SurfaceProgram): ResolutionResult {
    const errors: ResolutionError[] = []
    const table = collectTable(program.declarations, errors)
    for (const decl of program.declarations) {
        validateDeclaration(decl, table, errors)
    }
    return { table, errors, ok: errors.length === 0 }
}

/** Phase one: build the declaration table, reporting declaration-level errors. */
function collectTable(
    declarations: readonly Declaration[],
    errors: ResolutionError[],
): DeclarationTable {
    const types = new Map<string, ResolvedData>()
    const variants = new Map<string, string>()
    const ambiguous = new Set<string>()

    for (const decl of declarations) {
        switch (decl.kind) {
            case "data": {
                if (RESERVED_DECLARATION_NAMES.includes(decl.name)) {
                    errors.push({
                        reason: "reserved-declaration-name",
                        message: `"${decl.name}" is reserved by the language and cannot name a ` +
                            `declaration — choose another name`,
                    })
                }
                if (types.has(decl.name)) {
                    errors.push({
                        reason: "duplicate-declaration",
                        message: `"${decl.name}" is declared more than once`,
                    })
                    continue
                }
                const resolved = resolveData(decl, errors)
                types.set(decl.name, resolved)
                for (const variant of resolved.variants) {
                    // A variant declared by two types is ambiguous bare and
                    // resolvable qualified (#84). Record both facts: the first
                    // declaration keeps the index entry so a diagnostic can name
                    // a candidate, and the ambiguity set forces qualification.
                    const existing = variants.get(variant.name)
                    if (existing !== undefined && existing !== decl.name) {
                        ambiguous.add(variant.name)
                    } else {
                        variants.set(variant.name, decl.name)
                    }
                }
                break
            }
        }
    }

    return { types, variants, ambiguousVariants: ambiguous }
}

/** Build one type's resolved form, reporting duplicate variant names. */
function resolveData(decl: DataDecl, errors: ResolutionError[]): ResolvedData {
    const variants: ResolvedVariant[] = []
    const folds: FoldDecl[] = []
    const seen = new Set<string>()

    for (const item of decl.items) {
        switch (item.kind) {
            case "variantDecl": {
                if (seen.has(item.name)) {
                    errors.push({
                        reason: "duplicate-variant",
                        message:
                            `"${decl.name}" declares the variant "${item.name}" more than once`,
                    })
                    continue
                }
                seen.add(item.name)
                variants.push({
                    name: item.name,
                    fields: item.fields.map((f) => ({ name: f.name, type: f.type })),
                })
                break
            }
            case "foldDecl":
                folds.push(item)
                break
        }
    }

    return decl.parent === undefined
        ? { name: decl.name, variants, folds }
        : { name: decl.name, parent: decl.parent, variants, folds }
}

/** Phase two: validate every reference in a declaration against the table. */
function validateDeclaration(
    decl: Declaration,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    switch (decl.kind) {
        case "data": {
            if (decl.parent !== undefined) {
                requireTypeName(decl.parent, `the parent of "${decl.name}"`, table, errors)
            }
            for (const item of decl.items) {
                validateBodyItem(decl, item, table, errors)
            }
            return
        }
    }
}

/** Validate one `data` body item. */
function validateBodyItem(
    decl: DataDecl,
    item: DataBodyItem,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    switch (item.kind) {
        case "variantDecl":
            for (const field of item.fields) {
                const context = `field "${field.name}" of "${item.name}"`
                validateType(field.type, context, table, errors)
            }
            return
        case "foldDecl":
            validateFold(decl, item, table, errors)
            return
    }
}

/**
 * Validate a fold: its spec's types, its contract clauses, and its arms.
 *
 * An arm head's bindings beyond the variant's field count bind the fold's `in:`
 * value (`surface-grammar.md` §5.1, overview §12.19), so the *minimum* binding
 * count is enforced here — a head with fewer bindings than its variant's fields
 * is an arity error.
 */
function validateFold(
    decl: DataDecl,
    fold: FoldDecl,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    if (fold.spec !== undefined) {
        validateSpec(fold.spec, `fold "${fold.name}"`, table, errors)
    }
    const resolved = table.types.get(decl.name)

    for (const arm of fold.arms) {
        if (arm.head.variant === undefined) {
            // `_` is exhaustiveness over an *open* variant set (§5.1), which is
            // comb inheritance's business (#86). The core's fold form has no
            // open-wildcard handler, and expanding `_` against the current
            // variant set would be wrong the moment a subtype adds one.
            errors.push({
                reason: "wildcard-arm",
                message: `the wildcard arm \`_\` in \`fold ${fold.name}\` has no core ` +
                    `counterpart yet — name each variant, or wait for comb inheritance ` +
                    `(#86) to give \`_\` a semantics`,
            })
            continue
        }
        const variant = resolved?.variants.find((v) => v.name === arm.head.variant)
        if (variant === undefined) {
            errors.push({
                reason: "unknown-variant",
                message: `"${decl.name}" has no variant "${arm.head.variant}" — a fold arm must ` +
                    `name one of its type's variants`,
            })
        }
        if (variant !== undefined && arm.head.bindings.length < variant.fields.length) {
            errors.push({
                reason: "arity-mismatch",
                message: `the arm for "${variant.name}" binds ${arm.head.bindings.length} ` +
                    `name(s) but the variant has ${variant.fields.length} field(s)`,
            })
        }
        // The arm body's references are elaboration's concern: which operation a
        // bare name denotes depends on the receiver's type, and the bindings
        // themselves are this pass's contribution to its scope.
    }
}

/** Validate every type in a spec record (`in:`/`out:` are the only typed keys). */
function validateSpec(
    spec: SpecRecord,
    owner: string,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    for (const entry of spec.entries) {
        if (entry.kind === "type") {
            const context = `the "${entry.key}" of ${owner}`
            validateType(entry.type, context, table, errors)
        }
        // `expr` values (a `properties` record) name operations rather than
        // types; validating those belongs to the law machinery, not to name
        // resolution.
    }
}

/** Validate a type expression's names. */
function validateType(
    type: AtomType,
    context: string,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    requireTypeName(type.name, context, table, errors)
}

/**
 * Require that a type name is a built-in or a declared type.
 *
 * There is no third possibility: the surface has no type variables (§3.8), so
 * an unknown name is always an error and never a minted variable.
 */
function requireTypeName(
    name: string,
    context: string,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    if (BUILTIN_TYPE_NAMES.includes(name)) return
    if (table.types.has(name)) return
    errors.push({
        reason: "unknown-type",
        message: `"${name}" (in ${context}) is not a declared type — the surface has no type ` +
            `variables, so every type name must be declared or built in`,
    })
}

/**
 * Validate the names an expression mentions against an arm's bindings.
 *
 * Resolution does not walk expressions: which declared operation a bare
 * `camelCase` name denotes, and whether a message chain's selector resolves,
 * both depend on the receiver's *type* — elaboration's material, reached
 * through Ω. The names this pass contributes to that scope are the arm head's
 * bindings, which it validates for arity above.
 */

// ── Convenience ──────────────────────────────────────────────────────────────

/** Render resolution errors as one message per line, for tests and the CLI. */
export function formatResolutionErrors(errors: readonly ResolutionError[]): string {
    return errors.map((e) => `${e.reason}: ${e.message}`).join("\n")
}
