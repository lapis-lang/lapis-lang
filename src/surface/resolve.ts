/**
 * Name resolution for the surface language — the first tree-consuming pass.
 *
 * The pass walks the surface AST and answers the four questions elaboration
 * cannot answer locally:
 *
 * 1. **Which declarations exist**, and what each contributes — declared type
 *    names, their variants and fields, and their operations. This is the
 *    declaration table, and it is what makes the bare-vs-qualified rule
 *    decidable: a bare name resolves iff it is unique in scope.
 * 2. **Whether every type name resolves.** The surface has no type variables
 *    and no type parameters, permanently (`grammar.ts`'s `atomType`), so a name
 *    that is neither built in nor declared has no legitimate meaning. It is an
 *    error at the annotation, not an opaque variable minted for later: a minted
 *    variable would fail somewhere else entirely, far from the misspelling.
 * 3. **Whether every constructor resolves.** A construction names its variant
 *    inside a body, where `unknown-type` cannot reach, so constructor position
 *    gets its own walk: the name must denote a declared variant, a qualifier
 *    must name the type that declares it, and the keyword sequence must equal
 *    the variant's declared field sequence.
 * 4. **Whether a reserved reference was taken as a declaration name.**
 *    `Family` and `Self` are the language-defined recursive references; a user
 *    declaration may not shadow them, or the same spelling would flip the
 *    recursion discipline by what else happens to be in scope.
 *
 * Resolution is a separate pass rather than grammar gates because every one of
 * these questions is *whole-program*: `data List` may declare `Cons` before
 * `data Nat` refers to it, and the surface has no ordering rule.
 */

import type {
    AtomType,
    CaseArm,
    Construction,
    DataBodyItem,
    DataDecl,
    Declaration,
    Expr,
    FoldDecl,
    Primary,
    SpecRecord,
    SurfaceProgram,
} from "./ast.ts"
// ── Diagnostics ──────────────────────────────────────────────────────────────

/**
 * A resolution failure: a rule, the offending name, and a message that names
 * the remedy.
 *
 * The message *text* is not yet pinned. This pass fixes the *reasons*: one
 * place per rejection for the diagnostic vocabulary to be pinned against.
 */
export interface ResolutionError {
    readonly reason:
        | "reserved-declaration-name"
        | "duplicate-declaration"
        | "duplicate-variant"
        | "unknown-type"
        | "unknown-variant"
        | "unknown-constructor"
        | "ambiguous-constructor"
        | "bad-qualifier"
        | "selector-mismatch"
        | "arity-mismatch"
        | "duplicate-spec-key"
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
     * Variant name → **every** declaring type's name, for bare resolution.
     *
     * Every candidate is kept so an ambiguity diagnostic can name each side.
     * Bare use resolves only when exactly one candidate is unrelated to the
     * others; see `ambiguousVariants`.
     */
    readonly variants: ReadonlyMap<string, readonly string[]>
    /**
     * Variant names whose declarers are not all one lineage — bare use is
     * ambiguous.
     *
     * A parent and a child that both declare a variant are *not* ambiguous: the
     * child's declaration is the parent's, narrowed (comb inheritance), so a
     * bare construction still denotes one constructor. Only declarers with no
     * ancestry relation collide.
     */
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
 * The names the language defines and no declaration may take.
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
                types.set(decl.name, resolveData(decl, errors))
                break
            }
        }
    }

    // The variant index needs every declaration before it can classify a
    // collision, because "several declaring types" is not yet ambiguity: a
    // parent and child that both declare a variant are one constructor.
    const variants = new Map<string, string[]>()
    for (const data of types.values()) {
        for (const variant of data.variants) {
            const candidates = variants.get(variant.name)
            if (candidates === undefined) variants.set(variant.name, [data.name])
            else if (!candidates.includes(data.name)) candidates.push(data.name)
        }
    }

    const ambiguous = new Set<string>()
    for (const [name, candidates] of variants) {
        if (!allOneLineage(candidates, types)) ambiguous.add(name)
    }

    return { types, variants, ambiguousVariants: ambiguous }
}

/**
 * Whether every declarer of one variant name belongs to a single inheritance
 * chain — i.e. whether they are one constructor rather than a collision.
 *
 * A child re-declaring an inherited variant is narrowing it (comb inheritance),
 * so `List` and `IntList <: List` both declaring `Cons` is *not* ambiguous: bare
 * `Cons` still denotes one constructor. Two types with no ancestry relation are
 * a genuine collision, and the qualified form is required.
 */
function allOneLineage(
    candidates: readonly string[],
    types: ReadonlyMap<string, ResolvedData>,
): boolean {
    for (let i = 0; i < candidates.length; i++) {
        for (let j = i + 1; j < candidates.length; j++) {
            const a = candidates[i]!
            const b = candidates[j]!
            if (!isAncestorOf(a, b, types) && !isAncestorOf(b, a, types)) return false
        }
    }
    return true
}

/** Whether `ancestor` is `name`'s parent, grandparent, … (declared names only). */
function isAncestorOf(
    ancestor: string,
    name: string,
    types: ReadonlyMap<string, ResolvedData>,
): boolean {
    const seen = new Set<string>()
    let current = types.get(name)?.parent
    while (current !== undefined && !seen.has(current)) {
        if (current === ancestor) return true
        seen.add(current)
        current = types.get(current)?.parent
    }
    return false
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
        case "mapDecl":
            // A `map` is otherwise unvalidated and dropped, but its transforms are
            // still expressions, and a constructor may appear in one.
            if (item.spec !== undefined) {
                validateSpec(item.spec, `map "${item.name}"`, table, errors)
            }
            for (const transform of item.transforms) {
                validateExpression(transform.body, table, errors)
            }
            return
    }
}

/**
 * Validate a fold: its spec's types, its contract clauses, and its arms.
 *
 * An arm head binds exactly the variant's fields. The fold's `in:` parameter is
 * not one of them: it is machinery-supplied and read from the body as `in`, in
 * the same way `self` is (`surface-grammar.md` §4.1). That is why the core's
 * handler list and the arm head agree on the field count — `E-Fold` walks
 * `variant.fields` (`lc.md` §3.1) and the head names no more than that.
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

    for (const clause of fold.contractClauses) {
        // A clause body is an expression like any other, so a constructor may
        // appear in it and must be resolved there.
        validateExpression(clause.body, table, errors)
    }

    for (const arm of fold.arms) {
        validateArm(decl, fold, arm, resolved, table, errors)
    }
}

/**
 * Validate one case arm: its head against the variant set, and its body's
 * constructor references.
 */
function validateArm(
    decl: DataDecl,
    fold: FoldDecl,
    arm: CaseArm,
    resolved: ResolvedData | undefined,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    if (arm.head.variant === undefined) {
        // `_` is exhaustiveness over an *open* variant set, which is comb
        // inheritance's business. The core's fold form has no open-wildcard
        // handler, and expanding `_` against the current variant set would be
        // wrong the moment a subtype adds one.
        errors.push({
            reason: "wildcard-arm",
            message: `the wildcard arm \`_\` in \`fold ${fold.name}\` has no core ` +
                `counterpart yet — name each variant, or wait for comb inheritance ` +
                `to give \`_\` a semantics`,
        })
        validateExpression(arm.body, table, errors)
        return
    }

    const variant = resolved?.variants.find((v) => v.name === arm.head.variant)
    if (variant === undefined) {
        errors.push({
            reason: "unknown-variant",
            message: `"${decl.name}" has no variant "${arm.head.variant}" — a fold arm must ` +
                `name one of its type's variants`,
        })
    }
    if (variant !== undefined) {
        validateArmBindings(fold, variant, arm, errors)
    }

    validateExpression(arm.body, table, errors)
}

/**
 * An arm head binds exactly the variant's fields.
 *
 * The count is exact, not a minimum. Too few leaves a field unnamed; too many
 * names a slot the emitted handler does not have, which the emitter would
 * silently drop — the failure mode that made a two-parameter fold elaborate to
 * a one-parameter definition.
 */
function validateArmBindings(
    fold: FoldDecl,
    variant: ResolvedVariant,
    arm: CaseArm,
    errors: ResolutionError[],
): void {
    const bound = arm.head.bindings.length
    const fields = variant.fields.length
    if (bound === fields) return
    errors.push({
        reason: "arity-mismatch",
        message: bound < fields
            ? `the arm for "${variant.name}" binds ${bound} name(s), but the variant has ` +
                `${fields} field(s) — every field must be named`
            : `the arm for "${variant.name}" binds ${bound} name(s), but the variant has ` +
                `${fields} field(s) and \`fold ${fold.name}\` binds no extra argument — ` +
                `the \`in:\` value is read from the body as \`in\``,
    })
}

/**
 * Validate a spec record: every entry's type, and the key's multiplicity.
 *
 * `specRecord` is a keyword *list*, so nothing in the grammar stops a key
 * appearing twice, and `specType` reads the first match — the second would be
 * silently dropped. A repeated `in:` is the dangerous case: it *looks* like the
 * way to declare a second operand, resolves cleanly, and then elaborates to a
 * one-parameter operation. It is rejected here instead.
 */
function validateSpec(
    spec: SpecRecord,
    owner: string,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    const seen = new Set<string>()
    for (const entry of spec.entries) {
        if (seen.has(entry.key)) {
            errors.push({
                reason: "duplicate-spec-key",
                message: `${owner} declares "${entry.key}" more than once in its spec record — ` +
                    `each key may appear once, and a repeated one is silently dropped`,
            })
        }
        seen.add(entry.key)

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

// ── Expressions ──────────────────────────────────────────────────────────────

/**
 * Validate an expression's constructor references.
 *
 * Constructor position is the one naming position `unknown-type` cannot reach,
 * so it needs its own walk. A *constructor* is a `pascalIdent` in
 * expression position — a `variantRef` or a `construction` — and nothing else:
 * `camelCase` names are bindings or operation references, and a literal is
 * whatever text a declared pattern matched. So the walk needs no scope: an arm
 * binding is a `nameOrKeyword` (`ident` and keywords, never `pascalIdent`), and
 * cannot shadow a constructor.
 *
 * Every expression form is covered, because a constructor can appear anywhere:
 * a construction's field values, a call's receiver and parts, a `binop`'s
 * operands, and a `unary`'s operand, through any depth of parentheses.
 */
function validateExpression(
    expr: Expr,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    switch (expr.kind) {
        case "binop":
            validateExpression(expr.lhs, table, errors)
            validateExpression(expr.rhs, table, errors)
            return
        case "unary":
            validatePrimary(expr.operand, table, errors)
            return
        case "call":
            validatePrimary(expr.receiver, table, errors)
            for (const part of expr.parts) validateExpression(part.value, table, errors)
            return
        default:
            validatePrimary(expr, table, errors)
    }
}

/** Validate one primary's constructor reference. */
function validatePrimary(
    primary: Primary,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    switch (primary.kind) {
        case "paren":
            validateExpression(primary.inner, table, errors)
            return
        case "construction":
            validateConstruction(primary, table, errors)
            return
        case "variantRef":
            validateConstruction(
                {
                    kind: "construction",
                    qualifier: primary.qualifier,
                    variant: primary.name,
                    fields: [],
                },
                table,
                errors,
            )
            return
        // A literal is matched text, a `ref` is a binding or an operation
        // reference, and an `opRef` is a function value — none introduces a
        // constructor, so none is this pass's to resolve.
        case "lit":
        case "ref":
        case "opRef":
            return
    }
}

/**
 * Validate a construction (or a nullary variant reference) against the variants
 * in scope.
 *
 * Three rules:
 *
 * 1. **A qualifier must name a declared type that declares the variant.** An
 *    undeclared qualifier, or a type whose member set lacks the variant, is
 *    `bad-qualifier` — this is the `(Ghost One)` / `(A Two)` case.
 * 2. **A bare name must be unambiguous.** No candidate anywhere is
 *    `unknown-constructor`; several candidates unrelated by ancestry is
 *    `ambiguous-constructor`, naming each. A parent and child that both declare
 *    it are one constructor, not a collision.
 * 3. **Every field must be named exactly once, and nothing else.** Field names
 *    bind by name, so the order they are written in carries no meaning: a
 *    construction supplies a set of `field: value` pairs, and elaboration emits
 *    them in declaration order. A name that is missing, duplicated, or undeclared
 *    leaves a slot unbound or a value without a slot — `selector-mismatch`.
 */
function validateConstruction(
    construction: Construction,
    table: DeclarationTable,
    errors: ResolutionError[],
): void {
    const { qualifier, variant: name, fields } = construction

    for (const field of fields) validateExpression(field.value, table, errors)

    const declarers = qualifier === undefined
        ? resolveBareConstructor(name, table, errors)
        : resolveQualifiedConstructor(qualifier, name, table, errors)
    if (declarers === undefined || declarers.length === 0) return

    // The rule reads the *declared* field set. Several declarers of one lineage
    // share it, so any candidate will do; a genuine collision was reported above.
    const declared = table.types.get(declarers[0]!)?.variants.find((v) => v.name === name)
    if (declared === undefined) return
    requireSelector(
        name,
        qualifier,
        fields.map((f) => f.key),
        declared.fields.map((f) => f.name),
        errors,
    )
}

/**
 * A bare construction's declaring types, or `undefined` when the name is
 * unknown or ambiguous (each already reported).
 */
function resolveBareConstructor(
    name: string,
    table: DeclarationTable,
    errors: ResolutionError[],
): readonly string[] | undefined {
    const candidates = table.variants.get(name)
    if (candidates === undefined || candidates.length === 0) {
        errors.push({
            reason: "unknown-constructor",
            message: `"${name}" is not a declared variant — a construction must name a variant ` +
                `declared by a type in scope`,
        })
        return undefined
    }
    if (table.ambiguousVariants.has(name)) {
        errors.push({
            reason: "ambiguous-constructor",
            message:
                `"${name}" is ambiguous — declared by ${listOf(candidates)}; qualify it with ` +
                `the declaring type, as in "${candidates[0]} ${name}"`,
        })
        return undefined
    }
    return candidates
}

/**
 * A qualified construction's declaring type, or `undefined` when the qualifier
 * or variant does not resolve (each already reported).
 *
 * A qualifier names the _declaring_ type, so the variant must be declared by it
 * directly — not merely inherited into its member set. Which type constructs an
 * inherited variant is a separate question, decided with comb inheritance.
 */
function resolveQualifiedConstructor(
    qualifier: string,
    name: string,
    table: DeclarationTable,
    errors: ResolutionError[],
): readonly string[] | undefined {
    const type = table.types.get(qualifier)
    if (type === undefined) {
        errors.push(
            table.types.has(qualifier)
                ? {
                    reason: "bad-qualifier",
                    message: `"${qualifier}" declares no variant "${name}" — a qualifier must ` +
                        `name the type that declares the constructor`,
                }
                : {
                    reason: "bad-qualifier",
                    message: `"${qualifier}" (qualifying "${name}") is not a declared type`,
                },
        )
        return undefined
    }
    if (!type.variants.some((v) => v.name === name)) {
        errors.push({
            reason: "bad-qualifier",
            message: `"${qualifier}" declares no variant "${name}" — a qualifier must name the ` +
                `type that declares the constructor`,
        })
        return undefined
    }
    return [qualifier]
}

/**
 * Require that a construction names exactly the variant's declared fields.
 *
 * The comparison is on the **sets**: field names bind by name, so
 * `P2 y: … x: …` supplies the same two slots as `P2 x: … y: …` and is equally
 * well-formed. Order is not part of a construction's meaning — the caller names
 * each slot, and elaboration emits the arguments in declaration order from the
 * names. Only a name that is missing, duplicated, or undeclared leaves a slot
 * unbound or a value with no slot, which is the rejection.
 */
function requireSelector(
    variant: string,
    qualifier: string | undefined,
    written: readonly string[],
    declared: readonly string[],
    errors: ResolutionError[],
): void {
    const label = qualifier === undefined ? variant : `${qualifier} ${variant}`
    const missing = declared.filter((field) => !written.includes(field))
    const unknown = written.filter((field) => !declared.includes(field))
    const duplicated = written.filter((field, i) => written.indexOf(field) !== i)

    if (missing.length === 0 && unknown.length === 0 && duplicated.length === 0) return

    const problems: string[] = []
    if (unknown.length > 0) problems.push(`no field ${listOf(unknown)}`)
    if (missing.length > 0) problems.push(`missing ${listOf(missing)}`)
    if (duplicated.length > 0) problems.push(`${listOf(duplicated)} given twice`)
    errors.push({
        reason: "selector-mismatch",
        message: `"${label}" declares ${fieldList(declared)}, but it is constructed with ` +
            `${fieldList(written)} — ${problems.join(", ")}`,
    })
}

/** `["a", "b"]` → `` `a`, `b` `` — for diagnostics. */
function listOf(names: readonly string[]): string {
    return names.map((n) => `\`${n}\``).join(", ")
}

/** A field sequence for a diagnostic, or "no fields" when empty. */
function fieldList(names: readonly string[]): string {
    return names.length === 0 ? "no fields" : `the fields ${listOf(names)}`
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

// ── Convenience ──────────────────────────────────────────────────────────────

/** Render resolution errors as one message per line, for tests and the CLI. */
export function formatResolutionErrors(errors: readonly ResolutionError[]): string {
    return errors.map((e) => `${e.reason}: ${e.message}`).join("\n")
}
