/**
 * Elaboration: surface declarations → core μ-types + `Ω` operations.
 *
 * The core represents terms as concrete LC syntax — `OpSig.definition` is source
 * text, parsed and applied on demand by `LCEval.evalOp`. So elaboration emits
 * source text rather than constructing a core AST, and the result is checked by
 * exactly the machinery that checks hand-written core terms:
 *
 *   data Stack / Empty / Push value: Any rest: Family / fold size
 *     →  \e:Stack. fold [Stack] e { Empty() -> 0, Push(_, rest) -> (1 + rest) }
 */

import {
    Any,
    AnyType,
    DataType,
    Family,
    FamilyType,
    Field,
    Nothing,
    NothingType,
    type TypeSlot,
    Variant,
} from "../core/types.ts"

import { LCTypeCheck, OpDeclarationError, OpRegistry, OpSig, type Type } from "../core/index.ts"

import { TypeRegistry } from "../core/grammar.ts"

import type {
    AtomType,
    CaseArm,
    Construction,
    DataDecl,
    Expr,
    FoldDecl,
    Primary,
    SurfaceProgram,
} from "./ast.ts"

// ── Result ───────────────────────────────────────────────────────────────────

/** A `fold` declaration elaborated to an operation definition. */
export interface ElaboratedOperation {
    readonly name: string
    /** The operation's parameter types, in order (the fold's `in:` value). */
    readonly paramTypes: readonly Type[]
    /** The operation's result type (the spec's `out:`). */
    readonly resultType: Type
    /** The defining LC term, as concrete syntax. */
    readonly definition: string
    /** The surface declaration this operation came from. */
    readonly source: FoldDecl
}

/**
 * Why one declaration failed to elaborate.
 *
 * The *reasons* are the stable part; the message text is provisional, the same
 * convention `ResolutionError` follows — the vocabulary is pinned by the
 * diagnostics work, not by this pass.
 */
export interface ElaborationError {
    /**
     * The emitted definition does not type as the declared signature —
     * `paramTypes → resultType`. Every way the two can disagree is this one
     * reason, because they are one condition: the signature comes from the spec
     * (`in:` value, `out:` result) and the definition from the arms, and `Ω`
     * requires them to agree component-wise (`lc.md` §2.5, well-formedness).
     */
    readonly reason: "not-well-formed"
    /** The operation whose elaboration failed. */
    readonly operation: string
    readonly message: string
}

/** The outcome of elaborating a program. */
export interface ElaborationResult {
    /** The declared types, in source order. */
    readonly types: readonly DataType[]
    /** The declared operations, in source order. */
    readonly operations: readonly ElaboratedOperation[]
    /** A registry populated with `types` — ready for `LCTypeCheck`/`LCEval`. */
    readonly registry: TypeRegistry
    /**
     * `Ω`, populated with the operations that passed — in declaration order.
     *
     * A failed operation is absent rather than fatal: the failure is
     * per-operation, so the rest of the program stays usable, mirroring
     * `ResolutionResult`'s `ok` + `errors` shape. `errors` says which ones and
     * why.
     */
    readonly opRegistry: OpRegistry
    /** The per-declaration failures, in source order. */
    readonly errors: readonly ElaborationError[]
    /** Whether every declaration elaborated to a well-formed operation. */
    readonly ok: boolean
}

/**
 * Elaborate a resolved program.
 *
 * Every `data` declaration in the program is built in **one group**
 * (`DataType.buildAll`), so a field may name any other declared type regardless
 * of declaration order — the group resolves the references simultaneously. That
 * is the same knot the `DataTypeBuilder` API exposes for hand-built fixtures, and
 * it is what makes a program's declarations order-independent, matching the
 * resolver's whole-program view.
 *
 * Elaboration **has a verdict**: each emitted operation is checked against its
 * declared signature before it is installed in `Ω`, and a declaration that does
 * not hold up is reported in `errors` instead of being emitted as text the core
 * would reject downstream. The check is the core's own
 * (`LCTypeCheck.opWellFormedness`), not a second implementation of it — the
 * point is that `Ω`'s entry and the pipeline's verdict are the same judgement.
 */
export function elaborateProgram(program: SurfaceProgram): ElaborationResult {
    const dataDecls = program.declarations.filter((d): d is DataDecl => d.kind === "data")

    // Two-phase, because a declaration's fields may name any other declaration:
    // every builder handle exists first (each with its own lineage), then the
    // variants reference those handles, then the group publishes and resolves
    // every reference simultaneously. This is the same knot `DataType.buildAll`
    // exposes to hand-built fixtures — the reason a program's declarations are
    // order-independent here, matching the resolver's whole-program view.
    const handles = new Map<string, ReturnType<typeof DataType.define>>()
    for (const decl of dataDecls) handles.set(decl.name, DataType.define(decl.name))

    const builders = dataDecls.map((decl) => buildDeclaration(decl, handles))
    const types = builders.length === 0 ? [] : DataType.buildAll(...builders)

    const registry = new TypeRegistry()
    for (const type of types) registry.register(type)

    const opRegistry = new OpRegistry()
    const operations: ElaboratedOperation[] = []
    const errors: ElaborationError[] = []

    // Operations are declared in source order, so `Ω`'s stratification order is
    // the program's. A fold whose definition references an earlier fold checks
    // against it; a self-reference or forward reference is still rejected by
    // `declare`'s acyclicity check, and surfaces here as `not-well-formed`.
    for (const decl of dataDecls) {
        for (const operation of elaborateFolds(decl, types)) {
            const verdict = installOperation(operation, registry, opRegistry)
            if (verdict === undefined) {
                operations.push(operation)
            } else {
                errors.push({
                    reason: "not-well-formed",
                    operation: operation.name,
                    message: verdict,
                })
            }
        }
    }

    return {
        types,
        operations,
        registry,
        opRegistry,
        errors,
        ok: errors.length === 0,
    }
}

/**
 * Check one operation against its declared signature and install it in `Ω`.
 *
 * Returns `undefined` on success, or the reason it failed. Installation happens
 * here rather than in a later pass so that every `operations` entry is
 * simultaneously an `Ω` entry — the invariant the result type promises.
 *
 * `declare` also enforces acyclicity (a definition may only reference earlier
 * operations) and name shape. Both are reported as failures of this operation
 * rather than thrown: `Ω` is a stratified environment, so an operation whose
 * definition names itself (every recursive fold) or a later operation cannot be
 * installed. That is a declaration the environment refuses, not a crash.
 */
function installOperation(
    operation: ElaboratedOperation,
    registry: TypeRegistry,
    opRegistry: OpRegistry,
): string | undefined {
    const sig = new OpSig(
        operation.name,
        [...operation.paramTypes],
        operation.resultType,
        operation.definition,
    )
    // The checker is built per call so it sees the `Ω` accumulated so far —
    // a definition may reference an earlier operation, and `Ω` is the context
    // that check needs.
    const checker = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    try {
        opRegistry.declare(sig, checker.opWellFormedness)
        return undefined
    } catch (error) {
        // `OpDeclarationError` separates the operation name from the failed
        // check's reason; the name is already the error's `operation` field, so
        // the message carries only the reason — otherwise every diagnostic reads
        // "operation "x": …" after the caller has already been told which one.
        if (error instanceof OpDeclarationError) return error.reason
        return error instanceof Error ? error.message : String(error)
    }
}

// ── Declarations ─────────────────────────────────────────────────────────────

/**
 * One `data` declaration → a builder, with its lineage taken from `handles`.
 *
 * The builder is derived from the declaration's existing handle rather than
 * created fresh, so it shares that handle's lineage and the build group can
 * knot a *reference* to this type (a field of another declaration) into this
 * declaration's published instance.
 */
function buildDeclaration(
    decl: DataDecl,
    handles: ReadonlyMap<string, ReturnType<typeof DataType.define>>,
): ReturnType<typeof DataType.define> {
    let builder = handles.get(decl.name) ?? DataType.define(decl.name)
    for (const item of decl.items) {
        if (item.kind !== "variantDecl") continue
        const fields = item.fields.map((f) =>
            new Field(f.name, elaborateType(f.type, decl.name, handles))
        )
        builder = builder.addVariant(new Variant(item.name, fields))
    }
    return builder
}

/**
 * A surface type name → a core `Type` slot. `Family` and `Self` must not collapse:
 *
 * - `Family` is the μ-bound α, written in field position. It stays the symbolic
 *   `FamilyType`, resolved per carrier at point of use, so a recursive field is
 *   open by construction.
 * - `Self` is the *declaring* type, which is what makes `Num add <in: Self, out:
 *   Self>` return its operand's type. It resolves to the owner's handle — the
 *   builder during construction, the published instance after.
 *
 * A declared name yields its handle, not a copy: the slot type admits a builder so
 * the build group can knot forward and mutual references, and a name-only
 * placeholder would make every cross-type field a distinct object. The map's value
 * type is a parameter, so a builder map yields `TypeSlot` and a published map
 * yields `Type` — no cast between them.
 */
function elaborateType<T extends TypeSlot>(
    type: AtomType,
    owner: string,
    handles: ReadonlyMap<string, T>,
): T | FamilyType | AnyType | NothingType {
    switch (type.name) {
        case "Family":
            return Family
        case "Self":
            return handleFor(owner, handles)
        case "Any":
            return Any
        case "Nothing":
            return Nothing
        default:
            // Every other name in type position is a *declaration*.
            return handleFor(type.name, handles)
    }
}

/**
 * A declared type's handle.
 *
 * Resolution has already rejected an undeclared name, so every name reaching
 * here is declared. A name with no handle means the caller built the handle map
 * from the wrong declaration set — a caller bug, rejected loudly rather than
 * silently substituting another type.
 */
function handleFor<T>(name: string, handles: ReadonlyMap<string, T>): T {
    const handle = handles.get(name)
    if (handle === undefined) {
        throw new TypeError(
            `elaborate: no handle for the declared type "${name}" — a name reaching ` +
                `elaboration must be in the build group`,
        )
    }
    return handle
}

// ── Folds ────────────────────────────────────────────────────────────────────

/**
 * Every `fold` in a declaration, elaborated to an operation definition.
 *
 * Each fold is elaborated and then handed to the install step, which decides
 * whether it holds up. Whether the definition agrees with the signature is the
 * install step's question, so nothing is filtered here.
 */
function elaborateFolds(
    decl: DataDecl,
    types: readonly DataType[],
): ElaboratedOperation[] {
    const self = types.find((t) => t.name === decl.name)
    if (self === undefined) return []
    const published = publishedHandles(types)
    return decl.items.flatMap((item) =>
        item.kind === "foldDecl" ? [elaborateFold(item, decl, self, published)] : []
    )
}

/**
 * The published types, indexed by name as `elaborateType`'s handle map.
 *
 * A *published* instance stands in for its own handle: the map's value type is
 * `Type`, so `elaborateType` yields a real `Type` — the registry's instance
 * rather than a fresh, structurally-equal stand-in, and no cast is needed to
 * state a signature.
 */
function publishedHandles(types: readonly DataType[]): ReadonlyMap<string, Type> {
    const handles = new Map<string, Type>()
    for (const type of types) handles.set(type.name, type)
    return handles
}

/**
 * `fold size <in: S, out: T>` → an operation over the declaring type.
 *
 * The definition is a curried lambda chain whose body is the core fold. The
 * **carrier** is always the first parameter — the arms destructure the declaring
 * type's variants, so the fold's receiver is fixed by where it is declared. An
 * `in:` adds exactly one more (`surface-syntax.md` §2.3: an operation takes the
 * receiver and at most one `in:` value), which is what makes `add` an operation
 * of two arguments while `size` has one.
 *
 * Arms become the core's comma-separated handler list, keyed by variant name
 * with positional bindings. The parameter's name comes from the arms: a head
 * binds the variant's fields, and the binding beyond that is the author's name
 * for the extra lambda (`surface-grammar.md` §4.1). That is why `Zero other ->
 * other` works with no core change — `other` is a lambda the emitter introduces,
 * never a handler binding, so `E-Fold`'s walk over `variant.fields` (`lc.md`
 * §3.1) never has to reach it.
 */
function elaborateFold(
    fold: FoldDecl,
    decl: DataDecl,
    self: DataType,
    published: ReadonlyMap<string, Type>,
): ElaboratedOperation {
    const outType = specType(fold, "out", self, decl.name, published)
    const hasParameter = fold.spec?.entries.some((e) => e.key === "in" && e.kind === "type") ??
        false
    // The carrier is the first parameter and always present; `in:` is a second
    // argument, never a replacement for it (`elaboration.md` §3.1).
    const paramTypes: Type[] = [self]
    if (hasParameter) paramTypes.push(specType(fold, "in", self, decl.name, published))

    const ctx: RenderCtx = { decl, published, inBinding: emittedInBinding(fold) }
    const handlers = fold.arms.map((arm) => renderArm(arm, ctx))
    const parameters = hasParameter ? [ctx.inBinding] : []
    const definition = lambdaChain(decl.name, parameters, paramTypes.slice(1)) +
        `fold [${decl.name}] e { ${handlers.join(", ")} }`
    return {
        name: fold.name,
        paramTypes,
        resultType: outType,
        definition,
        source: fold,
    }
}

/**
 * The name the fold's extra argument is bound to in the emitted core term.
 *
 * The surface spells it `in` — a keyword, read from an arm body like `self`.
 * The core reserves that word for its `let … in` delimiter (`LC_RESERVED_WORDS`)
 * and admits only `[A-Za-z0-9_]` in an identifier, so the emitted binder needs a
 * core-legal spelling; the reference sites render through the same value, so the
 * two cannot drift.
 *
 * The name is made **hygienic** against the arm's own bindings: a field may be
 * named `in_` (it is an ordinary identifier), so the first candidate that the
 * variant's fields do not already use wins. The last candidate needs no check —
 * only one field name is tried against it.
 */
function emittedInBinding(fold: FoldDecl): string {
    const bound = new Set<string>()
    for (const arm of fold.arms) {
        for (const binding of arm.head.bindings) bound.add(binding)
    }
    for (const candidate of ["in_", "in__", "in___", "in____"]) {
        if (!bound.has(candidate)) return candidate
    }
    // Four `in_`-suffixed fields in one variant is not a case worth carrying
    // more candidates for; a collision here is a name the author chose.
    return "in_____"
}

/**
 * The emitted lambda chain: the carrier as `e`, then one lambda per `in:`
 * parameter.
 *
 * The core's `E-Op` applies a definition by currying (`lc.md` §3.1, where
 * `def(op) = λx₁:σ₁. … λxₙ:σₙ. t`), so the definition's shape must be a lambda
 * per declared parameter — one short is a definition that does not type as its
 * signature, which is what made a two-parameter fold elaborate to a
 * one-parameter term.
 *
 * Every binder is annotated. The core's `T-Abs` reads the type from the binder,
 * so an unannotated `\other.` has no type and the definition fails to parse —
 * the annotation is syntax, not decoration.
 */
function lambdaChain(
    carrier: string,
    parameters: readonly string[],
    parameterTypes: readonly Type[],
): string {
    let chain = `\\e:${carrier}. `
    for (let i = 0; i < parameters.length; i++) {
        chain += `\\${parameters[i]}:${parameterTypes[i]!.toString()}. `
    }
    return chain
}

/**
 * A spec entry's type, or a default.
 *
 * `in:` defaults to the declaring type — a fold over a `Stack` takes a `Stack`,
 * which is also what the arm-beyond-field bindings refer to. `out:` has no
 * defensible default beyond the lattice top, which every type is a subtype of.
 */
function specType(
    fold: FoldDecl,
    key: "in" | "out",
    self: DataType,
    ownerName: string,
    published: ReadonlyMap<string, Type>,
): Type {
    const entry = fold.spec?.entries.find((e) => e.key === key && e.kind === "type")
    if (entry === undefined || entry.kind !== "type") {
        return key === "in" ? self : Any
    }
    // A published handle map yields `Type`, so the signature needs no cast.
    return elaborateType(entry.type, ownerName, published)
}
/** What the renderer needs besides the expression: the program's declared types. */
interface RenderCtx {
    /** The enclosing declaration, for `Family`/`Self` in expression position. */
    readonly decl: DataDecl
    /** The program's published types, for a construction's declared field order. */
    readonly published: ReadonlyMap<string, Type>
    /** The core spelling of the fold's extra argument — see `emittedInBinding`. */
    readonly inBinding: string
}

/**
 * One case arm → one core handler. The core separates bindings with **spaces**
 * and handlers with **commas** — `{ Empty() -> 0, Push(v rest) -> rest }`. Getting
 * this wrong is silent: the parse just fails, with no hint that a separator is the
 * cause.
 *
 * Only the variant's fields appear in the handler's binding list. An arm head's
 * bindings beyond that count *name* the fold's `in:` parameter, which is a
 * curried lambda around the whole fold (`surface-grammar.md` §4.1) — emitting
 * the name here would rebind it inside the handler, and `E-Fold`'s walk over
 * `variant.fields` (`lc.md` §3.1) would never supply a value for it.
 *
 * A wildcard arm is rejected rather than expanded: `_` means exhaustiveness over an
 * *open* variant set, and expanding it against the current set would be wrong the
 * moment a subtype adds a variant. The resolver reports it, so this function is
 * only reached on the resolved path.
 */
function renderArm(arm: CaseArm, ctx: RenderCtx): string {
    const body = renderExpr(arm.body, ctx)
    // The resolver guarantees a named variant; `_` is rejected there because the
    // core's fold form cannot express an open wildcard.
    const bindings = arm.head.bindings.slice(0, fieldCount(arm, ctx))
    return `${arm.head.variant}(${bindings.join(" ")}) -> ${body}`
}

/**
 * How many fields the arm's variant declares — the number of head bindings that
 * belong to the handler rather than naming the fold's parameter.
 *
 * A miss falls back to the written count, so a caller bug yields the pre-existing
 * behaviour instead of dropping a binding that had a slot.
 */
function fieldCount(arm: CaseArm, ctx: RenderCtx): number {
    for (const type of ctx.published.values()) {
        if (!(type instanceof DataType)) continue
        const variant = type.findVariant(arm.head.variant ?? "")
        if (variant !== undefined) return variant.fields.length
    }
    return arm.head.bindings.length
}

// ── Expressions ──────────────────────────────────────────────────────────────

/**
 * Render an expression as core concrete syntax.
 *
 * The core's surface is small and positional: construction is `Variant(args)`
 * with commas, a symbolic operation is applied between its operands, and a
 * declared operation is applied by juxtaposition. Named-argument construction
 * therefore becomes positional here (`elaboration.md` §2.7) — the whole point of
 * elaboration.
 */
function renderExpr(expr: Expr, ctx: RenderCtx): string {
    switch (expr.kind) {
        case "binop":
            return `(${renderExpr(expr.lhs, ctx)} ${expr.op} ` +
                `${renderExpr(expr.rhs, ctx)})`
        case "unary":
            return `${expr.op} ${renderPrimary(expr.operand, ctx)}`
        case "call":
            return renderCall(expr.receiver, expr.parts, expr.messages, ctx)
        default:
            return renderPrimary(expr, ctx)
    }
}
/**
 * A selector's parts are the operation's keyword sequence, which the core spells by
 * applying: `receiver size` is `size(receiver)`. A keyword send eliminates its
 * receiver, so the receiver is the operation's argument, not its owner — hence the
 * positional pass.
 *
 * The reverse holds for an unlabelled send: `Succ p` is a send of `p` **to** `Succ`,
 * which the core spells `p(Succ)`. That is why the order below is
 * `message(receiver)`.
 */
function renderCall(
    receiver: Primary,
    parts: readonly { key: string; value: Expr }[],
    messages: readonly string[],
    ctx: RenderCtx,
): string {
    let rendered = renderPrimary(receiver, ctx)
    for (const message of messages) {
        rendered = `${message}(${rendered})`
    }
    if (parts.length > 0) {
        const args = parts.map((p) => renderExpr(p.value, ctx))
        const selector = parts.map((p) => p.key).join(":")
        rendered = `${selector}(${[rendered, ...args].join(", ")})`
    }
    return rendered
}

/** Render a primary as core concrete syntax. */
function renderPrimary(primary: Primary, ctx: RenderCtx): string {
    switch (primary.kind) {
        case "lit":
            return primary.text
        case "ref":
            // `Family`/`Self` in expression position denote the recursive
            // position; the core spells that as the enclosing type's name.
            if (primary.name === "Family" || primary.name === "Self") return ctx.decl.name
            // The fold's extra argument: same rename as its binder, or the two
            // would disagree.
            if (primary.name === "in") return ctx.inBinding
            return primary.name
        case "variantRef":
            // A zero-field variant is a *construction* in the core, not a bare
            // name: `Empty` in the core's syntax is a variable reference, and
            // `Empty()` is the nullary constructor (`lc.md` §2.2's
            // `variantProd`). The surface spells the constructor by name alone
            // (`grammar.ts`'s `construction`), so elaboration supplies the parens.
            return `${primary.name}()`
        case "construction": {
            // The core's construction is positional, so the named arguments are
            // emitted in the variant's **declaration** order. The caller wrote
            // each field by name and the order they wrote it in carries no
            // meaning; resolution has already ensured the names are exactly the
            // declared set, so every field finds its slot.
            const declared = declaredFieldOrder(primary, ctx)
            const values = new Map(primary.fields.map((f) => [f.key, f.value]))
            const args = declared.map((name) => {
                const value = values.get(name)
                return value === undefined ? "" : renderExpr(value, ctx)
            })
            return `${primary.variant}(${args.join(", ")})`
        }
        case "paren":
            return `(${renderExpr(primary.inner, ctx)})`
        case "opRef":
            return primary.qualifier === undefined
                ? primary.name
                : `${primary.qualifier} ${primary.name}`
    }
}

/**
 * A construction's declared field order, as the core will emit it.
 *
 * The variant is looked up among the program's published types. Resolution has
 * already rejected an undeclared variant and a field set that is not the
 * declared one, so a miss here is a caller bug — elaboration invoked on an
 * unresolved program. The field list falls back to the written order in that
 * case rather than dropping arguments.
 */
function declaredFieldOrder(construction: Construction, ctx: RenderCtx): readonly string[] {
    for (const type of ctx.published.values()) {
        const variant = type instanceof DataType
            ? type.findVariant(construction.variant)
            : undefined
        if (variant !== undefined) return variant.fields.map((f) => f.name)
    }
    return construction.fields.map((f) => f.key)
}
