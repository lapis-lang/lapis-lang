/**
 * Elaboration: surface declarations → core μ-types + `Ω` operations.
 *
 * The core represents terms as **concrete LC syntax**: `OpSig.definition` is
 * "the operation's defining LC term, as concrete-syntax source text", parsed and
 * applied on demand by `LCEval.evalOp`. There is no shared core AST to construct,
 * so elaboration emits source text and hands it to the existing one-pass grammar.
 * That is the same contract `Ω` already honours for every operation definition,
 * so elaborated text is checked by exactly the machinery that checks hand-written
 * core terms.
 *
 * The mapping is `elaboration.md` §3.1:
 *
 * ```
 * data Stack
 *     Empty
 *     Push value: Any rest: Family
 *     fold size <in: Stack, out: Any>
 *         Empty -> 0
 *         Push _ rest -> 1 + rest
 * ```
 *
 * becomes a `DataType` whose `Push` has a `Family`-typed `rest` field — `Family`
 * is the μ-bound α, so a recursive field needs no type-name lookup — and an
 * operation whose LC definition is
 *
 * ```
 * \e:Stack. fold [Stack] e { Empty() -> 0, Push(_, rest) -> (1 + rest) }
 * ```
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
    Type,
    type TypeSlot,
    Variant,
} from "../core/types.ts"

import { TypeRegistry } from "../core/grammar.ts"

import type { AtomType, CaseArm, DataDecl, Expr, FoldDecl, Primary, SurfaceProgram } from "./ast.ts"

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

/** The outcome of elaborating a program. */
export interface ElaborationResult {
    /** The declared types, in source order. */
    readonly types: readonly DataType[]
    /** The declared operations, in source order. */
    readonly operations: readonly ElaboratedOperation[]
    /** A registry populated with `types` — ready for `LCTypeCheck`/`LCEval`. */
    readonly registry: TypeRegistry
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

    const operations = dataDecls.flatMap((decl) => elaborateFolds(decl, types))
    return { types, operations, registry }
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
 * A surface type expression → a core `Type` slot.
 *
 * The input is an `AtomType`, which is the whole surface type grammar — a type
 * is always a name, never a shape. `Family` and `Self` are **different
 * references** and must not collapse:
 *
 * - **`Family`** is the μ-bound α, written in *field* position
 *   (`surface-grammar.md` §3.5). It stays the symbolic `FamilyType`, which the
 *   core resolves per carrier at the point of use (`resolveFamily`), so a
 *   recursive field is open by construction.
 * - **`Self`** is the *declaring type*, written in a spec's `in:`/`out:` — which
 *   is what makes `Num add <in: Self, out: Self>` return its operand's type. It
 *   resolves to the owner's own handle: during construction that is the builder
 *   (which the slot type admits, so the group knots it), and after publication
 *   it is the real instance.
 *
 * A declared name yields that declaration's **handle**, not a copy. The slot type
 * admits a builder precisely so the build group can resolve a forward or mutual
 * reference into the real published instance; handing back a name-only
 * placeholder instead would make every cross-type field a distinct object and
 * break structural comparison.
 *
 * The handle map's value type is a parameter, so a *builder* map yields
 * `TypeSlot` (what construction needs) and a *published* map yields `Type` (what
 * a spec's signature needs) — one set of name rules, no cast to bridge them.
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

/** Every `fold` in a declaration, elaborated to an operation definition. */
function elaborateFolds(
    decl: DataDecl,
    types: readonly DataType[],
): ElaboratedOperation[] {
    const self = types.find((t) => t.name === decl.name)
    if (self === undefined) return []
    const published = publishedHandles(types)
    return decl.items.flatMap((item) => {
        if (item.kind !== "foldDecl") return []
        return [elaborateFold(item, decl, self, published)]
    })
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
 * The definition is a lambda over the fold's `in:` value whose body is the core
 * fold. Arms become the core's comma-separated handler list, keyed by variant
 * name with positional bindings — the arm head's bindings *are* the handler's
 * binding list, in order, which is why §5.1's "bindings beyond the field count
 * bind the input" needs no translation.
 */
function elaborateFold(
    fold: FoldDecl,
    decl: DataDecl,
    self: DataType,
    published: ReadonlyMap<string, Type>,
): ElaboratedOperation {
    const inType = specType(fold, "in", self, decl.name, published)
    const outType = specType(fold, "out", self, decl.name, published)

    const handlers = fold.arms.map((arm) => renderArm(arm, decl))
    return {
        name: fold.name,
        paramTypes: [inType],
        resultType: outType,
        definition: `\\e:${decl.name}. fold [${decl.name}] e { ${handlers.join(", ")} }`,
        source: fold,
    }
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

/**
 * One case arm → one core handler: `Variant(x y) -> body`.
 *
 * The core separates a handler's **bindings with spaces** and its **handlers
 * with commas** — `{ Empty() -> 0, Push(v rest) -> rest }`. Getting this wrong is
 * silent: the parse simply fails, with no indication that a separator is the
 * cause.
 *
 * A wildcard arm (`_`) would need the declaring type's complete variant set to
 * expand into named handlers. The core's merged fold form has a pattern arm that
 * could carry it, but a pattern source is not what `_` means — `_` is
 * exhaustiveness over an *open* variant set (`surface-grammar.md` §5.1), which is
 * comb inheritance's business (#86). An arm that names no variant therefore
 * cannot be elaborated faithfully here, and silently expanding it against the
 * *current* variant set would be wrong the moment a subtype adds one. It is
 * rejected instead — the resolver reports it, and this function is only reached
 * on the resolved path.
 */
function renderArm(arm: CaseArm, decl: DataDecl): string {
    const body = renderExpr(arm.body, decl)
    // The resolver guarantees a named variant; `_` is rejected there because the
    // core's fold form cannot express an open wildcard.
    return `${arm.head.variant}(${arm.head.bindings.join(" ")}) -> ${body}`
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
function renderExpr(expr: Expr, decl: DataDecl): string {
    switch (expr.kind) {
        case "binop":
            return `(${renderExpr(expr.lhs, decl)} ${expr.op} ` +
                `${renderExpr(expr.rhs, decl)})`
        case "unary":
            return `${expr.op} ${renderPrimary(expr.operand, decl)}`
        case "call":
            return renderCall(expr.receiver, expr.parts, expr.messages, decl)
        default:
            return renderPrimary(expr, decl)
    }
}

/**
 * Render a message chain.
 *
 * A selector's parts are the operation's keyword sequence, which the core spells
 * by applying the operation: `receiver size` is `size(receiver)`. The surface's
 * receiver-taking rule (§3.3: a keyword send eliminates its receiver) means the
 * receiver is the operation's argument, not the operation's owner — so the
 * rendered form passes it positionally.
 *
 * The reverse holds for an unlabelled send: §3.1's `unaryExpr ::= unaryExpr ␣
 * ident` makes `Succ p` a send of `p` **to** `Succ`, which the core spells
 * `p(Succ)` — `p` applied to `Succ`, not the other way round. That is why the
 * order below is `message(receiver)`.
 */
function renderCall(
    receiver: Primary,
    parts: readonly { key: string; value: Expr }[],
    messages: readonly string[],
    decl: DataDecl,
): string {
    let rendered = renderPrimary(receiver, decl)
    for (const message of messages) {
        rendered = `${message}(${rendered})`
    }
    if (parts.length > 0) {
        const args = parts.map((p) => renderExpr(p.value, decl))
        const selector = parts.map((p) => p.key).join(":")
        rendered = `${selector}(${[rendered, ...args].join(", ")})`
    }
    return rendered
}

/** Render a primary as core concrete syntax. */
function renderPrimary(primary: Primary, decl: DataDecl): string {
    switch (primary.kind) {
        case "lit":
            return primary.text
        case "ref":
            // `Family`/`Self` in expression position denote the recursive
            // position; the core spells that as the enclosing type's name.
            if (primary.name === "Family" || primary.name === "Self") return decl.name
            return primary.name
        case "variantRef":
            // A zero-field variant is a *construction* in the core, not a bare
            // name: `Empty` in the core's syntax is a variable reference, and
            // `Empty()` is the nullary constructor (`lc.md` §2.2's
            // `variantProd`). The surface spells the constructor by name alone
            // (`surface-grammar.md` §3.4), so elaboration supplies the parens.
            return `${primary.name}()`
        case "construction": {
            const args = primary.fields.map((f) => renderExpr(f.value, decl))
            return `${primary.variant}(${args.join(", ")})`
        }
        case "paren":
            return `(${renderExpr(primary.inner, decl)})`
        case "opRef":
            return primary.qualifier === undefined
                ? primary.name
                : `${primary.qualifier} ${primary.name}`
    }
}
