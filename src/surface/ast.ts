/**
 * The surface language's abstract syntax.
 *
 * Exists because `DerivationTree` records *where* a `@rule` matched, not the
 * shape of a production: a repeated production nests as same-label nodes
 * carrying partial values, so a pass over it cannot tell a partial value from
 * a complete one. The AST is built by the productions' own semantic actions,
 * which see each production exactly once. `parseToTree` remains the vehicle for
 * spans, diagnostics, and unparsing.
 */

// ── Expressions (`grammar.ts`'s `expr`) ───────────────────────────────────────

/**
 * Three application forms plus the primaries. No application production, no
 * anonymous binder — see `grammar.ts`'s `expr`.
 */
export type Expr = Call | BinOp | UnaryOp | Primary

/** A receiver and its message chain. */
export interface Call {
    readonly kind: "call"
    readonly receiver: Primary
    /**
     * The selector's keyword parts, in source order. Empty for a bare operation
     * reference, which is a value, not a call. Collected greedily: when any
     * `key: arg` is present, all of them belong to this one call.
     */
    readonly parts: readonly KeyArg[]
    /** Unlabelled messages in the chain (the postfix unary send). */
    readonly messages: readonly string[]
}

/** A keyword part: `name: expr`. */
export interface KeyArg {
    readonly key: string
    readonly value: Expr
}

/** A binary call: one flat, left-associative precedence level. */
export interface BinOp {
    readonly kind: "binop"
    readonly op: string
    readonly lhs: Expr
    readonly rhs: Expr
}

/** A unary call: a name applied at level 3. */
export interface UnaryOp {
    readonly kind: "unary"
    readonly op: string
    readonly operand: Primary
}

/**
 * The primaries (§3.2's `primary`).
 *
 * A `pascalIdent` in expression position is a *variant reference* — a
 * zero-field variant read as a value (§3.4). A variant with fields is
 * *constructed*, which is `Construction`.
 */
export type Primary =
    | Lit
    | Ref
    | VariantRef
    | Construction
    | Paren
    | OpRef

/** A literal: whatever text a declared pattern matched (§2.4). */
export interface Lit {
    readonly kind: "lit"
    readonly text: string
}

/** A `camelCase` name in expression position — a binding or a declared operation. */
export interface Ref {
    readonly kind: "ref"
    readonly name: string
}

/**
 * A zero-field variant as a value: `Red`, or qualified `Color Red`.
 * `qualifier` is the declaring type's name when written; bare is the default and
 * qualification is disambiguation.
 */
export interface VariantRef {
    readonly kind: "variantRef"
    readonly qualifier?: string
    readonly name: string
}

/**
 * A construction with fields: `Point2D x: 1 y: 2`, or qualified
 * `Point Point2D x: 1 y: 2`.
 *
 * Fields are **named arguments**: each `field: value` pair binds by name, so the
 * order they are written in carries no meaning. Resolution requires the names to
 * be exactly the variant's declared set; elaboration emits the values in
 * declaration order, which is what the core's positional construction needs.
 */
export interface Construction {
    readonly kind: "construction"
    readonly qualifier?: string
    readonly variant: string
    readonly fields: readonly KeyArg[]
}

/** A parenthesized expression — the only way to re-open a message chain. */
export interface Paren {
    readonly kind: "paren"
    readonly inner: Expr
}

/**
 * An operation reference — the only spelling of a function value. An unbound
 * `camelCase` name in `primary` position resolves through the enclosing bindings,
 * then `Ω`.
 */
export interface OpRef {
    readonly kind: "opRef"
    readonly qualifier?: string
    readonly name: string
}

// ── Types ─────────────────────────────────────────────────────────────────────

/**
 * A type is always a name, never a shape. There is no function-type production,
 * so no declaration can state `σ -> τ` and no position could inhabit one; an
 * operation's type is its `FunType` chain in `Ω`.
 *
 * No type variables, no type parameters — permanently. Subtyping is the sole
 * abstraction mechanism. `Family`/`Self` are reserved as declaration names.
 */
export interface AtomType {
    readonly kind: "atom"
    readonly name: string
}

// ── Spec records ────────────────────────────────────────────────────────────

/**
 * The recognized keys carry different shapes: `in`/`out` a type, `aux` a
 * reference, `properties` an expression; `para`/`histo` are bare flags. An
 * unknown key still parses as an expression so it can be reported rather than
 * rejected as a parse failure.
 */
export interface SpecRecord {
    readonly entries: readonly SpecEntry[]
}

/** One spec entry, discriminated by the key's value shape. */
export type SpecEntry =
    /** `in: Type` / `out: Type` — a declared type, not an expression. */
    | { readonly key: string; readonly kind: "type"; readonly type: AtomType }
    /** `properties: (…), <flags>` — an expression value. */
    | { readonly key: string; readonly kind: "expr"; readonly value: Expr }
    /** `aux: #name` — a zygomorphism's auxiliary fold reference. */
    | { readonly key: string; readonly kind: "aux"; readonly name: string }
    /** `para` / `histo` — a bare flag. */
    | { readonly key: string; readonly kind: "flag" }

// ── Declarations ────────────────────────────────────────────────────────────

/** A program is `declaration*` — there are no expression statements. */
export interface SurfaceProgram {
    readonly declarations: readonly Declaration[]
}

/** Only `data` has a production; the other five forms plug into this same pipeline. */
export type Declaration = DataDecl

/** `data Name <: Parent?` with an indented body. The head is a bare `pascalIdent`. */
export interface DataDecl {
    readonly kind: "data"
    readonly name: string
    readonly parent?: string
    readonly items: readonly DataBodyItem[]
}

/** A `data` body item. */
export type DataBodyItem = VariantDecl | FoldDecl | MapDecl

/** Fields in declaration order; the surface spells them by name. */
export interface VariantDecl {
    readonly kind: "variantDecl"
    readonly name: string
    readonly fields: readonly FieldDecl[]
}

/** One variant field: `name: Type`. */
export interface FieldDecl {
    readonly name: string
    readonly type: AtomType
}

/**
 * `fold name specRecord?` with an indented body. Contract clauses parse here
 * because they are `foldItem`s; their semantics — the bindable-name set per
 * clause kind and the head arity — are a resolution rule, not elaboration.
 */
export interface FoldDecl {
    readonly kind: "foldDecl"
    readonly name: string
    readonly spec?: SpecRecord
    readonly contractClauses: readonly ContractClause[]
    readonly arms: readonly CaseArm[]
}

/**
 * A map is field-keyed, not variant-keyed: each transform names a field and
 * binds its own parameter, so only the named fields change. Recursion through
 * `Family` descends automatically — that is what makes it a map rather than a
 * fold that happens to rebuild.
 */
export interface MapDecl {
    readonly kind: "mapDecl"
    readonly name: string
    readonly spec?: SpecRecord
    readonly transforms: readonly FieldTransform[]
}

/**
 * One field transform: `field param -> expr`. `param` binds the field's current
 * value, so a transform needs no lambda form of its own.
 */
export interface FieldTransform {
    readonly field: string
    readonly param: string
    readonly body: Expr
}

/** `demands: self | expr` — a clause kind, its bindable names, its body. */
export interface ContractClause {
    readonly kind: "demands" | "ensures" | "invariant" | "rescue"
    readonly bindings: readonly string[]
    readonly body: Expr
}

/**
 * `armHead -> armBody`. Bindings beyond the variant's field count bind the
 * fold's `in:` value — the only seed-binding mechanism.
 */
export interface CaseArm {
    readonly head: ArmHead
    readonly body: Expr
}

/** An arm head: a variant name (or `_`) and its bindings. */
export interface ArmHead {
    /** `undefined` for the wildcard arm `_`. */
    readonly variant?: string
    readonly bindings: readonly string[]
}
