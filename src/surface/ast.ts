/**
 * The surface language's abstract syntax.
 *
 * This is the artifact the two tree-consuming passes (`NameResolverPass`,
 * `ElaboratorPass`) operate on. It exists because the engine's
 * `DerivationTree` retains *where a `@rule` matched*, not the shape of a
 * production: a repeated production yields nested same-label nodes carrying
 * partial values (a `many()` over a rule produces
 * `[as] → [as] → [as] → [one]`), and a fixed-arity `seq` yields one node with
 * no children. A pass dispatching on those labels fires once per repetition and
 * cannot tell a partial value from a complete one.
 *
 * The AST is produced by the surface grammar's own semantic actions
 * (`.map`/`chain`), which see each production exactly once. The derivation tree
 * is still available via `parseToTree` — it is the right vehicle for spans,
 * diagnostics, and unparsing.
 *
 * See `_docs/theory/surface-grammar.md` for the productions these types mirror.
 */

// ── Expressions (`surface-grammar.md` §3) ────────────────────────────────────

/**
 * An expression.
 *
 * The surface has exactly three operation-application forms plus the primaries
 * (§3.1) — there is no application production and no anonymous binder (§3.2,
 * §3.6.1):
 *
 * - `Call` — a receiver plus a (possibly empty) message chain.
 * - `BinOp` — `lhs op rhs`, one flat precedence level, left-associative.
 * - `UnaryOp` — `op rhs` in a prefix position (`not x`), and the postfix
 *   unary send of §3.1's `unaryExpr`.
 *
 * A *primitive* is one of the `Primary` variants below.
 */
export type Expr = Call | BinOp | UnaryOp | Primary

/** A receiver followed by its messages — the message chain of §3.3. */
export interface Call {
    readonly kind: "call"
    readonly receiver: Primary
    /**
     * The selector's keyword parts and their arguments, in source order.
     *
     * Empty for a bare operation reference (`double`), which is a value, not a
     * call. Greedy collection (§3.3): when any `key: arg` is present, *all* of
     * them belong to this one call — they are never nested sends.
     */
    readonly parts: readonly KeyArg[]
    /** Unlabelled messages in the chain (`unaryExpr`'s postfix send). */
    readonly messages: readonly string[]
}

/** A keyword part: `name: expr`. */
export interface KeyArg {
    readonly key: string
    readonly value: Expr
}

/** A binary call: `lhs op rhs` (§3.1 level 2, uniform precedence). */
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
 * A zero-field variant read as a value: `Red`, or qualified `Color Red` (§3.4).
 *
 * `qualifier` is the declaring type's name when written, `undefined` when bare.
 * Bare is the default; qualification is disambiguation (#84).
 */
export interface VariantRef {
    readonly kind: "variantRef"
    readonly qualifier?: string
    readonly name: string
}

/**
 * A construction with fields: `Point2D x: 1 y: 2`, or qualified
 * `Point Point2D x: 1 y: 2` (§3.4, §2.7 of `elaboration.md`).
 *
 * Fields are positional in declaration order; the surface spells them by name
 * and elaboration resolves names to positions.
 */
export interface Construction {
    readonly kind: "construction"
    readonly qualifier?: string
    readonly variant: string
    readonly fields: readonly KeyArg[]
}

/** A parenthesized expression — the only way to re-open a message chain (§3.3). */
export interface Paren {
    readonly kind: "paren"
    readonly inner: Expr
}

/**
 * An operation reference — a function value (§3.6.1).
 *
 * A function value is *only* an operation reference: there is no block literal,
 * so an unbound `camelCase` name in `primary` position resolves through the
 * enclosing bindings and then `Ω`.
 */
export interface OpRef {
    readonly kind: "opRef"
    readonly qualifier?: string
    readonly name: string
}

// ── Types (§3.8) ─────────────────────────────────────────────────────────────

/**
 * `( typeExpr )` | `pascalIdent` | `Family` | `Self` | `Any` | `Nothing` (§3.8).
 *
 * This is the whole type grammar, so a surface type is never anything but a
 * name. There is deliberately no function-type production: an operation
 * reference is the only way to *name* a function value (§3.6.1), and an
 * operation's type is its declared `FunType` chain in `Ω` rather than something
 * written in a declaration. A `σ -> τ` production would therefore build a type
 * that no surface position could inhabit.
 *
 * There are no type variables and no type parameters, permanently (§3.8,
 * overview §12.29): `atomType` admits no lowercase production and no
 * declaration takes a parameter list. Subtyping is the sole abstraction
 * mechanism.
 *
 * `Family` and `Self` are the recursive self-references and are reserved as
 * declaration names (#101); that gate is applied at declaration, not here.
 */
export interface AtomType {
    readonly kind: "atom"
    readonly name: string
}

// ── Spec records (§3.7) ──────────────────────────────────────────────────────

/**
 * A spec record: `<in: Int, out: Int, para>`.
 *
 * The recognized keys have different value shapes (§3.7's table) — `in`/`out`
 * carry a *type*, `aux` a reference, `properties` an expression, and
 * `para`/`histo` are bare flags. An unknown key is still parsed (as an
 * expression value) so it can be reported with its own diagnostic rather than
 * as a parse failure (#99).
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
    /** `aux: #name` — a zygomorphism's auxiliary fold reference (§4.3). */
    | { readonly key: string; readonly kind: "aux"; readonly name: string }
    /** `para` / `histo` — a bare flag. */
    | { readonly key: string; readonly kind: "flag" }

// ── Declarations (§4, §5) ────────────────────────────────────────────────────

/** A program is `declaration*` — there are no expression statements (§4). */
export interface SurfaceProgram {
    readonly declarations: readonly Declaration[]
}

/**
 * A declaration. This PBI implements `data`; the other five forms are #97's and
 * later PBIs' production sets, plugged into this same pipeline.
 */
export type Declaration = DataDecl

/**
 * `data Name <: Parent?` with an indented body (§4.1).
 *
 * The head is a bare `pascalIdent` — never a parameter list (§4.1, §12.29).
 */
export interface DataDecl {
    readonly kind: "data"
    readonly name: string
    readonly parent?: string
    readonly items: readonly DataBodyItem[]
}

/** A `data` body item (§4.1). */
export type DataBodyItem = VariantDecl | FoldDecl | MapDecl

/** `pascalIdent ( ident ":" typeExpr )*` — fields in declaration order (§4.1). */
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
 * `fold name specRecord?` with an indented body (§5.1).
 *
 * `contractClauses` are parsed here because they are `foldItem`s, but their
 * *semantics* — the closed bindable-name set per clause kind and the head arity
 * — belong to #110 and are not elaborated by this PBI.
 */
export interface FoldDecl {
    readonly kind: "foldDecl"
    readonly name: string
    readonly spec?: SpecRecord
    readonly contractClauses: readonly ContractClause[]
    readonly arms: readonly CaseArm[]
}

/**
 * `map name specRecord?` with an indented body (§5.3).
 *
 * A map is **field-keyed**, not variant-keyed: each transform names a *field* and
 * binds its own parameter, so the structure is preserved and only the named
 * fields change. Recursion through `Family`/`Self` fields is automatic, which is
 * what distinguishes a map from a fold — a fold must name every variant and
 * thread the recursion itself, and only a map is eligible for pipeline fusion
 * (`merge`).
 */
export interface MapDecl {
    readonly kind: "mapDecl"
    readonly name: string
    readonly spec?: SpecRecord
    readonly transforms: readonly FieldTransform[]
}

/**
 * One field transform: `field param -> expr`.
 *
 * The same `ident binding "->" expr` shape a fold arm uses, keyed on a field name
 * instead of a variant name. `param` binds the field's current value, so a
 * transform needs no lambda form of its own.
 */
export interface FieldTransform {
    readonly field: string
    readonly param: string
    readonly body: Expr
}

/** `demands: self | expr` — a clause kind, its bindable names, its body (§5.1). */
export interface ContractClause {
    readonly kind: "demands" | "ensures" | "invariant" | "rescue"
    readonly bindings: readonly string[]
    readonly body: Expr
}

/**
 * `armHead -> armBody` (§5.1).
 *
 * The arm head is a variant name followed by bindings for its fields. Bindings
 * beyond the variant's field count bind the fold's `in:` value — the *only*
 * seed-binding mechanism (overview §12.19).
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
