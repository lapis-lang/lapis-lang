/**
 * The Lapis surface language — public exports.
 *
 * The pipeline is hybrid, and that is deliberate. The core calculus is a
 * *one-pass executable grammar*: a production carries its semantic action, so
 * parsing and checking are the same walk (`LCTypeCheck`, `LCEval`). The surface
 * language needs two things the core does not:
 *
 * - **Whole-program knowledge before elaboration.** A declaration's meaning
 *   depends on every other declaration (which variants exist, which operations
 *   are in scope), and the surface has no declaration ordering rule.
 * - **A representation to elaborate *from*.** The surface cannot be interpreted
 *   in place: its message-chain syntax has no core counterpart, so something has
 *   to hold the parsed form while the target is constructed.
 *
 * So the surface is parse-to-*AST*, then two tree-consuming passes
 * (`resolveProgram`, `elaborateProgram`), and the result is LC source text that
 * the core's own one-pass grammar accepts. The retained `DerivationTree` from
 * `parseToTree` remains available alongside the AST for spans, diagnostics, and
 * unparsing — it is the right vehicle for those, because it preserves exactly
 * where each production matched.
 *
 * ```
 * surface source
 *      │  SurfaceParse              (executable grammar → surface AST)
 *      ├─ resolveProgram            (declaration table, reserved names, names)
 *      ├─ elaborateProgram          (AST → DataType + Ω operations, as LC source)
 *      └─ LCTypeCheck / LCEval      (the core's one-pass grammar)
 * ```
 */

// The AST the passes consume.
export type {
    ArmHead,
    AtomType,
    BinOp,
    Call,
    CaseArm,
    Construction,
    ContractClause,
    DataBodyItem,
    DataDecl,
    Declaration,
    Expr,
    FieldDecl,
    FieldTransform,
    FoldDecl,
    KeyArg,
    Lit,
    MapDecl,
    OpRef,
    Paren,
    Primary,
    Ref,
    SpecEntry,
    SpecRecord,
    SurfaceProgram,
    UnaryOp,
    VariantDecl,
    VariantRef,
} from "./ast.ts"

// The grammar (the AST-producing interpretation).
export { AbstractSurface, SurfaceParse, type SurfaceShape } from "./grammar.ts"

// Lexical productions, exposed for diagnostics and for #34's unparser.
export {
    charLiteral,
    ident,
    isSymbolicOpChar,
    keyword,
    pascalIdent,
    patternLiteral,
    specialValue,
    stringLiteral,
    SURFACE_KEYWORDS,
    symbolicOp,
} from "./lexemes.ts"

// Layout primitives — `surface-grammar.md` §7's L1/L2 rules.
export {
    ARM_BODY_COLUMN,
    ARM_COLUMN,
    comment,
    DECL_BODY_COLUMN,
    hws,
    hws1,
    INDENT_UNIT,
    lineEnd,
    newline,
    spaces,
    trivia,
} from "./layout.ts"

// Name resolution.
export {
    BUILTIN_TYPE_NAMES,
    type DeclarationTable,
    formatResolutionErrors,
    RESERVED_DECLARATION_NAMES,
    type ResolutionError,
    type ResolutionResult,
    type ResolvedData,
    type ResolvedVariant,
    resolveProgram,
} from "./resolve.ts"

// Elaboration to the core.
export { type ElaboratedOperation, elaborateProgram, type ElaborationResult } from "./elaborate.ts"
