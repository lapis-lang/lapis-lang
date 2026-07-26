export { LapisParser } from './grammar.ts';
export type { LapisShape } from './grammar.ts';
export {
    Node,
    // Literals
    IntLit,
    StringLit,
    SymbolLit,
    // References
    Ident,
    VariantRef,
    SelfRef,
    FamilyRef,
    CoSelfRef,
    OldRef,
    PrevRef,
    AuxRef,
    // Composite expressions
    Block,
    Record,
    RecordEntry,
    ArrayLit,
    // Operations
    BinarySend,
    UnarySend,
    KeywordSend,
    PrefixSend,
    // Spec
    Spec,
    SpecEntry,
    // Contract
    ContractClause,
    // Field & variant
    Field,
    Variant,
    CaseArm,
    Satisfies,
    // Sub-declarations
    FoldDecl,
    UnfoldDecl,
    MapDecl,
    MergeDecl,
    // Top-level declarations
    DataDecl,
    BehaviorDecl,
    ProtocolDecl,
    RelationDecl,
    QueryDecl,
    IoDecl,
    // Module
    Module,
} from './ast.ts';
export type {
    ContractKind,
    DataBodyItem,
    BehaviorBodyItem,
    ProtocolBodyItem,
    TopLevelDecl,
} from './ast.ts';

// ── Semantic types ────────────────────────────────────────────────────────────
// The type system for the Lapis Core (LC). See _docs/core-calculus.md and
// src/types.ts for the full documentation.

export {
    // Type classes
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
    // Typed AST
    TypedExpr,
    // Environments
    TypeEnv,
    NameEnv,
    // Convenience constructors
    Any,
    Nothing,
    Int,
    String_ as StringType,
    Bool,
    Number_ as NumberType,
    Object_ as ObjectType,
    Array_ as ArrayType,
} from './types.ts';

// ── Name resolution ───────────────────────────────────────────────────────────
// The first semantic layer: resolves names in the AST. See src/nameresolver.ts.

export {
    resolveModule,
    NameResolutionError,
    ResolvedIdent,
    ResolvedVariantRef,
} from './nameresolver.ts';

// ── Type checking ────────────────────────────────────────────────────────────
// The second semantic layer: type-checks the resolved AST. See src/typechecker.ts.

export {
    typeCheckModule,
    TypeError_ as LapisTypeError,
} from './typechecker.ts';
