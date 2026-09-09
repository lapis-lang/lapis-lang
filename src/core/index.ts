/**
 * Lapis Core Calculus (F_{<:μν}) — public exports.
 *
 * See _docs/theory/lc.md for the formal specification.
 */

// Types (lc.md §2.1)
export {
    Any,
    AnyType,
    CodataType,
    DataType,
    Field,
    FunType,
    IntersectionType,
    Nothing,
    NothingType,
    Observer,
    PatternDataType,
    PolymorphicType,
    Token,
    TokenType,
    Type,
    TypeEnv,
    TypeVar,
    TypeVarEnv,
    Variant,
} from "./types.ts"

// Values (lc.md §2.3)
export { SpanClosure, Value, ValueEnv, VariantVal } from "./values.ts"

// Subtyping (lc.md §4)
export { isSubtype, join, meet, typeEquals } from "./subtyping.ts"

// Grammar — concrete syntax for LC (parse, don't validate)
export { AbstractLC, type LCShape, TypeRegistry } from "./grammar.ts"

// Derivation trees + semantic passes
export { DerivationNode, DerivationTree, SemanticPass } from "@lapis-lang/lang-forma"

// First-class inference rules + metatheory verification
// (lc.md §3+§5 — collected from @requires/@ensures metadata; Progress + Preservation via lang-forma)
export {
    checkPreservation,
    checkProgress,
    type ClassifiedRule,
    classifyRule,
    classifyRules,
    collectRules,
    formatRule,
    type FormattedInferenceRule,
    type InferenceRule,
    type MetatheoryReport,
    type PreservationCheck,
    type PreservationResult,
    type ProgressGap,
    type ProgressResult,
    type RuleClause,
    type RuleKind,
    type RuleRole,
    verifyMetatheory,
} from "@lapis-lang/lang-forma"

// Type-checking grammar subclass (lc.md §5 — parse, don't validate)
// One-pass type checker: parses LC text and produces types.
// Inference rules: `LCTypeCheck.rules` (static) or `collectRules(LCTypeCheck)`.
export { LCTypeCheck } from "./typing_grammar.ts"

// Evaluation grammar subclass (lc.md §3 — parse, don't evaluate separately)
// One-pass evaluator: parses LC text and produces values via _forward.
export { EvalErrorValue, LCEval, SpanCodataVal } from "./eval_grammar.ts"
