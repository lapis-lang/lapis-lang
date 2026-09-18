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
export {
    SpanClosure,
    TokenVal,
    Value,
    ValueEnv,
    valueEquals,
    valueSize,
    VariantVal,
} from "./values.ts"

// Laws (lc.md §2.4, §7.2 — the equational theory environment E)
export {
    LAW_KINDS,
    type LawDecl,
    LawDeclarationError,
    LawError,
    type LawKind,
    type LawProvenance,
    LawRegistry,
    type LawTypeChecker,
    SCHEMA_ARITY,
    screenableDomain,
    type SubSpaceSpec,
} from "./laws.ts"

// Law checking (semantics.md §5.4 — regime-based: finite → exhaustion →
// discharged; machineFinite → sub-space exhaustion → discharged scoped;
// residual → certified screen → asserted)
export {
    type CertifiedCoverage,
    type CertifiedPosition,
    declareCheckedLaw,
    declareCheckedLawWithRegistry,
    type EvalTerm,
    finiteInhabitants,
    inhabitantsUpToSize,
    installPatternLookup,
    makeEvalTerm,
    type ScreeningRegime,
    screeningRegime,
    screenLaw,
    type ScreenOutcome,
    type SubSpaceSweep,
} from "./law_checking.ts"

// Subtyping (lc.md §4)
export { isSubtype, join, meet, typeEquals } from "./subtyping.ts"

// Operation symbols (lc.md §2.2, §2.4 — Ω environment + named application)
export { OpDeclarationError, OpRegistry, OpSig } from "./ops.ts"

// Grammar — concrete syntax for LC (parse, don't validate)
export { AbstractLC, LC_RESERVED_WORDS, type LCShape, TypeRegistry } from "./grammar.ts"

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
    type Counterexample,
    type CounterexampleOptions,
    type CounterexampleResult,
    findCounterexamples,
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

// Type algebra (type-algebra.md §3+§4 — the contexts and coefficients
// readings of the type equation)
export {
    type Coefficients,
    coefficients,
    type ContextSpec,
    derivative,
    MAX_COEFFICIENT,
    setPatternLookup,
} from "./type_algebra.ts"

// The pattern language (the AST, parser, and language-equation
// counting of pattern constructors; the token universe is ASCII by fiat)
export {
    CHARACTER_UNIVERSE_SIZE,
    enumeratePattern,
    makePatternCountEnv,
    MAX_PATTERN_COUNT,
    parsePattern,
    type PatternAST,
    patternCoefficients,
    type PatternCountEnv,
    patternCounts,
    PatternParseError,
    patternToString,
} from "./pattern_lang.ts"

// Law testing (law-testing.md — the property-based harness with ∂T-based
// structural shrinking; the promotion of the test-local law harness)
export {
    type ContextPath,
    contextPaths,
    DerivativeGenerator,
    type DerivativeGeneratorOptions,
    plug,
    renderValue,
} from "./law_testing.ts"

// Evaluation grammar subclass (lc.md §3 — parse, don't evaluate separately)
// One-pass evaluator: parses LC text and produces values via _forward.
export { EvalErrorValue, LCEval, SpanCodataVal } from "./eval_grammar.ts"
