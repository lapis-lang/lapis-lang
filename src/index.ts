/**
 * Lapis Core Calculus (F_{<:μν}) — public exports.
 *
 * See _docs/theory/lc.md for the formal specification.
 */

// Types (lc.md §2.1)
export {
    Type,
    TypeVar,
    FunType,
    DataType,
    Variant,
    Field,
    PatternDataType,
    CodataType,
    Observer,
    TokenType,
    AnyType,
    NothingType,
    IntersectionType,
    TypeVarEnv,
    TypeEnv,
    Token,
    Any,
    Nothing,
} from "./types.ts";

// Terms (lc.md §2.2)
export {
    Term,
    Var,
    Lam,
    App,
    VariantCon,
    PatternMatch,
    FoldHandler,
    PatternHandler,
    Fold,
    PatternFold,
    Obs,
    UnfoldGenerator,
    Unfold,
    CofoldHandler,
    Cofold,
    TypeAbs,
    TypeApp,
    Let,
} from "./terms.ts";

// Values (lc.md §2.3)
export {
    Value,
    Closure,
    VariantVal,
    MatchVal,
    CodataVal,
    ValueEnv,
    isValue,
    isFullyEvaluated,
} from "./values.ts";

// Subtyping (lc.md §4)
export { isSubtype, typeEquals } from "./subtyping.ts";

// Grammar — concrete syntax for LC (parse, don't validate)
export {
    AbstractLC,
    LCAST,
    TypeRegistry,
    type LCShape,
} from "./grammar.ts";

// Type-checking grammar subclass (lc.md §5 — parse, don't validate)
export { LCTypeCheck } from "./typing_grammar.ts";

// Typing (lc.md §5) — tree-walking (to be replaced by grammar subclass)
export { TypeChecker, TypeError_, substituteType } from "./typing.ts";

// Evaluation (lc.md §3) — tree-walking (to be replaced by grammar subclass)
export { Evaluator, EvalError } from "./eval.ts";

// Soundness (lc.md §6) — to be replaced by @ensures contracts
export {
    canStep,
    checkProgress,
    checkSoundness,
    type SoundnessResult,
} from "./soundness.ts";