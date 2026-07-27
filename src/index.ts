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

// Typing (lc.md §5)
export { TypeChecker, TypeError_, substituteType } from "./typing.ts";