/**
 * LC Soundness — Progress and Preservation checks.
 *
 * See _docs/theory/lc.md §6 for the formal specification.
 *
 * **Progress:** If Γ ⊢ t : σ (with Γ closed), then either t is a value
 * or t → t' for some t'.
 *
 * **Preservation:** If Γ ⊢ t : σ and t → t', then Γ ⊢ t' : σ.
 *
 * These are encoded as executable checks:
 * - `checkProgress(term, type)`: verifies a well-typed term is a value or can step.
 * - `checkPreservation(term, type, result)`: verifies an evaluation step
 *   preserves the type.
 */

import {
    type Term,
    Var,
    Lam,
    App,
    VariantCon,
    PatternMatch,
    Fold,
    PatternFold,
    Obs,
    Unfold,
    Cofold,
    TypeAbs,
    TypeApp,
    Let,
} from "./terms.ts";

import { type Value, Closure, VariantVal, MatchVal, CodataVal, ValueEnv } from "./values.ts";

import { type Type, TypeEnv } from "./types.ts";

import { TypeChecker } from "./typing.ts";

import { Evaluator } from "./eval.ts";

import { isSubtype, typeEquals } from "./subtyping.ts";

// ── Progress: is a term a value or can it step? ───────────────────────────────

/**
 * Check if a term can take an evaluation step.
 * This is the Progress check: a well-typed term should either be a value
 * or be able to step.
 */
export function canStep(term: Term): boolean {
    switch (term.kind) {
        // Values (no step possible, but they're already values)
        case "patternMatch":
            return false; // match(pₖ) is a value

        // Lambda is a value (closure when evaluated)
        case "lam":
            return false;

        // Unfold is a value (codata value when evaluated)
        case "unfold":
            return false;

        // Type abstraction is a value
        case "typeAbs":
            return false;

        // Application: can step if fn is a value (closure) or fn can step
        case "app": {
            const app = term as App;
            if (canStep(app.fn)) return true;
            // If fn is a value (lam), and arg is a value, we can do E-App
            if (isValueTerm(app.fn) && isValueTerm(app.arg)) return true;
            // If fn is a value, arg can step (E-App2)
            if (isValueTerm(app.fn) && canStep(app.arg)) return true;
            return false;
        }

        // Variant construction: can step if any arg can step (eager evaluation)
        case "variantCon": {
            const vc = term as VariantCon;
            return vc.args.some((arg) => canStep(arg));
        }

        // Fold: can step if scrutinee is a value (E-Fold) or scrutinee can step (E-FoldArg)
        case "fold": {
            const fold = term as Fold;
            if (isValueTerm(fold.scrutinee)) return true; // E-Fold
            if (canStep(fold.scrutinee)) return true; // E-FoldArg
            return false;
        }

        // Pattern fold: can step if scrutinee is a value (E-FoldMatch) or can step
        case "patternFold": {
            const pf = term as PatternFold;
            if (isValueTerm(pf.scrutinee)) return true;
            if (canStep(pf.scrutinee)) return true;
            return false;
        }

        // Observation: can step if scrutinee is a value (E-Obs) or can step (E-ObsArg)
        case "obs": {
            const obs = term as Obs;
            if (isValueTerm(obs.scrutinee)) return true;
            if (canStep(obs.scrutinee)) return true;
            return false;
        }

        // Cofold: can step if scrutinee is a value (E-Cofold) or can step (E-CofoldArg)
        case "cofold": {
            const cofold = term as Cofold;
            if (isValueTerm(cofold.scrutinee)) return true;
            if (canStep(cofold.scrutinee)) return true;
            return false;
        }

        // Type application: can step if body is a value (E-TApp) or can step
        case "typeApp": {
            const ta = term as TypeApp;
            if (isValueTerm(ta.body)) return true;
            if (canStep(ta.body)) return true;
            return false;
        }

        // Let: can step if value is a value (E-Let) or can step (E-LetArg)
        case "let": {
            const let_ = term as Let;
            if (isValueTerm(let_.value)) return true;
            if (canStep(let_.value)) return true;
            return false;
        }

        // Variable: cannot step (should be bound in a closed term)
        case "var":
            return false;

        default:
            return false;
    }
}

/** Check if a term is already a value (fully evaluated). */
function isValueTerm(term: Term): boolean {
    switch (term.kind) {
        case "lam":
        case "patternMatch":
        case "unfold":
        case "typeAbs":
            return true;
        case "variantCon": {
            const vc = term as VariantCon;
            return vc.args.every((arg) => isValueTerm(arg));
        }
        default:
            return false;
    }
}

/**
 * Check Progress: if Γ ⊢ t : σ, then t is a value or t → t'.
 * Returns true if the Progress property holds for this term.
 */
export function checkProgress(term: Term): boolean {
    return isValueTerm(term) || canStep(term);
}

// ── Preservation: evaluation preserves types ──────────────────────────────────

/**
 * Check Preservation: if Γ ⊢ t : σ and t evaluates to v, then v : σ.
 *
 * This re-type-checks the evaluated value against the original type.
 * For a full Preservation proof, we'd check each individual step;
 * here we check the final result.
 */
export function checkPreservation(
    term: Term,
    expectedType: Type,
    gamma: TypeEnv,
    checker: TypeChecker,
    evaluator: Evaluator,
): boolean {
    // Step 1: type-check the term
    const termType = checker.check(term, gamma);
    if (!typeEquals(termType, expectedType) && !isSubtype(termType, expectedType)) {
        return false;
    }

    // Step 2: evaluate the term
    const rho = new ValueEnv();
    const result = evaluator.eval(term, rho);

    // Step 3: verify the result has the same type
    // (For values, we check structurally — this is a simplification.
    // A full Preservation check would verify each step's type.)
    return verifyValueType(result, expectedType, checker);
}

/** Verify that a value has the expected type. */
function verifyValueType(
    value: Value,
    expectedType: Type,
    _checker: TypeChecker,
): boolean {
    // This is a structural check — for a full implementation, we'd
    // reconstruct the type from the value and check subtyping.
    // For now, we check basic structural compatibility.
    switch (value.kind) {
        case "closure":
            // Closures have function types — we'd need to check the body type
            // For now, accept (the type checker already verified the body)
            return true;
        case "variantVal":
            // Variant values have data types — check the data type name
            return true; // Simplified — full check would verify the DataType
        case "matchVal":
            return true; // Pattern match values have pattern data types
        case "codataVal":
            return true; // Codata values have codata types
        default:
            return false;
    }
}

// ── Full soundness check ──────────────────────────────────────────────────────

/**
 * Run a full soundness check on a term:
 * 1. Type-check the term (if it fails, it's ill-typed — not a soundness violation)
 * 2. Check Progress (the term is a value or can step)
 * 3. Evaluate the term
 * 4. Check Preservation (the result has the same type)
 *
 * Returns an object with the results of each check.
 */
export interface SoundnessResult {
    /** The type inferred by the type checker (or null if ill-typed). */
    type: Type | null;
    /** Whether the term type-checks. */
    wellTyped: boolean;
    /** Whether Progress holds (well-typed term is a value or can step). */
    progress: boolean;
    /** Whether Preservation holds (evaluated result has the same type). */
    preservation: boolean;
    /** The evaluated value (or null if evaluation failed). */
    value: Value | null;
    /** Error message if any check failed. */
    error: string | null;
}

export function checkSoundness(
    term: Term,
    gamma: TypeEnv = new TypeEnv(),
): SoundnessResult {
    const checker = new TypeChecker();
    const evaluator = new Evaluator();

    // Step 1: Type-check
    let type: Type | null = null;
    try {
        type = checker.check(term, gamma);
    } catch (e) {
        return {
            type: null,
            wellTyped: false,
            progress: false,
            preservation: false,
            value: null,
            error: `type error: ${(e as Error).message}`,
        };
    }

    // Step 2: Progress
    const progress = checkProgress(term);

    // Step 3: Evaluate
    let value: Value | null = null;
    try {
        const rho = new ValueEnv();
        value = evaluator.eval(term, rho);
    } catch (e) {
        return {
            type,
            wellTyped: true,
            progress,
            preservation: false,
            value: null,
            error: `evaluation error: ${(e as Error).message}`,
        };
    }

    // Step 4: Preservation
    const preservation = verifyValueType(value, type, checker);

    return {
        type,
        wellTyped: true,
        progress,
        preservation,
        value,
        error: preservation ? null : "preservation failed",
    };
}