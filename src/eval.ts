/**
 * LC Evaluation — the evaluation rules of the Lapis Core Calculus.
 *
 * See _docs/theory/lc.md §3 for the formal specification.
 *
 *   E-App:       (λx:σ. t) v → [x ↦ v] t
 *   E-Fold:      fold [T] (Cₖ(vⱼ)) {Cᵢ(xⱼ) → tᵢ} → [xⱼ ↦ vⱼ'] tₖ
 *   E-FoldMatch: fold [T] (match(pₖ)) {pᵢ → tᵢ} → [match ↦ tok] tₖ
 *   E-Obs:       (unfold [T] s {oⱼ → gⱼ}).oₖ → gₖ(s)
 *   E-Cofold:    cofold [T] (unfold [T] s {oⱼ → gⱼ}) {oⱼ(xⱼ) → t} → [xⱼ ↦ gⱼ(s)] t
 *   E-Let:       let x:σ = v in u → [x ↦ v] u
 *   E-TApp:      (Λα <: σ. t) [τ] → [α ↦ τ] t
 *
 * Evaluation is eager for data (μ), lazy for codata (ν).
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

import {
    type Value,
    Closure,
    VariantVal,
    MatchVal,
    CodataVal,
    ValueEnv,
} from "./values.ts";

import { type Type, DataType, CodataType } from "./types.ts";

// ── Evaluation error ──────────────────────────────────────────────────────────

/** Thrown when evaluation gets stuck (a well-typed term should never get stuck). */
export class EvalError extends Error {
    override readonly name = "EvalError";
    constructor(message: string) {
        super(message);
    }
}

// ── The evaluator ─────────────────────────────────────────────────────────────

/**
 * The LC evaluator. Evaluates a term to a value under environment ρ.
 *
 * Eager for data (μ): variant fields are evaluated to values at construction.
 * Lazy for codata (ν): unfold stores the seed, generators are deferred.
 */
export class Evaluator {
    /**
     * Evaluate a term to a value under environment ρ.
     * Throws EvalError if the term gets stuck (should not happen for well-typed terms).
     */
    eval(term: Term, rho: ValueEnv): Value {
        switch (term.kind) {
            case "var":
                return this.evalVar(term as Var, rho);
            case "lam":
                return this.evalLam(term as Lam, rho);
            case "app":
                return this.evalApp(term as App, rho);
            case "variantCon":
                return this.evalVariantCon(term as VariantCon, rho);
            case "patternMatch":
                return this.evalPatternMatch(term as PatternMatch, rho);
            case "fold":
                return this.evalFold(term as Fold, rho);
            case "patternFold":
                return this.evalPatternFold(term as PatternFold, rho);
            case "obs":
                return this.evalObs(term as Obs, rho);
            case "unfold":
                return this.evalUnfold(term as Unfold, rho);
            case "cofold":
                return this.evalCofold(term as Cofold, rho);
            case "typeAbs":
                return this.evalTypeAbs(term as TypeAbs, rho);
            case "typeApp":
                return this.evalTypeApp(term as TypeApp, rho);
            case "let":
                return this.evalLet(term as Let, rho);
            default:
                throw new EvalError(`unknown term kind: ${(term as Term).kind}`);
        }
    }

    // ── E-Var: look up in ρ ───────────────────────────────────────────────────

    protected evalVar(term: Var, rho: ValueEnv): Value {
        const val = rho.lookup(term.name);
        if (val === undefined) {
            throw new EvalError(`unbound variable: ${term.name}`);
        }
        return val;
    }

    // ── E-Lam: create closure ─────────────────────────────────────────────────

    protected evalLam(term: Lam, rho: ValueEnv): Value {
        return new Closure(
            term.param,
            term.paramType,
            term.body,
            rho.toMap(),
        );
    }

    // ── E-App: (λx:σ. t) v → [x ↦ v] t ────────────────────────────────────────

    protected evalApp(term: App, rho: ValueEnv): Value {
        const fn = this.eval(term.fn, rho);
        const arg = this.eval(term.arg, rho);

        if (!(fn instanceof Closure)) {
            throw new EvalError("cannot apply non-function");
        }

        // E-App: substitute the argument into the body
        const bodyEnv = ValueEnv.from(fn.env).extend(fn.param, arg);
        return this.eval(fn.body, bodyEnv);
    }

    // ── E-VariantCon: eager construction ──────────────────────────────────────

    protected evalVariantCon(term: VariantCon, rho: ValueEnv): Value {
        // Eager: evaluate all fields to values
        const fields = new Map<string, Value>();
        const variant = term.dataType.findVariant(term.variantName);
        if (!variant) {
            throw new EvalError(`unknown variant: ${term.variantName}`);
        }

        for (let i = 0; i < term.args.length; i++) {
            const field = variant.fields[i];
            const arg = term.args[i]!;
            if (field) {
                fields.set(field.name, this.eval(arg, rho));
            }
        }

        return new VariantVal(term.variantName, term.dataType, fields);
    }

    // ── E-PatternMatch: already a value ───────────────────────────────────────

    protected evalPatternMatch(term: PatternMatch, _rho: ValueEnv): Value {
        return new MatchVal(term.patternIndex, term.dataType, term.token);
    }

    // ── E-Fold: fold [T] (Cₖ(vⱼ)) {Cᵢ(xⱼ) → tᵢ} → [xⱼ ↦ vⱼ'] tₖ ────────────────

    protected evalFold(term: Fold, rho: ValueEnv): Value {
        const scrutinee = this.eval(term.scrutinee, rho);

        if (!(scrutinee instanceof VariantVal)) {
            throw new EvalError("fold scrutinee is not a variant value");
        }

        const handler = term.findHandler(scrutinee.variantName);
        if (!handler) {
            throw new EvalError(`no handler for variant: ${scrutinee.variantName}`);
        }

        // Build the handler environment: bind field names to values
        // For recursive fields, the value is already evaluated (eager data)
        // and is passed as-is (it's already a VariantVal, which is the folded result
        // at this stage — in a proper fold, recursive fields would be folded first,
        // but since we evaluate eagerly, the value is already there).
        let handlerEnv = rho;
        const variant = term.dataType.findVariant(scrutinee.variantName);
        if (variant) {
            for (let i = 0; i < variant.fields.length; i++) {
                const field = variant.fields[i]!;
                const binding = handler.fieldBindings[i];
                if (binding) {
                    const fieldValue = scrutinee.fields.get(field.name);
                    if (fieldValue !== undefined) {
                        handlerEnv = handlerEnv.extend(binding, fieldValue);
                    }
                }
            }
        }

        return this.eval(handler.body, handlerEnv);
    }

    // ── E-FoldMatch: fold [T] (match(pₖ)) {pᵢ → tᵢ} → [match ↦ tok] tₖ ──────────

    protected evalPatternFold(term: PatternFold, rho: ValueEnv): Value {
        const scrutinee = this.eval(term.scrutinee, rho);

        if (!(scrutinee instanceof MatchVal)) {
            throw new EvalError("pattern fold scrutinee is not a match value");
        }

        const handler = term.handlers.find((h) => h.patternIndex === scrutinee.patternIndex);
        if (!handler) {
            throw new EvalError(`no handler for pattern: ${scrutinee.patternIndex}`);
        }

        // Bind `match` to the token
        const handlerEnv = rho.extend("match", scrutinee);
        return this.eval(handler.body, handlerEnv);
    }

    // ── E-Obs: (unfold [T] s {oⱼ → gⱼ}).oₖ → gₖ(s) ────────────────────────────

    protected evalObs(term: Obs, rho: ValueEnv): Value {
        const scrutinee = this.eval(term.scrutinee, rho);

        if (!(scrutinee instanceof CodataVal)) {
            throw new EvalError("observation scrutinee is not a codata value");
        }

        const generator = scrutinee.generators.find((g) => g.observerName === term.observerName);
        if (!generator) {
            throw new EvalError(`no generator for observer: ${term.observerName}`);
        }

        // E-Obs: run the generator with the seed
        const genEnv = ValueEnv.from(scrutinee.env).extend("self", scrutinee.seed);
        return this.eval(generator.body, genEnv);
    }

    // ── E-Unfold: lazy codata value ───────────────────────────────────────────

    protected evalUnfold(term: Unfold, rho: ValueEnv): Value {
        // Lazy: store the seed (evaluated) and generators (deferred)
        const seed = this.eval(term.seed, rho);
        return new CodataVal(
            term.codataType,
            seed,
            term.generators,
            rho.toMap(),
        );
    }

    // ── E-Cofold: cofold [T] (unfold [T] s {oⱼ → gⱼ}) {oⱼ(xⱼ) → t} → [xⱼ ↦ gⱼ(s)] t ─

    protected evalCofold(term: Cofold, rho: ValueEnv): Value {
        const scrutinee = this.eval(term.scrutinee, rho);

        if (!(scrutinee instanceof CodataVal)) {
            throw new EvalError("cofold scrutinee is not a codata value");
        }

        // Run all generators to get observation values
        const allObservers = term.codataType.allObservers();
        let handlerEnv = rho;

        for (let i = 0; i < allObservers.length; i++) {
            const observer = allObservers[i]!;
            const binding = term.handler.fieldBindings[i];
            if (!binding) {
                throw new EvalError(`missing binding for observer: ${observer.name}`);
            }

            const generator = scrutinee.generators.find((g) => g.observerName === observer.name);
            if (!generator) {
                throw new EvalError(`no generator for observer: ${observer.name}`);
            }

            const genEnv = ValueEnv.from(scrutinee.env).extend("self", scrutinee.seed);
            const obsValue = this.eval(generator.body, genEnv);
            handlerEnv = handlerEnv.extend(binding, obsValue);
        }

        return this.eval(term.handler.body, handlerEnv);
    }

    // ── E-TAbs: type abstraction is a value (no evaluation needed) ─────────────

    protected evalTypeAbs(term: TypeAbs, rho: ValueEnv): Value {
        // Type abstractions are polymorphic values — for now, evaluate the body
        // as a closure-like value. A proper implementation would defer evaluation
        // until type application. Simplified for now.
        return new Closure(
            term.typeVarName,
            term.bound,
            term.body,
            rho.toMap(),
        );
    }

    // ── E-TApp: (Λα <: σ. t) [τ] → [α ↦ τ] t ──────────────────────────────────

    protected evalTypeApp(term: TypeApp, rho: ValueEnv): Value {
        // Simplified: evaluate the body directly (type erasure)
        return this.eval(term.body, rho);
    }

    // ── E-Let: let x:σ = v in u → [x ↦ v] u ───────────────────────────────────

    protected evalLet(term: Let, rho: ValueEnv): Value {
        const value = this.eval(term.value, rho);
        const bodyEnv = rho.extend(term.name, value);
        return this.eval(term.body, bodyEnv);
    }
}