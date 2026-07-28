/**
 * LC Evaluation — a grammar subclass that evaluates LC terms during parsing.
 *
 * Following the grammar-as-semantics pattern (like STLCEval in zipper-grammar):
 * the evaluation judgment `ρ ⊢ t ⇓ v` becomes a parameterised production
 * `exprProd(ρ): Parser<Value>`. `chain` threads the environment through
 * sub-productions. `_forward` re-evaluates closure bodies under extended
 * environments — the higher-order attribute mechanism.
 *
 * Evaluation rules (lc.md §3):
 *
 *   E-App:       (λx:σ. t) v → [x ↦ v] t
 *   E-Let:       let x:σ = v in u → [x ↦ v] u
 *   E-Fold:      fold [T] (Cₖ(vⱼ)) {Cᵢ(xⱼ) → tᵢ} → [xⱼ ↦ vⱼ'] tₖ
 *   E-Obs:       (unfold [T] s {oⱼ → gⱼ}).oₖ → gₖ(s)
 *   E-Cofold:    cofold [T] (unfold [T] s {oⱼ → gⱼ}) {oⱼ(xⱼ) → t} → [xⱼ ↦ gⱼ(s)] t
 *   E-TApp:      (Λα <: σ. t) [τ] → [α ↦ τ] t  (type erasure)
 *
 * Higher-order attributes via _forward:
 *   E-App:    re-parses closure body under ρ[x := v]
 *   E-Fold:   re-parses matching handler body under ρ[xⱼ := vⱼ]
 *   E-Obs:    re-parses generator body under ρ[self := seed]
 *   E-Cofold: re-parses all generators, then handler body under ρ[xⱼ := gⱼ(s)]
 *
 * E-Let is same-pass (no _forward): def's value is available from chain,
 * so body is parsed under ρ[x := def] directly.
 *
 * See _docs/theory/lc.md §3 for the formal specification.
 * See _docs/theory/grammar-as-semantics.md for the architecture.
 */

import {
    assert,
    char,
    empty,
    epsilon,
    invariant,
    or,
    type Parser,
    rule,
    sepBy,
    seq,
    type Span,
} from "@lapis-lang/zipper-grammar"

import { Any, CodataType, DataType, type Type } from "./types.ts"

import { AbstractLC, type LCShape } from "./grammar.ts"

import { SpanClosure, Value, ValueEnv, VariantVal } from "./values.ts"

// ── Shape for evaluation ──────────────────────────────────────────────────────

interface EvalShape extends LCShape {
    expr: Value
    atom: Value
    type: Type
}

// ── Sentinel values ───────────────────────────────────────────────────────────

/**
 * Placeholder value used when parsing a lambda/fold/unfold body for span
 * capture. The body is parsed under an env where the parameter is bound to
 * this sentinel, so `varRef` succeeds (the value is never used — only the
 * span is kept). Must be non-null because `ValueEnv.lookup` returns
 * `undefined` for unbound names.
 */
class PlaceholderValue extends Value {
    readonly kind = "__placeholder__"
}
const PLACEHOLDER: Value = new PlaceholderValue()

/**
 * Error sentinel returned when evaluation fails (unknown variant, unbound
 * variable, type mismatch, etc.). This is a proper Value subclass so it can
 * be distinguished from real values via `instanceof EvalErrorValue`.
 */
export class EvalErrorValue extends Value {
    readonly kind = "__eval_error__"
    constructor(readonly message: string) {
        super()
    }
}
const EVAL_ERROR = (msg: string) => new EvalErrorValue(msg)

// ── Span-carrying handler/generator info ──────────────────────────────────────

/** A fold handler with span-captured body (for deferred evaluation). */
interface SpanHandler {
    variantName: string
    bindings: string[]
    bodySpan: Span
}

/** An unfold generator with span-captured body (for deferred evaluation). */
interface SpanGenerator {
    observerName: string
    bodySpan: Span
}

// ── SpanCodataVal — codata value with span-captured generators ────────────────

/**
 * A codata value that stores generator body spans (not pre-evaluated bodies).
 * When an observer is called, the generator body is re-evaluated via `_forward`.
 */
export class SpanCodataVal extends Value {
    readonly kind = "codataVal"
    constructor(
        readonly codataType: CodataType,
        readonly seed: Value,
        readonly generators: SpanGenerator[],
        readonly env: ValueEnv,
    ) {
        super()
    }
}

// ── The evaluation grammar ────────────────────────────────────────────────────

/**
 * One-pass evaluator. Parses LC text and produces values.
 *
 *   parseWith("\\x:Any. x", ValueEnv.empty()) → Set { SpanClosure("x", ...) }
 *
 * Evaluation rules encoded as production overrides:
 *
 *   E-Var:  ρ(x) = v  ⟹  ρ ⊢ x ⇓ v
 *   E-Lam:  ρ ⊢ λx:σ.t ⇓ ⟨x, σ, span, ρ⟩  (closure capturing env + body span)
 *   E-App:  ρ ⊢ t ⇓ ⟨x,σ,span,ρ₁⟩ ∧ ρ ⊢ u ⇓ v ⟹ ρ ⊢ t u ⇓ ρ₁[x↦v] ⊢ body ⇓ w
 *   E-Let:  ρ ⊢ t ⇓ v ∧ ρ[x↦v] ⊢ u ⇓ w  ⟹  ρ ⊢ let x:σ=t in u ⇓ w
 *   E-Fold:  fold [T] (Cₖ(vⱼ)) {Cᵢ(xⱼ) → tᵢ} → [xⱼ ↦ vⱼ] tₖ  (via _forward)
 *   E-Obs:   (unfold [T] s {oⱼ → gⱼ}).oₖ → gₖ(s)  (via _forward)
 *   E-Unfold: unfold [T] s {oⱼ → gⱼ} ⇓ codata value (lazy: spans stored)
 *
 * For E-App, E-Fold, and E-Obs, the body is re-evaluated via `_forward` under
 * the extended environment.
 */
@invariant((self: LCEval) => self.start() !== undefined)
export class LCEval extends AbstractLC<EvalShape> {
    /** The source text, stored so semantic actions can re-parse substrings. */
    private _input: string = ""

    /**
     * Base offset of the current parse relative to `_input`. The outer parse
     * starts at 0; a nested `_forward` re-parse of a substring starting at
     * offset `S` sets this to `S`, so spans captured inside the re-parse are
     * absolute (relative to the original `_input`), not relative to the
     * substring. This lets closures captured during a re-parse be applied
     * later against the original input.
     */
    private _inputOffset: number = 0

    /**
     * Parse and evaluate input under `rho`.
     * Returns the set of possible values (usually one; empty = eval error).
     */
    parseWith(input: string, rho: ValueEnv): Set<Value> {
        this._input = input
        this._inputOffset = 0
        return this._parseWith(input, this.exprProd(rho))
    }

    override start(): Parser<Value> {
        return this.exprProd(new ValueEnv())
    }

    // ── Context extension: extend ρ with x ↦ PLACEHOLDER ──────────────────────

    protected override extendCtx(ctx: unknown, name: string, _type: Type): unknown {
        if (ctx instanceof ValueEnv) {
            return ctx.extend(name, PLACEHOLDER)
        }
        return ctx
    }

    // ── Semantic actions (used by base productions for atoms) ────────────────

    protected varRef(name: string, ctx: unknown): Value {
        if (ctx instanceof ValueEnv) {
            const val = ctx.lookup(name)
            if (val === undefined) {
                return EVAL_ERROR(`unbound variable: ${name}`)
            }
            return val
        }
        return EVAL_ERROR(`varRef: ctx is not a ValueEnv`)
    }

    protected paren(e: Value): Value {
        return e
    }

    protected variantCon(name: string, args: Value[]): Value {
        const dataType = this.registry.lookupVariant(name)
        if (!dataType) return EVAL_ERROR(`unknown variant: ${name}`)
        const variant = dataType.findVariant(name)
        if (!variant) return EVAL_ERROR(`variant ${name} not found in ${dataType.name}`)

        const fields = new Map<string, Value>()
        for (let i = 0; i < args.length; i++) {
            const field = variant.fields[i]
            if (field) {
                fields.set(field.name, args[i]!)
            }
        }
        return new VariantVal(name, dataType, fields)
    }

    // ── E-Lam: override lambdaProd to capture body span ──────────────────────

    /**
     * Override `lambdaProd` to capture the body's input span in a `SpanClosure`
     * instead of evaluating the body. The body is parsed under a placeholder
     * env (so `x` is bound and the parse succeeds), but only the **span** is
     * kept — the body's value is discarded. The real evaluation happens when
     * the closure is applied (`appProd` re-parses the substring via `_forward`).
     */
    // λx:σ. t  — E-Lam (captures body span for _forward)
    @rule
    protected override lambdaProd(ctx: unknown): Parser<Value> {
        return seq(
            this.lambdaHead,
            this.ident,
            this.ws,
            char(":"),
            this.ws,
            this.typeProd,
            this.ws,
            char("."),
            this.ws,
        ).chain(([, param, , , , ty]) => {
            assert(typeof param === "string", "lambda param must be a string")
            assert(ty !== undefined, "lambda type must be defined")
            const placeholderCtx = this.extendCtx(ctx, param, ty)
            return this.exprProd(placeholderCtx)
                .map((_body, span) =>
                    new SpanClosure(
                        param,
                        ty,
                        {
                            start: span.start + this._inputOffset,
                            end: span.end + this._inputOffset,
                        },
                        ctx as ValueEnv,
                    )
                )
        }).map(([, result]) => result)
    }

    // ── E-App: override appProd for evaluation via chain + _forward ───────────

    /**
     * Override application to evaluate via chain:
     * parse fn → get fnVal; parse arg → get argVal;
     * if fnVal is a SpanClosure, re-evaluate body via `_forward` under
     * extended env; else empty (eval error).
     */
    // t u  — E-App via chain + _forward
    @rule
    protected override appProd(ctx: unknown): Parser<Value> {
        return or(
            this.appProd(ctx)
                .map((fnVal) => ({ fnVal }))
                .chain(({ fnVal }) =>
                    seq(this.ws1, this.typeAppProd(ctx))
                        .map(([, argVal]) => ({ fnVal, argVal }))
                        .chain(({ fnVal, argVal }) => {
                            if (!(fnVal instanceof SpanClosure)) {
                                return empty() as unknown as Parser<Value>
                            }
                            const bodyEnv = fnVal.env.extend(fnVal.param, argVal)
                            const savedOffset = this._inputOffset
                            this._inputOffset = fnVal.bodySpan.start
                            try {
                                const results = [...this._forward(
                                    this._input,
                                    fnVal.bodySpan,
                                    this.exprProd(bodyEnv),
                                )]
                                if (results.length === 0) {
                                    return empty() as unknown as Parser<Value>
                                }
                                return epsilon<Value>(results[0]!)
                            } finally {
                                this._inputOffset = savedOffset
                            }
                        })
                        .map(([, result]) => result)
                )
                .map(([, result]) => result),
            this.typeAppProd(ctx) as unknown as Parser<Value>,
        )
    }

    // ── E-Let: override letProd for same-pass evaluation ──────────────────────

    /**
     * Override `letProd` to parse the body under the real env (extended with
     * def's value). Unlike `lambdaProd`, the body is evaluated in the same
     * pass — `def`'s value is available from the `chain`, so the body parser
     * runs under `ρ[name:=def]` directly. No span capture or `_forward` needed.
     */
    // let x:σ = t in u  — E-Let (same-pass evaluation)
    @rule
    protected override letProd(ctx: unknown): Parser<Value> {
        return seq(
            this.kw("let"),
            this.ws1,
            this.ident,
            this.ws,
            char(":"),
            this.ws,
            this.typeProd,
            this.ws,
            char("="),
            this.ws,
        ).chain(([, , name]) =>
            this.exprProd(ctx)
                .map((def) => ({ name, def }))
                .chain(({ name, def }) =>
                    seq(this.ws1, this.kw("in"), this.ws1)
                        .chain(() => {
                            const bodyCtx = (ctx as ValueEnv).extend(name, def)
                            return this.exprProd(bodyCtx)
                                .map((body) => body)
                        })
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        ).map(([, result]) => result)
    }

    // ── E-Fold: override foldProd for span capture + _forward ─────────────────

    /**
     * Override `foldProd` to capture handler body spans. When the fold is
     * evaluated, the scrutinee is already a value. We find the matching
     * handler, bind field values to handler bindings, and re-evaluate the
     * handler body via `_forward` under the extended environment.
     */
    // fold [T] e {Cᵢ(xⱼ) → tᵢ}  — E-Fold (span-captured handlers + _forward)
    @rule
    protected override foldProd(ctx: unknown): Parser<Value> {
        return seq(
            this.kw("fold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd,
            this.ws,
            char("]"),
            this.ws,
        ).chain(([, , , , ty]) => {
            assert(ty instanceof DataType, "fold type must be a DataType")
            const dataType = ty as DataType
            return this.exprProd(ctx)
                .chain((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.spanFoldHandlers(dataType, ctx)
                                .chain((handlers) =>
                                    seq(this.ws, char("}"))
                                        .map(() => this.evalFold(dataType, scrutinee, handlers))
                                )
                                .map(([, result]) => result)
                        )
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        }).map(([, result]) => result)
    }

    /** Parse fold handlers, capturing body spans instead of evaluating. */
    // Cᵢ(xⱼ) → tᵢ, ...  — fold handlers (span-captured for _forward)
    @rule
    protected spanFoldHandlers(
        dataType: DataType,
        ctx: unknown,
    ): Parser<SpanHandler[]> {
        return sepBy(
            this.spanFoldHandler(dataType, ctx),
            seq(this.ws, char(","), this.ws),
        )
    }

    // Cᵢ(xⱼ) → tᵢ  — single fold handler (span-captured)
    @rule
    protected spanFoldHandler(
        dataType: DataType,
        ctx: unknown,
    ): Parser<SpanHandler> {
        return seq(
            this.variantName,
            this.ws,
            char("("),
            this.ws,
            sepBy(this.ident, this.ws1).opt(),
            this.ws,
            char(")"),
            this.ws,
            this.arrow,
            this.ws,
        ).chain(([vName, , , , bindings]) => {
            const variant = dataType.findVariant(vName)
            if (!variant) {
                return empty() as unknown as Parser<SpanHandler>
            }
            const bindingList = (bindings as string[] | undefined) ?? []
            let extendedCtx = ctx
            for (let i = 0; i < bindingList.length; i++) {
                const field = variant.fields[i]
                if (field) {
                    extendedCtx = this.extendCtx(extendedCtx, bindingList[i]!, field.type)
                }
            }
            return this.exprProd(extendedCtx)
                .map((_body, span) => ({
                    variantName: vName,
                    bindings: bindingList,
                    bodySpan: {
                        start: span.start + this._inputOffset,
                        end: span.end + this._inputOffset,
                    } as Span,
                }))
        }).map(([, result]) => result)
    }

    /** Evaluate a fold: find matching handler, bind fields, _forward body. */
    private evalFold(
        dataType: DataType,
        scrutinee: Value,
        handlers: SpanHandler[],
    ): Value {
        if (!(scrutinee instanceof VariantVal)) {
            return EVAL_ERROR("fold scrutinee is not a VariantVal")
        }
        const handler = handlers.find((h) => h.variantName === scrutinee.variantName)
        if (!handler) {
            return EVAL_ERROR(`no handler for variant: ${scrutinee.variantName}`)
        }

        const variant = dataType.findVariant(scrutinee.variantName)
        if (!variant) {
            return EVAL_ERROR(`variant ${scrutinee.variantName} not found in ${dataType.name}`)
        }

        let handlerEnv = new ValueEnv()
        for (let i = 0; i < variant.fields.length; i++) {
            const field = variant.fields[i]!
            const binding = handler.bindings[i]
            if (binding) {
                const fieldValue = scrutinee.fields.get(field.name)
                if (fieldValue !== undefined) {
                    handlerEnv = handlerEnv.extend(binding, fieldValue)
                }
            }
        }

        const savedOffset = this._inputOffset
        this._inputOffset = handler.bodySpan.start
        try {
            const results = [...this._forward(
                this._input,
                handler.bodySpan,
                this.exprProd(handlerEnv),
            )]
            if (results.length === 0) {
                return EVAL_ERROR("fold handler body evaluation produced no results")
            }
            return results[0]!
        } finally {
            this._inputOffset = savedOffset
        }
    }

    // ── E-Unfold: override unfoldProd for span capture ───────────────────────

    /**
     * Override `unfoldProd` to capture generator body spans. The unfold
     * produces a `SpanCodataVal` that stores the seed value and span-captured
     * generators. When an observer is called, the generator body is
     * re-evaluated via `_forward`.
     */
    // unfold [T] s {oⱼ → gⱼ}  — E-Unfold (span-captured generators)
    @rule
    protected override unfoldProd(ctx: unknown): Parser<Value> {
        return seq(
            this.kw("unfold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd,
            this.ws,
            char("]"),
            this.ws,
        ).chain(([, , , , ty]) => {
            assert(ty instanceof CodataType, "unfold type must be a CodataType")
            const codataType = ty as CodataType
            return this.exprProd(ctx)
                .chain((seed) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.spanUnfoldGenerators(codataType, ctx)
                                .chain((generators) =>
                                    seq(this.ws, char("}"))
                                        .map(() =>
                                            new SpanCodataVal(
                                                codataType,
                                                seed,
                                                generators,
                                                ctx as ValueEnv,
                                            )
                                        )
                                )
                                .map(([, result]) => result)
                        )
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        }).map(([, result]) => result)
    }

    /** Parse unfold generators, capturing body spans. */
    // oⱼ → gⱼ, ...  — unfold generators (span-captured)
    @rule
    protected spanUnfoldGenerators(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<SpanGenerator[]> {
        return sepBy(
            this.spanUnfoldGenerator(codataType, ctx),
            seq(this.ws, char(","), this.ws),
        )
    }

    // oⱼ → gⱼ  — single unfold generator (span-captured)
    @rule
    protected spanUnfoldGenerator(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<SpanGenerator> {
        return seq(
            this.ident,
            this.ws,
            this.arrow,
            this.ws,
        ).chain(([obsName]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty() as unknown as Parser<SpanGenerator>
            }
            const extendedCtx = this.extendCtx(ctx, "self", Any)
            return this.exprProd(extendedCtx)
                .map((_body, span) => ({
                    observerName: obsName,
                    bodySpan: {
                        start: span.start + this._inputOffset,
                        end: span.end + this._inputOffset,
                    } as Span,
                }))
        }).map(([, result]) => result)
    }

    // ── E-Cofold: override cofoldProd for span capture + _forward ────────────

    /**
     * Override `cofoldProd` to capture the handler body span. When the cofold
     * is evaluated, the scrutinee should be a `SpanCodataVal`. We run each
     * generator to get observation values, bind them to the handler's field
     * bindings, and re-evaluate the handler body via `_forward`.
     *
     * E-Cofold: cofold [T] (unfold [T] s {oⱼ → gⱼ}) {oⱼ(xⱼ) → t}
     *           → [xⱼ ↦ gⱼ(s)] t
     */
    // cofold [T] e {oⱼ(xⱼ) → t}  — E-Cofold (span-captured handler + _forward)
    @rule
    protected override cofoldProd(ctx: unknown): Parser<Value> {
        return seq(
            this.kw("cofold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd,
            this.ws,
            char("]"),
            this.ws,
        ).chain(([, , , , ty]) => {
            assert(ty instanceof CodataType, "cofold type must be a CodataType")
            const codataType = ty as CodataType
            return this.exprProd(ctx)
                .chain((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .chain(() =>
                            this.spanCofoldHandler(codataType, ctx)
                                .chain((handler) =>
                                    seq(this.ws, char("}"))
                                        .map(() =>
                                            this.evalCofold(
                                                codataType,
                                                scrutinee,
                                                handler,
                                                ctx as ValueEnv,
                                            )
                                        )
                                )
                                .map(([, result]) => result)
                        )
                        .map(([, result]) => result)
                )
                .map(([, result]) => result)
        }).map(([, result]) => result)
    }

    /** Parse cofold handler, capturing body span. */
    // oⱼ(xⱼ) → t  — cofold handler (span-captured)
    @rule
    protected spanCofoldHandler(
        codataType: CodataType,
        ctx: unknown,
    ): Parser<{ observerName: string; bindings: string[]; bodySpan: Span }> {
        return seq(
            this.ident,
            this.ws,
            char("("),
            this.ws,
            sepBy(this.ident, this.ws1),
            this.ws,
            char(")"),
            this.ws,
            this.arrow,
            this.ws,
        ).chain(([obsName, , , , bindings]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty() as unknown as Parser<
                    { observerName: string; bindings: string[]; bodySpan: Span }
                >
            }
            const bindingList = (bindings as string[] | undefined) ?? []
            let extendedCtx = ctx
            for (let i = 0; i < bindingList.length; i++) {
                extendedCtx = this.extendCtx(extendedCtx, bindingList[i]!, Any)
            }
            return this.exprProd(extendedCtx)
                .map((_body, span) => ({
                    observerName: obsName,
                    bindings: bindingList,
                    bodySpan: {
                        start: span.start + this._inputOffset,
                        end: span.end + this._inputOffset,
                    } as Span,
                }))
        }).map(([, result]) => result)
    }

    /**
     * Evaluate a cofold: run all generators on the seed, bind results to
     * handler bindings, re-evaluate handler body via _forward.
     */
    private evalCofold(
        codataType: CodataType,
        scrutinee: Value,
        handler: { observerName: string; bindings: string[]; bodySpan: Span },
        _ctx: ValueEnv,
    ): Value {
        if (!(scrutinee instanceof SpanCodataVal)) {
            return EVAL_ERROR("cofold scrutinee is not a SpanCodataVal")
        }

        // Run each generator to get observation values
        const allObservers = codataType.allObservers()
        let handlerEnv = new ValueEnv()

        // Build a map from observer name to binding for O(1) lookup
        const bindingMap = new Map<string, string>()
        for (let i = 0; i < handler.bindings.length; i++) {
            // The handler lists one observer: handler.observerName
            // with bindings[0..n] as its field bindings.
            // Map the observer name to its first binding (single-result case).
            if (i === 0) {
                bindingMap.set(handler.observerName, handler.bindings[i]!)
            }
        }

        for (const observer of allObservers) {
            const binding = bindingMap.get(observer.name)
            if (!binding) continue

            const generator = scrutinee.generators.find(
                (g) => g.observerName === observer.name,
            )
            if (!generator) {
                return EVAL_ERROR(`no generator for observer: ${observer.name}`)
            }

            // Run the generator: re-evaluate body with self = seed
            const genEnv = scrutinee.env.extend("self", scrutinee.seed)
            const savedOffset = this._inputOffset
            this._inputOffset = generator.bodySpan.start
            try {
                const results = [...this._forward(
                    this._input,
                    generator.bodySpan,
                    this.exprProd(genEnv),
                )]
                if (results.length === 0) {
                    return EVAL_ERROR(`generator ${observer.name} produced no results`)
                }
                handlerEnv = handlerEnv.extend(binding, results[0]!)
            } finally {
                this._inputOffset = savedOffset
            }
        }

        // Re-evaluate the handler body with observation values bound
        const savedOffset = this._inputOffset
        this._inputOffset = handler.bodySpan.start
        try {
            const results = [...this._forward(
                this._input,
                handler.bodySpan,
                this.exprProd(handlerEnv),
            )]
            if (results.length === 0) {
                return EVAL_ERROR("cofold handler body produced no results")
            }
            return results[0]!
        } finally {
            this._inputOffset = savedOffset
        }
    }

    // ── E-Obs: override obsProd for evaluation via chain + _forward ───────────

    /**
     * Override `obsProd` to evaluate observations. When the scrutinee is a
     * `SpanCodataVal`, find the matching generator, bind `self` to the seed,
     * and re-evaluate the generator body via `_forward`.
     */
    // e.o  — E-Obs via chain + _forward
    @rule
    protected override obsProd(ctx: unknown): Parser<Value> {
        return or(
            this.obsProd(ctx)
                .map((scrutVal) => ({ scrutVal }))
                .chain(({ scrutVal }) =>
                    seq(this.ws, char("."), this.ws, this.ident)
                        .map(([, , , obsName]) => ({ scrutVal, obsName }))
                        .chain(({ scrutVal, obsName }) => {
                            if (!(scrutVal instanceof SpanCodataVal)) {
                                return empty() as unknown as Parser<Value>
                            }
                            const generator = scrutVal.generators.find(
                                (g) => g.observerName === obsName,
                            )
                            if (!generator) {
                                return empty() as unknown as Parser<Value>
                            }
                            const genEnv = scrutVal.env.extend("self", scrutVal.seed)
                            const savedOffset = this._inputOffset
                            this._inputOffset = generator.bodySpan.start
                            try {
                                const results = [...this._forward(
                                    this._input,
                                    generator.bodySpan,
                                    this.exprProd(genEnv),
                                )]
                                if (results.length === 0) {
                                    return empty() as unknown as Parser<Value>
                                }
                                return epsilon<Value>(results[0]!)
                            } finally {
                                this._inputOffset = savedOffset
                            }
                        })
                        .map(([, result]) => result)
                )
                .map(([, result]) => result),
            this.appProd(ctx),
        )
    }

    // ── Stubs for abstract methods not used by overridden productions ─────────
    // These are never called because we override the productions that call them.

    protected lam(_param: string, _type: Type, _body: Value): Value {
        throw new Error("LCEval.lam: unreachable — lambdaProd is overridden")
    }
    protected app(_fn: Value, _arg: Value): Value {
        throw new Error("LCEval.app: unreachable — appProd is overridden")
    }
    protected let_(_name: string, _type: Type, _def: Value, _body: Value): Value {
        throw new Error("LCEval.let_: unreachable — letProd is overridden")
    }
    protected obs(_scrutinee: Value, _observerName: string): Value {
        throw new Error("LCEval.obs: unreachable — obsProd is overridden")
    }
    protected fold(
        _dataType: DataType,
        _scrutinee: Value,
        _handlers: { variantName: string; bindings: string[]; body: Value }[],
        _resultType: Type,
    ): Value {
        throw new Error("LCEval.fold: unreachable — foldProd is overridden")
    }
    protected unfold(
        _codataType: CodataType,
        _seed: Value,
        _generators: { observerName: string; body: Value }[],
        _seedType: Type,
    ): Value {
        throw new Error("LCEval.unfold: unreachable — unfoldProd is overridden")
    }
    protected typeAbs(_tyVar: string, _bound: Type, _body: Value): Value {
        // E-TAbs: type abstraction is a value (no evaluation needed).
        // The body was parsed under a PLACEHOLDER env (via extendCtx), so
        // _body may contain PlaceholderValue objects for type-variable
        // references. This is fine — type abstractions are erased at runtime,
        // and the body is only re-evaluated via _forward when the type
        // abstraction is applied (typeApp returns the body directly).
        return _body
    }
    protected typeApp(body: Value, _argType: Type): Value {
        // E-TApp: (Λα<:σ. t) [τ] → [α ↦ τ] t
        // Type erasure: evaluate the body directly (types erased at runtime).
        return body
    }
    protected cofold(
        _codataType: CodataType,
        _scrutinee: Value,
        _handler: { observerName: string; bindings: string[]; body: Value },
        _resultType: Type,
    ): Value {
        throw new Error("LCEval.cofold: unreachable — cofoldProd is overridden")
    }
}
