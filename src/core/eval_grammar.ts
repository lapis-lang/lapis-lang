/**
 * LC Evaluation — a grammar subclass that evaluates LC terms during parsing.
 *
 * Following the grammar-as-semantics pattern (like STLCEval in lang-forma):
 * the evaluation judgment `ρ ⊢ t ⇓ v` becomes a parameterised production
 * `exprProd(ρ): Parser<Value>`. `bind` threads the environment through
 * sub-productions. `_forward` re-evaluates closure bodies under extended
 * environments — the higher-order attribute mechanism.
 *
 * Evaluation rules (lc.md §3):
 *
 *   E-App:       (λx:σ. t) v → [x ↦ v] t
 *   E-Let:       let x:σ = v in u → [x ↦ v] u
 *   E-Fold:      fold [T] v {Cᵢ(xⱼ) → tᵢ, match("pₖ") → uₖ} →
 *                a VariantVal scrutinee fires its variant arm: [xⱼ ↦ vⱼ'] tₖ
 *                a TokenVal scrutinee fires the pattern arm: [match ↦ tok] uₖ
 *                (one rule, TWO arm kinds — the value-kind disjointness makes
 *                the per-arm readings independent within one handler list)
 *   E-Obs:       (unfold [T] s {oⱼ → gⱼ}).oₖ → gₖ(s)
 *   E-Cofold:    cofold [T] (unfold [T] s {oⱼ → gⱼ}) {oⱼ(xⱼ) → t} → [xⱼ ↦ gⱼ(s)] t
 *   E-TApp:      (Λα <: σ. t) [τ] → [α ↦ τ] t  (type erasure)
 *   E-Op:        op(v₁, ..., vₙ) → def(op) v₁ ... vₙ  (definition applied via _forward)
 *   E-OpArg:     op(v₁, ..., tᵢ, ..., vₙ) → op(v₁, ..., tᵢ', ..., vₙ)  (leftmost;
 *                realized structurally — args are atoms evaluated in seq order)
 *
 * Higher-order attributes via _forward:
 *   E-App:    re-parses closure body under ρ[x := v]
 *   E-Fold:   re-parses matching handler body under ρ[xⱼ := vⱼ]
 *   E-Obs:    re-parses generator body under ρ[self := seed]
 *   E-Cofold: re-parses all generators, then handler body under ρ[xⱼ := gⱼ(s)]
 *
 * E-Let is same-pass (no _forward): def's value is available from bind,
 * so body is parsed under ρ[x := def] directly.
 *
 * E-Op opens a definition window: the op's defining term (from Ω) is
 * evaluated under a temporarily swapped `_input` (the definition source, not
 * the parse input), then applied to the argument values leftmost via
 * `_forward`. Closures captured inside the window carry the definition
 * source as their `input`, so they stay applicable after the window closes.
 * The window's parses must be unambiguous (exactly one result) — the window
 * is internal, so ambiguity is an error, not a choice (see `evalOp`).
 *
 * See _docs/theory/lc.md §3 for the formal specification.
 * See _docs/theory/grammar-as-semantics.md for the architecture.
 */

import {
    assert,
    char,
    empty,
    ensures,
    epsilon,
    invariant,
    or,
    type Parser,
    requires,
    rule,
    sepBy,
    seq,
    type Span,
} from "@lapis-lang/lang-forma"

import { Any, CodataType, DataType, FamilyType, type Type } from "./types.ts"

import { patternToString } from "./pattern_lang.ts"

import { type OpSig } from "./ops.ts"

import { AbstractLC, type LCShape } from "./grammar.ts"

import { SpanClosure, TokenVal, Value, ValueEnv, VariantVal } from "./values.ts"
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

/**
 * A fold handler arm — ONE discriminated record for both member kinds (the
 * merged fold form): a VARIANT arm carries the constructor name and its
 * field bindings; a PATTERN arm carries the pattern's CANONICAL source (the
 * evaluator's dispatch keys canonical form). Each arm's body span is
 * captured for deferred `_forward` evaluation; exactly one payload is
 * present — the `kind` tag is the record's discriminant.
 */
type SpanHandler =
    | { kind: "variant"; variantName: string; bindings: string[]; bodySpan: Span }
    | { kind: "pattern"; patternSource: string; bodySpan: Span }

/** An unfold generator with span-captured body (for deferred evaluation). */
interface SpanGenerator {
    observerName: string
    bodySpan: Span
}

// ── SpanCodataVal — codata value with span-captured generators ────────────────

/**
 * A codata value that stores generator body spans (not pre-evaluated bodies).
 * When an observer is called, the generator body is re-evaluated via `_forward`.
 *
 * `input` is the source text the generator spans index into — the codata dual
 * of `SpanClosure.input`. For unfolds in the main parse it is the parse
 * input; for unfolds evaluated inside an operation definition (E-Op's
 * definition window) it is the definition source. Carrying it on the value
 * keeps an escaping codata value (e.g. an op returning an unfold) observable
 * after the window closes, and a codata value passed into an op observable
 * inside it.
 */
export class SpanCodataVal extends Value {
    readonly kind = "codataVal"
    constructor(
        readonly codataType: CodataType,
        readonly seed: Value,
        readonly generators: SpanGenerator[],
        readonly env: ValueEnv,
        /** The source text that the generator spans index into. */
        readonly input: string = "",
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

    /**
     * ρ membership for the token gate: a name bound in ρ is a term variable
     * (`patternTokenProd` falls through to `varProd`), so a PascalCase
     * variable always evaluates to its ρ value — the registry's pattern-type
     * entry never shadows it.
     */
    protected override nameBound(name: string, ctx: unknown): boolean {
        return ctx instanceof ValueEnv && ctx.lookup(name) !== undefined
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
    @rule({ rule: "E-Lam", production: "lambdaProd" })
    protected override lambdaProd(ctx: unknown): Parser<Value> {
        return seq(
            this.lambdaHead,
            this.ident,
            this.ws,
            char(":"),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("."),
            this.ws,
        ).bind(([, param, , , , ty]) => {
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
                        this._input,
                    )
                )
        })
    }

    // ── E-App: override appProd for evaluation via bind + _forward ───────────

    /**
     * Override application to evaluate via bind:
     * parse fn → get fnVal; parse arg → get argVal;
     * if fnVal is a SpanClosure, re-evaluate body via `_forward` under
     * extended env; else empty (eval error).
     */
    // t u  — E-App via bind + _forward
    @rule({ rule: "E-App", production: "appProd" })
    protected override appProd(ctx: unknown): Parser<Value> {
        return or(
            this.appProd(ctx)
                .map((fnVal) => ({ fnVal }))
                .bind(({ fnVal }) =>
                    seq(this.ws1, this.typeAppProd(ctx))
                        .map(([, argVal]) => ({ fnVal, argVal }))
                        .bind(({ fnVal, argVal }) => {
                            if (!(fnVal instanceof SpanClosure)) {
                                return empty<Value>()
                            }
                            const bodyEnv = fnVal.env.extend(fnVal.param, argVal)
                            const savedInput = this._input
                            const savedOffset = this._inputOffset
                            this._input = fnVal.input
                            this._inputOffset = fnVal.bodySpan.start
                            try {
                                const results = [...this._forward(
                                    fnVal.input,
                                    fnVal.bodySpan,
                                    this.exprProd(bodyEnv),
                                )]
                                if (results.length === 0) {
                                    return empty<Value>()
                                }
                                return epsilon<Value>(results[0]!)
                            } finally {
                                this._input = savedInput
                                this._inputOffset = savedOffset
                            }
                        })
                ),
            this.typeAppProd(ctx),
        )
    }

    // ── E-Let: override letProd for same-pass evaluation ──────────────────────

    /**
     * Override `letProd` to parse the body under the real env (extended with
     * def's value). Unlike `lambdaProd`, the body is evaluated in the same
     * pass — `def`'s value is available from the `bind`, so the body parser
     * runs under `ρ[name:=def]` directly. No span capture or `_forward` needed.
     */
    // let x:σ = t in u  — E-Let (same-pass evaluation)
    @rule({ rule: "E-Let", production: "letProd" })
    protected override letProd(ctx: unknown): Parser<Value> {
        return seq(
            this.kw("let"),
            this.ws1,
            this.ident,
            this.ws,
            char(":"),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("="),
            this.ws,
        ).bind(([, , name]) =>
            this.exprProd(ctx)
                .map((def) => ({ name, def }))
                .bind(({ name, def }) =>
                    seq(this.ws1, this.kw("in"), this.ws1)
                        .bind(() => {
                            const bodyCtx = (ctx as ValueEnv).extend(name, def)
                            return this.exprProd(bodyCtx)
                                .map((body) => body)
                        })
                )
        )
    }

    // ── E-Fold: override foldProd for span capture + _forward ─────────────────

    /**
     * Override `foldProd` to capture handler body spans. When the fold is
     * evaluated, the scrutinee is already a value. We find the matching
     * handler, bind field values to handler bindings, and re-evaluate the
     * handler body via `_forward` under the extended environment.
     */
    // fold [T] e {Cᵢ(xⱼ) → tᵢ}  — E-Fold (span-captured handlers + _forward)
    @rule({ rule: "E-Fold", production: "foldProd" })
    protected override foldProd(ctx: unknown): Parser<Value> {
        return seq(
            this.kw("fold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("]"),
            this.ws,
        ).bind(([, , , , ty]) => {
            // The annotation must be a DataType. A wrong-kind annotation
            // (e.g. `fold [Stream] ...`) rejects the branch (`empty<Value>()`)
            // like any other failed step — a throw here would surface as a
            // crash instead of a clean parse rejection.
            if (!(ty instanceof DataType)) {
                return empty<Value>()
            }
            const dataType = ty
            return this.exprProd(ctx)
                .bind((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.spanFoldHandlers(dataType, ctx)
                                .bind((handlers) =>
                                    seq(this.ws, char("}"))
                                        .map(() =>
                                            this.evalFold(
                                                dataType,
                                                scrutinee,
                                                handlers,
                                                ctx as ValueEnv,
                                            )
                                        )
                                )
                        )
                )
        })
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
        // ONE alternation over both member kinds (the merged fold form): the
        // variant head captures the constructor's bindings; the pattern head
        // captures the body under `match : Token` (the extended context —
        // this override threads ctx, so the binding rides in the parsed
        // spans). The two heads are lexically disjoint, the `or` unambiguous.
        return or(
            seq(
                this.variantName,
                this.ws,
                char("("),
                this.ws,
                sepBy(this.ident, this.ws1),
                this.ws,
                char(")"),
                this.ws,
                this.arrow,
                this.ws,
            ).bind(([vName, , , , bindings]): Parser<SpanHandler> => {
                const variant = dataType.findVariant(vName)
                if (!variant) {
                    return empty<SpanHandler>()
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
                        kind: "variant" as const,
                        variantName: vName,
                        bindings: bindingList,
                        bodySpan: {
                            start: span.start + this._inputOffset,
                            end: span.end + this._inputOffset,
                        } as Span,
                    }))
            }),
            seq(
                this.kw("match"),
                char("("), // tight paren — the pattern form's discipline
                this.ws,
                this.patternString,
                this.ws,
                char(")"),
                this.ws,
                this.arrow,
                this.ws,
            ).bind(([, , , patternSource]): Parser<SpanHandler> => {
                const resolved = this.patternTypeName(patternSource as string)
                // The handler-head premise reads the LINEAGE (the same rule
                // the variant fold's `findVariant` applies): a comb child's
                // fold handles a pattern its parent declared. Keying on the
                // index owner's name alone would deny the child its
                // inherited members.
                if (
                    resolved === undefined ||
                    !this.registry.declaresPattern(dataType, resolved.source)
                ) {
                    return empty<SpanHandler>()
                }
                return this.exprProd(ctx)
                    .map((_body, span) => ({
                        kind: "pattern" as const,
                        patternSource: resolved.source,
                        bodySpan: {
                            start: span.start + this._inputOffset,
                            end: span.end + this._inputOffset,
                        } as Span,
                    }))
            }),
        )
    }

    /** Evaluate a fold: find matching handler, bind fields, _forward body. */
    private evalFold(
        dataType: DataType,
        scrutinee: Value,
        handlers: SpanHandler[],
        ambientEnv: ValueEnv,
    ): Value {
        // The kind dispatch — the merged fold's one step decides by the
        // scrutinee's VALUE shape: a VariantVal takes the variant arm
        // (recursive-field walk); a TokenVal takes the pattern arm (single
        // step, `match` binds RAW). The two routes never mix within one
        // step; the diagnostics name both shapes so a broken scrutinee is
        // reported honestly.
        if (scrutinee instanceof VariantVal) {
            return this.evalFoldVariantArm(dataType, scrutinee, handlers, ambientEnv)
        }
        if (scrutinee instanceof TokenVal) {
            return this.evalFoldPatternArm(dataType, scrutinee, handlers, ambientEnv)
        }
        return EVAL_ERROR("fold scrutinee is neither a VariantVal nor a TokenVal of the carrier")
    }

    /** E-Fold's variant arm: the recursive-field walk (the existing route). */
    private evalFoldVariantArm(
        dataType: DataType,
        scrutinee: VariantVal,
        handlers: SpanHandler[],
        ambientEnv: ValueEnv,
    ): Value {
        const handler = handlers.find((h) =>
            h.kind === "variant" && h.variantName === scrutinee.variantName
        )
        if (!handler || handler.kind !== "variant") {
            return EVAL_ERROR(`no handler for variant: ${scrutinee.variantName}`)
        }

        const variant = dataType.findVariant(scrutinee.variantName)
        if (!variant) {
            return EVAL_ERROR(`variant ${scrutinee.variantName} not found in ${dataType.name}`)
        }

        // The handler body is evaluated in the fold's ambient scope (ρ)
        // extended with the field bindings — the handler's free variables
        // resolve lexically. (E-Fold: [xⱼ ↦ vⱼ] tₖ, a substitution into the
        // ambient scope, not a fresh one.)
        let handlerEnv = ambientEnv
        for (let i = 0; i < variant.fields.length; i++) {
            const field = variant.fields[i]!
            const binding = handler.bindings[i]
            if (binding) {
                const fieldValue = scrutinee.fields.get(field.name)
                if (fieldValue !== undefined) {
                    // E-Fold: a Family-typed field (the μ-bound) binds the
                    // *folded* result — vⱼ' = fold [T] vⱼ {Cᵢ → tᵢ} — matching
                    // the type checker, which binds it to σ (the fold's result
                    // type). Non-recursive fields bind raw.
                    // The recursion terminates: fieldValue is a proper
                    // subterm of the scrutinee (structural recursion).
                    const boundValue = field.type instanceof FamilyType &&
                            fieldValue instanceof VariantVal
                        ? this.evalFold(dataType, fieldValue, handlers, ambientEnv)
                        : fieldValue
                    handlerEnv = handlerEnv.extend(binding, boundValue)
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

    /**
     * E-Fold's pattern arm (the merged fold's token route): dispatch the
     * token scrutinee to its handler, bind `match`, and replay the body span.
     * The carrier check reads the LINEAGE, not just the name: the token's
     * `dataTypeName` is the introduction form's resolved OWNER (the index
     * pick — a comb child's inherited pattern introduces a PARENT-named
     * token), so a name-equality check alone would reject a legitimate
     * `fold [Child] <inherited-token>` (the same asymmetry the handler gates
     * widened to `declaresPattern` — the fold path's carrier membership is
     * lineage-wide).
     */
    private evalFoldPatternArm(
        dataType: DataType,
        scrutinee: TokenVal,
        handlers: SpanHandler[],
        ambientEnv: ValueEnv,
    ): Value {
        const tokenOwner = this.registry.lookup(scrutinee.dataTypeName)
        // The carrier check reads the LINEAGE in the subtyping direction:
        // the token's owner must be the fold carrier itself OR one of its
        // ANCESTORS (the child <: parent direction makes an ancestor-named
        // token valid everywhere the descendant carrier's fold is — the
        // same rule the checker's scrutinee premise applies via isSubtype).
        // An UNRELATED carrier that declares the identical pattern is NOT
        // an ancestor: its token cannot dispatch through this fold, however
        // equal the canonical sources are — a shared pattern string does
        // not put one carrier in the other's lineage.
        //
        // The pattern-membership clause applies to the ANCESTOR arm only
        // (the inherited pattern is what carries the token into this
        // lineage): the carrier's OWN token (owner === dataType) passes the
        // carrier check unconditionally — the bare atom is the carrier's
        // value whatever its text, and the HANDLER dispatch below is what
        // reports the no-handler miss for a text that names no declared
        // pattern.
        const tokenOwnerIsAncestor = tokenOwner instanceof DataType &&
            tokenOwner !== dataType &&
            (() => {
                for (let p = dataType.parent; p !== null; p = p.parent) {
                    if (p === tokenOwner) return true
                }
                return false
            })()
        const carrierHandles = tokenOwner === dataType ||
            (tokenOwnerIsAncestor &&
                tokenOwner.allPatterns().some((p) => patternToString(p) === scrutinee.text))
        if (!carrierHandles) {
            return EVAL_ERROR(
                `token type ${scrutinee.dataTypeName} does not match fold carrier ${dataType.name}`,
            )
        }
        const handler = handlers.find((h) =>
            h.kind === "pattern" && h.patternSource === scrutinee.text
        )
        if (!handler || handler.kind !== "pattern") {
            return EVAL_ERROR(`no handler for pattern: ${scrutinee.text}`)
        }

        // E-Fold's pattern arm: [match ↦ tok] tₖ — the token value itself
        // binds to
        // `match` (it is already a value; a single-step extraction), and the
        // body replays in the fold's ambient scope extended with it — the
        // handler's free variables resolve lexically.
        const handlerEnv = ambientEnv.extend("match", scrutinee)

        const savedOffset = this._inputOffset
        this._inputOffset = handler.bodySpan.start
        try {
            const results = [...this._forward(
                this._input,
                handler.bodySpan,
                this.exprProd(handlerEnv),
            )]
            if (results.length === 0) {
                return EVAL_ERROR(
                    "pattern fold handler body evaluation produced no results",
                )
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
    @rule({ rule: "E-Unfold", production: "unfoldProd" })
    protected override unfoldProd(ctx: unknown): Parser<Value> {
        return seq(
            this.kw("unfold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("]"),
            this.ws,
        ).bind(([, , , , ty]) => {
            // The annotation must be a CodataType. A wrong-kind annotation
            // (e.g. `unfold [Nat] ...`) rejects the branch (`empty<Value>()`)
            // like any other failed step — a throw here would surface as a
            // crash instead of a clean parse rejection.
            if (!(ty instanceof CodataType)) {
                return empty<Value>()
            }
            const codataType = ty
            return this.exprProd(ctx)
                .bind((seed) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.spanUnfoldGenerators(codataType, ctx)
                                .bind((generators) =>
                                    seq(this.ws, char("}"))
                                        .map(() =>
                                            new SpanCodataVal(
                                                codataType,
                                                seed,
                                                generators,
                                                ctx as ValueEnv,
                                                this._input,
                                            )
                                        )
                                )
                        )
                )
        })
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
        ).bind(([obsName]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty<SpanGenerator>()
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
        })
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
    @rule({ rule: "E-Cofold", production: "cofoldProd" })
    protected override cofoldProd(ctx: unknown): Parser<Value> {
        return seq(
            this.kw("cofold"),
            this.ws1,
            char("["),
            this.ws,
            this.typeProd(this.typeVarCtx(ctx)),
            this.ws,
            char("]"),
            this.ws,
        ).bind(([, , , , ty]) => {
            // The annotation must be a CodataType. A wrong-kind annotation
            // (e.g. `cofold [Nat] ...`) rejects the branch (`empty<Value>()`)
            // like any other failed step — a throw here would surface as a
            // crash instead of a clean parse rejection.
            if (!(ty instanceof CodataType)) {
                return empty<Value>()
            }
            const codataType = ty
            return this.exprProd(ctx)
                .bind((scrutinee) =>
                    seq(this.ws, char("{"), this.ws)
                        .bind(() =>
                            this.spanCofoldHandler(codataType, ctx)
                                .bind((handler) =>
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
                        )
                )
        })
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
        ).bind(([obsName, , , , bindings]) => {
            const observer = codataType.findObserver(obsName)
            if (!observer) {
                return empty<
                    { observerName: string; bindings: string[]; bodySpan: Span }
                >()
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
        })
    }

    /**
     * Evaluate a cofold: run all generators on the seed, bind results to
     * handler bindings, re-evaluate handler body via _forward.
     */
    private evalCofold(
        codataType: CodataType,
        scrutinee: Value,
        handler: { observerName: string; bindings: string[]; bodySpan: Span },
        ambientEnv: ValueEnv,
    ): Value {
        if (!(scrutinee instanceof SpanCodataVal)) {
            return EVAL_ERROR("cofold scrutinee is not a SpanCodataVal")
        }

        // Run each generator to get observation values
        const allObservers = codataType.allObservers()
        // The handler body is evaluated in the cofold's ambient scope (ρ)
        // extended with the observation bindings — the handler's free
        // variables resolve lexically, symmetrically with E-Fold.
        let handlerEnv = ambientEnv

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

            // Run the generator: re-evaluate body with self = seed. The
            // generator's span indexes into the codata value's own input
            // (which may differ from the current `_input` when the cofold
            // scrutinee crossed an E-Op definition window).
            const genEnv = scrutinee.env.extend("self", scrutinee.seed)
            const savedInput = this._input
            const savedOffset = this._inputOffset
            this._input = scrutinee.input
            this._inputOffset = generator.bodySpan.start
            try {
                const results = [...this._forward(
                    scrutinee.input,
                    generator.bodySpan,
                    this.exprProd(genEnv),
                )]
                if (results.length === 0) {
                    return EVAL_ERROR(`generator ${observer.name} produced no results`)
                }
                handlerEnv = handlerEnv.extend(binding, results[0]!)
            } finally {
                this._input = savedInput
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

    // ── E-Op: override opProd for definition application via _forward ────────

    /**
     * Override `opProd` to apply the operation's definition (E-Op):
     *
     *   op(v₁, ..., vₙ) → def(op) v₁ ... vₙ
     *
     * The arguments are already values (atoms evaluated in `seq` order —
     * E-OpArg's leftmost discipline, realized structurally). The definition
     * is evaluated under a **definition window**: `_input` is swapped to the
     * definition source (it is not part of the parse input), so spans captured
     * inside the window index into the definition text. The window is closed
     * in a `finally` — nested op applications (an op referencing an earlier
     * op) stack windows correctly by save/restore.
     *
     * The definition is applied to the argument values leftmost via
     * `_forward` re-parses (the E-App mechanism), so an op computes exactly as
     * if its definition had been `let`-bound and called — but the named form
     * is never inlined into the parse input, keeping operation identity
     * recognizable to law-aware passes.
     */
    // op(t₁, ..., tₙ)  — E-Op (definition application via _forward)
    @rule({ rule: "E-Op", production: "opProd" })
    protected override opProd(ctx: unknown): Parser<Value> {
        return seq(
            this.opIdent,
            char("("),
            this.ws,
        ).bind(([opName]) => {
            const opSig = this.opRegistry.lookup(opName)
            if (!opSig) {
                return empty<Value>()
            }
            return sepBy(this.atomProd(ctx), seq(this.ws, char(","), this.ws))
                .bind((args) =>
                    seq(this.ws, char(")"))
                        .map(() => this.evalOp(opSig, args))
                )
        })
    }

    /**
     * Apply an operation's definition to argument values (E-Op).
     *
     * Opens the definition window, evaluates the definition source to a
     * closure, then applies it to the argument values leftmost. Arity is
     * enforced against the signature — the op form is fixed-arity, not
     * curried.
     *
     * **Determinism policy:** each internal `_forward` parse (the definition
     * and every application step) must yield exactly one result. The window
     * is internal — the caller never sees its parse forest — so a silent
     * first-pick would hide ambiguity from every caller and make evaluation
     * order-dependent. An ambiguous (or empty) parse is reported as an
     * `EvalErrorValue` naming the op and the step that failed, instead.
     */
    private evalOp(opSig: OpSig, args: Value[]): Value {
        if (args.length !== opSig.paramTypes.length) {
            return EVAL_ERROR(
                `op ${opSig.name}: expected ${opSig.paramTypes.length} arguments, got ${args.length}`,
            )
        }

        // Open the definition window: the definition source becomes `_input`
        // so spans captured while evaluating it index into the definition.
        const savedInput = this._input
        const savedOffset = this._inputOffset
        this._input = opSig.definition
        this._inputOffset = 0
        try {
            // Evaluate the definition to a closure. Exactly one parse result
            // is required: a definition that parses ambiguously (or not at
            // all) is a registry authoring bug, not an input to choose among.
            // Unlike a top-level parse — where the caller sees the whole
            // forest — this window is internal, so a silent first-pick would
            // hide ambiguity from every caller. Fail loudly instead.
            const defResults = [...this._forward(
                opSig.definition,
                { start: 0, end: opSig.definition.length },
                this.exprProd(new ValueEnv()),
            )]
            if (defResults.length === 0) {
                return EVAL_ERROR(`op ${opSig.name}: definition produced no results`)
            }
            if (defResults.length > 1) {
                return EVAL_ERROR(
                    `op ${opSig.name}: definition is ambiguous (${defResults.length} parses) — ` +
                        "operation definitions must be unambiguous",
                )
            }
            let fn = defResults[0]!

            // Apply the definition to the argument values, leftmost. Each
            // application step must also yield exactly one result — same
            // determinism requirement, same reasoning.
            for (const arg of args) {
                if (!(fn instanceof SpanClosure)) {
                    return EVAL_ERROR(`op ${opSig.name}: definition is not a function`)
                }
                const bodyEnv = fn.env.extend(fn.param, arg)
                this._input = fn.input
                this._inputOffset = fn.bodySpan.start
                const appResults = [...this._forward(
                    fn.input,
                    fn.bodySpan,
                    this.exprProd(bodyEnv),
                )]
                if (appResults.length === 0) {
                    return EVAL_ERROR(`op ${opSig.name}: application produced no results`)
                }
                if (appResults.length > 1) {
                    return EVAL_ERROR(
                        `op ${opSig.name}: application is ambiguous ` +
                            `(${appResults.length} parses of the definition body) — ` +
                            "operation definitions must be unambiguous",
                    )
                }
                fn = appResults[0]!
            }
            return fn
        } finally {
            // Close the definition window.
            this._input = savedInput
            this._inputOffset = savedOffset
        }
    }

    // ── E-Obs: override obsProd for evaluation via bind + _forward ───────────

    /**
     * Override `obsProd` to evaluate observations. When the scrutinee is a
     * `SpanCodataVal`, find the matching generator, bind `self` to the seed,
     * and re-evaluate the generator body via `_forward`.
     */
    // e.o  — E-Obs via bind + _forward
    @rule({ rule: "E-Obs", production: "obsProd" })
    protected override obsProd(ctx: unknown): Parser<Value> {
        return or(
            this.obsProd(ctx)
                .map((scrutVal) => ({ scrutVal }))
                .bind(({ scrutVal }) =>
                    seq(this.ws, char("."), this.ws, this.ident)
                        .map(([, , , obsName]) => ({ scrutVal, obsName }))
                        .bind(({ scrutVal, obsName }) => {
                            // Capture-phase leniency: inside a lambda body
                            // being parsed for span capture, a parameter is
                            // bound to PLACEHOLDER — its observation cannot
                            // fire yet. The same leniency varRef and
                            // variantCon already have: keep the parse alive
                            // with a placeholder so the surrounding closure's
                            // span is captured; the observation runs via
                            // _forward when the closure is applied.
                            if (
                                !(scrutVal instanceof SpanCodataVal) &&
                                !(scrutVal instanceof PlaceholderValue)
                            ) {
                                return empty<Value>()
                            }
                            if (scrutVal instanceof PlaceholderValue) {
                                return epsilon<Value>(PLACEHOLDER)
                            }
                            const generator = scrutVal.generators.find(
                                (g) => g.observerName === obsName,
                            )
                            if (!generator) {
                                return empty<Value>()
                            }
                            const genEnv = scrutVal.env.extend("self", scrutVal.seed)
                            // The generator's span indexes into the codata
                            // value's own input (which may differ from the
                            // current `_input` when the value crossed an E-Op
                            // definition window).
                            const savedInput = this._input
                            const savedOffset = this._inputOffset
                            this._input = scrutVal.input
                            this._inputOffset = generator.bodySpan.start
                            try {
                                const results = [...this._forward(
                                    scrutVal.input,
                                    generator.bodySpan,
                                    this.exprProd(genEnv),
                                )]
                                if (results.length === 0) {
                                    return empty<Value>()
                                }
                                return epsilon<Value>(results[0]!)
                            } finally {
                                this._input = savedInput
                                this._inputOffset = savedOffset
                            }
                        })
                ),
            this.appProd(ctx),
        )
    }

    // ── Stubs for abstract methods not used by overridden productions ─────────
    // These are never called because we override the productions that call them.

    // ── Semantic-action stubs with metatheory contracts ─────────────────────
    //
    // These methods are never called at runtime (the productions that invoke
    // them are overridden above). The @requires/@ensures contracts are
    // declarative metadata for the lang-forma rule model (collectRules /
    // checkProgress / checkPreservation) — they encode the evaluation rules'
    // premise/conclusion structure so the metatheory engine can verify
    // Progress and Preservation without hand-written proofs.

    /**
     * E-Lam: a lambda evaluates to a closure (a value). No premises — a
     * lambda is always a normal form (value-rule).
     */
    @ensures(
        (_self: LCEval, _args: [string, Type, Value], _old, result: Value) =>
            result instanceof SpanClosure,
        { rule: "E-Lam", role: "conclusion", formula: "result : ⟨x, σ, span, ρ⟩" },
    )
    protected lam(_param: string, _type: Type, _body: Value): Value {
        throw new Error("LCEval.lam: unreachable — lambdaProd is overridden")
    }

    /**
     * E-App: (λx:σ. t) v → [x ↦ v] t. Premise: fn is a SpanClosure.
     * Step-rule — the application transitions by re-evaluating the body.
     */
    @requires(
        (_self: LCEval, fn: Value, _arg: Value) => fn instanceof SpanClosure,
        { rule: "E-App", role: "premise", formula: "fn : ⟨x, σ, span, ρ⟩", type: "τ" },
    )
    @ensures(
        () => true,
        { rule: "E-App", role: "conclusion", formula: "result : w", type: "τ" },
    )
    protected app(_fn: Value, _arg: Value): Value {
        throw new Error("LCEval.app: unreachable — appProd is overridden")
    }

    /**
     * E-Let: let x:σ = v in u → [x ↦ v] u. Premise: def is a value.
     * Step-rule — the let transitions by evaluating the body under the
     * extended environment.
     */
    @requires(
        () => true,
        { rule: "E-Let", role: "premise", formula: "def : v", type: "τ" },
    )
    @ensures(
        () => true,
        { rule: "E-Let", role: "conclusion", formula: "result : w", type: "τ" },
    )
    protected let_(_name: string, _type: Type, _def: Value, _body: Value): Value {
        throw new Error("LCEval.let_: unreachable — letProd is overridden")
    }

    /**
     * E-Obs: (unfold [T] s {oⱼ → gⱼ}).oₖ → gₖ(s). Premise: scrutinee is a
     * SpanCodataVal. Step-rule — the observation transitions by re-evaluating
     * the generator body.
     */
    @requires(
        (_self: LCEval, scrutinee: Value, _observerName: string) =>
            scrutinee instanceof SpanCodataVal,
        { rule: "E-Obs", role: "premise", formula: "scrutinee : codataVal", type: "τ" },
    )
    @ensures(
        () => true,
        { rule: "E-Obs", role: "conclusion", formula: "result : w", type: "τ" },
    )
    protected obs(_scrutinee: Value, _observerName: string): Value {
        throw new Error("LCEval.obs: unreachable — obsProd is overridden")
    }

    /**
     * E-Fold: fold [T] (Cₖ(vⱼ)) {Cᵢ(xⱼ) → tᵢ} → [xⱼ ↦ vⱼ] tₖ.
     * Premise: scrutinee is a VariantVal. Step-rule — the fold transitions
     * by re-evaluating the matching handler body.
     */
    @requires(
        (
            _self: LCEval,
            _dataType: DataType,
            scrutinee: Value,
            _handlers: unknown[],
            _resultType: Type,
        ) => scrutinee instanceof VariantVal,
        {
            rule: "E-Fold",
            role: "premise",
            formula: "scrutinee : Cₖ(vⱼ) (variant arm) ∨ scrutinee : TokenVal (pattern arm)",
            type: "τ",
        },
    )
    @ensures(
        () => true,
        { rule: "E-Fold", role: "conclusion", formula: "result : w", type: "τ" },
    )
    protected fold(
        _dataType: DataType,
        _scrutinee: Value,
        _handlers: (
            | { kind: "variant"; variantName: string; bindings: string[]; body: Value }
            | { kind: "pattern"; patternSource: string; body: Value }
        )[],
        _resultType: Type,
    ): Value {
        throw new Error("LCEval.fold: unreachable — foldProd is overridden")
    }

    /**
     * E-Unfold: unfold [T] s {oⱼ → gⱼ} ⇓ codata value. No premises — an
     * unfold is always a value (value-rule). The generators are stored as
     * spans for lazy re-evaluation.
     */
    @ensures(
        (_self: LCEval, _args: [CodataType, Value, unknown[], Type], _old, result: Value) =>
            result instanceof SpanCodataVal,
        { rule: "E-Unfold", role: "conclusion", formula: "result : codataVal" },
    )
    protected unfold(
        _codataType: CodataType,
        _seed: Value,
        _generators: { observerName: string; body: Value }[],
        _seedType: Type,
    ): Value {
        throw new Error("LCEval.unfold: unreachable — unfoldProd is overridden")
    }

    /**
     * E-TAbs: a type abstraction is a value (type erasure — no evaluation
     * needed). No premises — value-rule. The `production` key links this
     * rule to the `typeAbsProd` production (which is NOT overridden in
     * LCEval, so the linkage comes from contract metadata instead of
     * `@rule({ rule: ... })` on the production).
     */
    @ensures(
        () => true,
        {
            rule: "E-TAbs",
            role: "conclusion",
            formula: "result : Λα<:σ. t",
            production: "typeAbsProd",
        },
    )
    protected typeAbs(_tyVar: string, _bound: Type, _body: Value): Value {
        // E-TAbs: type abstraction is a value (no evaluation needed).
        // The body was parsed under a PLACEHOLDER env (via extendCtx), so
        // _body may contain PlaceholderValue objects for type-variable
        // references. This is fine — type abstractions are erased at runtime,
        // and the body is only re-evaluated via _forward when the type
        // abstraction is applied (typeApp returns the body directly).
        return _body
    }

    /**
     * E-TApp: (Λα<:σ. t) [τ] → [α ↦ τ] t. Premise: body is a value (the
     * type abstraction's evaluated body). Step-rule — type erasure returns
     * the body directly. The `production` key links this rule to the
     * `typeAppProd` production (not overridden in LCEval).
     */
    @requires(
        () => true,
        { rule: "E-TApp", role: "premise", formula: "body : Λα<:σ. t", type: "τ" },
    )
    @ensures(
        () => true,
        {
            rule: "E-TApp",
            role: "conclusion",
            formula: "result : t[α:=τ]",
            type: "τ",
            production: "typeAppProd",
        },
    )
    protected typeApp(body: Value, _argType: Type): Value {
        // E-TApp: (Λα<:σ. t) [τ] → [α ↦ τ] t
        // Type erasure: evaluate the body directly (types erased at runtime).
        return body
    }

    /**
     * E-Cofold: cofold [T] (unfold [T] s {oⱼ → gⱼ}) {oⱼ(xⱼ) → t} →
     * [xⱼ ↦ gⱼ(s)] t. Premise: scrutinee is a SpanCodataVal. Step-rule —
     * the cofold transitions by running generators then re-evaluating the
     * handler body.
     */
    @requires(
        (
            _self: LCEval,
            _codataType: CodataType,
            scrutinee: Value,
            _handler: unknown,
            _resultType: Type,
        ) => scrutinee instanceof SpanCodataVal,
        { rule: "E-Cofold", role: "premise", formula: "scrutinee : codataVal", type: "τ" },
    )
    @ensures(
        () => true,
        { rule: "E-Cofold", role: "conclusion", formula: "result : w", type: "τ" },
    )
    protected cofold(
        _codataType: CodataType,
        _scrutinee: Value,
        _handler: { observerName: string; bindings: string[]; body: Value },
        _resultType: Type,
    ): Value {
        throw new Error("LCEval.cofold: unreachable — cofoldProd is overridden")
    }

    /**
     * E-Op: op(v₁, ..., vₙ) → def(op) v₁ ... vₙ. Premise: the operation is
     * declared in Ω and the arguments are values. Step-rule — the application
     * transitions by applying the definition. The `production` key links this
     * rule to the `opProd` production (which is overridden above with
     * `@rule({ rule: "E-Op", production: "opProd" })`).
     */
    @requires(
        (_self: LCEval, opName: string, _args: Value[]) =>
            _self.opRegistry.lookup(opName) !== undefined,
        { rule: "E-Op", role: "premise", formula: "op ∈ Ω  ∧  args : v₁...vₙ", type: "τ" },
    )
    @ensures(
        () => true,
        { rule: "E-Op", role: "conclusion", formula: "result : w", type: "τ" },
    )
    protected opApp(_opName: string, _args: Value[]): Value {
        throw new Error("LCEval.opApp: unreachable — opProd is overridden")
    }

    /**
     * E-Token: `Ident` resolving to a registered `DataType` evaluates
     * to the matched token — the raw text as a `TokenVal`. The token is an
     * axiom of the operational semantics (lc.md §2.3): no subterm evaluation,
     * the value IS the matched text.
     */
    protected matchedToken(dataTypeName: string, text: string): Value {
        return new TokenVal(dataTypeName, text)
    }

    /**
     * E-Pattern: `match("p")` evaluates to the matched token — the pattern's
     * CANONICAL source as a `TokenVal` of the pattern-matched type. The token
     * is an axiom of the operational semantics (lc.md §1): no subterm
     * evaluation, the value IS the carried text. The text here is the
     * canonical pattern source (`patternToString` — the declared pattern's
     * identity, lifted one level from the bare token atom's text = name): the
     * token names the DECLARED pattern, so two spellings of one AST introduce
     * equal tokens (`size()` included — the canonical source's length), and
     * the token's text re-parses to the very pattern it was introduced with.
     * A later revision introducing real matched text would extend the form,
     * not this value shape.
     *
     * Value-rule (no premises — the premises on the pattern are enforced by
     * the base `patternMatchProd` gate, not Γ/ρ judgments), like E-Lam and
     * E-Unfold: the conclusion is the token value. The production is NOT
     * overridden — the inherited base production runs unchanged (its virtual
     * `matchedPattern` dispatches to the implementation below), so the gate
     * lives in exactly one place and the checker (which shares the same base
     * production) and this evaluator can never diverge. The rule-model
     * linkage comes from the contract's `production` key — the mechanism
     * E-TAbs/E-TApp use for their non-overridden productions.
     *
     * The action is only reached on the verified path — the base production
     * commits its conclusion via `epsilon` after the gate — so this contract
     * encodes both the conclusion the rule model reads and the production
     * linkage.
     */
    @ensures(
        (_self: LCEval, _args: [string, string, string], _old, result: Value) =>
            result instanceof TokenVal,
        {
            rule: "E-Pattern",
            role: "conclusion",
            formula: "result : TokenVal",
            production: "patternMatchProd",
        },
    )
    protected matchedPattern(
        dataTypeName: string,
        patternSource: string,
        _rawSource: string,
    ): Value {
        return new TokenVal(dataTypeName, patternSource, "pattern")
    }
}
