/**
 * LC Law Derivation — the `derivable` regime's discharge engine.
 *
 * See _docs/theory/type-algebra.md §6 (the BMF derivation design) and
 * _docs/theory/semantics.md §5.4 (the `derivable` regime row).
 *
 * The `derivable` regime proves a law claim by **induction over the fold
 * schema**: the induction motive is the law's own axiom schema (the functor
 * fixes the motive), the case structure is read off the carrier's variants,
 * and every case closes with a bounded, search-free move sequence —
 * fold-computation unfolding (E-Fold at the symbolic level, from checked Ω
 * definitions), congruence, the induction hypothesis at the recursion
 * positions, and one-step axiom instantiation from E's
 * `primitive`/`discharged` laws. A claim whose every case closes is
 * **derivable**: a real proof, installed `discharged` (like exhaustion —
 * derivation is proof, not screen).
 *
 * The engine is deliberately NOT a prover: no search, no backtracking, no
 * unification. Each case gets a fixed-priority move sequence under a step
 * budget; a claim the budget cannot close is honestly not derivable and
 * stays screened. Soundness is by construction (every move is either the
 * language's own fold computation rule, an installed unconditional axiom,
 * the structural induction hypothesis, or congruence); incompleteness is
 * the honest residual the provenance ladder already names.
 *
 * ## The derivable fragment (the characterization)
 *
 * Operationally: a claim is derivable iff this engine closes every schema
 * instance's every variant case within the budgets. Stated as a test:
 *
 * 1. **Definition shape** — `def(op)` is a lambda chain whose body is a
 *    `fold [T]` whose scrutinee is one of the lambda's parameters (the
 *    recursion axis). `unfold`/`cofold`/`let`/type abstractions, and folds
 *    with compound scrutinees, are outside the fragment (loud
 *    shape-rejection naming the construct — never a silent mis-read).
 * 2. **Case structure** — one case per variant of the axis carrier
 *    (`allVariants()`); a case's Family-typed (μ-bound) fields carry the
 *    the IH; non-Self data-typed fields do not (the direct-recursion
 *    boundary — the same depth-≤ 1 chain rule the ∂T machinery states).
 * 3. **Closure** — every schema instance (both directions for
 *    argument-taking kinds) closes within the move set and budgets.
 *
 * Sound (each closed derivation is a real proof) and deliberately
 * incomplete (budget-bounded, syntactic axiom matching, single-axis
 * induction): a claim that does not close routes to the residual screen,
 * which keeps its falsification power.
 *
 * ## Scope boundaries (first cut)
 *
 * - **Intrinsic kinds only** — `associative`, `commutative`, `identity`,
 *   `idempotent`, `involutory`, `absorbing`. `distributive` routes
 *   residual (a two-op schema doubles the skeleton; the single-op engine
 *   lands first).
 * - **Pattern carriers** — outside the fragment (no variant cases to
 *   skeletonize; their honest routes are machineFinite sub-space sweeps or
 *   the screen).
 * - **One induction axis** — the outermost fold's scrutinee parameter.
 *   Claims needing nested/double induction (the canonical example:
 *   `commutative` on Nat's `add`) stay not-derivable — the fragment's
 *   honest edge.
 * - **Axiom base** — only `primitive`/`discharged` laws of the ops a
 *   claim's handlers reference. An `asserted` law is never an axiom step:
 *   using one would launder declaration risk into `discharged` (the
 *   derived law's soundness is relative to its axioms).
 * - **No type-level rewrites** — the move set is entirely term-level and
 *   individually sound; the Fiore–Leinster caution (type-algebra.md §6) is
 *   honored structurally: raw algebraic manipulations (subtraction/division
 *   tricks, seven-trees-in-one) have no representation in this engine.
 */

import type { Parser } from "@lapis-lang/lang-forma"

import {
    ARGUMENT_KINDS,
    type LawDecl,
    type LawKind,
    type LawProvenance,
    LawRegistry,
    RELATIONAL_KINDS,
    SCHEMA_VARIABLE_COUNT,
} from "./laws.ts"

import { type CheckedOpSig, OpRegistry } from "./ops.ts"

import { AbstractLC, type LCShape, TypeRegistry } from "./grammar.ts"

import { CodataType, DataType, FamilyType, Nothing, type Type, TypeEnv, Variant } from "./types.ts"

// ── The symbolic term AST ─────────────────────────────────────────────────────

/**
 * The symbolic term forms the derivation engine reads and rewrites.
 *
 * The engine's reader is a grammar subclass (`DerivationReader`) over the
 * SAME LC concrete-syntax productions (`grammar.ts`), with these terms as
 * semantic actions — not a hand-rolled syntax scan. Reading and evaluation
 * therefore agree by construction (the reader's productions ARE the
 * evaluator's productions). The term forms the fragment does not admit
 * (`let`, type abstraction, unfold, cofold, observation) are still
 * RECOGNIZED — their reader actions throw `DefinitionShapeError` naming
 * the construct, so a definition outside the fragment is rejected loudly
 * (never silently mis-read, which would be a soundness hole; never lost to
 * a bare parse rejection, which would lose the diagnostic).
 */
export type Term =
    | { readonly k: "var"; readonly name: string }
    | { readonly k: "lam"; readonly param: string; readonly body: Term }
    | { readonly k: "app"; readonly fn: Term; readonly arg: Term }
    /** A named operation application from Ω — the law-relevant form. */
    | { readonly k: "op"; readonly name: string; readonly args: readonly Term[] }
    /** A variant construction `Cᵢ(tⱼ…)` — the fold-computation redex head. */
    | { readonly k: "con"; readonly variant: string; readonly args: readonly Term[] }
    /** The fold form — the engine's unfold move's subject. */
    | {
        readonly k: "fold"
        readonly carrier: string
        readonly scrutinee: Term
        readonly handlers: readonly {
            readonly variantName: string
            readonly bindings: readonly string[]
            readonly body: Term
        }[]
    }
    /** An observation `t.o` — the codata elimination (rejected by the reader). */
    | { readonly k: "obs"; readonly scrutinee: Term; readonly observer: string }

/** Syntactic term equality — the reflexivity/congruence moves' comparison. */
function termEquals(a: Term, b: Term): boolean {
    if (a.k !== b.k) return false
    switch (a.k) {
        case "var":
            return a.name === (b as typeof a).name
        case "lam":
            return a.param === (b as typeof a).param &&
                termEquals(a.body, (b as typeof a).body)
        case "app":
            return termEquals(a.fn, (b as typeof a).fn) &&
                termEquals(a.arg, (b as typeof a).arg)
        case "op":
            return a.name === (b as typeof a).name &&
                a.args.length === (b as typeof a).args.length &&
                a.args.every((arg, i) => termEquals(arg, (b as typeof a).args[i]!))
        case "con":
            return a.variant === (b as typeof a).variant &&
                a.args.length === (b as typeof a).args.length &&
                a.args.every((arg, i) => termEquals(arg, (b as typeof a).args[i]!))
        case "fold":
            return a.carrier === (b as typeof a).carrier &&
                termEquals(a.scrutinee, (b as typeof a).scrutinee) &&
                a.handlers.length === (b as typeof a).handlers.length &&
                a.handlers.every((h, i) =>
                    h.variantName === (b as typeof a).handlers[i]!.variantName &&
                    h.bindings.join(",") ===
                        (b as typeof a).handlers[i]!.bindings.join(",") &&
                    termEquals(h.body, (b as typeof a).handlers[i]!.body)
                )
        case "obs":
            return a.observer === (b as typeof a).observer &&
                termEquals(a.scrutinee, (b as typeof a).scrutinee)
    }
}

/** Render a term back to LC-like source (error messages, open-case reports). */
export function renderTerm(term: Term): string {
    switch (term.k) {
        case "var":
            return term.name
        case "lam":
            return `\\${term.param}:_ . ${renderTerm(term.body)}`
        case "app":
            return `(${renderTerm(term.fn)} ${renderTerm(term.arg)})`
        case "op":
            return `${term.name}(${term.args.map(renderTerm).join(", ")})`
        case "con":
            return term.args.length > 0
                ? `${term.variant}(${term.args.map(renderTerm).join(", ")})`
                : `${term.variant}()`
        case "fold":
            return `fold [${term.carrier}] ${renderTerm(term.scrutinee)} {${
                term.handlers
                    .map((h) => `${h.variantName}(${h.bindings.join(" ")}) → ${renderTerm(h.body)}`)
                    .join(", ")
            }}`
        case "obs":
            return `${renderTerm(term.scrutinee)}.${term.observer}`
    }
}

/**
 * Substitute a term for a variable name. Capture-avoiding by the reader's
 * discipline: the reader's handler bodies are closed over the case
 * pattern's field bindings, and the engine's substitutions bind field
 * names — a lambda in a body shadowing a substituted name is the only
 * interaction, handled by the shield here.
 */
function substVar(term: Term, name: string, replacement: Term): Term {
    switch (term.k) {
        case "var":
            return term.name === name ? replacement : term
        case "lam":
            return term.param === name ? term : {
                k: "lam",
                param: term.param,
                body: substVar(term.body, name, replacement),
            }
        case "app":
            return {
                k: "app",
                fn: substVar(term.fn, name, replacement),
                arg: substVar(term.arg, name, replacement),
            }
        case "op":
            return {
                k: "op",
                name: term.name,
                args: term.args.map((arg) => substVar(arg, name, replacement)),
            }
        case "con":
            return {
                k: "con",
                variant: term.variant,
                args: term.args.map((arg) => substVar(arg, name, replacement)),
            }
        case "fold":
            return {
                k: "fold",
                carrier: term.carrier,
                scrutinee: substVar(term.scrutinee, name, replacement),
                handlers: term.handlers.map((h) => ({
                    variantName: h.variantName,
                    bindings: h.bindings,
                    body: h.bindings.includes(name) ? h.body : substVar(h.body, name, replacement),
                })),
            }
        case "obs":
            return {
                k: "obs",
                scrutinee: substVar(term.scrutinee, name, replacement),
                observer: term.observer,
            }
    }
}

/** Collect a term's free op-application names (the axiom base's scan). */
function freeOps(term: Term, into: Set<string> = new Set()): Set<string> {
    switch (term.k) {
        case "var":
            return into
        case "con":
            for (const arg of term.args) freeOps(arg, into)
            return into
        case "lam":
            return freeOps(term.body, into)
        case "app":
            freeOps(term.fn, into)
            return freeOps(term.arg, into)
        case "op":
            into.add(term.name)
            for (const arg of term.args) freeOps(arg, into)
            return into
        case "fold":
            freeOps(term.scrutinee, into)
            for (const h of term.handlers) freeOps(h.body, into)
            return into
        case "obs":
            return freeOps(term.scrutinee, into)
    }
}

// ── The definition reader (a grammar subclass over the LC syntax) ────────────

/**
 * The shape the derivation engine reads out of a fold-built operation
 * definition (the fragment's admitted form).
 */
export interface DefShape {
    /** The definition's lambda parameters, in order. */
    params: readonly { readonly name: string; readonly type: Type }[]
    /** The outermost fold's scrutinee parameter's index — the recursion axis. */
    axis: number
    /** The axis carrier (the fold's annotated type, resolved from Ω). */
    carrier: DataType
    /** One handler per case; the field bindings carry the recursion marks
     * (a Family-typed field is the μ-bound occurrence — it carries the
     * induction hypothesis). */
    handlers: readonly {
        readonly variantName: string
        readonly variant: Variant
        readonly bindings: readonly {
            readonly name: string
            readonly carriesIH: boolean
        }[]
        readonly body: Term
    }[]
}

/** A definition-shape rejection: the offending construct, named. */
export class DefinitionShapeError extends Error {
    constructor(
        readonly definition: string,
        reason: string,
    ) {
        super(reason)
        this.name = "DefinitionShapeError"
    }
}

/** The reader's parse shape: expr = Term, atom = Term. */
interface ReaderShape extends LCShape {
    expr: Term
    atom: Term
}

/**
 * The derivation reader: the LC grammar's concrete syntax with symbolic
 * `Term` semantic actions.
 *
 * Reuses `AbstractLC`'s productions verbatim (the reader and the evaluator
 * parse the same syntax — the reader/evaluator agreement the plan pins is
 * structural), with actions that BUILD terms instead of checking or
 * evaluating. The Ω gate (`opProd`) resolves operation names from the
 * registry the caller binds, exactly as the evaluator's does — the reader's
 * op recognition IS the evaluator's (no re-scan, no drift).
 */
class DerivationReader extends AbstractLC<ReaderShape> {
    constructor(registry: TypeRegistry, omega: OpRegistry) {
        super()
        this.setRegistry(registry)
        this.setOpRegistry(omega)
    }

    override start(): Parser<Term> {
        return this.exprProd(new TypeEnv())
    }

    /** Read one LC source fragment to a symbolic `Term` (singleton forest). */
    read(source: string): Term | undefined {
        const results = [...this._parseWith(source, this.exprProd(new TypeEnv()))]
        return results.length === 1 ? results[0] : undefined
    }

    // ── Semantic actions: build terms ────────────────────────────────────────

    protected override lam(param: string, _type: Type, body: Term): Term {
        return { k: "lam", param, body }
    }

    protected override app(fn: Term, arg: Term): Term {
        return { k: "app", fn, arg }
    }

    protected override let_(
        _name: string,
        _type: Type,
        _def: Term,
        _body: Term,
    ): Term {
        throw new DefinitionShapeError("", "let-binding (`let x:σ = t in u`)")
    }

    protected override varRef(name: string, _ctx: unknown): Term {
        return { k: "var", name }
    }

    protected override paren(e: Term): Term {
        return e
    }

    protected override variantCon(name: string, args: Term[]): Term {
        return { k: "con", variant: name, args }
    }

    protected override obs(_scrutinee: Term, observerName: string): Term {
        throw new DefinitionShapeError(
            "",
            `observation (postfix \`.${observerName}\` — codata elimination)`,
        )
    }

    protected override fold(
        dataType: DataType,
        scrutinee: Term,
        handlers: { variantName: string; bindings: string[]; body: Term }[],
        _resultType: Type,
    ): Term {
        return {
            k: "fold",
            carrier: dataType.name,
            scrutinee,
            handlers: handlers.map((h) => ({
                variantName: h.variantName,
                bindings: h.bindings,
                body: h.body,
            })),
        }
    }

    protected override unfold(
        _codataType: CodataType,
        _seed: Term,
        _generators: { observerName: string; body: Term }[],
        _seedType: Type,
    ): Term {
        throw new DefinitionShapeError("", "unfold (an anamorphism)")
    }

    protected override cofold(
        _codataType: CodataType,
        _scrutinee: Term,
        _handler: { observerName: string; bindings: string[]; body: Term },
        _resultType: Type,
    ): Term {
        throw new DefinitionShapeError("", "cofold (codata elimination)")
    }

    protected override typeAbs(tyVar: string, _bound: Type, _body: Term): Term {
        throw new DefinitionShapeError(
            "",
            `type abstraction (\`^${tyVar} <: σ . t\` — polymorphism)`,
        )
    }

    protected override typeApp(_body: Term, argType: Type): Term {
        throw new DefinitionShapeError("", `type application (\`t [${argType}]\`)`)
    }

    protected override opApp(opName: string, args: Term[]): Term {
        return { k: "op", name: opName, args }
    }

    protected override matchedToken(dataTypeName: string, _text: string): Term {
        throw new DefinitionShapeError(
            "",
            `matched token (\`${dataTypeName}\` — a pattern-type atom)`,
        )
    }
}

/**
 * The fragment-rejected constructs, as source lexemes: each entry pairs a
 * keyword/lexeme with the construct's diagnostic (the loud shape error). A
 * lexeme occurrence in the definition's source names the offending construct
 * — the parse driver swallows the reader action's throw, so the pre-scan
 * preserves the diagnostic on the empty-forest path (the ONLY path that
 * consults it — a legal definition containing a keyword-shaped identifier
 * parses fine and never reaches the scan). Word-bounded on both sides (an
 * identifier containing a keyword never matches — `unfold` inside
 * `unfolded` is not the form).
 */
const REJECTED_CONSTRUCTS: readonly (readonly [string, string])[] = [
    ["unfold", "unfold (an anamorphism)"],
    ["cofold", "cofold (codata elimination)"],
    ["let", "let-binding (`let x:σ = t in u`)"],
    ["^", "type abstraction (`^α<:σ. t` — polymorphism)"],
]

/** Whether a source contains the lexeme as a word (bounded on both sides). */
function scanConstruct(source: string, needle: string): boolean {
    if (!source.includes(needle)) return false
    for (let i = source.indexOf(needle); i >= 0; i = source.indexOf(needle, i + 1)) {
        const before = i === 0 ? " " : source[i - 1]!
        const after = i + needle.length >= source.length ? " " : source[i + needle.length]!
        const boundary = (c: string): boolean => !/[a-zA-Z0-9_]/.test(c)
        if (boundary(before) && boundary(after)) return true
    }
    return false
}

/**
 * Read an operation's definition into a `DefShape` (the fragment's admitted
 * form), or throw `DefinitionShapeError` naming the offending construct.
 *
 * The admitted form: a lambda chain over the declared parameters, whose
 * body is a `fold [T]` whose scrutinee is one of the lambda's parameters
 * (the recursion axis), one handler per variant of the axis carrier.
 * Anything else — unfold, cofold, let, type abstraction, a compound fold
 * scrutinee, a missing handler, a lambda chain not covering the declared
 * parameters, a non-μ axis carrier — is a shape error.
 *
 * @throws DefinitionShapeError when the definition is outside the fragment.
 */
export function readDefShape(
    op: CheckedOpSig,
    registry: TypeRegistry,
    omega: OpRegistry,
): DefShape {
    const reader = new DerivationReader(registry, omega)
    let term: Term | undefined
    try {
        term = reader.read(op.definition)
    } catch (e) {
        if (e instanceof DefinitionShapeError) {
            throw new DefinitionShapeError(op.definition, e.message)
        }
        throw e
    }
    if (term === undefined) {
        // The parse yielded nothing. FIRST the rejected-construct pre-scan:
        // the parse driver swallows semantic-action throws (a rejected form's
        // action throw collapses that parse branch), so a definition using a
        // rejected construct surfaces as an empty forest rather than the
        // action's loud error — the pre-scan names the construct for the
        // diagnostic. The reader governs every ADMITTED shape; the pre-scan
        // only supplies the diagnostic the driver loses, and only when the
        // parse already failed (a legal definition containing a keyword-
        // shaped identifier still parses and never reaches this arm).
        for (const [needle, construct] of REJECTED_CONSTRUCTS) {
            if (scanConstruct(op.definition, needle)) {
                throw new DefinitionShapeError(op.definition, construct)
            }
        }
        throw new DefinitionShapeError(
            op.definition,
            "the definition does not parse as LC source (the reader and the " +
                "grammars disagree — routed residual, never mis-read)",
        )
    }

    // Peel the lambda chain, collecting the parameters. The parameter
    // TYPES come from the signature (`op.paramTypes`) — Ω's declaration is
    // the authority on what each parameter carries (well-formedness has
    // already checked the definition types as `paramTypes → resultType`, so
    // the chain's order matches the signature's order).
    const paramNames: string[] = []
    let body = term
    while (body.k === "lam") {
        paramNames.push(body.param)
        body = body.body
    }
    const params: { name: string; type: Type }[] = paramNames.map((name, i) => ({
        name,
        type: op.paramTypes[i]!,
    }))

    if (params.length !== op.paramTypes.length) {
        throw new DefinitionShapeError(
            op.definition,
            `the definition has ${params.length} lambda parameter(s), but the ` +
                `signature declares ${op.paramTypes.length} — the fragment's ` +
                `definitions are lambda chains over the declared parameters`,
        )
    }

    // The body must be a fold whose scrutinee is one of the parameters.
    if (body.k !== "fold") {
        throw new DefinitionShapeError(
            op.definition,
            `the definition's body is a ${body.k} term, not a fold — the ` +
                `fragment admits fold-built definitions (the recursion axis ` +
                `must be a fold's scrutinee)`,
        )
    }
    if (body.scrutinee.k !== "var") {
        throw new DefinitionShapeError(
            op.definition,
            `the fold's scrutinee is a ${body.scrutinee.k} term, not a ` +
                `parameter — the recursion axis must be a parameter ` +
                `(a compound scrutinee has no induction axis)`,
        )
    }
    const axis = params.findIndex((p) => p.name === (body.scrutinee as { name: string }).name)
    if (axis < 0) {
        throw new DefinitionShapeError(
            op.definition,
            `the fold's scrutinee "${body.scrutinee.name}" is not one of the ` +
                `definition's parameters — the recursion axis must be a ` +
                `parameter (free scrutinees are outside the fragment)`,
        )
    }

    // The axis carrier: the signature's declared type is the authority (Ω
    // types the operation; the fold's annotation agrees by well-formedness).
    const carrier = op.paramTypes[axis]
    if (!(carrier instanceof DataType)) {
        throw new DefinitionShapeError(
            op.definition,
            `the axis parameter's carrier ${carrier} is not a μ-type — ` +
                `pattern carriers have no variant cases to skeletonize ` +
                `(their routes are machineFinite sub-space sweeps or the screen)`,
        )
    }

    // Handlers: one per variant of the axis carrier, field bindings matched
    // against the variant's fields for the recursion marks.
    const handlers = body.handlers.map((h) => {
        const variant = carrier.findVariant(h.variantName)
        if (!variant) {
            throw new DefinitionShapeError(
                op.definition,
                `handler for "${h.variantName}", which is not a variant of the ` +
                    `axis carrier ${carrier.name}`,
            )
        }
        const bindings = h.bindings.map((name, i) => ({
            name,
            carriesIH: (variant.fields[i]?.type ?? Nothing) instanceof FamilyType,
        }))
        return { variantName: h.variantName, variant, bindings, body: h.body }
    })
    const missing = carrier.allVariants().filter((v) =>
        !handlers.some((h) => h.variantName === v.name)
    )
    if (missing.length > 0) {
        throw new DefinitionShapeError(
            op.definition,
            `no handler for variant(s) ${missing.map((v) => v.name).join(", ")} ` +
                `of the axis carrier ${carrier.name} — the skeleton needs a ` +
                `case per variant`,
        )
    }

    return { params, axis, carrier, handlers }
}

/**
 * The lambda-chain-stripped body of a definition, read silently (no
 * throws): the shape gate already admitted the TARGET op, but a CALLED
 * op's definition may itself be outside the fragment — then its
 * applications stay stuck (unsubstituted) and closure fails honestly if
 * the obligation needs them. The parameter names ride along — the same
 * parse supplies both (the E-Op substitution needs the chain's names).
 */
function readDefinitionSilent(
    op: CheckedOpSig,
    registry: TypeRegistry,
    omega: OpRegistry,
): { paramNames: readonly string[]; body: Term } | undefined {
    const reader = new DerivationReader(registry, omega)
    try {
        let term = reader.read(op.definition)
        if (term === undefined) return undefined
        const paramNames: string[] = []
        while (term.k === "lam") {
            paramNames.push(term.param)
            term = term.body
        }
        return { paramNames, body: term }
    } catch {
        return undefined
    }
}

// ── The symbolic schema instantiation (the skeleton's motive) ────────────────

/**
 * Per-kind schema variable names in operand order (lc.md §7.2) — the
 * symbolic counterpart of `law_checking.ts`'s `SCHEMA_NAMES` (the same
 * names, shared source: the axiom table in lc.md §7.2; the two stay in
 * sync because both render the same schema shapes, and the
 * cross-module coherence tests pin it).
 */
export const SCHEMA_VARIABLE_NAMES: Record<LawKind, readonly string[]> = {
    associative: ["a", "b", "c"],
    commutative: ["a", "b"],
    identity: ["a"],
    idempotent: ["a"],
    involutory: ["a"],
    absorbing: ["a"],
    distributive: ["a", "b", "c"],
}

/**
 * The per-kind axiom schema's symbolic shapes, mirroring
 * `law_checking.ts`'s `instantiate` (the value-level source-string builder)
 * and lc.md §7.2's axiom table. `f` is the target operation; the free
 * variables are the schema variables (bound by the case substitution);
 * `e`/`z` are substituted by the parsed argument term at instantiation.
 *
 * Argument-taking kinds contribute BOTH directions (lc.md §7.2) — the same
 * completeness rule the screen's `instantiate` applies.
 */
function schemaMotives(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    argument: Term | undefined,
): {
    readonly direction: "left" | "right" | undefined
    readonly left: Term
    readonly right: Term
}[] {
    const v = (name: string): Term => ({ k: "var", name })
    const fApp = (...args: Term[]): Term => ({ k: "op", name: op.name, args })

    switch (law.kind) {
        case "associative":
            return [{
                direction: undefined,
                left: fApp(fApp(v("a"), v("b")), v("c")),
                right: fApp(v("a"), fApp(v("b"), v("c"))),
            }]
        case "commutative":
            return [{
                direction: undefined,
                left: fApp(v("a"), v("b")),
                right: fApp(v("b"), v("a")),
            }]
        case "identity":
            // Both directions: f(e, a) ≡ a AND f(a, e) ≡ a — the same
            // completeness rule the screen's instantiate applies.
            return [
                { direction: "left", left: fApp(argument!, v("a")), right: v("a") },
                { direction: "right", left: fApp(v("a"), argument!), right: v("a") },
            ]
        case "idempotent":
            return [{
                direction: undefined,
                left: fApp(v("a"), v("a")),
                right: v("a"),
            }]
        case "involutory":
            return [{
                direction: undefined,
                left: fApp(fApp(v("a"))),
                right: v("a"),
            }]
        case "absorbing":
            // Both directions: f(z, a) ≡ z AND f(a, z) ≡ z.
            return [
                { direction: "left", left: fApp(argument!, v("a")), right: argument! },
                { direction: "right", left: fApp(v("a"), argument!), right: argument! },
            ]
        case "distributive":
            // Deferred (the plan's D9): the two-op schema routes residual —
            // the gate refuses relational kinds, so this arm is unreachable
            // through `deriveLaw`; kept for exhaustiveness.
            return []
    }
}

// ── The bounded discharger ────────────────────────────────────────────────────

/**
 * The unfold-fixpoint budget per case (type-algebra.md §6's bounded
 * engine): how many computation steps (E-Fold unfolds, E-Op substitutions)
 * one obligation's normalization may perform. Unfold grows terms (a fold
 * re-embeds its handlers), so the budget bounds every case absolutely —
 * the engine terminates on all inputs by construction.
 */
export const MAX_UNFOLDS_PER_CASE = 64

/**
 * The axiom+IH budget per case: how many non-computational rewrites (IH
 * applications + axiom steps) a case's closure may consume. A claim the
 * budget cannot close is honestly not derivable (the fragment's edge).
 */
export const MAX_STEPS_PER_CASE = 8

/**
 * How a case's obligation closed — the certificate's per-case record.
 * `reflexivity` means computation (unfold) closed it outright; `IH` and
 * `axiom` name the rewrite that closed the residual after unfolding.
 */
export type CaseClosure =
    | { readonly closedBy: "reflexivity"; readonly steps: number }
    | { readonly closedBy: "IH"; readonly steps: number }
    | { readonly closedBy: "axiom"; readonly steps: number }

/** One axiom schema instance's skeleton: one case per axis variant. */
export interface DerivationInstance {
    /** The schema direction (argument-taking kinds instantiate two). */
    readonly direction: "left" | "right" | undefined
    /** Per-axis-variant case, with how it closed. */
    readonly cases: readonly {
        readonly variant: string
        readonly closure: CaseClosure
    }[]
}

/**
 * The derivation certificate (the plan's D8): the visible provenance of a
 * `derivable`-discharged law — which cases closed how, and which axioms the
 * proof consumed (each `primitive`/`discharged` — the trust chain).
 */
export interface DerivationCertificate {
    /** The schema instances (one per direction for argument-taking kinds). */
    readonly instances: readonly DerivationInstance[]
    /** Every axiom consumed, with its provenance (all primitive|discharged). */
    readonly axiomsUsed: readonly {
        readonly op: string
        readonly kind: LawKind
        readonly provenance: LawProvenance
    }[]
    /**
     * The belt-and-braces screen's checked-instance count (the concrete
     * redundancy D7 mandates; `undefined` when the screen declined).
     */
    readonly screened?: number
}

/**
 * A failed derivation: the claim is not in the derivable fragment. The
 * report names the first open case (the honest edge) — a DECLINE, not a
 * falsification: the claim proceeds to the residual screen.
 */
export interface NotDerivable {
    readonly derivable: false
    /** The schema instance that stayed open. */
    readonly direction: "left" | "right" | undefined
    /** The variant whose case could not close. */
    readonly variant: string
    /** The obligation sides that stayed open, rendered. */
    readonly open: { readonly left: string; readonly right: string }
    /** Why the case stayed open (the failed move's reason). */
    readonly reason: string
}

/** The derivation outcome: a certificate (closed) or the open-case report. */
export type DerivationResult = DerivationCertificate | NotDerivable

/** An axiom candidate: one installed eligible law of a called operation. */
interface AxiomSource {
    readonly op: CheckedOpSig
    readonly law: LawDecl
}

/** An obligation pair to prove equal (the discharger's work unit). */
interface Obligation {
    left: Term
    right: Term
}

/**
 * The E-Fold computation rule at the symbolic level: unfold ONE fold term
 * whose scrutinee is a variant construction.
 *
 * `fold [T] Cᵢ(vⱼ…) {…}` unfolds to handler body `tᵢ` with field variables
 * bound to `vⱼ` and each RECURSIVE-field variable bound to the fold
 * RE-APPLIED to the corresponding subterm — the same substitution E-Fold
 * performs on concrete values (`evalFold`'s binding rule: a recursive field
 * binds the *folded* result), so the engine's rewriting and the evaluator
 * agree by construction.
 *
 * Returns the unfolded body, or `undefined` when the fold does not step
 * (the scrutinee is not a variant construction of the carrier, or no
 * handler matches — a stuck fold, which no move can close).
 */
function unfoldOne(fold: Extract<Term, { k: "fold" }>, registry: TypeRegistry): Term | undefined {
    if (fold.scrutinee.k !== "con") return undefined
    const carrier = registry.lookup(fold.carrier)
    if (!(carrier instanceof DataType)) return undefined
    const variant = carrier.findVariant(fold.scrutinee.variant)
    if (!variant) return undefined
    const handler = fold.handlers.find((h) => h.variantName === variant.name)
    if (!handler) return undefined

    // Bind the field variables: non-recursive fields bind the raw subterm;
    // Family fields (the μ-bound) bind the fold RE-APPLIED to the subterm
    // (E-Fold's vⱼ' = fold [T] vⱼ {Cᵢ → tᵢ} — the recursion continues
    // structurally).
    let body = handler.body
    for (let i = 0; i < variant.fields.length; i++) {
        const binding = handler.bindings[i]
        if (binding === undefined) continue
        const subterm: Term = fold.scrutinee.args[i] ?? { k: "var", name: "_" }
        const recurses = (variant.fields[i]?.type ?? Nothing) instanceof FamilyType
        const bound: Term = recurses
            ? {
                k: "fold",
                carrier: fold.carrier,
                scrutinee: subterm,
                handlers: fold.handlers,
            }
            : subterm
        body = substVar(body, binding, bound)
    }
    return body
}

/**
 * The E-Op computation rule at the symbolic level: apply a definition to
 * constructor-pattern operands.
 *
 * `op(v₁, …, vₙ)` with every `vᵢ` a constructor-pattern term (a closed
 * constructor spine, possibly over the case's field variables — a case
 * pattern is the symbolic counterpart of the VALUE the evaluator would
 * have) unfolds to the definition's body with the parameters substituted —
 * E-Op's definition application (`evalOp`: the definition's lambda chain
 * applied to the argument values leftmost). An op application over OPEN
 * schema variables stays: those are the obligations the IH/axiom moves
 * consume.
 */
function unfoldOpOne(
    opApp: Extract<Term, { k: "op" }>,
    registry: TypeRegistry,
    omega: OpRegistry,
): Term | undefined {
    // Each argument must SHALLOW-normalize to a pattern value (a constructor
    // shape over case variables). The normalization is shallow (not
    // leftmost-innermost full): a stuck fold's value depends on its
    // scrutinee's future value, so it is NOT a known value shape — an op
    // application with a stuck-fold operand stays an op application (the
    // evaluator would evaluate the operand first, and a stuck operand's
    // value is not known). Shallow = normalize step-by-step but stop at the
    // first sub-step where the whole term is already a pattern value (the
    // op applications INSIDE a stuck shape are not forced early).
    const args: Term[] = []
    for (const arg of opApp.args) {
        let current: Term = arg
        for (let i = 0; i < MAX_UNFOLDS_PER_CASE; i++) {
            if (isPatternValue(current)) break
            const stepped = stepOnce(current, registry, omega)
            if (stepped === undefined) break
            current = stepped
        }
        if (!isPatternValue(current)) return undefined
        args.push(current)
    }
    const definition = omega.lookup(opApp.name)
    if (!definition) return undefined
    const read = readDefinitionSilent(definition, registry, omega)
    if (read === undefined) return undefined
    const { paramNames, body } = read
    if (paramNames.length !== args.length) return undefined
    // Right-to-left substitution (later parameters first): the operand
    // for parameter i never mentions parameter names j > i by the chain's
    // structure, but a substitution's replacement containing a later
    // parameter's NAME (impossible here — operands are constructor
    // patterns over the case's variables, not the definition's) would be
    // shielded by substVar's lambda guard. Substitute in reverse order
    // for clarity and stability.
    let result = body
    for (let i = paramNames.length - 1; i >= 0; i--) {
        result = substVar(result, paramNames[i]!, args[i]!)
    }
    return result
}

/**
 * Whether a term is a constructor-pattern VALUE — the symbolic counterpart
 * of an argument value. The admitted shapes:
 *
 * - **Constructor spines** over pattern values: a case pattern's variables
 *   stand for the subvalues the case binds (E-Op applies definitions to
 *   VALUES; the symbolic level represents a value's shape).
 * - **Variables** — always (a case variable is the symbolic shape of the
 *   subvalue the case bound).
 * - **Op applications** — the definition's body with the operands
 *   substituted keeps the operands symbolic (they are values at evaluation
 *   time; the E-Fold scrutinee-first rule unfolds them when the fold
 *   fires). Without this, an outer op whose operand is an inner op
 *   application stays stuck while the mirrored side unfolds — the
 *   normalization loses symmetry.
 *
 * A FOLD term is deliberately NOT a pattern value: its value depends on
 * the scrutinee's future value (the evaluator evaluates the scrutinee
 * first; with an open scrutinee the value is not known). Blocking here
 * keeps op applications over stuck folds visible as op applications — the
 * axiom move then fires on the op shape itself (and treating a stuck fold
 * as a value would re-embed it into fold scrutinees, producing
 * fold-over-fold terms that can never step).
 */
function isPatternValue(term: Term): boolean {
    switch (term.k) {
        case "con":
            return term.args.every(isPatternValue)
        case "var":
            return true
        case "op":
            // An op application is a symbolic value: the E-Op substitution
            // is the definition's body with the operands substituted, and
            // the operands themselves stay symbolic (they are values at
            // evaluation time — the E-Fold scrutinee-first rule unfolds
            // them when the fold fires). Without this, an outer op whose
            // operand is an inner op application stays stuck while the
            // mirrored side unfolds — the normalization loses symmetry.
            return true
        case "fold":
            // A fold term is a stuck computation, not a value: its value
            // depends on the scrutinee's future value (the evaluator
            // evaluates the scrutinee first; with an open scrutinee the
            // value is not known). Blocking here keeps op applications over
            // stuck folds visible as op applications — the axiom move then
            // fires on the op shape itself.
            return false
        default:
            return false
    }
}

/**
 * Whether a term is a closed constructor spine (an E-Op substitutable
 * value): constructor applications over closed constructor spines. The
 * schema and case variables are NOT values (they are open), so a var never
 * substitutes.
 */
function isClosedConstructor(term: Term): boolean {
    switch (term.k) {
        case "con":
            return term.args.every(isClosedConstructor)
        default:
            return false
    }
}

/**
 * Normalize a term by repeatedly applying the computation rules (E-Fold
 * unfold, E-Op substitute) until none applies (fold-normal at the
 * computation level), bounded by `budget`. Returns `undefined` when the
 * budget exhausts (an incompleteness, never a hang).
 */
function normalize(
    term: Term,
    registry: TypeRegistry,
    omega: OpRegistry,
    budget: number,
): Term | undefined {
    let current = term
    let steps = 0
    for (;;) {
        const stepped = stepOnce(current, registry, omega)
        if (stepped === undefined) return current
        current = stepped
        steps++
        if (steps > budget) return undefined
    }
}

/**
 * Step a term once at the leftmost-innermost position where a computation
 * rule applies (E-Fold on a constructor-scrutinee fold; E-Op on a fully
 * closed op application; beta on an explicit lambda application). Returns
 * `undefined` when no rule applies.
 */
function stepOnce(
    term: Term,
    registry: TypeRegistry,
    omega: OpRegistry,
): Term | undefined {
    switch (term.k) {
        case "var":
            return undefined
        case "lam": {
            const body = stepOnce(term.body, registry, omega)
            return body === undefined ? undefined : { k: "lam", param: term.param, body }
        }
        case "app": {
            const fnNorm = stepOnce(term.fn, registry, omega)
            if (fnNorm !== undefined) return { k: "app", fn: fnNorm, arg: term.arg }
            const argNorm = stepOnce(term.arg, registry, omega)
            if (argNorm !== undefined) return { k: "app", fn: term.fn, arg: argNorm }
            // Beta-reduction: the evaluator's E-App applies a closure to an
            // argument. Symbolically: `(\x. body) arg` substitutes (the
            // reader's `app` form — op applications parse as `op`, never
            // bare application, so this is an explicit application).
            if (term.fn.k === "lam") {
                return substVar(term.fn.body, term.fn.param, term.arg)
            }
            return undefined
        }
        case "op": {
            // The unfold first: the evaluator applies the definition to the
            // operand values (E-OpArg → E-Op); an operand that is already a
            // symbolic value needs no further stepping. Only when the unfold
            // does not fire (a stuck operand — its value is not known) does
            // the engine step the args leftmost (their inner computation may
            // still make progress).
            const unfolded = unfoldOpOne(term, registry, omega)
            if (unfolded !== undefined) return unfolded
            for (let i = 0; i < term.args.length; i++) {
                const stepped = stepOnce(term.args[i]!, registry, omega)
                if (stepped !== undefined) {
                    const args = [...term.args]
                    args[i] = stepped
                    return { k: "op", name: term.name, args }
                }
            }
            return undefined
        }
        case "con":
            for (let i = 0; i < term.args.length; i++) {
                const stepped = stepOnce(term.args[i]!, registry, omega)
                if (stepped !== undefined) {
                    const args = [...term.args]
                    args[i] = stepped
                    return { k: "con", variant: term.variant, args }
                }
            }
            return undefined
        case "fold": {
            // E-Fold's scrutinee is evaluated first (the evaluator's
            // E-OpArg → E-Fold order): normalize the scrutinee, then fire on
            // a constructor scrutinee. A scrutinee that stays stuck (an op
            // application over an open variable, or a stuck fold) leaves the
            // whole fold stuck — the honest computation rule.
            //
            // Budget note: the scrutinee's normalization gets a FRESH budget
            // per fold, so a chain of nested folds can consume up to
            // budget² steps before the outer budget trips — termination
            // still holds (every term's step count is finite and strictly
            // decreasing along any single spine), but the bound is quadratic
            // in the nesting depth, not linear. The budgets are completeness
            // edges, not safety edges: exhaustion is an honest decline.
            const scrut = normalize(term.scrutinee, registry, omega, MAX_UNFOLDS_PER_CASE)
            if (scrut === undefined) return undefined
            if (scrut.k === "con") {
                return unfoldOne({ ...term, scrutinee: scrut }, registry)
            }
            if (!termEquals(scrut, term.scrutinee)) {
                return {
                    k: "fold",
                    carrier: term.carrier,
                    scrutinee: scrut,
                    handlers: term.handlers,
                }
            }
            return undefined
        }
        case "obs":
            return undefined
    }
}

/**
 * Apply the IH: for each claim instantiation at this case's recursion
 * variables, try to rewrite the obligation. A FULL syntactic match of one
 * side against an IH side replaces that side with the IH's other side (the
 * IH is an equality; either direction is sound). No unification, no partial
 * matching — the discipline that keeps the IH from fabricating proofs (the
 * misuse-guard test pins this).
 *
 * Returns the rewritten obligation, or `undefined` when no IH matches.
 */
function applyIH(
    left: Term,
    right: Term,
    ihPairs: readonly { readonly left: Term; readonly right: Term }[],
): Obligation | undefined {
    for (const pair of ihPairs) {
        if (termEquals(left, pair.left)) return { left: pair.right, right }
        if (termEquals(right, pair.left)) return { left, right: pair.right }
        if (termEquals(left, pair.right)) return { left: pair.left, right }
        if (termEquals(right, pair.right)) return { left, right: pair.left }
    }
    return undefined
}

/**
 * The IH move's second shape: match the NORMALIZED IH sides. The IH is an
 * equality of computations (`f(a, e) ≡ a`), so its sides unfold too — the
 * obligation's sides were normalized in step 2, and matching an unfolded
 * side against the IH's UN-normalized op shape would miss (the IH pair's
 * sides are normalized once here, then matched; the normalized pair is a
 * sound consequence of the IH by the computation rules' determinism).
 */
function applyIHNnormalized(
    left: Term,
    right: Term,
    ihPairs: readonly { readonly left: Term; readonly right: Term }[],
    registry: TypeRegistry,
    omega: OpRegistry,
): Obligation | undefined {
    const normalized: { left: Term; right: Term }[] = []
    for (const pair of ihPairs) {
        const l = normalize(pair.left, registry, omega, MAX_UNFOLDS_PER_CASE)
        const r = normalize(pair.right, registry, omega, MAX_UNFOLDS_PER_CASE)
        if (l === undefined || r === undefined) continue
        normalized.push({ left: l, right: r })
    }
    return applyIH(left, right, normalized)
}

/** The argument term of an argument-taking axiom law (read from source). */
function axiomArgument(
    law: Omit<LawDecl, "provenance">,
    registry: TypeRegistry,
    omega: OpRegistry,
): Term | undefined {
    if (!ARGUMENT_KINDS.includes(law.kind) || law.argument === undefined) return undefined
    const reader = new DerivationReader(registry, omega)
    try {
        const arg = reader.read(law.argument)
        if (arg === undefined) return undefined
        // Only a closed constructor argument instantiates syntactically (a
        // compound argument's shape depends on its free variables — outside
        // the fragment's syntactic matching).
        if (!isClosedConstructor(arg)) return undefined
        return arg
    } catch {
        return undefined
    }
}

/**
 * The symbolic axiom schema of ONE installed law (the axiom's op name in
 * the schema's `f` position), with the argument term instantiated.
 */
function axiomSchema(
    source: AxiomSource,
    registry: TypeRegistry,
    omega: OpRegistry,
): { readonly left: Term; readonly right: Term }[] {
    const argument = axiomArgument(source.law, registry, omega)
    if (ARGUMENT_KINDS.includes(source.law.kind) && argument === undefined) return []
    return schemaMotives(source.law, source.op, argument).map((m) => ({
        left: m.left,
        right: m.right,
    }))
}

/**
 * Rewrite an obligation by one axiom step: for each eligible axiom, render
 * its schema, then scan the obligation's subterm positions for a
 * schema-side match, rewriting the FIRST match to the schema's other side.
 * One step per call; the caller re-enters the move sequence
 * (reflexivity/congruence may then close).
 *
 * The direction is fixed by the match found (the axiom's ≡ is undirected;
 * the engine's rewrite direction is the one whose matched side determined
 * the rewrite).
 *
 * Returns the rewritten obligation, or `undefined` when no axiom applies.
 */
function applyAxiom(
    obligation: Obligation,
    axioms: readonly AxiomSource[],
    registry: TypeRegistry,
    omega: OpRegistry,
    onAxiom: (source: AxiomSource) => void,
): Obligation | undefined {
    for (const source of axioms) {
        for (const schema of axiomSchema(source, registry, omega)) {
            // Whole-side matches first (the schema side IS the obligation's
            // side), then subterm matches with ONE-WAY schema-var matching
            // (the schema variables — `a`, `b`, `c` — are patterns, matched
            // against the obligation's subterms; a deterministic first-order
            // one-way match, not search: each schema variable's binding is
            // forced by the first differing position, and an inconsistent
            // re-binding fails the match).
            const hit = rewriteWhole(obligation, schema.left, schema.right) ??
                rewriteWhole(obligation, schema.right, schema.left) ??
                axiomSubterm(obligation, schema)
            if (hit !== undefined) {
                onAxiom(source)
                return hit
            }
        }
    }
    return undefined
}

/** A term's variable leaves (the schema patterns' instantiation targets). */
function collectVars(term: Term, into: Set<string>): void {
    switch (term.k) {
        case "var":
            into.add(term.name)
            return
        case "con":
            for (const arg of term.args) collectVars(arg, into)
            return
        case "lam":
            collectVars(term.body, into)
            return
        case "app":
            collectVars(term.fn, into)
            collectVars(term.arg, into)
            return
        case "op":
            for (const arg of term.args) collectVars(arg, into)
            return
        case "fold":
            collectVars(term.scrutinee, into)
            for (const h of term.handlers) collectVars(h.body, into)
            return
        case "obs":
            collectVars(term.scrutinee, into)
            return
    }
}

/** Substitute a whole binding map over a term (schema-var instantiation). */
function substAll(term: Term, bindings: ReadonlyMap<string, Term>): Term {
    let result = term
    for (const [name, replacement] of bindings) {
        result = substVar(result, name, replacement)
    }
    return result
}

/**
 * One-way match: does `pattern` (whose free variables are the schema
 * patterns) match `term`? Returns the variable bindings when it does — the
 * first differing position forces each binding, an inconsistent re-binding
 * fails the match. Deterministic, no backtracking: a first-order one-way
 * match, not unification, not search (the discipline that keeps the axiom
 * move mechanical). Only first-order shapes (constructor/op spines) match
 * structurally; other kinds compare syntactically.
 */
function matchPattern(
    pattern: Term,
    term: Term,
    vars: ReadonlySet<string>,
    bindings: Map<string, Term>,
): boolean {
    if (pattern.k === "var" && vars.has(pattern.name)) {
        const existing = bindings.get(pattern.name)
        if (existing !== undefined) {
            return termEquals(existing, term)
        }
        bindings.set(pattern.name, term)
        return true
    }
    if (pattern.k !== term.k) return false
    switch (pattern.k) {
        case "con": {
            const t = term as typeof pattern
            if (pattern.variant !== t.variant) return false
            if (pattern.args.length !== t.args.length) return false
            for (let i = 0; i < pattern.args.length; i++) {
                if (!matchPattern(pattern.args[i]!, t.args[i]!, vars, bindings)) return false
            }
            return true
        }
        case "op": {
            const t = term as typeof pattern
            if (pattern.name !== t.name) return false
            if (pattern.args.length !== t.args.length) return false
            for (let i = 0; i < pattern.args.length; i++) {
                if (!matchPattern(pattern.args[i]!, t.args[i]!, vars, bindings)) return false
            }
            return true
        }
        default:
            return termEquals(pattern, term)
    }
}

/**
 * Whether a schema side is a BARE variable (a single schema variable, no
 * constructor/op structure). As a subterm rewrite PATTERN such a side
 * matches every subterm — using it as `from` rewrites any subterm into the
 * side's other direction (e.g. `add(a, Zero) ≡ a` used backwards turns an
 * arbitrary subterm into `add(subterm, Zero)`), growing the obligation
 * instead of reducing it. Whole-side matching is unaffected (there `from`
 * must equal a whole obligation side exactly — no wildcard). The axiom
 * move therefore orients subterm rewrites only from a STRUCTURAL side to a
 * (possibly variable) side: `add(a, Zero) → a` fires, `a → add(a, Zero)`
 * does not.
 */
function isBareVariable(term: Term, vars: ReadonlySet<string>): boolean {
    return term.k === "var" && vars.has(term.name)
}

/** The subterm-level axiom rewrite: first match, either side, either direction,
 * with one-way schema-var matching (the schema variables instantiate). */
function axiomSubterm(
    obligation: Obligation,
    schema: { readonly left: Term; readonly right: Term },
): Obligation | undefined {
    const vars = new Set<string>()
    collectVars(schema.left, vars)
    collectVars(schema.right, vars)
    for (
        const [from, to] of [
            [schema.left, schema.right] as const,
            [schema.right, schema.left] as const,
        ]
    ) {
        // A bare-variable `from` side is a wildcard: it matches any subterm
        // and rewrites it into the schema's other side — an EXPANSION that
        // grows the obligation (and is selected before the useful forward
        // rewrite, burning the budget on growth). Skip it; the whole-side
        // rewrite already handled the exact-match case, and the forward
        // direction (structural → variable) is the subterm orientation the
        // engine uses. A schema with NO structural side (both sides bare
        // variables) contributes no subterm rewrite at all.
        if (isBareVariable(from, vars)) continue
        const hit = matchRewrite(obligation.left, from, to, vars)
        if (hit !== undefined) return { left: hit, right: obligation.right }
        const hitR = matchRewrite(obligation.right, from, to, vars)
        if (hitR !== undefined) return { left: obligation.left, right: hitR }
    }
    return undefined
}

/**
 * One axiom rewrite in a subterm tree: the FIRST subterm the schema-side
 * pattern matches (one-way, with schema-var instantiation) rewrites to the
 * schema's other side, instantiated by the match's bindings.
 */
function matchRewrite(
    term: Term,
    from: Term,
    to: Term,
    vars: ReadonlySet<string>,
): Term | undefined {
    const bindings = new Map<string, Term>()
    if (matchPattern(from, term, vars, bindings)) {
        return substAll(to, bindings)
    }
    switch (term.k) {
        case "var":
            return undefined
        case "lam": {
            const body = matchRewrite(term.body, from, to, vars)
            return body === undefined ? undefined : { k: "lam", param: term.param, body }
        }
        case "app": {
            const fn = matchRewrite(term.fn, from, to, vars)
            if (fn !== undefined) return { k: "app", fn, arg: term.arg }
            const arg = matchRewrite(term.arg, from, to, vars)
            return arg === undefined ? undefined : { k: "app", fn: term.fn, arg }
        }
        case "op":
            for (let i = 0; i < term.args.length; i++) {
                const arg = matchRewrite(term.args[i]!, from, to, vars)
                if (arg !== undefined) {
                    const args = [...term.args]
                    args[i] = arg
                    return { k: "op", name: term.name, args }
                }
            }
            return undefined
        case "con":
            for (let i = 0; i < term.args.length; i++) {
                const arg = matchRewrite(term.args[i]!, from, to, vars)
                if (arg !== undefined) {
                    const args = [...term.args]
                    args[i] = arg
                    return { k: "con", variant: term.variant, args }
                }
            }
            return undefined
        case "fold": {
            // The scrutinee first (the leftmost-innermost discipline: the
            // scrutinee is evaluated before the handlers fire), then the
            // handler bodies.
            const scrut = matchRewrite(term.scrutinee, from, to, vars)
            if (scrut !== undefined) {
                return {
                    k: "fold",
                    carrier: term.carrier,
                    scrutinee: scrut,
                    handlers: term.handlers,
                }
            }
            for (let i = 0; i < term.handlers.length; i++) {
                const h = term.handlers[i]!
                const body = matchRewrite(h.body, from, to, vars)
                if (body !== undefined) {
                    const handlers = [...term.handlers]
                    handlers[i] = { variantName: h.variantName, bindings: h.bindings, body }
                    return {
                        k: "fold",
                        carrier: term.carrier,
                        scrutinee: term.scrutinee,
                        handlers,
                    }
                }
            }
            return undefined
        }
        case "obs":
            return undefined
    }
}

/** A whole-side rewrite helper (the pair-level match). */
function rewriteWhole(
    obligation: Obligation,
    from: Term,
    to: Term,
): Obligation | undefined {
    if (termEquals(obligation.left, from)) return { left: to, right: obligation.right }
    if (termEquals(obligation.right, from)) return { left: obligation.left, right: to }
    return undefined
}

/**
 * Prove one schema instance's obligation for ONE variant case, or report
 * the failed move.
 *
 * The fixed-priority move sequence (the plan's D4), no backtracking:
 *
 * 1. **Reflexivity** — syntactic term equality.
 * 2. **Normalize** — the computation fixpoint (E-Fold + E-Op) on both
 *    sides; reflexivity re-checked after (computation closes many
 *    obligations outright — the closure record is then the moves used).
 * 3. **Congruence decomposition** — same constructor head: recurse into
 *    arguments (the worklist grows; every pair must close).
 * 4. **IH application** — the claim re-instantiated at THIS case's
 *    recursion variables only; a full syntactic match rewrites one side.
 * 5. **Axiom application** — one step per pass from the eligible base.
 * 6. **Exhaustion** — no move applies or budget reached → open case.
 */
function proveCase(
    obligation: Obligation,
    ihPairs: readonly { readonly left: Term; readonly right: Term }[],
    axioms: readonly AxiomSource[],
    registry: TypeRegistry,
    omega: OpRegistry,
    budget: number,
    onAxiom: (source: AxiomSource) => void,
): { closure: CaseClosure; open?: Obligation; reason?: string } {
    let worklist: Obligation[] = [obligation]
    let steps = 0
    let usedIH = false
    let usedAxiom = false
    // The pairs already processed this case: an IH/axiom rewrite that
    // re-produces a seen pair (the mirror ping-pong — rewriting p to
    // add(p, e) and back) made NO progress; re-entering it would burn the
    // budget looping. A repeated pair is treated as a failed move (the
    // obligation stays, the next move is tried on the ORIGINAL — the rewrite
    // is sound but useless here).
    const seen = new Set<string>()
    const key = (o: Obligation): string => `${renderTerm(o.left)} ≡ ${renderTerm(o.right)}`

    for (;;) {
        const nextWorklist: Obligation[] = []
        for (const current of worklist) {
            // Mark the configuration as seen (progress tracking).
            seen.add(key(current))
            // 1. Reflexivity.
            if (termEquals(current.left, current.right)) continue

            // 2. Normalize (the computation rules) both sides.
            const left = normalize(current.left, registry, omega, MAX_UNFOLDS_PER_CASE)
            const right = normalize(current.right, registry, omega, MAX_UNFOLDS_PER_CASE)
            if (left === undefined || right === undefined) {
                return {
                    closure: closureKind(usedIH, usedAxiom, steps),
                    open: current,
                    reason: "the unfold budget exhausted during normalization",
                }
            }
            if (termEquals(left, right)) continue

            // 3. Congruence: same constructor head → recurse into arguments.
            if (left.k === "con" && right.k === "con" && left.variant === right.variant) {
                if (left.args.length !== right.args.length) {
                    return {
                        closure: closureKind(usedIH, usedAxiom, steps),
                        open: { left, right },
                        reason: `constructor ${left.variant} arity mismatch under congruence`,
                    }
                }
                for (let i = 0; i < left.args.length; i++) {
                    nextWorklist.push({ left: left.args[i]!, right: right.args[i]! })
                }
                continue
            }

            // 4. IH application (a full syntactic match rewrites one side).
            //    The IH's sides are normalized too: the IH is an EQUALITY of
            //    computations, and the obligation's sides have already been
            //    normalized — matching an unfolded side against an op-shaped
            //    IH side would miss the match (the misuse-guard discipline
            //    keeps the matching FULL-shape; normalizing both keeps it
            //    sound and precise).
            const ihHit = applyIH(left, right, ihPairs) ??
                applyIHNnormalized(left, right, ihPairs, registry, omega)
            if (ihHit !== undefined) {
                usedIH = true
                steps++
                if (steps > budget) {
                    return {
                        closure: closureKind(usedIH, usedAxiom, steps),
                        open: current,
                        reason: `the step budget (${budget}) exhausted — the ` +
                            `fragment's honest edge`,
                    }
                }
                // The rewrite's outcome splits three ways:
                //
                // - **Closes outright** (the rewrite made the pair
                //   reflexive): the configuration is discharged.
                // - **New configuration** (never seen): progress — push it
                //   and move on (the move sequence restarts on it).
                // - **Mirror** (re-produces a SEEN configuration — the
                //   ping-pong, rewriting p to add(p, e) and back): the
                //   rewrite made NO progress; the configuration stays and
                //   the NEXT move (the axiom) is tried on it — the move
                //   sequence does not restart on a useless rewrite.
                if (termEquals(ihHit.left, ihHit.right)) continue
                if (!seen.has(key(ihHit))) {
                    nextWorklist.push(ihHit)
                    continue
                }
                // A mirror: fall through to the axiom move on the SAME pair.
            }

            // 5. Axiom application (one step per pass).
            const axiomHit = applyAxiom({ left, right }, axioms, registry, omega, onAxiom)
            if (axiomHit !== undefined) {
                usedAxiom = true
                steps++
                if (steps > budget) {
                    return {
                        closure: closureKind(usedIH, usedAxiom, steps),
                        open: current,
                        reason: `the step budget (${budget}) exhausted — the ` +
                            `fragment's honest edge`,
                    }
                }
                if (termEquals(axiomHit.left, axiomHit.right)) continue
                // Progress guard: a rewritten pair that re-produces a seen
                // configuration is a loop (the rewrite made no progress).
                if (seen.has(key(axiomHit))) {
                    continue
                }
                nextWorklist.push(axiomHit)
                continue
            }

            // 6. Exhaustion: no move applies — the case stays open.
            return {
                closure: closureKind(usedIH, usedAxiom, steps),
                open: { left, right },
                reason: `no move applies: ${renderTerm(left)} ≢ ${renderTerm(right)}`,
            }
        }
        if (nextWorklist.length === 0) {
            // Everything closed; the record is the strongest move used and
            // the steps the case consumed.
            return { closure: closureKind(usedIH, usedAxiom, steps) }
        }
        if (nextWorklist.length > 256) {
            return {
                closure: closureKind(usedIH, usedAxiom, steps),
                open: nextWorklist[0],
                reason: "the obligation worklist exceeded 256 — the fragment's edge",
            }
        }
        worklist = nextWorklist
    }
}

/**
 * The certificate's closure record: the strongest move the case used, with
 * the number of budgeted steps (IH/axiom rewrites) the case consumed —
 * the visible distance from the configured budget.
 */
function closureKind(usedIH: boolean, usedAxiom: boolean, steps: number): CaseClosure {
    if (usedAxiom) return { closedBy: "axiom", steps }
    if (usedIH) return { closedBy: "IH", steps }
    return { closedBy: "reflexivity", steps }
}

/**
 * The schema variable that lands on operand position `axis` (the mapping
 * variable i ↦ position i % paramCount — the same rule `assignments`
 * enumerates). Returns the variable's NAME, or `undefined` when no
 * variable lands on the axis (an unswept axis — the claim does not
 * constrain the recursion axis; the skeleton has no induction to run).
 */
function schemaVariableFor(
    kind: LawKind,
    axis: number,
    paramCount: number,
): string | undefined {
    const count = SCHEMA_VARIABLE_COUNT[kind]
    for (let i = 0; i < count; i++) {
        if (i % paramCount === axis) return SCHEMA_VARIABLE_NAMES[kind][i]
    }
    return undefined
}

/**
 * Bind the axis-slot variable in a motive side to the case's term (the
 * case pattern for the case itself; a recursion variable for the IH). The
 * other schema variables stay free (the claim is universally quantified
 * over them).
 */
function bindAxis(motiveSide: Term, axisVar: string | undefined, pattern: Term): Term {
    if (axisVar === undefined) return motiveSide
    return substVar(motiveSide, axisVar, pattern)
}

// ── The gate and the entry ────────────────────────────────────────────────────

/**
 * The cheap syntactic gate (the plan's D6): whether the claim's target
 * operation's definition is in the fragment's admitted shape — a lambda
 * chain over the declared parameters whose body is a fold over one of the
 * parameters, one handler per axis variant, over a μ-type carrier. No `E`
 * is consulted, no evaluation runs; the gate is budget-free and syntactic.
 *
 * The gate admits nothing about closure — a passing gate means the claim
 * is *eligible* for the derivable regime's derivation attempt (routing
 * `"derivable"`); closure is the derivation's own outcome. A gate failure
 * is a loud shape-rejection with the construct named (the caller routes
 * residual).
 */
export function derivableFragment(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    registry: TypeRegistry,
    omega: OpRegistry,
): boolean {
    // Intrinsic kinds only (the plan's D9); `distributive` routes residual.
    if (RELATIONAL_KINDS.includes(law.kind)) return false
    // Pattern carriers have no variant cases to skeletonize.
    if (op.paramTypes.some((t) => !(t instanceof DataType))) return false
    try {
        readDefShape(op, registry, omega)
        return true
    } catch (e) {
        if (e instanceof DefinitionShapeError) return false
        throw e
    }
}

/**
 * Attempt the derivation of one law claim (the plan's D6 dispatch): build
 * the skeleton (the motive = the claim's schema; the cases = the axis
 * carrier's variants), discharge every instance's every case with the
 * bounded move sequence, and return either the certificate or the
 * open-case report.
 *
 * The axiom base: for each op the claim's HANDLER bodies reference (via
 * the symbolic `freeOps` scan — the same op references Ω's acyclicity check
 * scans, at the term level), the `primitive`/`discharged` laws installed in
 * `E`. An `asserted` law is never an axiom step (no laundering). The
 * certificate records every axiom consumed, with provenance — the visible
 * trust chain.
 *
 * @throws DefinitionShapeError when the target's definition is outside the
 *         fragment (the caller routes residual on this — the gate consults
 *         the same shape first, so a `derivable`-routed claim cannot hit it
 *         except through a race; kept loud for that reason).
 */
export function deriveLaw(
    law: Omit<LawDecl, "provenance">,
    op: CheckedOpSig,
    registry: TypeRegistry,
    omega: OpRegistry,
    laws: LawRegistry,
    budget: number = MAX_STEPS_PER_CASE,
): DerivationResult {
    // Relational kinds are deferred (the plan's D9): route residual.
    if (RELATIONAL_KINDS.includes(law.kind)) {
        return notDerivableAll(
            "distributive is outside the first cut's fragment (routes residual)",
        )
    }

    const shape = readDefShape(op, registry, omega)
    const handlerBodies = shape.handlers.map((h) => h.body)

    // The axiom base: the called ops' primitive/discharged laws (D5).
    const referenced = new Set<string>()
    for (const body of handlerBodies) freeOps(body, referenced)
    const axioms: AxiomSource[] = []
    for (const name of referenced) {
        const called = omega.lookup(name)
        if (!called) continue
        for (const installed of laws.lookup(name)) {
            if (installed.provenance === "primitive" || installed.provenance === "discharged") {
                axioms.push({ op: called, law: installed })
            }
        }
    }

    // The argument term (identity: e / absorbing: z) — read symbolically.
    let argument: Term | undefined
    if (ARGUMENT_KINDS.includes(law.kind)) {
        argument = axiomArgument(law, registry, omega)
        if (argument === undefined) {
            return notDerivableAll(
                `the argument term "${law.argument}" is not a closed constructor ` +
                    `term — the skeleton's syntactic motive needs a ` +
                    `constructor-shaped argument`,
            )
        }
    }

    // The motive: the claim's schema instances, symbolically.
    const motives = schemaMotives(law, op, argument)
    if (motives.length === 0) {
        return notDerivableAll("the schema has no symbolic motive (routes residual)")
    }

    // The skeleton: for each motive, for each axis variant, discharge the
    // case. The case substitution: the axis-slot schema variable becomes the
    // case pattern; the IH is the motive re-instantiated at each of the
    // case's recursion variables (the μ-bound fields — `carriesIH`).
    const axiomsUsed: { op: string; kind: LawKind; provenance: LawProvenance }[] = []
    const seenAxioms = new Set<string>()
    const onAxiom = (source: AxiomSource): void => {
        const key = `${source.op.name}/${source.law.kind}`
        if (!seenAxioms.has(key)) {
            seenAxioms.add(key)
            axiomsUsed.push({
                op: source.op.name,
                kind: source.law.kind,
                provenance: source.law.provenance,
            })
        }
    }

    const axisVar = schemaVariableFor(law.kind, shape.axis, op.paramTypes.length)
    if (axisVar === undefined) {
        return notDerivableAll(
            "no schema variable lands on the recursion axis — the skeleton has " +
                "no induction to run (routes residual)",
        )
    }

    const instances: DerivationInstance[] = []
    for (const motive of motives) {
        const cases: { variant: string; closure: CaseClosure }[] = []
        for (const handler of shape.handlers) {
            // The case pattern: the variant's constructor over the handler's
            // field-binding names (the case's variables).
            const pattern: Term = {
                k: "con",
                variant: handler.variantName,
                args: handler.bindings.map((b) => ({ k: "var" as const, name: b.name })),
            }
            const caseLeft = bindAxis(motive.left, axisVar, pattern)
            const caseRight = bindAxis(motive.right, axisVar, pattern)

            // The IH pairs: the motive re-instantiated at each recursion
            // variable (the μ-bound fields — the direct-recursion
            // boundary).
            const ihPairs: Obligation[] = []
            for (const binding of handler.bindings) {
                if (!binding.carriesIH) continue
                const recVar: Term = { k: "var", name: binding.name }
                ihPairs.push({
                    left: bindAxis(motive.left, axisVar, recVar),
                    right: bindAxis(motive.right, axisVar, recVar),
                })
            }

            // Discharge the case.
            const outcome = proveCase(
                { left: caseLeft, right: caseRight },
                ihPairs,
                axioms,
                registry,
                omega,
                budget,
                onAxiom,
            )
            if (outcome.open !== undefined) {
                return {
                    derivable: false,
                    direction: motive.direction,
                    variant: handler.variantName,
                    open: {
                        left: renderTerm(outcome.open.left),
                        right: renderTerm(outcome.open.right),
                    },
                    reason: outcome.reason ?? "no move applies",
                }
            }
            cases.push({
                variant: handler.variantName,
                closure: { ...outcome.closure, steps: outcome.closure.steps },
            })
        }
        instances.push({ direction: motive.direction, cases })
    }

    return { instances, axiomsUsed }
}

/** An all-cases-open NotDerivable report (a pre-skeleton decline). */
function notDerivableAll(reason: string): NotDerivable {
    return {
        derivable: false,
        direction: undefined,
        variant: "",
        open: { left: "", right: "" },
        reason,
    }
}
