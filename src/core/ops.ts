/**
 * LC Operation Symbols — the operation signature environment `Ω` and named
 * operation application support.
 *
 * See _docs/theory/lc.md §2.2, §2.4, §3 (E-Op/E-OpArg), §5.8 (T-Op).
 *
 *   Ω ::= ∅ | Ω, op:σ₁→...→σₙ→τ    operation signature (name ↦ argument/result types)
 *
 * `op(t₁, ..., tₙ)` is the application of a _named operation_ — the symbolic
 * identity of a fold declared in the surface language. It is _definitional_
 * sugar: `Ω` maps each operation name to its defining LC term, so the
 * application computes by applying the definition. The named form exists so
 * that operation identity survives `let`-inlining and substitution — an
 * optimizer can recognize two occurrences as the same algebraic operation,
 * which anonymous folds cannot express.
 *
 * ## Ω-acyclicity (declaration-order stratification)
 *
 * An operation may only reference operations declared **earlier** in `Ω`.
 * Every `op` application then terminates by induction on declaration order:
 * op _N_'s handlers call only ops _1..N-1_, each of which terminates on all
 * inputs by induction. Without the rule, a handler calling another operation
 * by name could cycle (`op A` calls `op B` calls `op A`), reintroducing
 * general recursion through `Ω` — termination would depend on a semantic
 * measure that is not syntactically visible.
 *
 * The check is a decidable dependency-graph condition, evaluated once per
 * declaration (stratification-class, the same family as Datalog's negation
 * stratification) — not a per-program semantic measure checker. It costs
 * nothing at evaluation time.
 *
 * ## Detection: lexical scan of the definition source
 *
 * In LC concrete syntax, a camelCase identifier immediately followed by `(` is
 * unambiguously a named operation application: variable application requires
 * whitespace (`f x`, never `f(x)`), and variant construction is PascalCase
 * (`Zero()`). The declaration-time check therefore scans the definition source
 * for that pattern and rejects references to operation names not already in
 * `Ω` (self-reference, forward reference, and cycles alike).
 *
 * The scan is **lexical, not token-level — by design and by necessity**:
 * `declare` runs before any parsing infrastructure exists (`Ω` is populated
 * before grammars are constructed — the grammar holds the registry), so the
 * check must be grammar-independent. This is exact for the current LC
 * concrete syntax, which has no string literals and no comments — the only
 * camelCase-ident-then-paren forms are op applications and the built-in
 * `match(pₖ)` form (excluded below). If a future syntax revision adds string
 * literals, comments, or other call-shaped constructs, the exclusion list
 * (or the scan itself) must be updated — until then, every match the scan
 * reports is a genuine op application.
 */

import { FunType, type Type } from "./types.ts"

/**
 * Language-level call forms excluded from the dependency scan — call-shaped
 * (`name(...)`), camelCase, and part of the language rather than members of
 * `Ω`. A closed vocabulary, like the law catalog: entries exist only when
 * the grammar itself defines a call form that would otherwise be mistaken
 * for an op application.
 *
 * - `match` — the pattern-matched construction `match(pₖ)` (lc.md §2.2,
 *   T-Pattern), introduced by the lexer, not an operation.
 */
const BUILTIN_CALL_FORMS: readonly string[] = ["match"]

// ── Operation signature ───────────────────────────────────────────────────────

/**
 * An operation signature: `op : σ₁ → ... → σₙ → τ`.
 *
 * The `definition` is the operation's defining LC term, as concrete-syntax
 * source. It is evaluated on demand (E-Op applies it to the argument values);
 * it is never inlined into the parse input, so the named form stays
 * recognizable to law-aware passes.
 */
export class OpSig {
    constructor(
        readonly name: string,
        readonly paramTypes: Type[],
        readonly resultType: Type,
        /** The defining LC term, as concrete-syntax source text. */
        readonly definition: string,
    ) {}

    /**
     * The full signature type `σ₁ → ... → σₙ → τ`.
     *
     * Not consumed by the core: T-Op checks the premises field-wise and E-Op
     * applies the definition, so neither needs the assembled function type.
     * It exists for the law machinery — law screening and derivation
     * discharge query an operation's signature as a single type (e.g. to
     * check that a `distributive:⊕` law's two operations have composable
     * signatures) — and for tools that print or compare signatures.
     */
    get signature(): Type {
        let result = this.resultType
        for (let i = this.paramTypes.length - 1; i >= 0; i--) {
            result = new FunType(this.paramTypes[i]!, result)
        }
        return result
    }
}

// ── Declaration errors ─────────────────────────────────────────────────────────

/**
 * Thrown by `OpRegistry.declare` when an operation declaration is invalid:
 * a malformed name, a duplicate, or an acyclicity violation (self-reference,
 * forward reference, or a cycle).
 */
export class OpDeclarationError extends Error {
    constructor(
        readonly opName: string,
        readonly reason: string,
    ) {
        super(`operation "${opName}": ${reason}`)
        this.name = "OpDeclarationError"
    }
}

// ── The operation registry (Ω) ────────────────────────────────────────────────

/**
 * `Ω` — the operation signature environment. Maps operation names to their
 * signatures and defining terms, in declaration order.
 *
 * The registry is append-only: `declare` adds an operation at the end of the
 * declaration order, and the acyclicity check runs against the operations
 * already present. This makes `Ω` acyclic by construction.
 */
export class OpRegistry {
    private readonly ops = new Map<string, OpSig>()
    /** Declaration order — the stratification order for the acyclicity check. */
    private readonly order: string[] = []

    /**
     * Declare an operation. Runs the declaration-time checks:
     *
     * 1. **Name shape** — camelCase (lowercase-first), matching the `opIdent`
     *    lexeme that `opProd` parses. A PascalCase name would collide with the
     *    variant namespace and never parse as an op application. Reserved
     *    words are allowed: the op form's tight paren is positionally
     *    disjoint from every keyword position, so an operation named `fold`
     *    is appliable (`fold(a, b)`).
     * 2. **Duplicate** — redeclaring an operation name is rejected; the
     *    signature and definition would silently diverge.
     * 3. **Acyclicity** — the definition may only reference operations already
     *    declared in `Ω` (declaration-order stratification). Self-reference,
     *    forward reference, and cycles are all rejected here.
     *
     * @throws OpDeclarationError on any invalid declaration.
     */
    declare(op: OpSig): void {
        // 1. Name shape: must match the `opIdent` lexeme (camelCase).
        if (!/^[a-z_][a-zA-Z0-9_]*$/.test(op.name)) {
            throw new OpDeclarationError(
                op.name,
                "operation names must be camelCase (lowercase-first) — the `opIdent` lexeme",
            )
        }

        // 2. Duplicate: redeclaration is rejected.
        if (this.ops.has(op.name)) {
            throw new OpDeclarationError(op.name, "operation is already declared in Ω")
        }

        // 3. Acyclicity: the definition may only reference earlier operations.
        for (const referenced of this.referencedOps(op.definition)) {
            if (referenced === op.name) {
                throw new OpDeclarationError(
                    op.name,
                    "self-reference — an operation may only reference operations declared earlier in Ω",
                )
            }
            if (!this.ops.has(referenced)) {
                throw new OpDeclarationError(
                    op.name,
                    `references "${referenced}", which is not declared earlier in Ω ` +
                        "(forward reference or cycle — declaration-order stratification)",
                )
            }
        }

        this.ops.set(op.name, op)
        this.order.push(op.name)
    }

    /** Look up an operation by name. */
    lookup(name: string): OpSig | undefined {
        return this.ops.get(name)
    }

    /** All declared operations, in declaration order. */
    all(): OpSig[] {
        return this.order.map((name) => this.ops.get(name)!)
    }

    /**
     * Scan concrete-syntax source for named operation applications.
     *
     * A camelCase identifier immediately followed by `(` is an op application
     * (`add(a, b)`); variable application requires whitespace (`f x`) and
     * variant construction is PascalCase (`Zero()`), so the pattern is
     * unambiguous in LC concrete syntax.
     *
     * The lookbehind guards against mid-identifier matches: without it,
     * `Zero(` would match at the lowercase `e`, yielding the phantom
     * reference `ero(`. The identifier must start at a non-identifier
     * character boundary.
     *
     * **Scope of the scan (exactness claim):** this is a lexical scan over the
     * definition source, not a token-level one — `declare` runs before
     * parsing infrastructure exists (`Ω` is populated before grammars are
     * constructed), so the check must be grammar-independent. It is exact for
     * the current LC concrete syntax, which has no string literals and no
     * comments; the language-level call forms (`BUILTIN_CALL_FORMS`, e.g.
     * `match(pₖ)`) are excluded because they are language constructs, not
     * operations. A future syntax revision adding string literals, comments,
     * or other call-shaped constructs must extend the exclusion list (or
     * replace the scan) — until then, every reported name is a genuine op
     * reference.
     *
     * **Over-approximation risk:** none today. If an exclusion is missed or a
     * new construct appears, the failure mode is a rejected declaration
     * (`OpDeclarationError` naming the phantom reference) — loud, not silent.
     */
    private referencedOps(source: string): Set<string> {
        const referenced = new Set<string>()
        // camelCase identifier immediately followed by "(", starting at a
        // non-identifier boundary
        const opCall = /(?<![a-zA-Z0-9_])[a-z_][a-zA-Z0-9_]*\(/g
        for (const match of source.matchAll(opCall)) {
            const name = match[0].slice(0, -1) // strip the trailing "("
            if (BUILTIN_CALL_FORMS.includes(name)) continue
            referenced.add(name)
        }
        return referenced
    }
}
