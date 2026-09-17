/**
 * LC Laws — the algebraic theory environment `E` and law declarations.
 *
 * See _docs/theory/lc.md §2.4, §7.2 (law schemas), and
 * _docs/theory/elaboration.md §6.1 (algebraic contracts).
 *
 *   E ::= ∅ | E, op:ℓ            equational theory (operation ↦ declared laws)
 *
 * A law is a membership claim in a **closed vocabulary** of algebraic
 * structures — never an arbitrary equation. The closed vocabulary is what
 * keeps rewriting terminating and the `≡` theory well-behaved (each kind
 * contributes a fixed axiom schema with known shape, and an exploiting
 * rewrite consumes only the schema's directed consequence).
 *
 * Laws live in `E`, attached to operation **names** (lc.md §2.2) — never in
 * the term grammar. `Ω` and `E` are separate environments: Ω carries the
 * operation's signature + defining term; E carries the laws declared for it.
 * Neither steps; laws generate the separate judgment `Ω; E ⊢ t ≡ u` (lc.md
 * §7), which is never evaluated — rewrites licensed by `≡` are a compiler
 * strategy (the `↝` relation), not part of the operational semantics.
 *
 * ## Provenance (the ladder, lc.md §2.4)
 *
 * Every law in `E` carries a provenance tag — evidence about the axiom,
 * never a gate on declaring or exploiting it:
 *
 * - **`primitive`** — builtin operations with pinned law sets; authority is
 *   the language definition.
 * - **`discharged`** — established by the compiler (finite/machine-finite
 *   exhaustion, or derivation from primitive laws — the follow-up discharge
 *   mechanisms).
 * - **`asserted`** — programmer declaration, screened (the screen falsifies,
 *   never establishes — semantics.md §5.4). Passing the screen is evidence,
 *   not proof.
 *
 * This module implements the `asserted` tier: declarations enter `E` only
 * through a regime-based check (law_checking.ts — the residual screen or
 * finite-regime exhaustion), and only checked laws are installed.
 */

import { type OpRegistry, type OpSig } from "./ops.ts"

import { isSubtype } from "./subtyping.ts"

import { DataType, PatternDataType, type Type } from "./types.ts"

/**
 * The evaluation-free type-checking entry the law declarations need
 * (argument terms must type against the target's carrier). Injected to avoid
 * importing the typing grammar (a cycle through grammar.ts).
 */
export interface LawTypeChecker {
    /** Type-check an LC source fragment; `undefined` when it does not check. */
    checkSource(source: string): Type | undefined
}

// ── The closed vocabulary ─────────────────────────────────────────────────────

/**
 * The closed vocabulary of law kinds. Each kind names one axiom schema
 * (lc.md §7.2); the schema's shape — how many operations it relates and what
 * arguments it takes — is fixed by the kind, which is what keeps the screen
 * and any exploiting rewrite mechanical.
 *
 * `identity`, `absorbing`, and `distributive` take arguments (`identity: e`,
 * `absorbing: z`, `distributive: g`) — see `LawDecl.argument`. The rest are
 * argument-free.
 */
export type LawKind =
    | "associative"
    | "commutative"
    | "identity"
    | "idempotent"
    | "involutory"
    | "absorbing"
    | "distributive"

/** The closed vocabulary, as a set — `declareLaw` rejects anything else. */
export const LAW_KINDS: readonly LawKind[] = [
    "associative",
    "commutative",
    "identity",
    "idempotent",
    "involutory",
    "absorbing",
    "distributive",
]

/** Kinds that require an argument term (`identity: e`, `absorbing: z`). */
export const ARGUMENT_KINDS: readonly LawKind[] = ["identity", "absorbing"]

/** Kinds that relate two operations (`distributive: g`). */
export const RELATIONAL_KINDS: readonly LawKind[] = ["distributive"]

// ── Provenance ────────────────────────────────────────────────────────────────

/**
 * The provenance ladder (lc.md §2.4): evidence about an axiom's authority.
 * `≡` and `↝` never consult provenance — an installed law is an axiom
 * regardless of tier; the tag records how its authority was established.
 */
export type LawProvenance = "primitive" | "discharged" | "asserted"

// ── Law declaration ───────────────────────────────────────────────────────────

/**
 * A declared law: one operation's claim to an axiom schema from the closed
 * vocabulary.
 *
 * `target` names the operation the law is about (intrinsic kinds) or the
 * operation distributing over the argument operation (`distributive: g` —
 * the relational law is attributed to the distributing operation, matching
 * the surface form `properties: (distributive: #sum)` on the distributing
 * fold). `argument` is the law's argument term as LC source
 * (`identity: e`, `absorbing: z`), in the same concrete-syntax form as
 * `OpSig.definition`.
 */
export interface LawDecl {
    readonly kind: LawKind
    /** The operation the law is attached to (an `Ω` member). */
    readonly target: string
    /** The law's argument term as LC source, for kinds that take one. */
    readonly argument?: string
    readonly provenance: LawProvenance
}

/**
 * A law declaration failure: the target operation and the failed check's
 * reason (unknown kind, argument shape, arity mismatch). Thrown by
 * `LawRegistry.declare` — a rejected declaration is an exceptional outcome
 * for the caller, who stated the claim as a fact.
 */
export class LawDeclarationError extends Error {
    constructor(
        readonly opName: string,
        readonly reason: string,
    ) {
        super(`law on "${opName}": ${reason}`)
        this.name = "LawDeclarationError"
    }
}

/**
 * A law falsified by a check (the residual screen or exhaustion): the failed
 * law, the sample bindings under which the two sides diverged, and both
 * sides' values.
 *
 * The checkers (law_checking.ts) throw this when an instance falsifies the
 * axiom; the declaration is rejected and nothing enters `E`. The claim is
 * accepted pre-provenance (`Omit<LawDecl, "provenance">`) — provenance is
 * the tag the caller INSTALLS after a passing check, never an input to it.
 * Rendered counterexample values are carried as strings (LC-like term
 * rendering) so the error is self-describing without exposing value
 * internals.
 */
export class LawError extends Error {
    constructor(
        readonly opName: string,
        readonly law: Omit<LawDecl, "provenance">,
        /** The sample bindings, as rendered `name = term` pairs. */
        readonly bindings: string[],
        /** Rendering of the axiom's left-hand side value. */
        readonly left: string,
        /** Rendering of the axiom's right-hand side value. */
        readonly right: string,
    ) {
        super(
            `law on "${opName}" falsified: ${law.kind}` +
                (law.argument ? `: ${law.argument}` : "") +
                `\n  under: ${bindings.join(", ")}` +
                `\n  ${law.kind} claims both sides equivalent, but\n` +
                `  left:  ${left}\n  right: ${right}`,
        )
        this.name = "LawError"
    }
}

// ── The law environment (E) ───────────────────────────────────────────────────

/**
 * `E` — the equational theory environment. Maps operation names to the laws
 * declared for them, in declaration order.
 *
 * Append-only like `Ω` (`OpRegistry`): `declareLaw` adds a law at the end of
 * the target's law list. Structural well-formedness (vocabulary membership,
 * argument shape, arity) is checked against `Ω` at declaration; regime-based
 * checking (the residual screen or finite exhaustion) is the caller's
 * separate step — `law_checking.ts` — and only checked laws are installed
 * here.
 *
 * **The trust boundary mirrors `OpRegistry`'s**: every entry in `E` carries
 * its provenance tag, and `declareLaw` only accepts laws the caller has
 * checked (screened, or exhausted to discharge — the finite regime). A caller
 * that bypasses the check and installs an unscreened `asserted` law
 * opts into the residual's honest risk (semantics.md §7.4); nothing here
 * prevents it, because provenance is evidence, not a gate.
 */
export class LawRegistry {
    private readonly laws = new Map<string, LawDecl[]>()

    /**
     * Validate a law claim structurally against `Ω` — every check
     * `declareLaw` runs, without mutating `E`. Returns the reason string on
     * the first failure, `undefined` when the claim is well-formed.
     *
     * Public so `declareCheckedLaw` (law_checking.ts) can run the structural
     * validation BEFORE the sample screen: a vocabulary/argument/arity error
     * must surface as `LawDeclarationError`, not as a screen artifact (a
     * `TypeError` from an unknown kind reaching the schema table, or a
     * screen with zero coverage silently installing the claim).
     *
     * Checks (elaboration.md §6.1, elaboration-time step 1):
     *
     * 1. **Closed vocabulary** — the kind is a member of `LAW_KINDS`.
     * 2. **Target exists** — the target operation is declared in `Ω`.
     * 3. **Argument shape** — argument-taking kinds carry an argument term;
     *    argument-free kinds carry none.
     * 4. **Relational shape** — `distributive`'s argument must name another
     *    declared **binary** operation (the schema instantiates `g(b, c)` —
     *    a unary or n-ary operand never evaluates; accepting it would install
     *    a law with zero coverage).
     * 5. **Arity** — intrinsic schemas pin the target's arity.
     * 6. **Schema typing** (checker injected) — the axiom must type against
     *    the target's signature: `checkSchemaWellTyped`.
     *
     * @returns the failure reason, or `undefined` when well-formed.
     */
    validateLaw(
        law: Omit<LawDecl, "provenance">,
        omega: OpRegistry,
        checker?: LawTypeChecker,
    ): string | undefined {
        const { kind, target, argument } = law

        // 1. Closed vocabulary.
        if (!LAW_KINDS.includes(kind)) {
            return `"${kind}" is not in the closed vocabulary`
        }

        // 2. The target must be a declared operation.
        const targetOp = omega.lookup(target)
        if (!targetOp) {
            return "the target operation is not declared in Ω"
        }

        // 3. Argument shape: argument kinds require one; others must not have one.
        if (ARGUMENT_KINDS.includes(kind)) {
            if (argument === undefined) {
                return `kind "${kind}" requires an argument term`
            }
        } else if (argument !== undefined && !RELATIONAL_KINDS.includes(kind)) {
            return `kind "${kind}" takes no argument`
        }

        // 4. Relational shape: `distributive: g` — g must be another declared
        //    binary operation (the law is between two Ω members, and the
        //    schema instantiates `g(b, c)`).
        if (RELATIONAL_KINDS.includes(kind)) {
            if (argument === undefined) {
                return `kind "${kind}" requires the operation it distributes over`
            }
            const otherOp = omega.lookup(argument)
            if (!otherOp) {
                return `distributes "${argument}", which is not declared in Ω`
            }
            if (otherOp.paramTypes.length !== 2) {
                return `distributes "${argument}", which has arity ${otherOp.paramTypes.length} — distributive requires a binary operand`
            }
        }

        // 5. Arity: each schema instantiates over a fixed argument count.
        const expectedArity = SCHEMA_ARITY[kind]
        if (targetOp.paramTypes.length !== expectedArity) {
            return `${kind} requires arity ${expectedArity}, but "${target}" has arity ${targetOp.paramTypes.length}`
        }

        // 6. Schema typing (checker injected): the axiom must type against the
        //    target's signature — otherwise the screen's instances evaluate to
        //    error sentinels and are silently skipped, installing a claim with
        //    zero coverage. Checked at declaration, where the failure is loud.
        if (checker) {
            const typingReason = checkSchemaWellTyped(kind, targetOp, argument, omega, checker)
            if (typingReason !== undefined) {
                return typingReason
            }
        }

        return undefined
    }

    /**
     * Declare a law on an operation: validate the claim structurally against
     * `Ω` (see `validateLaw`) and install it with the given provenance.
     *
     * @throws LawDeclarationError on any failed check.
     */
    declareLaw(
        law: Omit<LawDecl, "provenance">,
        omega: OpRegistry,
        provenance: LawProvenance = "asserted",
        checker?: LawTypeChecker,
    ): LawDecl {
        const reason = this.validateLaw(law, omega, checker)
        if (reason !== undefined) {
            throw new LawDeclarationError(law.target, reason)
        }

        const declared: LawDecl = { ...law, provenance }
        const list = this.laws.get(law.target) ?? []
        list.push(declared)
        this.laws.set(law.target, list)
        return declared
    }

    /** All laws declared on an operation, in declaration order. */
    lookup(target: string): readonly LawDecl[] {
        return this.laws.get(target) ?? []
    }

    /** Whether an operation carries a law of the given kind. */
    has(target: string, kind: LawKind): boolean {
        return this.lookup(target).some((law) => law.kind === kind)
    }

    /** All declared laws, flattened across targets (for screening sweeps). */
    all(): readonly LawDecl[] {
        return [...this.laws.values()].flat()
    }
}

/**
 * The axiom schema's operand arity per kind (lc.md §7.2): the arity the
 * target operation must have for the schema to instantiate.
 * `distributive` distributes a binary operation over another binary one.
 */
export const SCHEMA_ARITY: Record<LawKind, number> = {
    associative: 2,
    commutative: 2,
    identity: 2,
    idempotent: 2,
    involutory: 1,
    absorbing: 2,
    distributive: 2,
}

/**
 * Check a law's domain type: the screen walks the variants of data-typed
 * parameters (or draws matched tokens for pattern-typed ones — a
 * `PatternDataType` has a sample vocabulary, the token atom), so every
 * parameter must be a data type with variants or a declared pattern type.
 * Function-typed parameters (higher-order operations) are outside the first
 * cut's screen — a law over such an operation declares but cannot be
 * screened; the caller rejects it (zero coverage: the screen declined,
 * law_checking.ts).
 */
export function screenableDomain(op: { paramTypes: readonly Type[] }): boolean {
    return op.paramTypes.every((t) => t instanceof DataType || t instanceof PatternDataType)
}

/**
 * The schema-typing check (`validateLaw` step 6): every law's axiom must type
 * against the target's signature, or the screen's instances evaluate to error
 * sentinels and are silently skipped — installing a claim with zero coverage.
 * All checks here are evaluation-free (checker-injected LC source type-checking
 * plus subtyping); the screen still supplies the semantic evidence.
 *
 * What is checked, per schema shape (lc.md §7.2):
 *
 * - **Intrinsic schemas** instantiate the target's own applications whose
 *   results feed back as operands (`⊕(⊕(a,b),c)`): the result type must be a
 *   subtype of the operand carrier, and the argument term of
 *   `identity: e`/`absorbing: z` must type as the carrier (`e`/`z` appear as
 *   operands — LCEval does not type-check operation arguments, so a
 *   mistyped argument would surface as sentinels, not a declaration error).
 * - **`distributive: g`** composes two signatures: the target distributes
 *   `g` over `+`-shaped pairs — `f(a, g(b, c))` and `g(f(a,b), f(a,c))`. The
 *   related op's result must feed the target's operand slots, and the
 *   target's result must feed `g`'s slots.
 * - **Operand homogeneity**: every operand slot must accept the same
 *   samples (the schema sweeps one sample space through all slots; a
 *   heterogeneous signature makes the schema ill-typed by construction —
 *   the swap axioms would need cross-type samples).
 */
function checkSchemaWellTyped(
    kind: LawKind,
    op: OpSig,
    argument: string | undefined,
    omega: OpRegistry,
    checker: LawTypeChecker,
): string | undefined {
    const carrier = op.paramTypes[0]!

    // Operand homogeneity: one sample space for all operand slots.
    for (const param of op.paramTypes) {
        if (!paramTypeCompatible(param, carrier)) {
            return `${kind}'s schema requires homogeneous operand carriers, but "${op.name}" takes (${
                op.paramTypes.map(String).join(", ")
            })`
        }
    }

    if (kind === "distributive") {
        // f distributes g: f(a, g(b, c)) ≡ g(f(a, b), f(a, c)). g's result
        // must feed f's operand slots; f's result must feed g's slots.
        const g = omega.lookup(argument!)
        if (!g) return `distributes "${argument}", which is not declared in Ω`
        const gResult = g.resultType
        if (!isSubtype(gResult, carrier)) {
            return `distributive's operand "${g.name}" returns ${gResult}, which does not feed "${op.name}"'s operand carrier ${carrier}`
        }
        for (const param of g.paramTypes) {
            if (!isSubtype(op.resultType, param)) {
                return `distributive's operand "${g.name}" takes ${param}, but "${op.name}" returns ${op.resultType}`
            }
        }
        return undefined
    }

    // Intrinsic schemas: the target's result feeds its own operand slots.
    if (!isSubtype(op.resultType, carrier)) {
        return `${kind}'s axiom requires "${op.name}" to return into its operand carrier ${carrier}, but it returns ${op.resultType}`
    }

    // Argument-taking kinds: the argument term types as the carrier.
    if (ARGUMENT_KINDS.includes(kind)) {
        const argType = checker.checkSource(argument!)
        if (argType === undefined) {
            return `argument "${argument}" does not type-check`
        }
        if (!isSubtype(argType, carrier)) {
            return `argument "${argument}" types as ${argType}, not the operand carrier ${carrier}`
        }
    }

    return undefined
}

/**
 * Operand-carrier compatibility: one sample space must inhabit both slots.
 *
 * Two slots are compatible when they hold the same carrier — two `DataType`s
 * of the same name, two `PatternDataType`s of the same name, or the two
 * non-data permissive shapes (function types / anything else, which
 * `screenableDomain` separately disqualifies from screening). A mixed
 * data/pattern signature (`(Pat, Bool)`) is NOT compatible: the schema
 * sweeps one sample space through all slots, so the swapped axioms would
 * put a token in a variant slot (or vice versa) — the instances are ill-
 * typed by construction, `LCEval` does not enforce op argument types, and
 * the all-holes sweep would silently pass zero-coverage validation.
 */
function paramTypeCompatible(a: Type, b: Type): boolean {
    // Two pattern types: same name = same carrier (the token identity is
    // type-qualified — see `valueEquals`'s `TokenVal` branch).
    if (a instanceof PatternDataType && b instanceof PatternDataType) return a.equals(b)
    // Mixed data/pattern: never compatible.
    if (a instanceof PatternDataType !== (b instanceof PatternDataType)) return false
    // Two data types: same name.
    if (a instanceof DataType && b instanceof DataType) return a.equals(b)
    // At most one of the two is a DataType/PatternDataType — the other is a
    // non-data type (function, Any, …). Unscreenable regardless
    // (`screenableDomain` routes such signatures away), so compatibility is
    // moot here; conservatively report incompatible to fail loudly.
    return false
}
