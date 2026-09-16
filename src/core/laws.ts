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
 * through the residual screen (law_checking.ts), and only screened or
 * established laws are installed.
 */

import { type OpRegistry } from "./ops.ts"

import type { Type } from "./types.ts"

// The DataType class is used as a value (instanceof) here.
import { DataType } from "./types.ts"

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
 * A law falsified by the screen: the failed law, the sample bindings under
 * which the two sides diverged, and both sides' values.
 *
 * The screen (law_checking.ts) throws this when a sample falsifies the
 * axiom; the declaration is rejected and nothing enters `E`. Rendered
 * counterexample values are carried as strings (LC-like term rendering) so
 * the error is self-describing without exposing value internals.
 */
export class LawError extends Error {
    constructor(
        readonly opName: string,
        readonly law: LawDecl,
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
 * argument shape, arity) is checked against `Ω` at declaration; semantic
 * screening (the residual sample screen) is the caller's separate step —
 * `law_checking.ts` — and only screened laws are installed here.
 *
 * **The trust boundary mirrors `OpRegistry`'s**: every entry in `E` carries
 * its provenance tag, and `declareLaw` only accepts laws the caller has
 * screened (or established by a discharge mechanism — a later concern). A
 * caller that bypasses the screen and installs an unscreened `asserted` law
 * opts into the residual's honest risk (semantics.md §7.4); nothing here
 * prevents it, because provenance is evidence, not a gate.
 */
export class LawRegistry {
    private readonly laws = new Map<string, LawDecl[]>()

    /**
     * Declare a law on an operation: validate the claim structurally against
     * `Ω` and install it with the given provenance.
     *
     * Checks (elaboration.md §6.1, elaboration-time step 1):
     *
     * 1. **Closed vocabulary** — the kind is a member of `LAW_KINDS`.
     * 2. **Target exists** — the target operation is declared in `Ω`.
     * 3. **Argument shape** — argument-taking kinds carry an argument term;
     *    argument-free kinds carry none.
     * 4. **Relational shape** — `distributive`'s argument must name another
     *    declared operation (the law is between two `Ω` members).
     * 5. **Arity** — intrinsic schemas pin the target's arity
     *    (associative/commutative/identity/absorbing/distributive ⇒ arity 2;
     *    idempotent ⇒ arity 2; involutory ⇒ arity 1).
     *
     * @throws LawDeclarationError on any failed check.
     */
    declareLaw(
        law: Omit<LawDecl, "provenance">,
        omega: OpRegistry,
        provenance: LawProvenance = "asserted",
    ): LawDecl {
        const declared: LawDecl = { ...law, provenance }
        const { kind, target, argument } = declared

        // 1. Closed vocabulary.
        if (!LAW_KINDS.includes(kind)) {
            throw new LawDeclarationError(target, `"${kind}" is not in the closed vocabulary`)
        }

        // 2. The target must be a declared operation.
        const targetOp = omega.lookup(target)
        if (!targetOp) {
            throw new LawDeclarationError(target, "the target operation is not declared in Ω")
        }

        // 3. Argument shape: argument kinds require one; others must not have one.
        if (ARGUMENT_KINDS.includes(kind)) {
            if (argument === undefined) {
                throw new LawDeclarationError(target, `kind "${kind}" requires an argument term`)
            }
        } else if (argument !== undefined && !RELATIONAL_KINDS.includes(kind)) {
            throw new LawDeclarationError(target, `kind "${kind}" takes no argument`)
        }

        // 4. Relational shape: `distributive: g` — g must be another declared
        //    operation (the law is between two Ω members).
        if (RELATIONAL_KINDS.includes(kind)) {
            if (argument === undefined) {
                throw new LawDeclarationError(
                    target,
                    `kind "${kind}" requires the operation it distributes over`,
                )
            }
            if (!omega.lookup(argument)) {
                throw new LawDeclarationError(
                    target,
                    `distributes "${argument}", which is not declared in Ω`,
                )
            }
        }

        // 5. Arity: each schema instantiates over a fixed argument count.
        const expectedArity = SCHEMA_ARITY[kind]
        if (targetOp.paramTypes.length !== expectedArity) {
            throw new LawDeclarationError(
                target,
                `${kind} requires arity ${expectedArity}, but "${target}" has arity ${targetOp.paramTypes.length}`,
            )
        }

        const list = this.laws.get(target) ?? []
        list.push(declared)
        this.laws.set(target, list)
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
 * Check a law's domain type: the screen walks the variants of the
 * operation's parameter types to generate samples, so every parameter must
 * be a (data) type with variants. Function-typed parameters (higher-order
 * operations) are outside the first cut's screen — a law over such an
 * operation declares but cannot be screened; the caller installs it
 * `asserted` unscreened (the residual's honest risk, semantics.md §7.4).
 */
export function screenableDomain(op: { paramTypes: readonly Type[] }): boolean {
    return op.paramTypes.every((t) => t instanceof DataType)
}
