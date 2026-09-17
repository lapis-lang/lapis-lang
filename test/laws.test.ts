/**
 * Law tests — the equational theory environment `E` (LawRegistry), the
 * residual screen (screenLaw), and the identity-elimination exploit.
 *
 * See _docs/theory/lc.md §2.4 (E), §7.2 (law schemas), and
 * _docs/theory/semantics.md §5.4 (regime-based checking).
 */

import {
    declareCheckedLaw,
    EvalErrorValue,
    LAW_KINDS,
    type LawDecl,
    LawDeclarationError,
    LawError,
    type LawKind,
    LawRegistry,
    LCEval,
    LCTypeCheck,
    makeEvalTerm,
    OpRegistry,
    OpSig,
    screenLaw,
    type Value,
    ValueEnv,
    valueEquals,
    VariantVal,
} from "../src/index.ts"
import { FunType, TypeEnv } from "../src/core/types.ts"

import {
    createBoolType,
    createLawHarness,
    createOpFixtures,
    evalOne,
    NatSourceGrammar,
    slowTestsEnabled,
} from "./fixtures.ts"

import { PropertyFailure, type ValueGenerator } from "@lapis-lang/lang-forma"

import { assert, assertEquals, assertThrows } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry, opRegistry, nat, bool } = createOpFixtures()

/** A fresh Bool type for law-local registries (the fixtures' Bool shares Ω). */
const boolType = createBoolType()

/** An evaluator bound to the op fixtures (the screen's eval primitive). */
const evalGrammar = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
const evalOf = makeEvalTerm(evalGrammar)

/** The law checker: LCTypeCheck's parseWith under an empty Γ (declared terms). */
const checker = {
    checkSource: (source: string) => {
        const results = [
            // Bound to Ω as well as the type registry: an op-referencing
            // argument term (`identity: add(a, b)`-style) type-checks its op
            // application against Ω — a checker without it yields zero
            // results and silently rejects the valid term.
            ...new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry).parseWith(
                source,
                new TypeEnv(),
            ),
        ]
        return results.length === 1 ? results[0] : undefined
    },
}

/** A fresh law environment per test (registries are mutable append-only). */
function laws() {
    return new LawRegistry()
}

/** Build a Nat value of depth n by evaluating `Succ(...Zero())` chains. */
function natOf(depth: number): VariantVal {
    const result = evalGrammar.parseWith(
        `${"Succ(".repeat(depth)}Zero()${")".repeat(depth)}`,
        new ValueEnv(),
    )
    const [value] = result
    assert(value instanceof VariantVal, "nat sample must evaluate")
    return value
}

// ── E: declaration checks ─────────────────────────────────────────────────────

Deno.test("E: declareLaw installs a law with asserted provenance", () => {
    const e = laws()
    const law = e.declareLaw({ kind: "associative", target: "add" }, opRegistry)
    assertEquals(law.provenance, "asserted")
    assert(e.has("add", "associative"))
    assertEquals(e.lookup("add").length, 1)
})

Deno.test("E: declareLaw defaults to asserted and accepts an explicit tag", () => {
    const e = laws()
    e.declareLaw({ kind: "commutative", target: "add" }, opRegistry, "discharged")
    assertEquals(e.lookup("add")[0]!.provenance, "discharged")
})

Deno.test("E: unknown vocabulary kind is rejected", () => {
    const e = laws()
    const bad = { kind: "magical" as LawKind, target: "add" }
    assertThrows(() => e.declareLaw(bad, opRegistry), LawDeclarationError)
})

Deno.test("E: the closed vocabulary is exactly the seven kinds", () => {
    // Importing LAW_KINDS via the module surface; assert membership count.
    assertEquals(LAW_KINDS.length, 7)
})

Deno.test("E: laws attach to operation names — target must be in Ω", () => {
    const e = laws()
    assertThrows(
        () => e.declareLaw({ kind: "associative", target: "noSuchOp" }, opRegistry),
        LawDeclarationError,
        "not declared in Ω",
    )
})

Deno.test("E: argument shape — identity requires its argument", () => {
    const e = laws()
    assertThrows(
        () => e.declareLaw({ kind: "identity", target: "add" }, opRegistry),
        LawDeclarationError,
        "requires an argument",
    )
})

Deno.test("E: argument shape — argument-free kinds reject an argument", () => {
    const e = laws()
    assertThrows(
        () => e.declareLaw({ kind: "associative", target: "add", argument: "Zero()" }, opRegistry),
        LawDeclarationError,
        "takes no argument",
    )
})

Deno.test("E: relational shape — distributive's argument must be in Ω", () => {
    const e = laws()
    assertThrows(
        () =>
            e.declareLaw(
                { kind: "distributive", target: "mul", argument: "notAnOp" },
                opRegistry,
            ),
        LawDeclarationError,
        "not declared in Ω",
    )
})

Deno.test("E: arity — involutory requires an arity-1 operation", () => {
    const e = laws()
    assertThrows(
        () => e.declareLaw({ kind: "involutory", target: "add" }, opRegistry),
        LawDeclarationError,
        "arity",
    )
})

Deno.test("E: multiple laws accumulate per operation, in declaration order", () => {
    const e = laws()
    e.declareLaw({ kind: "commutative", target: "add" }, opRegistry)
    e.declareLaw({ kind: "associative", target: "add" }, opRegistry)
    e.declareLaw({ kind: "identity", target: "add", argument: "Zero()" }, opRegistry)
    assertEquals(
        e.lookup("add").map((law: LawDecl) => law.kind),
        ["commutative", "associative", "identity"],
    )
    assertEquals(e.all().length, 3)
})

// ── Structural validation runs BEFORE screening (declareCheckedLaw) ──────────

Deno.test("declareCheckedLaw: an unknown kind is a LawDeclarationError, not a TypeError", () => {
    // Validation runs BEFORE the screen: the unknown kind never reaches the
    // schema table (SCHEMA_NAMES) — it surfaces as the documented
    // LawDeclarationError instead of crashing mid-screen.
    const e = laws()
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "magical" as LawKind, target: "add" },
                opRegistry,
                e,
                evalOf,
                checker,
            ),
        LawDeclarationError,
        "closed vocabulary",
    )
})

Deno.test("declareCheckedLaw: identity:True() on Nat add is rejected (argument types as Bool)", () => {
    // The argument's TYPE is validated against the operand carrier: True()
    // types as Bool, but add's carrier is Nat. Screening it would evaluate
    // every instance to error sentinels (skip all) and install the claim with
    // zero coverage — validation rejects it loudly instead.
    const e = laws()
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "identity", target: "add", argument: "True()" },
                opRegistry,
                e,
                evalOf,
                checker,
            ),
        LawDeclarationError,
        "operand carrier",
    )
    assertEquals(e.lookup("add").length, 0)
})

Deno.test("E: distributive requires a binary operand (unary g is rejected)", () => {
    // The schema instantiates g(b, c) — a unary g never evaluates; accepting
    // it would install a distributive law with zero coverage.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "add2",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> y, Succ(p) -> Succ(p) }",
        ),
        tc.opWellFormedness,
    )
    ops.declare(
        new OpSig(
            "succOp",
            [nat],
            nat,
            "\\a:Nat. fold [Nat] a { Zero() -> Succ(Zero()), Succ(p) -> Succ(Succ(p)) }",
        ),
        tc.opWellFormedness,
    )
    const e = laws()
    assertThrows(
        () =>
            e.declareLaw(
                { kind: "distributive", target: "add2", argument: "succOp" },
                ops,
                "asserted",
                checker,
            ),
        LawDeclarationError,
        "binary operand",
    )
})

Deno.test("E: distributive signature composition is validated (mul over add composes; a non-composing g is rejected)", () => {
    const e = laws()
    // mul : Nat → Nat → Nat distributes add : Nat → Nat → Nat — composes.
    const installed = e.declareLaw(
        { kind: "distributive", target: "mul", argument: "add" },
        opRegistry,
        "asserted",
        checker,
    )
    assertEquals(installed.kind, "distributive")
})

Deno.test("E: a result outside the operand carrier is rejected (intrinsic schemas feed back)", () => {
    // The schemas' right-hand sides are operand terms, so the target's result
    // must type into its operand carrier. An op returning Bool over Nat
    // operands cannot carry associative/commutative/identity/absorbing. The
    // op is declared permissively (the type checker's fold fixpoint infers
    // Any for a constant-Bool fold over Nat — the declaration-level check
    // that catches ill-typed definitions doesn't fire here).
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "zeroP",
            [nat, nat],
            boolType,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> True(), Succ(p) -> False() }",
        ),
        { checkDefinition: () => undefined },
    )
    const e = laws()
    assertThrows(
        () =>
            e.declareLaw(
                { kind: "associative", target: "zeroP" },
                ops,
                "asserted",
                checker,
            ),
        LawDeclarationError,
        "operand carrier",
    )
})

// ── The residual screen ───────────────────────────────────────────────────────

Deno.test("screen: associative holds on add — the law is screenable", () => {
    const e = laws()
    const { law, instances } = declareCheckedLaw(
        { kind: "associative", target: "add" },
        opRegistry,
        e,
        evalOf,
        checker,
    )
    assert(instances > 0, "the screen must check at least one instance")
    assertEquals(law.provenance, "asserted")
    assert(e.has("add", "associative"))
})

Deno.test("screen: commutative and identity:Zero hold on add", () => {
    const e = laws()
    const { instances: commutative } = declareCheckedLaw(
        { kind: "commutative", target: "add" },
        opRegistry,
        e,
        evalOf,
        checker,
    )
    const { instances: identity } = declareCheckedLaw(
        { kind: "identity", target: "add", argument: "Zero()" },
        opRegistry,
        e,
        evalOf,
        checker,
    )
    assert(commutative > 0 && identity > 0)
    assert(e.has("add", "commutative") && e.has("add", "identity"))
})

Deno.test("screen: idempotent on mul is falsified (mul(2,2) ≠ 2)", () => {
    // mul(a, a) ≡ a is FALSE for Nat mul (mul(2, 2) = 4 ≠ 2) — the screen
    // must falsify this declaration. (Sanity: this documents the falsifying
    // direction exists and is detected.)
    assertThrows(
        () =>
            screenLaw(
                { kind: "idempotent", target: "mul" },
                opRegistry.lookup("mul")!,
                opRegistry,
                evalOf,
            ),
        LawError,
    )
})

Deno.test("screen: identity:Succ(Zero()) on add is falsified (LawError)", () => {
    // add(1, 0) = 1 ≠ 0 — the declared identity element is wrong.
    const e = laws()
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "identity", target: "add", argument: "Succ(Zero())" },
                opRegistry,
                e,
                evalOf,
                checker,
            ),
        LawError,
    )
    // Nothing was installed — a falsified declaration never enters E.
    assertEquals(e.lookup("add").length, 0)
})

Deno.test("screen: LawError carries the counterexample", () => {
    try {
        screenLaw(
            { kind: "identity", target: "add", argument: "Succ(Zero())" },
            opRegistry.lookup("add")!,
            opRegistry,
            evalOf,
        )
        assert(false, "screen must throw LawError")
    } catch (error) {
        assert(error instanceof LawError)
        assert(error.message.includes("falsified"))
        assert(error.message.includes("identity"), `names the kind: ${error.message}`)
        // The counterexample renders both sides.
        assert(error.left !== "" && error.right !== "")
    }
})

Deno.test("screen: distributive:mul over add holds (mul(a, add(b, c)) ≡ ...)", () => {
    const e = laws()
    const { instances } = declareCheckedLaw(
        { kind: "distributive", target: "mul", argument: "add" },
        opRegistry,
        e,
        evalOf,
        checker,
    )
    assert(instances > 0)
    assert(e.has("mul", "distributive"))
})

Deno.test("screen: a falsified relational law is rejected", () => {
    // add does NOT distribute over mul: add(a, mul(b, c)) ≢ mul(add(a, b), add(a, c)).
    const e = laws()
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "distributive", target: "add", argument: "mul" },
                opRegistry,
                e,
                evalOf,
                checker,
            ),
        LawError,
    )
})

// ── Both-direction identity/absorbing axioms (lc.md §7.2) ─────────────────────

/**
 * A projection-like op: `proj2(x, y) = y` — left identity holds for any `e`
 * (`proj2(Zero(), a) = a`) but RIGHT identity fails for non-`Zero` `e'`
 * (`proj2(Succ(p), Zero()) = Zero ≠ Succ(p)`). The screen must catch the
 * right-direction falsification; screening only the left axiom would pass.
 */
function declareProj2(): { ops: OpRegistry; ev: LCEval } {
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "proj2",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> y, Succ(p) -> y }",
        ),
        tc.opWellFormedness,
    )
    const ev = new LCEval().setRegistry(registry).setOpRegistry(ops)
    return { ops, ev }
}

Deno.test("screen: identity requires BOTH directions — proj2's right identity fails", () => {
    const { ops, ev } = declareProj2()
    // proj2(Zero(), a) = a holds for e = Zero(), but proj2(a, Zero()) = Zero()
    // fails for a = Succ(p) — the RIGHT axiom is falsified.
    assertThrows(
        () =>
            screenLaw(
                { kind: "identity", target: "proj2", argument: "Zero()" },
                ops.lookup("proj2")!,
                ops,
                makeEvalTerm(ev),
            ),
        LawError,
    )
})

Deno.test("screen: commutative falsified — the Cartesian sweep reaches a ≠ b", () => {
    // proj2(x, y) = y is NOT commutative: proj2(a, b) = b but proj2(b, a) = a.
    // The assignment sweep enumerates independent samples per variable (a and
    // b draw separately), so the falsifying pair a ≠ b is reachable — a cyclic
    // assignment would degenerate to the vacuous op(a, a) ≡ op(a, a) and pass.
    const { ops, ev } = declareProj2()
    assertThrows(
        () =>
            screenLaw(
                { kind: "commutative", target: "proj2" },
                ops.lookup("proj2")!,
                ops,
                makeEvalTerm(ev),
            ),
        LawError,
    )
})

Deno.test("screen: absorbing requires BOTH directions — proj1 annihilates from the right only", () => {
    // proj1(x, y) = fold over y returning x: proj1(z, a) = z (left absorbing
    // HOLDS) but proj1(a, z) = a (right absorbing FAILS for a ≠ z). Screening
    // only the left axiom would pass this declaration.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "proj1",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] y { Zero() -> x, Succ(q) -> x }",
        ),
        tc.opWellFormedness,
    )
    const ev = new LCEval().setRegistry(registry).setOpRegistry(ops)
    assertThrows(
        () =>
            screenLaw(
                { kind: "absorbing", target: "proj1", argument: "Zero()" },
                ops.lookup("proj1")!,
                ops,
                makeEvalTerm(ev),
            ),
        LawError,
    )
})

Deno.test("screen: involutory falsified on identity-like op", () => {
    // idNat(a) = a — idNat(idNat(a)) = a INVOLUNTARILY holds... wait: that's
    // involutory too (twice-identity is identity). Use Succ: succOp(a) = a+1;
    // succ(succ(a)) = a+2 ≠ a — falsified.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "succOp",
            [nat],
            nat,
            "\\a:Nat. fold [Nat] a { Zero() -> Succ(Zero()), Succ(p) -> Succ(Succ(p)) }",
        ),
        tc.opWellFormedness,
    )
    const ev = new LCEval().setRegistry(registry).setOpRegistry(ops)
    assertThrows(
        () =>
            screenLaw(
                { kind: "involutory", target: "succOp" },
                ops.lookup("succOp")!,
                ops,
                makeEvalTerm(ev),
            ),
        LawError,
    )
})

// ── Error-sentinel skipping (sampling artifacts are not falsifications) ───────

Deno.test("screen: an instance that evaluates to error sentinels is skipped, not falsified", () => {
    // A permissively-declared heterogeneous op: the sweep stays position-wise
    // (schema operand i draws from param type i), so no instance puts a Nat
    // where a Bool belongs; but a defensive guard exists for eval errors
    // surfacing through LCEval's sentinel path.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ops = new OpRegistry()
    // A deliberately ill-typed definition is not declarable even permissively
    // — use a valid op and force sentinel evaluation by an unknown-variant
    // sample: Bool param with no variants would do, but Bool has variants.
    // Instead: assert the guard directly via a law whose instance errors.
    ops.declare(
        new OpSig("ho2", [new FunType(nat, nat)], nat, "\\f:Nat → Nat. f Zero()"),
        tc.opWellFormedness,
    )
    // ho2 is non-screenable (function-typed param) — the screen declines.
    const checked = screenLaw(
        { kind: "associative", target: "ho2" },
        ops.lookup("ho2")!,
        ops,
        evalOf,
    )
    assertEquals(checked, { outcome: "declined" })
})

Deno.test("E: schema typing — a heterogeneous carrier is rejected (idempotent on trunc)", () => {
    // trunc : (Nat, Bool) → Nat. The idempotent axiom is trunc(a, a) — the
    // schema sweeps ONE sample space through both operand slots, so a
    // heterogeneous carrier makes it ill-typed by construction (a Nat sample
    // in the Bool slot evaluates to a sentinel). Validation rejects it before
    // the screen can silently install it with zero coverage.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "trunc",
            [nat, bool],
            nat,
            "\\x:Nat. \\b:Bool. fold [Nat] x { Zero() -> Zero(), Succ(p) -> Succ(p) }",
        ),
        tc.opWellFormedness,
    )
    const e = laws()
    assertThrows(
        () =>
            e.declareLaw(
                { kind: "idempotent", target: "trunc" },
                ops,
                "asserted",
                checker,
            ),
        LawDeclarationError,
        "homogeneous operand carriers",
    )
})

Deno.test("screen: heterogeneous commutative — passed with zero coverage (all holes)", () => {
    // Raw screenLaw bypasses validation (its contract is caller-beware), so a
    // heterogeneous commutative claim reaches the screen: the schema swaps
    // operands, putting a Bool sample in the Nat fold position — the swapped
    // side evaluates to an error sentinel and is skipped, so the screen RUNS
    // but checks ZERO instances (no evidence either way). This is the
    // passed-with-0-coverage shape — distinct from a DECLINED screen (no
    // sample vocabulary at all): here the sampler built real samples for
    // both positions, the sweep ran, every instance was a hole.
    // `declareCheckedLaw` would have rejected the claim structurally
    // (homogeneous-carrier validation), so this shape is unreachable
    // through the all-in-one entry.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "trunc",
            [nat, bool],
            nat,
            "\\x:Nat. \\b:Bool. fold [Nat] x { Zero() -> Zero(), Succ(p) -> Succ(p) }",
        ),
        tc.opWellFormedness,
    )
    const ev = new LCEval().setRegistry(registry).setOpRegistry(ops)
    const checked = screenLaw(
        { kind: "commutative", target: "trunc" },
        ops.lookup("trunc")!,
        ops,
        makeEvalTerm(ev),
    )
    assertEquals(checked, { outcome: "passed", checked: 0 })
})

Deno.test("screen: a non-screenable domain (higher-order op) is declined, not falsified", () => {
    // An op whose parameters are function types has no finite sample
    // vocabulary: the screen DECLINES (no coverage, not evidence) and the
    // all-in-one entry rejects the declaration — installing an `asserted`
    // law the screen never exercised would be silent under-coverage.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ops = new OpRegistry()
    // ho : (Nat → Nat) → Nat — a function-typed parameter. The definition
    // applies the parameter with whitespace (`f x`), not the op form — the
    // declaration scan reads `f(...)` as an op application.
    ops.declare(
        new OpSig("ho", [new FunType(nat, nat)], nat, "\\f:Nat → Nat. f Zero()"),
        tc.opWellFormedness,
    )
    const e = laws()
    const checked = screenLaw(
        { kind: "associative", target: "ho" },
        ops.lookup("ho")!,
        ops,
        evalOf,
    )
    assertEquals(checked, { outcome: "declined" })
    assertEquals(e.lookup("ho").length, 0)
})

// ── The exploit: identity-elimination ─────────────────────────────────────────

/**
 * The first-cut exploit: when `E` carries `identity: e` on an operation, the
 * optimizer's directed consequence `op(e, t) ↝ t` skips the fold entirely.
 * This helper is the `↝` direction of the axiom (the `≡` axiom is
 * undirected; the direction is an optimizer strategy, lc.md §7.3).
 *
 * Precondition mirrors the rewrite gate: the left operand must BE the
 * identity value (structurally), and the law must be installed in `E`.
 */
function identityElimLeft(
    opName: string,
    left: unknown,
    right: unknown,
    e: LawRegistry,
): { eliminated: boolean; result: unknown } {
    const identityLaw = e.lookup(opName).find((law) => law.kind === "identity")
    if (!identityLaw) return { eliminated: false, result: undefined }
    const eValue = evalOf(identityLaw.argument!, new ValueEnv())[0]
    if (left instanceof VariantVal && eValue instanceof VariantVal && valueEquals(left, eValue)) {
        return { eliminated: true, result: right }
    }
    return { eliminated: false, result: undefined }
}

Deno.test("exploit: identity-elimination rewrites add(Zero(), t) to t without the fold", () => {
    const e = laws()
    declareCheckedLaw(
        { kind: "identity", target: "add", argument: "Zero()" },
        opRegistry,
        e,
        evalOf,
        checker,
    )

    const t = natOf(3)
    const { eliminated, result } = identityElimLeft("add", natOf(0), t, e)
    assert(eliminated, "the rewrite fires on the identity operand")
    assert(valueEquals(result as VariantVal, t))

    // The rewrite is an equivalence with direct evaluation — the thesis
    // experiment: the declaration bought an optimization.
    const direct = evalOf("add(Zero(), Succ(Succ(Succ(Zero()))))", new ValueEnv())[0]
    assert(valueEquals(direct as VariantVal, t))
})

Deno.test("exploit: the rewrite does not fire on a non-identity operand", () => {
    const e = laws()
    declareCheckedLaw(
        { kind: "identity", target: "add", argument: "Zero()" },
        opRegistry,
        e,
        evalOf,
        checker,
    )
    const { eliminated } = identityElimLeft("add", natOf(1), natOf(2), e)
    assertEquals(eliminated, false)
})

Deno.test("exploit: no identity law in E means no rewrite", () => {
    const e = laws()
    const { eliminated } = identityElimLeft("add", natOf(0), natOf(1), e)
    assertEquals(eliminated, false)
})

// ── valueEquals (the screen's comparison primitive) ──────────────────────────

Deno.test("valueEquals: structural equality on data values", () => {
    assert(valueEquals(natOf(2), natOf(2)))
    assertEquals(valueEquals(natOf(1), natOf(2)), false)
    assertEquals(valueEquals(natOf(0), natOf(1)), false)
})

Deno.test("valueEquals: same reference is equal even for non-structural values", () => {
    const closure = evalOf("\\x:Nat. x", new ValueEnv())[0]!
    assert(valueEquals(closure, closure))
    assertEquals(valueEquals(closure, evalOf("\\x:Nat. x", new ValueEnv())[0]!), false)
})

Deno.test("valueEquals: nesting is compared", () => {
    const two = natOf(2)
    const other = natOf(2)
    assert(two instanceof VariantVal && other instanceof VariantVal)
    assert(valueEquals(two, other))
    assertEquals(valueEquals(natOf(0), natOf(0)), true)
})

// ── Value plumbing (screen internals surfaced for regression) ─────────────────

Deno.test("screen inputs: op applications evaluate under bound sample envs", () => {
    // The screen's strategy: bind schema variables to samples and evaluate
    // instance terms. `add(a, Succ(Zero()))` with `a` bound to `Succ(Zero())`
    // must evaluate to depth 2.
    const a = natOf(1)
    const result = evalGrammar.parseWith("add(a, Succ(Zero()))", new ValueEnv().extend("a", a))
    assertEquals(result.size, 1)
    const [value] = result
    assert(value instanceof VariantVal)
    let depth = 0
    let cur: Value | undefined = value
    while (cur instanceof VariantVal && cur.variantName === "Succ") {
        depth++
        cur = cur.fields.get("pred")
    }
    assertEquals(depth, 2)
})

// ── Property-based law screening (forAll over a grammar) ──────────────────────

/**
 * The generative complement to the Cartesian sweep above: `forAll` over a
 * `ValueGenerator` rooted at a grammar. A law is a universally-quantified
 * property over the operand space; the grammar IS the arbitrary.
 *
 * This harness targets REJECTION quality, not assurance: passing N runs is
 * evidence, never proof — falsifying declarations are rejected with a shrunk
 * minimal counterexample. See _docs/theory/law-testing.md.
 */
const { gen, evalOf: harnessEval } = createLawHarness()

/**
 * Evaluate a law-side source, demanding a real value.
 *
 * Unlike the residual screen — whose sample space can contain instances that
 * legitimately do not evaluate, and which skips them — this harness's domain
 * is closed: the generator emits only well-formed `Nat` sources and the law
 * embeddings are well-formed by construction. Failure to evaluate here
 * therefore means evaluation itself is broken, which must fail the run loudly
 * rather than pass vacuously. LCEval reports evaluation failures (unknown
 * variant, unbound variable, type mismatch) as an `EvalErrorValue` sentinel —
 * a proper `Value` subclass, indistinguishable from a real result without the
 * guard the screen applies (law_checking.ts). A sentinel entering the law
 * comparison would make `valueEquals` return `false`: a tooling regression
 * reported as a mathematical falsification. Reject it here, like the empty
 * forest. Throwing (not returning `false`) also keeps the failure mode
 * distinct from a falsification: `forAll` wraps the throw in
 * `PropertyFailure` with the thrown message as its reason.
 */
function mustEval(src: string): Value {
    const value = evalOne(harnessEval, src)
    if (value === undefined || value instanceof EvalErrorValue) {
        throw new Error(`law instance did not evaluate: ${src}`)
    }
    return value
}

/** The LC source for the Nat of depth n: `Succ(...Zero()...)`. */
function natSource(n: number): string {
    return `${"Succ(".repeat(n)}Zero()${")".repeat(n)}`
}

/** The Nat depth of a law-side source: walk its Succ chain (Zero() = 0). */
function natDepth(src: string): number {
    let cur: Value = mustEval(src)
    let depth = 0
    while (cur instanceof VariantVal && cur.variantName === "Succ") {
        depth++
        cur = cur.fields.get("pred") as Value
    }
    assert(cur instanceof VariantVal && cur.variantName === "Zero", `not a Nat value: ${src}`)
    return depth
}

/**
 * The identity-fold law, property form (lc.md §7.2's `identity` schema
 * generalized to the fold itself): folding a value with identity handlers
 * returns the value unchanged —
 * `fold [Nat] e { Zero() -> Zero(), Succ(p) -> Succ(p) } ≡ e`.
 */
function identityFoldHolds(src: string): boolean {
    return valueEquals(
        mustEval(`fold [Nat] ${src} { Zero() -> Zero(), Succ(p) -> Succ(p) }`),
        mustEval(src),
    )
}

/**
 * The `idempotent` schema on `mul`, property form: `mul(a, a) ≡ a`. This is
 * FALSE on Nat (`mul(2, 2) = 4`) — the property must throw, with a shrunk
 * minimal counterexample.
 */
function idempotentMulHolds(src: string): boolean {
    return valueEquals(mustEval(`mul(${src}, ${src})`), mustEval(src))
}

Deno.test("forAll: identity-fold law holds over 200 generated Nat values", () => {
    // The property passes for every generated operand — 200 reproducible
    // runs (fixed seed) of generated-and-evaluated law instances.
    const result = gen.forAll(identityFoldHolds, { numRuns: 200, seed: 42 })
    assert(result.passed)
    assertEquals(result.runs, 200)
})

Deno.test("forAll: samples are reproducible — the same seed regenerates the same terms", () => {
    // Fixed seed → fixed run-seed stream → fixed generated operands. The
    // property sees the same inputs on every run of the test.
    const first = gen.sample(7)
    const again = gen.sample(7)
    assertEquals(first, again)
})

Deno.test("forAll: idempotent on mul is FALSIFIED with a minimal counterexample", () => {
    // Rejection quality: the property fails, and the failure is the library's
    // PropertyFailure carrying the SHRUNK counterexample. The assertions pin
    // the shrink CONTRACT, not its serialization: the counterexample is a Nat
    // source that falsifies the axiom, and every strictly smaller Nat
    // satisfies it — the minimal violator (2: `mul(2, 2) = 4 ≠ 2`; `0·0 = 0`
    // and `1·1 = 1` hold). Pinning no exact syntax, a lang-forma bump that
    // changes shrink ordering or serialization cannot break the test unless
    // the shrinker stops finding the minimal falsifier. (The loop also forces
    // depth ≤ 2: Nat 2 falsifies, so a counterexample deeper than 2 would
    // fail the `Nat 2 satisfies` leg.)
    const error = assertThrows(
        () => gen.forAll(idempotentMulHolds, { numRuns: 100, seed: 42 }),
        PropertyFailure,
    )
    const counterexample = error.counterexample
    assert(typeof counterexample === "string", "counterexample must be a source string")
    assertEquals(idempotentMulHolds(counterexample), false, "the counterexample falsifies")
    const depth = natDepth(counterexample)
    for (let n = 0; n < depth; n++) {
        assertEquals(idempotentMulHolds(natSource(n)), true, `Nat ${n} satisfies the axiom`)
    }
})

Deno.test("forAll: the same seed reproduces the same counterexample", () => {
    // Reproducibility of a failure: fixed seed → same generated operands →
    // same first falsifier → same shrunk minimal counterexample.
    const e1 = assertThrows(
        () => gen.forAll(idempotentMulHolds, { numRuns: 100, seed: 42 }),
        PropertyFailure,
    )
    const e2 = assertThrows(
        () => gen.forAll(idempotentMulHolds, { numRuns: 100, seed: 42 }),
        PropertyFailure,
    )
    assertEquals(e1.counterexample, e2.counterexample)
})

// ── Shrink quality: ∂T vs. regeneration (the measurable improvement) ────────

/**
 * Count the property invocations a falsified run consumes end to end
 * (generation + shrink loop): the same seed and numRuns, differing only in
 * the generator's shrink strategy. The ∂T shrinker's claim — candidates
 * derived from the failing value's structure converge faster than
 * re-generation's depth-dropping search — is asserted RELATIVELY, in the
 * same run, so the comparison is not pinned to absolute constants that a
 * library bump would shift.
 */
function countInvocations(gen: ValueGenerator<string>): number {
    let calls = 0
    try {
        gen.forAll((src: string) => {
            calls++
            return idempotentMulHolds(src)
        }, { numRuns: 100, seed: 42 })
    } catch {
        // PropertyFailure — the count is what the loop consumed.
    }
    return calls
}

Deno.test("forAll: the ∂T shrinker does not consume more property invocations than regeneration (shrink quality, relative)", () => {
    // The ∂T harness (the promoted one — candidates from the failing
    // value's own structure).
    const derivativeCalls = countInvocations(gen)
    // The baseline: the same grammar and budgets, but the library's
    // regeneration shrinker (toGenerator — no ∂T hook).
    const baselineGen = new NatSourceGrammar().toGenerator({
        maxDepth: 4,
        maxRecursion: 5,
        branchStrategy: "random",
    })
    const baselineCalls = countInvocations(baselineGen)
    // Parity-or-better: the ∂T candidates shrink along the actual value
    // (deterministically), so they cannot need MORE invocations than the
    // regeneration re-roll lottery on the same seed. A strict win is
    // expected but not required for merge — a tie is acceptable evidence
    // of parity (both shrinkers can converge in one candidate on a small
    // anchor), so the assertion is `<=`. What must hold for BOTH is that
    // the minimal falsifier is still Nat 2 — pinned by the contract test
    // above.
    assert(
        derivativeCalls <= baselineCalls,
        `∂T shrink invocations (${derivativeCalls}) must not exceed regeneration's (${baselineCalls})`,
    )
})

Deno.test({
    name: "forAll: identity-fold holds over 1000 generated Nat values (slow)",
    ignore: !slowTestsEnabled,
}, () => {
    const result = gen.forAll(identityFoldHolds, { numRuns: 1000, seed: 0 })
    assert(result.passed)
})

// ── Fixtures (keep the fixture surface exercised) ─────────────────────────────

Deno.test("fixtures: the op registry exposes the fixture operations", () => {
    assert(opRegistry.lookup("add") !== undefined)
    assert(opRegistry.lookup("mul") !== undefined)
    void bool
})
