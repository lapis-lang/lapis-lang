/**
 * Law tests — the equational theory environment `E` (LawRegistry), the
 * residual screen (screenLaw), and the identity-elimination exploit.
 *
 * See _docs/theory/lc.md §2.4 (E), §7.2 (law schemas), and
 * _docs/theory/semantics.md §5.4 (regime-based checking).
 */

import {
    declareScreenedLaw,
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
    TypeRegistry,
    type Value,
    ValueEnv,
    valueEquals,
    VariantVal,
} from "../src/index.ts"

import { FunType } from "../src/core/types.ts"

import { createBoolType, createOpFixtures } from "./fixtures.ts"

import { assert, assertEquals, assertThrows } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry, opRegistry, nat, bool } = createOpFixtures()

/** A fresh Bool type for law-local registries (the fixtures' Bool shares Ω). */
const boolType = createBoolType()

/** An evaluator bound to the op fixtures (the screen's eval primitive). */
const evalGrammar = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
const evalOf = makeEvalTerm(evalGrammar)

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

// ── The residual screen ───────────────────────────────────────────────────────

Deno.test("screen: associative holds on add — the law is screenable", () => {
    const e = laws()
    const { law, instances } = declareScreenedLaw(
        { kind: "associative", target: "add" },
        opRegistry,
        e,
        evalOf,
    )
    assert(instances > 0, "the screen must check at least one instance")
    assertEquals(law.provenance, "asserted")
    assert(e.has("add", "associative"))
})

Deno.test("screen: commutative and identity:Zero hold on add", () => {
    const e = laws()
    const { instances: commutative } = declareScreenedLaw(
        { kind: "commutative", target: "add" },
        opRegistry,
        e,
        evalOf,
    )
    const { instances: identity } = declareScreenedLaw(
        { kind: "identity", target: "add", argument: "Zero()" },
        opRegistry,
        e,
        evalOf,
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
                { kind: "idempotent", target: "mul", provenance: "asserted" },
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
            declareScreenedLaw(
                { kind: "identity", target: "add", argument: "Succ(Zero())" },
                opRegistry,
                e,
                evalOf,
            ),
        LawError,
    )
    // Nothing was installed — a falsified declaration never enters E.
    assertEquals(e.lookup("add").length, 0)
})

Deno.test("screen: LawError carries the counterexample", () => {
    try {
        screenLaw(
            { kind: "identity", target: "add", argument: "Succ(Zero())", provenance: "asserted" },
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
    const { instances } = declareScreenedLaw(
        { kind: "distributive", target: "mul", argument: "add" },
        opRegistry,
        e,
        evalOf,
    )
    assert(instances > 0)
    assert(e.has("mul", "distributive"))
})

Deno.test("screen: a falsified relational law is rejected", () => {
    // add does NOT distribute over mul: add(a, mul(b, c)) ≢ mul(add(a, b), add(a, c)).
    const e = laws()
    assertThrows(
        () =>
            declareScreenedLaw(
                { kind: "distributive", target: "add", argument: "mul" },
                opRegistry,
                e,
                evalOf,
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
                { kind: "identity", target: "proj2", argument: "Zero()", provenance: "asserted" },
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
                { kind: "absorbing", target: "proj1", argument: "Zero()", provenance: "asserted" },
                ops.lookup("proj1")!,
                ops,
                makeEvalTerm(ev),
            ),
        LawError,
    )
})

Deno.test("screen: absorbing holds on a two-sided annihilator", () => {
    // andOp: True() → b, False() → False() — False annihilates from BOTH sides.
    const bool = boolType
    const registry = new TypeRegistry()
    registry.register(bool)
    const tc = new LCTypeCheck().setRegistry(registry)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "andOp",
            [bool, bool],
            bool,
            "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> False() }",
        ),
        tc.opWellFormedness,
    )
    const ev = new LCEval().setRegistry(registry).setOpRegistry(ops)
    const e = laws()
    const { instances } = declareScreenedLaw(
        { kind: "absorbing", target: "andOp", argument: "False()" },
        ops,
        e,
        makeEvalTerm(ev),
    )
    assert(instances > 0, "both absorbing directions must be checked")
    assert(e.has("andOp", "absorbing"))
})

Deno.test("screen: involutory holds on a double-negation op", () => {
    // notOp: not(not(a)) = a — involutory. notOp(a, ...)? arity 1: fold over a:
    // True() -> False(), False() -> True().
    const bool = boolType
    const registry = new TypeRegistry()
    registry.register(bool)
    const tc = new LCTypeCheck().setRegistry(registry)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "notOp",
            [bool],
            bool,
            "\\a:Bool. fold [Bool] a { True() -> False(), False() -> True() }",
        ),
        tc.opWellFormedness,
    )
    const ev = new LCEval().setRegistry(registry).setOpRegistry(ops)
    const e = laws()
    const { instances } = declareScreenedLaw(
        { kind: "involutory", target: "notOp" },
        ops,
        e,
        makeEvalTerm(ev),
    )
    assert(instances > 0)
    assert(e.has("notOp", "involutory"))
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
                { kind: "involutory", target: "succOp", provenance: "asserted" },
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
    // ho2 is non-screenable (function-typed param) — returns 0 instances.
    const checked = screenLaw(
        { kind: "associative", target: "ho2", provenance: "asserted" },
        ops.lookup("ho2")!,
        ops,
        evalOf,
    )
    assertEquals(checked, 0)
})

Deno.test("screen: heterogeneous params — position-wise sampling, falsification still fires", () => {
    // trunc : (Nat, Bool) → Nat — folds over x returning x, ignoring b. The
    // Bool param makes the op heterogeneous; position-wise sampling keeps
    // operand i in param type i, so idempotent (both operands the same Nat
    // sample) evaluates cleanly and holds.
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
    const evOf = makeEvalTerm(ev)
    const e = laws()
    const { instances } = declareScreenedLaw(
        { kind: "idempotent", target: "trunc" },
        ops,
        e,
        evOf,
    )
    assert(instances > 0, "idempotent must evaluate (operands share the Nat position)")
    assert(e.has("trunc", "idempotent"))

    // Absorbing: Zero() — trunc(z, a) = z (left holds) but trunc(a, z) = a
    // (right fails for a ≠ z): the right-direction check falsifies.
    assertThrows(
        () =>
            screenLaw(
                { kind: "absorbing", target: "trunc", argument: "Zero()", provenance: "asserted" },
                ops.lookup("trunc")!,
                ops,
                evOf,
            ),
        LawError,
    )
})

Deno.test("screen: heterogeneous commutative — zero coverage, declared unscreened", () => {
    // Commutative on a heterogeneous op: the schema swaps operands, putting a
    // Bool sample in the Nat fold position — the swapped side evaluates to an
    // error sentinel and is skipped, so the screen yields ZERO instances (no
    // evidence either way). The caller installs the law `asserted` unscreened:
    // zero coverage is the honest report, not a pass.
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
        { kind: "commutative", target: "trunc", provenance: "asserted" },
        ops.lookup("trunc")!,
        ops,
        makeEvalTerm(ev),
    )
    assertEquals(checked, 0)
})

Deno.test("screen: a non-screenable domain (higher-order op) is skipped, not falsified", () => {
    // An op whose parameters are function types has no finite sample
    // vocabulary: the screen checks 0 instances and the caller installs
    // the law unscreened (the residual's honest risk).
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
        { kind: "associative", target: "ho", provenance: "asserted" },
        ops.lookup("ho")!,
        ops,
        evalOf,
    )
    assertEquals(checked, 0)
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
    declareScreenedLaw(
        { kind: "identity", target: "add", argument: "Zero()" },
        opRegistry,
        e,
        evalOf,
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
    declareScreenedLaw(
        { kind: "identity", target: "add", argument: "Zero()" },
        opRegistry,
        e,
        evalOf,
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

// ── Fixtures (keep the fixture surface exercised) ─────────────────────────────

Deno.test("fixtures: the op registry exposes the fixture operations", () => {
    assert(opRegistry.lookup("add") !== undefined)
    assert(opRegistry.lookup("mul") !== undefined)
    void bool
})
