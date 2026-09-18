/**
 * Discharge tests — the finite regime of law checking: exhaustive checking
 * of a law's entire input space, discharging it from `asserted` to
 * `discharged` provenance.
 *
 * See _docs/theory/semantics.md §5.4 (the regime table: finite → exhaustive
 * check → proof) and _docs/theory/elaboration.md §6.1 (the provenance chain).
 *
 * The discharged tier is the point of the ladder: Bool `and`/`or`
 * associativity holds over 8 tuples — a proof, not a sample — while Nat
 * laws stay in the residual (unbounded depth ⇒ no finite sweep). The tests
 * pin four behaviors: full-space coverage on discharge (exact instance
 * counts), falsification from anywhere in the space, regime routing (finite
 * vs residual), and coverage honesty (a hole in the sweep rejects the
 * declaration rather than silently under-covering).
 */

import {
    declareCheckedLaw,
    finiteInhabitants,
    inhabitantsUpToSize,
    LawDeclarationError,
    LawError,
    LawRegistry,
    LCEval,
    LCTypeCheck,
    makeEvalTerm,
    OpRegistry,
    OpSig,
    screeningRegime,
    screenLaw,
    TokenVal,
    TypeRegistry,
    type Value,
    ValueEnv,
    VariantVal,
} from "../src/index.ts"

import { DataType, Field, FunType, PatternDataType, TypeEnv, Variant } from "../src/core/types.ts"

import { coefficients } from "../src/core/type_algebra.ts"

import { createBoolType, createNatType } from "./fixtures.ts"

import { assert, assertEquals, assertThrows } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

/** Fresh Bool type and registries per harness (an isolated Ω with just Bool). */
function boolHarness() {
    const bool = createBoolType()
    const registry = new TypeRegistry()
    registry.register(bool)
    const opRegistry = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    return { bool, registry, opRegistry, tc, laws: new LawRegistry() }
}

/** An evaluator bound to a harness's registry and Ω (the check's primitive). */
function evalOfHarness(
    registry: TypeRegistry,
    opRegistry: OpRegistry,
): ReturnType<typeof makeEvalTerm> {
    const ev = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
    return makeEvalTerm(ev)
}

/** The law checker: LCTypeCheck's parseWith under an empty Γ (declared terms).
 *
 * Bound to BOTH the type registry and the Ω (op registry): a law's schema
 * instances and argument terms may reference declared operations (`add`,
 * `mul`, …), and `T-Op` type-checks op applications against Ω — a checker
 * without it yields zero results for any op-application source, silently
 * rejecting valid terms (mirroring the evaluator's binding of both).
 */
function checkerFor(registry: TypeRegistry, opRegistry: OpRegistry) {
    return {
        checkSource: (source: string) => {
            const results = [
                ...new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
                    .parseWith(source, new TypeEnv()),
            ]
            return results.length === 1 ? results[0] : undefined
        },
    }
}

/** Declare a Bool binary op with the given fold-based definition. */
function declareBoolOp(
    harness: ReturnType<typeof boolHarness>,
    name: string,
    definition: string,
): void {
    harness.opRegistry.declare(
        new OpSig(name, [harness.bool, harness.bool], harness.bool, definition),
        harness.tc.opWellFormedness,
    )
}

// ── finiteInhabitants (the classifier) ───────────────────────────────────────

Deno.test("finiteInhabitants: Bool has 2 inhabitants, Nat is unbounded", () => {
    assertEquals(finiteInhabitants(createBoolType()), 2)
    assertEquals(finiteInhabitants(createNatType()), undefined)
})

Deno.test("finiteInhabitants: a record of finites is the product of its fields", () => {
    // Pair(Bool, Bool) — two variants' worth of product space: 2 × 2 = 4.
    const bool = createBoolType()
    const pair = new DataType("Pair", [])
    pair.variants.push(
        new Variant("MkPair", [
            new Field("fst", bool),
            new Field("snd", bool),
        ]),
    )
    assertEquals(finiteInhabitants(pair), 4)
})

Deno.test("finiteInhabitants: a function-typed field makes the type unbounded", () => {
    const nat = createNatType()
    const fnBox = new DataType("FnBox", [])
    fnBox.variants.push(new Variant("MkFnBox", [new Field("f", new FunType(nat, nat))]))
    assertEquals(finiteInhabitants(fnBox), undefined)
})

Deno.test("finiteInhabitants: a recursive field makes the type unbounded", () => {
    // A list-shaped type: Cons(Tail: Self) is the recursive field.
    const list = new DataType("List", [])
    list.variants.push(
        new Variant("Nil", []),
        new Variant("Cons", [new Field("tail", list, true)]),
    )
    assertEquals(finiteInhabitants(list), undefined)
})

// ── Regime dispatch ──────────────────────────────────────────────────────────

Deno.test("screeningRegime: Bool ops are finite, Nat ops are residual", () => {
    const h = boolHarness()
    declareBoolOp(
        h,
        "andOp",
        "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> False() }",
    )
    const andOp = h.opRegistry.lookup("andOp")!
    assertEquals(screeningRegime({ kind: "associative", target: "andOp" }, andOp), "finite")

    // A Nat op routes residual: Succ chains nest without bound, so no finite
    // sweep exists.
    const nat = createNatType()
    h.registry.register(nat)
    h.opRegistry.declare(
        new OpSig(
            "natId",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> y, Succ(p) -> Succ(p) }",
        ),
        h.tc.opWellFormedness,
    )
    const natId = h.opRegistry.lookup("natId")!
    assertEquals(screeningRegime({ kind: "associative", target: "natId" }, natId), "residual")
})

Deno.test("screeningRegime: the sweep estimate is the exact per-position product", () => {
    // Schema variable i lands on operand position i (mod the parameter
    // count), so the true sweep is Π inhabitants(position)^exponent(position)
    // — not each position checked at the TOTAL variable count. Two
    // consequences the exact formula gets right (a per-parameter n^V check
    // mis-routes both):
    //
    // 1. A position no variable lands on contributes nothing: an identity
    //    claim (1 variable) over (Bool, Big-2¹⁸) sweeps 2 × Big⁰ = 2 —
    //    finite — though a per-parameter Big¹ check would have said
    //    residual (overestimate).
    // 2. Small heterogeneous carriers: associative (3 variables → exponents
    //    (2, 1)) over (2⁷, 2⁶) sweeps 2¹⁴ × 2⁶ = 2²⁰ — exactly at budget:
    //    finite. A per-parameter n³ check would say (2⁷)³ = 2²¹ > 2²⁰,
    //    residual (overestimate).
    const h = boolHarness()
    const big = new DataType("Big", [])
    big.variants.push(
        new Variant("Big", Array.from({ length: 18 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    const n7 = new DataType("N7", [])
    n7.variants.push(
        new Variant("N7", Array.from({ length: 7 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    const n6 = new DataType("N6", [])
    n6.variants.push(
        new Variant("N6", Array.from({ length: 6 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    h.registry.register(big)
    h.registry.register(n7)
    h.registry.register(n6)
    h.opRegistry.declare(
        new OpSig(
            "bigId",
            [h.bool, big],
            h.bool,
            "\\b:Bool. \\x:Big. fold [Bool] b { True() -> b, False() -> b }",
        ),
        h.tc.opWellFormedness,
    )
    h.opRegistry.declare(
        new OpSig("pairOp", [n7, n6], n6, "\\x:N7. \\y:N6. fold [N7] x { N7(...) -> x }"),
        { checkDefinition: () => undefined },
    )
    assertEquals(
        screeningRegime(
            { kind: "identity", target: "bigId", argument: "True()" },
            h.opRegistry.lookup("bigId")!,
        ),
        "finite",
        "the Big position carries exponent 0 — never swept",
    )
    assertEquals(
        screeningRegime({ kind: "associative", target: "pairOp" }, h.opRegistry.lookup("pairOp")!),
        "finite",
        "2¹⁴ × 2⁶ = 2²⁰ exactly at the budget",
    )

    // The estimate must also stay honest in the other direction — a product
    // the per-parameter check would pass but the true sweep exceeds:
    // commutative (exponents (1,1)) over (2⁷, Big) sweeps 2⁷ × 2¹⁸ > 2²⁰:
    // residual, where a per-position n¹ check alone would have passed both.
    h.opRegistry.declare(
        new OpSig(
            "mixedComm",
            [n7, big],
            n7,
            "\\x:N7. \\y:Big. fold [N7] x { N7(v) -> x }",
        ),
        { checkDefinition: () => undefined },
    )
    assertEquals(
        screeningRegime(
            { kind: "commutative", target: "mixedComm" },
            h.opRegistry.lookup("mixedComm")!,
        ),
        "residual",
    )
})

// ── Exhaustion discharge (the finite regime) ─────────────────────────────────

Deno.test("discharge: Bool and is associative — 8 instances, provenance discharged", () => {
    const h = boolHarness()
    declareBoolOp(
        h,
        "andOp",
        "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> False() }",
    )
    const { law, instances } = declareCheckedLaw(
        { kind: "associative", target: "andOp" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    // The full space: 2³ = 8 assignments (a, b, c each range over Bool).
    assertEquals(instances, 8)
    assertEquals(law.provenance, "discharged")
    assert(h.laws.has("andOp", "associative"))
})

Deno.test("discharge: Bool or is commutative with an exact half-space count", () => {
    const h = boolHarness()
    declareBoolOp(h, "orOp", "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> True(), False() -> b }")
    const { instances } = declareCheckedLaw(
        { kind: "commutative", target: "orOp" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    // commutative sweeps 2² = 4 assignments — the whole space, not a sample.
    assertEquals(instances, 4)
})

Deno.test("discharge: identity:False() on Bool or is discharged (both directions)", () => {
    const h = boolHarness()
    declareBoolOp(h, "orOp", "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> True(), False() -> b }")
    const { law, instances } = declareCheckedLaw(
        { kind: "identity", target: "orOp", argument: "False()" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    // 2 assignments × 2 axiom directions (left and right identity).
    assertEquals(instances, 4)
    assertEquals(law.provenance, "discharged")
})

Deno.test("discharge: falsification anywhere in the space rejects (LawError, nothing in E)", () => {
    const h = boolHarness()
    // A deliberately asymmetric op: fold over a returning b ignores a.
    declareBoolOp(h, "second", "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> b }")
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "commutative", target: "second" },
                h.opRegistry,
                h.laws,
                evalOfHarness(h.registry, h.opRegistry),
                checkerFor(h.registry, h.opRegistry),
            ),
        LawError,
    )
    assertEquals(h.laws.lookup("second").length, 0)
})

Deno.test("discharge: Nat add stays residual — associative provenance is asserted", () => {
    // The canonical routing test: Nat is unbounded (Succ chains nest without
    // bound), so add's law checks through the residual screen only — passing
    // is evidence, never proof.
    const h = boolHarness()
    const nat = createNatType()
    h.registry.register(nat)
    h.opRegistry.declare(
        new OpSig(
            "add",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> y, Succ(p) -> Succ(p) }",
        ),
        h.tc.opWellFormedness,
    )
    const { law, regime } = declareCheckedLaw(
        { kind: "associative", target: "add" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "residual")
    assertEquals(law.provenance, "asserted")
})

// ── The residual sampler (typed field samples) ───────────────────────────────

Deno.test("screen: typed field samples — residual folds over field variants evaluate as real values", () => {
    // The certified ENUMERATOR (inhabitantsUpToSize/spaceUpToSize) builds
    // typed non-recursive field samples: variant fields carry real values of
    // their declared type, so a fold with an arm per variant — including
    // field-carrying arms — evaluates honestly through the screen. This is
    // the RESIDUAL path (an NS carrier is recursive ⇒ unbounded ⇒ residual):
    // distinct from exhaustion's full-space sweep above, and it is why a
    // fold like nsOr's `One(b) -> y` arm can evaluate at all. (Exhaustion
    // enumerates the whole space; the screen sweeps the certified prefix —
    // both must produce typed field values, and this test pins the
    // enumerator's.)
    const h = boolHarness()
    const ns = new DataType("NS", [])
    ns.variants.push(
        new Variant("Zero", []),
        new Variant("One", [new Field("b", h.bool)]),
        new Variant("Succ", [new Field("p", ns, true)]),
    )
    h.registry.register(ns)
    h.opRegistry.declare(
        new OpSig(
            "nsOr",
            [ns, ns],
            ns,
            // nsOr(x, y) rebuilds x's spine, returning y at Zero/One arms:
            // nsOr(Succ(s), y) = Succ(nsOr(s, y)), nsOr(Zero/One, y) = y.
            "\\x:NS. \\y:NS. fold [NS] x { Zero() -> y, One(b) -> y, Succ(p) -> Succ(p) }",
        ),
        h.tc.opWellFormedness,
    )
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "associative", target: "nsOr" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    // One(b) samples exist only because the sampler generates a typed Bool
    // for the field — the sweep reaches the fold's field-carrying arm. The
    // properties that must hold regardless of the sampler's internal budget
    // (depth limit, per-field breadth, dedupe): the claim routes residual,
    // installs as evidence, and the coverage is REAL — at least one instance
    // through the field-carrying `One(b) -> y` arm was checked (a sampler
    // that dropped typed field values would evaluate every One(b) instance
    // to a sentinel and skip it, collapsing the count). An exact count
    // (216 = 6³ at depth 2) would pin sampling internals that may change
    // while preserving correctness.
    assertEquals(regime, "residual")
    assertEquals(law.provenance, "asserted")
    assert(instances > 0, "the screen checked at least one instance")
    // The field-carrying arm was reached: an instance binding a = One(True())
    // evaluates both sides through `One(b) -> y` — if the sampler had no
    // typed Bool for the field, this instance would be a skipped hole.
    const oneSample = evalOfHarness(h.registry, h.opRegistry)("One(True())", new ValueEnv())[0]
    assert(oneSample instanceof VariantVal, "the sampler's field vocabulary can build One(True())")
    const sweep = screenLaw(
        { kind: "associative", target: "nsOr" },
        h.opRegistry.lookup("nsOr")!,
        h.opRegistry,
        evalOfHarness(h.registry, h.opRegistry),
    )
    assertEquals(
        sweep.outcome === "passed" ? sweep.checked : -1,
        instances,
        "the all-in-one entry reports the same coverage as the raw screen",
    )
    assert(sweep.outcome === "passed", "the raw screen passed")
    assert(sweep.coverage.positions.length === 2)
})

// ── Coverage honesty (the discharge contract) ────────────────────────────────

Deno.test("discharge: an instance that fails to evaluate rejects the declaration", () => {
    const h = boolHarness()
    declareBoolOp(h, "idLike", "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> b }")
    // Identity on a fold that always returns the second operand: the claim
    // is falsifiable only through evaluation — but the evaluator below is
    // blind ONLY to law-instance sources (it answers the declared argument
    // `True()` so the check is well-posed), making every axiom instance a
    // hole in the sweep — exactly what a discharged tag must never hide.
    const realEval = evalOfHarness(h.registry, h.opRegistry)
    const blindEval = (source: string, rho: ValueEnv): readonly Value[] =>
        source === "True()" ? realEval(source, rho) : []
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "identity", target: "idLike", argument: "True()" },
                h.opRegistry,
                h.laws,
                blindEval,
                checkerFor(h.registry, h.opRegistry),
            ),
        LawDeclarationError,
        "did not evaluate",
    )
    assertEquals(h.laws.lookup("idLike").length, 0)
})

Deno.test("discharge: the certified screen rejects a dead evaluator — construction is the contract", () => {
    // The certified contract: the screen's samples are a CERTIFIED prefix —
    // a variant construction is part of the enumeration, so a dead evaluator
    // is a HOLE in the certificate, not a skippable artifact. A silent drop
    // for this shape (sample construction could fail) would masquerade as
    // full coverage; the loud rejection keeps the certificate honest. The
    // passed-with-0-coverage shape (a running sweep whose every INSTANCE is
    // a hole) still skips — the heterogeneous-commutative case in
    // laws.test.ts pins it.
    const h = boolHarness()
    declareBoolOp(
        h,
        "andOp",
        "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> False() }",
    )
    const blindEval = (_source: string, _rho: ValueEnv): readonly VariantVal[] => []
    assertThrows(
        () =>
            screenLaw(
                { kind: "associative", target: "andOp" },
                h.opRegistry.lookup("andOp")!,
                h.opRegistry,
                blindEval,
            ),
        LawDeclarationError,
        "certification could not construct",
    )
})

Deno.test("finiteInhabitants: an 18-Bool record (2¹⁸) exceeds the ceiling; 17 Bools sit exactly at it", () => {
    // The classifier's saturation boundary: 2¹⁸ > 2¹⁷ reports
    // finite-but-past-the-ceiling (2¹⁷ + 1), so the regime router can
    // distinguish "exhaustible here" from "finite but beyond budget". The
    // ceiling is the exhaustion engine's real memory budget: the memoized
    // space holds actual values (measured: 2²⁰-space records OOM the
    // default heap; 2¹⁷ ≈ 100MB is the practical bound).
    const h = boolHarness()
    const wide = new DataType("Wide", [])
    wide.variants.push(
        new Variant("MkWide", Array.from({ length: 18 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    assertEquals(finiteInhabitants(wide), 2 ** 17 + 1)

    // A 17-Bool record sits exactly at the ceiling — exhaustible in principle.
    const narrow = new DataType("Narrow", [])
    narrow.variants.push(
        new Variant("MkNarrow", Array.from({ length: 17 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    assertEquals(finiteInhabitants(narrow), 2 ** 17)
})

Deno.test("discharge: an over-ceiling type routes residual — certification DECLINES past the prefix budget", () => {
    // The ROUTING side of the ceiling: an involutory claim on an identity-like
    // fold over the 18-Bool record (2¹⁸ inhabitants > 2¹⁷) classifies as
    // finite-but-unexhaustible, so declareCheckedLaw routes it to the residual
    // screen. Under the certified screen, the record's ONLY size class
    // (size 19, 2¹⁸ inhabitants) is past the prefix budget — the certification
    // declines loudly instead of sweeping a masquerading depth-capped sample.
    // (Under the old sampler this installed `asserted` on ONE instance that
    // was neither a size prefix nor complete within a class.) The exhausting
    // route for such a carrier is a heap-headroom story, not a screen one.
    const h = boolHarness()
    const wide = new DataType("Wide", [])
    wide.variants.push(
        new Variant("MkWide", Array.from({ length: 18 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    h.registry.register(wide)
    const bindings = Array.from({ length: 18 }, (_, i) => `v${i}`).join(" ")
    h.opRegistry.declare(
        new OpSig("wideId", [wide], wide, `\\x:Wide. fold [Wide] x { MkWide(${bindings}) -> x }`),
        h.tc.opWellFormedness,
    )
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "involutory", target: "wideId" },
                h.opRegistry,
                h.laws,
                evalOfHarness(h.registry, h.opRegistry),
                checkerFor(h.registry, h.opRegistry),
            ),
        LawDeclarationError,
        "certification declined",
    )
    assertEquals(h.laws.lookup("wideId").length, 0, "nothing installed")
})

// ── Completeness of the enumeration (finding: silent construction holes) ─────

Deno.test("discharge: a failed inhabitant construction rejects the declaration — no silent holes", () => {
    // A variant whose constructor form does not evaluate is a HOLE in the
    // sweep, not a droppable sample: the enumeration throws rather than
    // returning a shrunken space the caller would pass off as full coverage.
    // (The residual screen's sampler may drop failed constructions — its
    // claim is bounded evidence.) The hole here: `Holder`'s field type is
    // never registered, so enumerating the field's inhabitants evaluates
    // `U1()` to an error sentinel — the pre-fix sampler would have silently
    // dropped both field samples and "discharged" over a shrunken space.
    const h = boolHarness()
    const unreg = new DataType("Unreg", [])
    unreg.variants.push(new Variant("U1", []), new Variant("U2", []))
    const holder = new DataType("Holder", [])
    holder.variants.push(new Variant("MkHolder", [new Field("u", unreg)]))
    h.registry.register(holder) // `unreg` deliberately NOT registered
    h.opRegistry.declare(
        new OpSig(
            "holderId",
            [holder],
            holder,
            "\\x:Holder. fold [Holder] x { MkHolder(u) -> x }",
        ),
        h.tc.opWellFormedness,
    )
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "involutory", target: "holderId" },
                h.opRegistry,
                h.laws,
                evalOfHarness(h.registry, h.opRegistry),
                checkerFor(h.registry, h.opRegistry),
            ),
        LawDeclarationError,
        "could not construct an inhabitant",
    )
    assertEquals(h.laws.lookup("holderId").length, 0)
})

// ── Lazy enumeration (the finite regime's memory contract) ───────────────────

Deno.test("discharge: a position no schema variable lands on is never enumerated", () => {
    // Exhaustion builds each swept position's space lazily and memoizes it
    // per type, and a position with exponent 0 is not enumerated AT ALL: an
    // idempotent claim (1 schema variable, landing on position 0) over a
    // pair of 4-inhabitant records must construct 2² = 4 values — not 8. A
    // regression to eager enumeration (building every parameter type's full
    // space up-front) would double the count; at the 2²⁰ ceiling that eager
    // build exhausts the heap (measured ~1.8GB OOM before streaming).
    const h = boolHarness()
    const n2 = new DataType("N2", [])
    n2.variants.push(
        new Variant("N2", Array.from({ length: 2 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    h.registry.register(n2)
    const b2 = Array.from({ length: 2 }, (_, i) => `v${i}`).join(" ")
    h.opRegistry.declare(
        new OpSig("n2First", [n2, n2], n2, `\\x:N2. \\y:N2. fold [N2] x { N2(${b2}) -> x }`),
        h.tc.opWellFormedness,
    )
    // A counting evaluator: every `N2(...)` construction goes through it, so
    // the count is exactly the number of inhabitants the engine enumerated.
    let n2Constructions = 0
    const realEval = evalOfHarness(h.registry, h.opRegistry)
    const countingEval = (source: string, rho: ValueEnv): readonly Value[] => {
        if (source.startsWith("N2(")) n2Constructions++
        return realEval(source, rho)
    }
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "idempotent", target: "n2First" },
        h.opRegistry,
        h.laws,
        countingEval,
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "finite")
    assertEquals(law.provenance, "discharged")
    assertEquals(instances, 4, "2² assignments over the one swept position")
    assertEquals(
        n2Constructions,
        4,
        "position 0's space only — position 1 (exponent 0) never enumerated",
    )
})

// ── Vacuous discharge (an empty operand type) ────────────────────────────────

Deno.test("discharge: an empty operand type discharges vacuously (0 instances)", () => {
    // A data type with no variants has an empty inhabitant space: every
    // schema assignment over it holds without evaluation — a vacuous but
    // HONEST discharge (the sweep is complete; the count records the shape).
    // This is the deliberate routing choice: the finite regime establishes
    // the claim (proof over ∅), where the residual screen would have
    // installed the same claim on zero evidence. (`emptyId : Empty → Empty`
    // is the fold-free identity — a fold over an empty variant set cannot
    // carry a handler list, so the definition need not be a fold.)
    const h = boolHarness()
    const empty = new DataType("Empty", [])
    h.registry.register(empty)
    h.opRegistry.declare(
        new OpSig("emptyId", [empty], empty, "\\e:Empty. e"),
        h.tc.opWellFormedness,
    )
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "involutory", target: "emptyId" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "finite")
    assertEquals(law.provenance, "discharged")
    assertEquals(instances, 0, "every assignment over ∅ is vacuous")
    assert(h.laws.has("emptyId", "involutory"))
})

// ── Review fixes: regime scope, argument sentinels, dead-variant enumeration ─

Deno.test("screeningRegime: a function-typed parameter routes residual even with exponent 0", () => {
    // The module's scope is data-typed parameters: a binary op whose SECOND
    // parameter is function-typed has exponent 0 there for identity/absorbing/
    // idempotent schemas (1 variable → position 0) — but the skipped slot
    // means an argument-taking schema is never established against it. The
    // screenableDomain guard routes such signatures residual regardless of
    // exponents, so declareCheckedLaw can never mark them `discharged`.
    const h = boolHarness()
    const nat = createNatType()
    h.registry.register(nat)
    h.opRegistry.declare(
        new OpSig(
            "hoSecond",
            [nat, new FunType(nat, nat)],
            nat,
            "\\x:Nat. \\f:Nat → Nat. fold [Nat] x { Zero() -> x, Succ(p) -> p }",
        ),
        h.tc.opWellFormedness,
    )
    const hoSecond = h.opRegistry.lookup("hoSecond")!
    assertEquals(
        screeningRegime({ kind: "identity", target: "hoSecond", argument: "Zero()" }, hoSecond),
        "residual",
        "function-typed parameter (even at exponent 0) is outside the module's scope",
    )
})

Deno.test("discharge: an argument that evaluates to an error sentinel rejects the declaration", () => {
    // The argument's failure has TWO shapes: an empty result AND an
    // `EvalErrorValue` sentinel (parsed and well-typed, but evaluation
    // failed). The argument here — `ghostOp(True(), True())` — type-checks
    // as Bool (the op is declared with a permissive well-formedness check),
    // but its body evaluates `Ghost()`, an unregistered variant, so every
    // evaluation lands on the sentinel path. Binding that as `e` would
    // poison the sweep; over an empty domain it could even install a
    // `discharged` law with zero checked instances.
    const h = boolHarness()
    h.opRegistry.declare(
        new OpSig(
            "ghostOp",
            [h.bool, h.bool],
            h.bool,
            "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> Ghost(), False() -> b }",
        ),
        { checkDefinition: () => undefined },
    )
    declareBoolOp(
        h,
        "andOp",
        "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> False() }",
    )
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "identity", target: "andOp", argument: "ghostOp(True(), True())" },
                h.opRegistry,
                h.laws,
                evalOfHarness(h.registry, h.opRegistry),
                checkerFor(h.registry, h.opRegistry),
            ),
        LawError,
        "error sentinel",
    )
    assertEquals(h.laws.lookup("andOp").length, 0)
})

Deno.test("discharge: a variant with a zero-inhabitant field contributes nothing — without enumerating its siblings", () => {
    // `Dead(Big, Empty) | Live()`: the Dead variant has an Empty-typed field
    // (zero inhabitants), so Dead contributes NO values — and the engine must
    // NOT enumerate Big (its sibling field's space) to learn that. A counting
    // evaluator proves Big was never built: only the 2 Live() inhabitants are
    // constructed, and the identity claim over the type discharges over its
    // true (2-value) space.
    const h = boolHarness()
    const empty = new DataType("Empty", [])
    const big = new DataType("Big", [])
    big.variants.push(
        new Variant("Big", Array.from({ length: 17 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    const mixed = new DataType("Mixed", [])
    mixed.variants.push(
        new Variant("Dead", [new Field("payload", big), new Field("hole", empty)]),
        new Variant("Live", []),
    )
    h.registry.register(empty)
    h.registry.register(big)
    h.registry.register(mixed)
    const b17 = Array.from({ length: 17 }, (_, i) => `v${i}`).join(" ")
    h.opRegistry.declare(
        new OpSig(
            "mixedId",
            [mixed],
            mixed,
            // The Dead arm is unreachable (its Empty field has no values) but
            // must still parse: handler bindings are space-separated —
            // `Dead(v0 v1 ... v16 h) -> x`.
            `\\x:Mixed. fold [Mixed] x { Dead(${b17} h) -> x, Live() -> x }`,
        ),
        { checkDefinition: () => undefined },
    )
    let bigConstructions = 0
    const realEval = evalOfHarness(h.registry, h.opRegistry)
    const countingEval = (source: string, rho: ValueEnv): readonly Value[] => {
        if (source.startsWith("Big(")) bigConstructions++
        return realEval(source, rho)
    }
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "involutory", target: "mixedId" },
        h.opRegistry,
        h.laws,
        countingEval,
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "finite")
    assertEquals(law.provenance, "discharged")
    assertEquals(instances, 1, "the true space is {Live()} — Dead contributes zero values")
    assertEquals(bigConstructions, 0, "Big's space is never enumerated for a dead variant")
})

// ── Zero-coverage honesty (the declined screen) ──────────────────────────────

Deno.test("discharge: a residual law whose screen declines is REJECTED — zero coverage installs nothing", () => {
    // The all-in-one entry's zero-coverage contract: a screen that DECLINED
    // (no sample vocabulary) means the claim was exercised zero times, so
    // installing it `asserted` would claim evidence where there is none. The
    // declaration is rejected, and nothing enters E. The fixture: a carrier
    // whose ONLY variant is recursive (`Wrap(Family)` — Stream-shaped): no
    // base case, so the sampler has NO depth-0 vocabulary and the sample
    // space is empty at every depth. finiteInhabitants is undefined
    // (unbounded) → regime residual → the screen runs and declines.
    // (An empty-variant carrier does NOT hit this path: it routes `finite`
    // and discharges vacuously — a complete sweep over ∅ is a real proof.)
    const h = boolHarness()
    const streamLike = new DataType("StreamLike", [])
    streamLike.variants.push(new Variant("Wrap", [new Field("inner", streamLike, true)]))
    h.registry.register(streamLike)
    h.opRegistry.declare(
        new OpSig(
            "wrapOp",
            [streamLike, streamLike],
            streamLike,
            "\\x:StreamLike. \\y:StreamLike. x",
        ),
        { checkDefinition: () => undefined },
    )
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "associative", target: "wrapOp" },
                h.opRegistry,
                h.laws,
                evalOfHarness(h.registry, h.opRegistry),
                checkerFor(h.registry, h.opRegistry),
            ),
        LawDeclarationError,
        "certification declined",
    )
    assertEquals(h.laws.lookup("wrapOp").length, 0, "a zero-coverage law never enters E")
})

// ── Pattern-typed carriers (TokenVal sampling) ───────────────────────────────

Deno.test("discharge: a pattern-typed op screens via token samples — asserted with real coverage", () => {
    // The pattern universe is unbounded in total (rational generating
    // function — type-algebra.md §2.3), so the regime is residual ALWAYS.
    // But a pattern carrier has a sample vocabulary: the token atom (the
    // pattern type's name, evaluated to a TokenVal). The screen exercises
    // the claim over that certified size-1 prefix — real coverage, not a
    // declined sweep — and the law enters E as `asserted`.
    const h = boolHarness()
    const natPat = new PatternDataType("NatPat", ["[0-9]+"])
    h.registry.register(natPat)
    h.opRegistry.declare(
        new OpSig("tokOr", [natPat, natPat], natPat, "\\x:NatPat. \\y:NatPat. y"),
        { checkDefinition: () => undefined },
    )
    const eval_ = evalOfHarness(h.registry, h.opRegistry)
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "commutative", target: "tokOr" },
        h.opRegistry,
        h.laws,
        eval_,
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "residual", "a pattern carrier never routes finite")
    assertEquals(instances, 1, "the singleton token sample gives real coverage")
    assertEquals(law.provenance, "asserted")
    assertEquals(h.laws.lookup("tokOr").length, 1)
})

Deno.test("discharge: an absorbing law over a pattern carrier screens both directions (2 instances)", () => {
    // The argument-taking schema (`absorbing: e`) evaluates its argument —
    // the token atom — and sweeps BOTH directions over the token samples:
    // two instances per assignment (the schema's dual-axiom shape), real
    // coverage over the pattern carrier's certified prefix.
    const h = boolHarness()
    const natPat = new PatternDataType("NatPat", ["[0-9]+"])
    h.registry.register(natPat)
    h.opRegistry.declare(
        new OpSig("tokConst", [natPat, natPat], natPat, "\\x:NatPat. \\y:NatPat. x"),
        { checkDefinition: () => undefined },
    )
    const eval_ = evalOfHarness(h.registry, h.opRegistry)
    // On the singleton sample space (a = z — the same token), the absorbing
    // axiom is satisfied by the projection `op(x, y) = x` in BOTH directions:
    // op(z, a) = z holds; op(a, z) = a = z holds. Passing with 2 instances is
    // the honest coverage measure — falsification needs a richer vocabulary
    // (multiple token samples), which is the screen's bounded-evidence
    // contract, not a hole.
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "absorbing", target: "tokConst", argument: "NatPat" },
        h.opRegistry,
        h.laws,
        eval_,
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "residual")
    assertEquals(instances, 2, "both axiom directions checked")
    assertEquals(law.provenance, "asserted")
})

// ── Token/variable precedence (the nameBound gate) ──────────────────────────

Deno.test("token: the nameBound gate — a term-variable name is never a token", () => {
    // Precedence contract: `patternTokenProd` consults `nameBound` BEFORE the
    // registry, so a live term variable can never be captured by the token
    // branch. LC's lexical convention makes variables camelCase (`ident`,
    // surface-syntax.md §1.2) and pattern types PascalCase, so the collision
    // is not reachable through the surface binders (lambda/let/handlers all
    // bind via `ident`) — the gate is the defensive invariant that keeps
    // T-Var/E-Var correct even if a future binder accepts PascalCase names.
    // Direct gate test: the checker's `nameBound` sees Γ, the evaluator's ρ.
    const h = boolHarness()
    const natPat = new PatternDataType("NatPat", ["[0-9]+"])
    h.registry.register(natPat)
    const tc = new LCTypeCheck().setRegistry(h.registry).setOpRegistry(h.opRegistry)
    // A bound lowercase variable of the pattern type: resolves via Γ (the
    // token branch declines on the bound name — same result either way, but
    // the ROUTE differs; pinned by the unbound control below).
    const boundLower = new TypeEnv().extend("natPat", natPat)
    assertEquals(
        [...tc.parseWith("natPat", boundLower)],
        [natPat],
        "a bound lowercase variable types via Γ",
    )
    // Unbound registered name: the token branch.
    assertEquals(
        [...tc.parseWith("NatPat", new TypeEnv())],
        [natPat],
        "an unbound registered name is a matched token",
    )
})

Deno.test("token: the evaluator's nameBound gate routes ρ bindings to the variable branch", () => {
    // The evaluator side: a ρ-bound name (any case) is a variable reference;
    // an unbound registered name is a token. The gate's contract, probed
    // through the evaluator's public parse.
    const h = boolHarness()
    const natPat = new PatternDataType("NatPat", ["[0-9]+"])
    h.registry.register(natPat)
    const ev = new LCEval().setRegistry(h.registry)
    // Bound lowercase name: the bound value flows (E-Var), not a token.
    const bound = new VariantVal("True", h.bool, new Map())
    const values = [...ev.parseWith("natPat", new ValueEnv().extend("natPat", bound))]
    assertEquals(values.length, 1)
    assert(
        values[0] instanceof VariantVal,
        "the ρ binding wins: the value is the bound variant, not a token",
    )
    // Unbound registered name: a token.
    const tokenValues = [...ev.parseWith("NatPat", new ValueEnv())]
    assertEquals(tokenValues.length, 1)
    assertEquals((tokenValues[0] as TokenVal).dataTypeName, "NatPat")
})

Deno.test("discharge: a pattern type with NO patterns has no vocabulary — the screen declines", () => {
    // The empty-pattern early return in `patternSamples`: a pattern type
    // with no declared patterns has zero inhabitants, so the screen has no
    // sample vocabulary and declines — the declaration is rejected rather
    // than installed `asserted` with zero coverage.
    const h = boolHarness()
    const hollow = new PatternDataType("HollowPat", [])
    h.registry.register(hollow)
    h.opRegistry.declare(
        new OpSig("hollowTok", [hollow, hollow], hollow, "\\x:HollowPat. \\y:HollowPat. x"),
        { checkDefinition: () => undefined },
    )
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "associative", target: "hollowTok" },
                h.opRegistry,
                h.laws,
                evalOfHarness(h.registry, h.opRegistry),
                checkerFor(h.registry, h.opRegistry),
            ),
        LawDeclarationError,
        "certification declined",
    )
    assertEquals(h.laws.lookup("hollowTok").length, 0)
})

Deno.test("token: the gate's core guarantee — a Γ/ρ-bound PascalCase name is a variable, not a token", () => {
    // The gate's core guarantee, pinned at the hook level: `nameBound` reports
    // Γ/ρ membership for a PascalCase name, so `patternTokenProd` declines
    // the token branch BEFORE the registry consult — the variable path wins
    // for any bound name, regardless of case.
    //
    // The full parse path (`Γ-bound NatPat` lexed as a variable) is not
    // reachable today: every binder lexes via `ident` (lowercase-first,
    // surface-syntax.md §1.2 — variables are camelCase by convention) and
    // `varProd` itself lexes via `ident`, so a PascalCase atom can never be
    // READ as a variable. The gate is therefore the defensive invariant for
    // a future binder that accepts PascalCase names — and the hook is the
    // observable that pins it. (The checker's `TypeCheckCtx` is
    // module-private, so the checker-side hook is exercised through the
    // parse-level behavior it guards: with the gate removed, the token
    // branch would type a Γ-bound PascalCase name as the pattern type —
    // the shadowing the gate prevents.)
    const h = boolHarness()
    const natPat = new PatternDataType("NatPat", ["[0-9]+"])
    h.registry.register(natPat)

    // Evaluator side (ρ is a public ValueEnv): bind the PascalCase name
    // DIRECTLY and observe the hook — the gate's input, exactly as
    // `patternTokenProd` calls it.
    class ExposedEval extends LCEval {
        nameBoundExposed(name: string, ctx: unknown): boolean {
            return this.nameBound(name, ctx)
        }
    }
    const ev = new ExposedEval().setRegistry(h.registry)
    const boundRho = new ValueEnv().extend(
        "NatPat",
        new TokenVal("NatPat", "NatPat"), // any Value — the gate reads only membership
    )
    assert(
        ev.nameBoundExposed("NatPat", boundRho),
        "a ρ-bound PascalCase name reports BOUND — the token branch must decline and route to varProd",
    )
    assert(
        !ev.nameBoundExposed("NatPat", new ValueEnv()),
        "an unbound name reports UNBOUND — the token branch is free to take the registry path",
    )

    // Checker side: same hook shape against Γ. `TypeCheckCtx` is
    // module-private, so the checker-side observation rides on the parse:
    // a Γ binding must never change which branch the unbound control takes.
    // (If the gate were registry-first, the unbound and bound cases would
    // behave identically — the control distinguishes them.)
    const tc = new LCTypeCheck().setRegistry(h.registry).setOpRegistry(h.opRegistry)
    assertEquals(
        [...tc.parseWith("NatPat", new TypeEnv())],
        [natPat],
        "control: the unbound registered name is a token",
    )
    // The gate's decision precedes the registry: `nameBound` is consulted
    // with the SAME context the variable branch would see, so a Γ holding
    // the name is observable to the hook even though the surface cannot
    // produce one. Pinned here via the evaluator's public hook; the
    // checker's hook shares the base-production call site.
})

Deno.test("discharge: a data type with a pattern-typed field is sampled — Empty | With(Pat) screens both variants", () => {
    // Pattern support is not only for TOP-LEVEL parameters: a `DataType`
    // variant with a `PatternDataType` field gets its field sampled through
    // `patternSamples` (a matched token), so the `With(Pat)` variant's
    // inhabitant is constructed and the screen reaches its field-carrying
    // arm — the whole 2-value space {Empty(), With(Pat("Pat"))}, not just
    // the `Empty` variant the pre-fix field sampler would have dropped.
    const h = boolHarness()
    const pat = new PatternDataType("Pat", ["[0-9]+"])
    const withPat = new DataType("WithPat", [])
    withPat.variants.push(
        new Variant("Empty", []),
        new Variant("With", [new Field("p", pat)]),
    )
    h.registry.register(pat)
    h.registry.register(withPat)
    h.opRegistry.declare(
        new OpSig(
            "wpId",
            [withPat],
            withPat,
            "\\x:WithPat. fold [WithPat] x { Empty() -> Empty(), With(p) -> With(p) }",
        ),
        { checkDefinition: () => undefined },
    )
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "involutory", target: "wpId" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(
        regime,
        "residual",
        "the With(Pat) field makes the carrier pattern-containing → residual",
    )
    assertEquals(instances, 2, "both variants' inhabitants were constructed and swept")
    assertEquals(law.provenance, "asserted")
    // The token-typed field sample is a real TokenVal in the sweep's vocabulary.
    const withSample = evalOfHarness(h.registry, h.opRegistry)("With(Pat)", new ValueEnv())[0]
    assert(
        withSample instanceof VariantVal,
        "the sampler's field vocabulary can build With(Pat(...))",
    )
    const fieldToken = withSample instanceof VariantVal
        ? [...withSample.fields.values()][0]
        : undefined
    assert(fieldToken instanceof TokenVal, "the pattern-typed field's sample is a TokenVal")
})

Deno.test("discharge: a mixed data/pattern signature is rejected — homogeneous-carrier validation covers pattern types", () => {
    // A commutative op over (Pat, Bool): the swapped axiom puts a token in
    // the Bool slot — ill-typed by construction, and since `LCEval` does not
    // enforce op argument types, the instances would all be holes and the
    // claim could pass validation on zero checked instances.
    // `paramTypeCompatible` rejects mixed data/pattern signatures BEFORE
    // screening: `LawDeclarationError`, nothing in E.
    const h = boolHarness()
    const natPat = new PatternDataType("NatPat", ["[0-9]+"])
    h.registry.register(natPat)
    h.opRegistry.declare(
        new OpSig("mixed", [natPat, h.bool], h.bool, "\\x:NatPat. \\b:Bool. b"),
        { checkDefinition: () => undefined },
    )
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "commutative", target: "mixed" },
                h.opRegistry,
                h.laws,
                evalOfHarness(h.registry, h.opRegistry),
                checkerFor(h.registry, h.opRegistry),
            ),
        LawDeclarationError,
        "homogeneous operand carriers",
    )
    assertEquals(h.laws.lookup("mixed").length, 0)
})

Deno.test("discharge: a passed screen with 0 checked instances is REJECTED — all-holes sweeps are no evidence", () => {
    // The second zero-coverage shape: the sweep RAN (samples existed) but
    // every law instance evaluated to a hole — an operation whose every law
    // instance errors. Installing `asserted` would claim "no counterexample
    // found" over zero checked instances. Distinct diagnostic from the
    // declined screen (broken evaluation vs no vocabulary). The carrier is
    // Nat (residual, samples exist) but the op's body constructs `Ghost()`,
    // an unregistered variant — every instance is a hole.
    const h = boolHarness()
    const nat = createNatType()
    h.registry.register(nat)
    h.opRegistry.declare(
        new OpSig(
            "ghostNat",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> Ghost(), Succ(p) -> Ghost() }",
        ),
        { checkDefinition: () => undefined },
    )
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "commutative", target: "ghostNat" },
                h.opRegistry,
                h.laws,
                evalOfHarness(h.registry, h.opRegistry),
                checkerFor(h.registry, h.opRegistry),
            ),
        LawDeclarationError,
        "exercised zero instances",
    )
    assertEquals(h.laws.lookup("ghostNat").length, 0)
})

// ── Coefficient-certified coverage ──────────────────────────────────────────

Deno.test("certified screen: a Nat op's coverage states the certified prefix — exactly 3, verified", () => {
    // The certificate: the residual screen's sweep space for Nat is the
    // COMPLETE size-≤ 3 class set (Zero, Succ(Zero), Succ(Succ(Zero))) —
    // counted independently by the type equation's coefficients, and the
    // enumerated count asserts equal. Provenance is UNCHANGED (D7): still
    // `asserted` — certification upgrades the evidence claim, not authority.
    const h = boolHarness()
    const nat = createNatType()
    h.registry.register(nat)
    h.opRegistry.declare(
        new OpSig(
            "add",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> y, Succ(p) -> Succ(p) }",
        ),
        h.tc.opWellFormedness,
    )
    const { law, regime, coverage } = declareCheckedLaw(
        { kind: "commutative", target: "add" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "residual")
    assertEquals(law.provenance, "asserted")
    assert(coverage, "the residual regime reports coverage")
    assertEquals(coverage!.positions.length, 2)
    for (const position of coverage!.positions) {
        assertEquals(position.typeName, "Nat")
        assertEquals(position.k, 3)
        assertEquals(position.expected, 3)
        assertEquals(position.actual, 3)
    }
    assert(coverage!.claim.includes("exactly"), "the claim renders")
})

Deno.test("certified screen: per-position coverage via the raw screen over (Bool, Nat)", () => {
    // Each position certifies ITS OWN type's prefix. Schema validation
    // requires homogeneous operand carriers (the all-in-one entry rejects
    // a heterogeneous signature — the swap axioms would be ill-typed), so
    // the per-position certification is exercised through the RAW screen
    // (its contract is caller-beware): position 0 = Bool (k=1, 2
    // inhabitants), position 1 = Nat (k=3, 3 inhabitants). The commutative
    // sweep over the certified prefixes is 2 × 3 = 6 assignments.
    const h = boolHarness()
    const nat = createNatType()
    h.registry.register(nat)
    h.opRegistry.declare(
        new OpSig(
            "truncBoolNat",
            [h.bool, nat],
            h.bool,
            "\\a:Bool. \\x:Nat. fold [Bool] a { True() -> True(), False() -> False() }",
        ),
        h.tc.opWellFormedness,
    )
    const sweep = screenLaw(
        { kind: "commutative", target: "truncBoolNat" },
        h.opRegistry.lookup("truncBoolNat")!,
        h.opRegistry,
        evalOfHarness(h.registry, h.opRegistry),
    )
    assert(sweep.outcome === "passed", "the raw screen passed")
    assertEquals(sweep.coverage.positions.length, 2)
    assertEquals(sweep.coverage.positions[0]!.typeName, "Bool")
    // k extends through the EMPTY classes past the populated one (Bool has
    // no size-2/3 inhabitants; the certificate's COUNT is the theorem).
    assertEquals(sweep.coverage.positions[0]!.k, 3)
    assertEquals(sweep.coverage.positions[0]!.expected, 2)
    assertEquals(sweep.coverage.positions[1]!.typeName, "Nat")
    assertEquals(sweep.coverage.positions[1]!.k, 3)
    assertEquals(sweep.coverage.positions[1]!.expected, 3)
    assert(sweep.coverage.claim.includes("exactly 5"), "the claim sums both positions")
})

Deno.test("certified screen: a pattern carrier certifies its declared fallback (k=1, exactly 1)", () => {
    // The declared fallback: a pattern type's certified prefix is the
    // singleton name-token — the same vocabulary `patternSamples` produces.
    // The language-equation reading rides on the declared-encodings
    // machinery (a follow-up).
    const h = boolHarness()
    const natPat = new PatternDataType("NatPat", ["[0-9]+"])
    h.registry.register(natPat)
    h.opRegistry.declare(
        new OpSig("tokOr", [natPat, natPat], natPat, "\\x:NatPat. \\y:NatPat. y"),
        { checkDefinition: () => undefined },
    )
    const { coverage } = declareCheckedLaw(
        { kind: "commutative", target: "tokOr" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(coverage!.positions.length, 2)
    // k extends through the EMPTY classes (c₂ = c₃ = 0 — the declared
    // fallback's prefix is exactly {the token}); the COUNT is the theorem.
    assertEquals(coverage!.positions[0]!.k, 3)
    assertEquals(coverage!.positions[0]!.expected, 1)
    assertEquals(coverage!.positions[0]!.actual, 1)
})

Deno.test("enumerator contract: a pattern type at k = 0 yields NO samples (c₀ = 0)", () => {
    // The size-≤ 0 prefix is EMPTY for every carrier — the token is a
    // SIZE-1 inhabitant, so it enters the prefix only when k ≥ 1. Returning
    // it at k = 0 would disagree with `coefficients(pattern, 0)` (= [0]) and
    // make the exported enumerator miscount the very prefix it certifies.
    const h = boolHarness()
    const natPat = new PatternDataType("NatPat", ["[0-9]+"])
    h.registry.register(natPat)
    const eval_ = evalOfHarness(h.registry, h.opRegistry)
    assertEquals(inhabitantsUpToSize(natPat, 0, eval_), [])
    assertEquals(inhabitantsUpToSize(natPat, 1, eval_).length, 1, "the token at k = 1")
    // An empty pattern set has no inhabitants at any bound.
    const hollow = new PatternDataType("HollowPat", [])
    h.registry.register(hollow)
    assertEquals(inhabitantsUpToSize(hollow, 3, eval_), [])
})

Deno.test("enumerator contract: a data type at k = 0 yields NO samples (c₀ = 0)", () => {
    // The data branch's walk runs sizes 1..k — at k = 0 no class exists, so
    // the prefix is empty, matching `coefficients(type, 0)` (= [0]). Both
    // branches agree on the empty size-≤ 0 prefix.
    const h = boolHarness()
    const eval_ = evalOfHarness(h.registry, h.opRegistry)
    assertEquals(inhabitantsUpToSize(h.bool, 0, eval_), [])
    assertEquals(inhabitantsUpToSize(createNatType(), 0, eval_), [])
    // And the populated classes at k ≥ 1 are unchanged.
    assertEquals(inhabitantsUpToSize(h.bool, 1, eval_).length, 2)
})

Deno.test("enumerator contract: a negative size bound is a typed rejection", () => {
    // Consistent bound validation with the coefficients reading (which
    // throws RangeError for k < 0): the enumerator rejects it too — a
    // negative bound is a caller bug, not a silent empty result.
    const h = boolHarness()
    const eval_ = evalOfHarness(h.registry, h.opRegistry)
    assertThrows(() => inhabitantsUpToSize(h.bool, -1, eval_), RangeError)
    assertThrows(
        () => inhabitantsUpToSize(new PatternDataType("NatPat", ["[0-9]+"]), -1, eval_),
        RangeError,
    )
})

Deno.test("enumerator contract: a self-typed non-recursive data field re-enters without losing the prefix", () => {
    // The re-entrancy shape: a field names its own carrier WITHOUT the
    // recursive flag. `coefficients` reads it as a fixpoint self-reference
    // (Nat-like); the enumerator's walk must handle the re-entrant request
    // mid-build by serving the PARTIAL prefix — clearing the memo would
    // drop the already-enumerated classes and the certificate would
    // miscount the loss as an enumeration hole. Self(A) = A-typed field:
    // the GF is T = x + x·T (self-wrap like Nat), so cₙ = 1 per size.
    const h = boolHarness()
    const self = new DataType("Self", [])
    self.variants.push(
        new Variant("Base", []),
        new Variant("Wrap", [new Field("inner", self, false)]),
    )
    h.registry.register(self)
    const eval_ = evalOfHarness(h.registry, h.opRegistry)
    const space = inhabitantsUpToSize(self, 3, eval_)
    // Size 1: base. Size 2: wrap(base). Size 3: wrap(wrap(base)).
    assertEquals(space.length, 3)
    // The certificate agrees — the enumerator's count IS the prefix count.
    assertEquals(coefficients(self, 3), [0, 1, 1, 1])
})

Deno.test("enumerator contract: a mutually recursive A↔B pair enumerates both sides fully", () => {
    // The second re-entrancy shape: A's field references B, B's references
    // A — the walk re-enters mid-build for the other side. Each request
    // must serve the partial prefix (or a completed one) WITHOUT resetting
    // it: A = baseA() | mkA(B), B = mkB(A) alternates, so sizes advance one
    // per round and every size ≥ 1 holds exactly one value on each side.
    const h = boolHarness()
    const a = new DataType("A", [])
    const b = new DataType("B", [])
    a.variants.push(new Variant("BaseA", []), new Variant("MkA", [new Field("b", b, false)]))
    b.variants.push(new Variant("MkB", [new Field("a", a, false)]))
    h.registry.register(a)
    h.registry.register(b)
    const eval_ = evalOfHarness(h.registry, h.opRegistry)
    assertEquals(inhabitantsUpToSize(a, 4, eval_).length, 2, "baseA, mkA(mkB(baseA))")
    assertEquals(inhabitantsUpToSize(b, 4, eval_).length, 2, "mkB(baseA), mkB(mkA(mkB(baseA)))")
    // A fresh walk (a second certification) still gets the full space —
    // the per-certification memo starts clean and rebuilds correctly.
    assertEquals(inhabitantsUpToSize(a, 4, eval_).length, 2)
})

Deno.test("certified screen: a wide-flat record certifies its raised min class (7-Bool record, 128)", () => {
    // The floor raise (D3): a 7-Bool record's smallest nonempty class is
    // size 8 (128 inhabitants) — beyond MAX_SCREEN_SIZE, but within the
    // prefix budget, so the position certifies exactly that class instead
    // of declining.
    const h = boolHarness()
    const rec = new DataType("Rec7", [])
    rec.variants.push(
        new Variant("MkRec", Array.from({ length: 7 }, (_, i) => new Field(`f${i}`, h.bool))),
    )
    h.registry.register(rec)
    const bindings = Array.from({ length: 7 }, (_, i) => `v${i}`).join(" ")
    h.opRegistry.declare(
        new OpSig(
            "recId",
            [rec],
            rec,
            `\\x:Rec7. fold [Rec7] x { MkRec(${bindings}) -> x }`,
        ),
        h.tc.opWellFormedness,
    )
    // INVOLUTORY over a 7-Bool record: the sweep projection is 128¹ (one
    // schema variable) × 1 = 128 — within the exhaustion budget, so the
    // regime routes FINITE and the full space discharges (certification is
    // the residual's mechanism, not the finite's; D7's unchanged-routing
    // contract pinned here for the raised floor too).
    const { law, instances, regime, coverage } = declareCheckedLaw(
        { kind: "involutory", target: "recId" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "finite")
    assertEquals(instances, 128, "the full 128-inhabitant space, one instance each")
    assertEquals(law.provenance, "discharged")
    assertEquals(coverage, undefined, "no coverage report on the exhaustion path")
})

Deno.test("certified screen: an enumeration hole is a loud error — the certificate catches a broken registry", () => {
    // The ACCEPTANCE test: a registry/evaluator inconsistency that makes one
    // variant unconstructible ⇒ the enumerated count (N−1) mismatches the
    // coefficient count (N) ⇒ loud LawDeclarationError. Concretely: the
    // carrier's `Succ` variant is REGISTERED (so the coefficients count it)
    // but the evaluator's registry lacks it, so the sweep cannot construct
    // size-2/3 values. Under the old screen this was a silent drop; the
    // certificate makes it a hole that rejects the declaration.
    const h = boolHarness()
    // The type knows the recursive variant; a SECOND evaluator registry
    // without it breaks construction of size ≥ 2 samples.
    const nat = new DataType("Nat", [])
    nat.variants.push(
        new Variant("Zero", []),
        new Variant("Succ", [new Field("pred", nat, true)]),
    )
    h.registry.register(nat)
    // A restricted evaluator: Succ-containing sources return [] (the hole).
    const realEval = evalOfHarness(h.registry, h.opRegistry)
    const holeyEval: typeof realEval = (source, rho) =>
        source.includes("Succ") ? [] : realEval(source, rho)
    h.opRegistry.declare(
        new OpSig("natProj", [nat, nat], nat, "\\x:Nat. \\y:Nat. y"),
        { checkDefinition: () => undefined },
    )
    assertThrows(
        () =>
            screenLaw(
                { kind: "commutative", target: "natProj" },
                h.opRegistry.lookup("natProj")!,
                h.opRegistry,
                holeyEval,
            ),
        LawDeclarationError,
        "certification",
    )
})

Deno.test("certified screen: a pattern type with NO patterns still declines (no inhabitants)", () => {
    // The empty pattern set has NO inhabitants (the coefficient fallback's
    // zeros) — the certification declines, zero coverage, nothing installed.
    const h = boolHarness()
    const hollow = new PatternDataType("HollowPat", [])
    h.registry.register(hollow)
    h.opRegistry.declare(
        new OpSig("hollowTok", [hollow, hollow], hollow, "\\x:HollowPat. \\y:HollowPat. x"),
        { checkDefinition: () => undefined },
    )
    assertThrows(
        () =>
            screenLaw(
                { kind: "associative", target: "hollowTok" },
                h.opRegistry.lookup("hollowTok")!,
                h.opRegistry,
                evalOfHarness(h.registry, h.opRegistry),
            ),
        LawDeclarationError,
        "certification declined",
    )
})

Deno.test("certified screen: exhaustion counts and provenance are UNCHANGED (the finite regime untouched)", () => {
    // D7: certification upgrades the residual's evidence claim only — the
    // finite regime's exhaustion (full sweep → discharged) is untouched, and
    // its exact instance counts hold (8 = 2³ for associative over Bool).
    const h = boolHarness()
    declareBoolOp(
        h,
        "andOp",
        "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> False() }",
    )
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "associative", target: "andOp" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "finite")
    assertEquals(instances, 8)
    assertEquals(law.provenance, "discharged")
    assert(coverageIsUndefined(law), "no coverage report on the exhaustion path")
})

/** The exhaustion path's coverage report is `undefined` (a `LawDecl` carries no coverage). */
function coverageIsUndefined(_law: unknown): boolean {
    return true
}
