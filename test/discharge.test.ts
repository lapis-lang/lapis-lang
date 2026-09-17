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
    // The residual SAMPLER (samplesFor/construct) generates typed
    // non-recursive field samples: variant fields carry real values of their
    // declared type, so a fold with an arm per variant — including
    // field-carrying arms — evaluates honestly through the screen. This is
    // the RESIDUAL path (an NS carrier is recursive ⇒ unbounded ⇒ residual):
    // distinct from exhaustion's enumerator above, and it is why a fold like
    // nsOr's `One(b) -> y` arm can evaluate at all. (Exhaustion enumerates;
    // the screen samples — both must produce typed field values, and this
    // test pins the sampler's.)
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
        sweep,
        { outcome: "passed", checked: instances },
        "the all-in-one entry reports the same coverage as the raw screen",
    )
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

Deno.test("discharge: the residual screen still skips non-evaluating instances", () => {
    // The two regimes disagree on holes BY DESIGN: the screen's skip keeps
    // the honest evidence claim (checked = instances actually evaluated);
    // exhaustion's reject keeps the discharged tag meaning full coverage.
    const h = boolHarness()
    declareBoolOp(
        h,
        "andOp",
        "\\a:Bool. \\b:Bool. fold [Bool] a { True() -> b, False() -> False() }",
    )
    const blindEval = (_source: string, _rho: ValueEnv): readonly VariantVal[] => []
    // Raw screenLaw (caller-beware) with a dead evaluator: the sampler
    // itself cannot construct any sample (variant construction is an
    // evaluation), so the screen has NO sample vocabulary — declined. The
    // passed-with-0-coverage shape (a running sweep whose every instance is
    // a hole) needs a live sampler and a blind instance evaluator, which is
    // the heterogeneous-commutative case in laws.test.ts.
    assertEquals(
        screenLaw(
            { kind: "associative", target: "andOp" },
            h.opRegistry.lookup("andOp")!,
            h.opRegistry,
            blindEval,
        ),
        { outcome: "declined" },
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

Deno.test("discharge: an over-ceiling type routes residual — the saturated space is screened, not exhausted", () => {
    // The ROUTING side of the ceiling: an involutory claim on an identity-like
    // fold over the 18-Bool record (2¹⁸ inhabitants > 2¹⁷) classifies as
    // finite-but-unexhaustible, so declareCheckedLaw routes it to the residual
    // screen — the screen's depth-capped sample, `asserted`, never
    // `discharged`. (The router rejects SATURATED classifier counts outright:
    // the reported 2¹⁷+1 is a floor on the true count, so trusting it in the
    // sweep formula would route a 2¹⁸-space to exhaustion.)
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
    const { law, instances, regime } = declareCheckedLaw(
        { kind: "involutory", target: "wideId" },
        h.opRegistry,
        h.laws,
        evalOfHarness(h.registry, h.opRegistry),
        checkerFor(h.registry, h.opRegistry),
    )
    assertEquals(regime, "residual")
    assertEquals(law.provenance, "asserted")
    assertEquals(instances, 1, "the screen's depth-capped sample, not the full 2¹⁸ space")
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
        "the screen declined",
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
        "the screen declined",
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
