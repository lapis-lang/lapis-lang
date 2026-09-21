/**
 * Derivable-regime tests — the BMF derivation engine: fold-induction proofs
 * of law claims from primitive/discharged laws, and the honest residual
 * fallback when the engine cannot close.
 *
 * See _docs/theory/type-algebra.md §6 (the derivable regime's design) and
 * _docs/issue63-plan.md (the worked derivation the tests pin).
 *
 * The tests pin the three canonical outcomes (the plan's §3):
 * - **Claim 1** — `identity: Zero` on `add` derives from the fold schema
 *   alone (zero axiom steps);
 * - **Claim 2** — `identity: Zero` on `addZero` derives from `add`'s
 *   primitive law (the fold-composition/fusion shape);
 * - **Claim 3** — `commutative` on `add` is NOT derivable (needs a nested
 *   double induction — the fragment's honest edge) and stays residual.
 *
 * Plus the reader's shape gates, the IH misuse guard (the soundness
 * invariant), the axiom-eligibility filter (no laundering), the budget
 * behavior, and the end-to-end routing through `declareCheckedLaw`.
 */

import {
    declareCheckedLaw,
    DefinitionShapeError,
    type DefShape,
    derivableFragment,
    type DerivationCertificate,
    deriveLaw,
    LawError,
    LawRegistry,
    LCEval,
    LCTypeCheck,
    makeEvalTerm,
    OpRegistry,
    OpSig,
    readDefShape,
    type ScreeningRegime,
    screeningRegime,
    TypeRegistry,
} from "../src/index.ts"

import { createBoolType, createNatType } from "./fixtures.ts"

import { assert, assertEquals, assertThrows } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

/** Fresh Nat-based registries per harness (an isolated Ω + E + registry). */
function natHarness() {
    const nat = createNatType()
    const bool = createBoolType()
    const registry = new TypeRegistry()
    registry.register(nat)
    registry.register(bool)
    const opRegistry = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ev = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
    return {
        nat,
        bool,
        registry,
        opRegistry,
        tc,
        eval_: makeEvalTerm(ev),
        laws: new LawRegistry(),
    }
}

/** Declare a Nat op whose definition's lambda count sets the arity. */
function declareNatOp(
    h: ReturnType<typeof natHarness>,
    name: string,
    definition: string,
): void {
    // The arity is the definition's lambda-chain length (the well-formedness
    // check enforces the agreement — declaring the honest shape).
    const paramCount = (definition.match(/\\[a-zA-Z_][a-zA-Z0-9_]*:/g) ?? []).length
    h.opRegistry.declare(
        new OpSig(
            name,
            Array.from({ length: paramCount }, () => h.nat),
            h.nat,
            definition,
        ),
        h.tc.opWellFormedness,
    )
}

/** The canonical `add`: fold over the first parameter, recursion passes `p` through. */
const ADD_DEF = "\\a:Nat. \\b:Nat. fold [Nat] a { Zero() -> b, Succ(p) -> Succ(p) }"

/** The fold-composition shape: recursion continues into `add(p, b)`. */
const ADD_ZERO_DEF = "\\a:Nat. \\b:Nat. fold [Nat] a { Zero() -> b, Succ(p) -> Succ(add(p, b)) }"

/** A constant-second handler: the IH misuse guard's target. */
const CONST_B_DEF = "\\a:Nat. \\b:Nat. fold [Nat] a { Zero() -> b, Succ(p) -> Zero() }"

/** The identity-law argument's source (the Zero constructor). */
const ZERO_ARG = "Zero()"

// ── The definition reader (defShape) ─────────────────────────────────────────

Deno.test("readDefShape: add's definition reads with the axis and recursion marks", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    const add = h.opRegistry.lookup("add")!
    const shape = readDefShapeFor(add, h)
    assertEquals(shape.params.length, 2)
    assertEquals(shape.axis, 0)
    assertEquals(shape.carrier.name, "Nat")
    assertEquals(shape.handlers.length, 2)
    const succ = shape.handlers.find((hh) => hh.variantName === "Succ")!
    assertEquals(succ.bindings.length, 1)
    assertEquals(succ.bindings[0]!.carriesIH, true)
    const zero = shape.handlers.find((hh) => hh.variantName === "Zero")!
    assertEquals(zero.bindings.length, 0)
})

Deno.test("readDefShape: a nested-constructor body (double) parses", () => {
    const h = natHarness()
    declareNatOp(
        h,
        "double",
        "\\n:Nat. fold [Nat] n { Zero() -> Zero(), Succ(p) -> Succ(Succ(p)) }",
    )
    const shape = readDefShapeFor(h.opRegistry.lookup("double")!, h)
    assertEquals(shape.axis, 0)
    assertEquals(shape.handlers.length, 2)
})

Deno.test("readDefShape: loud rejections name the construct", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    // unfold — rejected with the construct named. The probe op declares with
    // a well-formed fold definition (Ω's well-formedness runs at declare);
    // the override supplies the unfold source for the shape read.
    const unfoldDef = "\\s:Stream. unfold [Stream] s { head -> Zero(), tail -> s }"
    h.opRegistry.declare(
        new OpSig(
            "badUnfold",
            [h.nat],
            h.nat,
            "\\n:Nat. fold [Nat] n { Zero() -> Zero(), Succ(p) -> p }",
        ),
        h.tc.opWellFormedness,
    )
    const shapeError = assertThrows(
        () => readDefShapeFor(h.opRegistry.lookup("badUnfold")!, h, unfoldDef),
        DefinitionShapeError,
    )
    // The rejection names the offending construct (an unfold) — not a bare
    // parse failure.
    assert(shapeError.message.includes("unfold"))

    // A fold whose scrutinee is a compound term — no induction axis.
    const compoundDef = "\\a:Nat. \\b:Nat. fold [Nat] add(a, b) { Zero() -> Zero(), Succ(p) -> p }"
    assertThrows(
        () => readDefShapeRaw(h, compoundDef),
        DefinitionShapeError,
    )

    // A non-fold body.
    assertThrows(
        () => readDefShapeRaw(h, "\\a:Nat. \\b:Nat. a"),
        DefinitionShapeError,
    )

    // A lambda chain not covering the declared parameters: add declares
    // TWO parameters; the override's chain has one.
    assertThrows(
        () =>
            readDefShapeFor(
                h.opRegistry.lookup("add")!,
                h,
                "\\a:Nat. fold [Nat] a { Zero() -> Zero(), Succ(p) -> p }",
            ),
        DefinitionShapeError,
    )
})

Deno.test("readDefShape: shape checks beyond well-formedness are loud", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    // A compound-scrutinee fold with COMPLETE handlers: Ω's well-formedness
    // accepts it (T-Fold is exhaustive), but the fragment's shape check
    // rejects it — the recursion axis must be a parameter. (A fold MISSING a
    // handler is already rejected earlier — Ω's T-Fold types it Any, so the
    // declaration itself fails; the fragment's own completeness check guards
    // the same invariant for the shape reader.)
    const compoundDef = "\\a:Nat. \\b:Nat. fold [Nat] add(a, b) { Zero() -> Zero(), Succ(p) -> p }"
    const opRegistry = h.opRegistry
    opRegistry.declare(
        new OpSig(
            "compoundScrut",
            [h.nat, h.nat],
            h.nat,
            compoundDef,
        ),
        h.tc.opWellFormedness,
    )
    const shapeError = assertThrows(
        () => readDefShapeFor(opRegistry.lookup("compoundScrut")!, h),
        DefinitionShapeError,
    )
    assert(shapeError.message.includes("scrutinee"))
})

// ── The gate ─────────────────────────────────────────────────────────────────

Deno.test("derivableFragment: a fold-built definition passes; others decline", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    const add = h.opRegistry.lookup("add")!
    const law = { kind: "identity" as const, target: "add", argument: ZERO_ARG }
    assertEquals(derivableFragment(law, add, h.registry, h.opRegistry), true)

    // A definition whose body is not a fold: the gate declines (loudly at
    // the derivation, silently at the gate — routing only).
    h.opRegistry.declare(
        new OpSig("notFold", [h.nat, h.nat], h.nat, "\\a:Nat. \\b:Nat. a"),
        h.tc.opWellFormedness,
    )
    assertEquals(
        derivableFragment(
            { kind: "identity", target: "notFold", argument: ZERO_ARG },
            h.opRegistry.lookup("notFold")!,
            h.registry,
            h.opRegistry,
        ),
        false,
    )

    // Relational kinds route residual (deferred — the plan's D9).
    assertEquals(
        derivableFragment(
            { kind: "distributive", target: "add", argument: "add" },
            add,
            h.registry,
            h.opRegistry,
        ),
        false,
    )
})

// ── The engine: the canonical claims ─────────────────────────────────────────

Deno.test("deriveLaw: identity: Zero on add derives from the fold schema alone", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    const add = h.opRegistry.lookup("add")!
    const result = deriveLaw(
        { kind: "identity", target: "add", argument: ZERO_ARG },
        add,
        h.registry,
        h.opRegistry,
        h.laws,
    )
    assert(!("derivable" in result), `expected a certificate, got: ${JSON.stringify(result)}`)
    const cert = result as DerivationCertificate
    // Zero axioms used (the fold schema closes it).
    assertEquals(cert.axiomsUsed.length, 0)
    // Two instances (identity's both directions), each with two cases.
    assertEquals(cert.instances.length, 2)
    for (const instance of cert.instances) {
        assertEquals(instance.cases.length, 2)
        for (const c of instance.cases) {
            assert(
                c.closure.closedBy === "reflexivity" || c.closure.closedBy === "IH",
                `case ${c.variant} closed by ${c.closure.closedBy}`,
            )
        }
    }
})

Deno.test("deriveLaw: identity: Zero on addZero derives from add's primitive law", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    declareNatOp(h, "addZero", ADD_ZERO_DEF)
    // The primitive tier (language fiat — the test IS the fiat; D5).
    h.laws.declareLaw(
        { kind: "identity", target: "add", argument: ZERO_ARG },
        h.opRegistry,
        "primitive",
    )
    const addZero = h.opRegistry.lookup("addZero")!
    const result = deriveLaw(
        { kind: "identity", target: "addZero", argument: ZERO_ARG },
        addZero,
        h.registry,
        h.opRegistry,
        h.laws,
    )
    assert(!("derivable" in result), `expected a certificate, got: ${JSON.stringify(result)}`)
    // The axiom base records exactly add's primitive identity law.
    assertEquals(result.axiomsUsed.length, 1)
    assertEquals(result.axiomsUsed[0]!.op, "add")
    assertEquals(result.axiomsUsed[0]!.kind, "identity")
    assertEquals(result.axiomsUsed[0]!.provenance, "primitive")
})

Deno.test("deriveLaw: associative on add closes with the IH at the step case", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    const add = h.opRegistry.lookup("add")!
    const result = deriveLaw(
        { kind: "associative", target: "add" },
        add,
        h.registry,
        h.opRegistry,
        h.laws,
    )
    assert(!("derivable" in result), `expected a certificate, got: ${JSON.stringify(result)}`)
    // The Succ cases close (by IH — the recursion variable p carries the
    // motive); the Zero case closes by computation + reflexivity.
    for (const instance of result.instances) {
        assertEquals(instance.cases.length, 2)
    }
})

Deno.test("deriveLaw: commutative on add is NOT derivable (the honest edge)", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    const add = h.opRegistry.lookup("add")!
    const result = deriveLaw(
        { kind: "commutative", target: "add" },
        add,
        h.registry,
        h.opRegistry,
        h.laws,
    )
    assert("derivable" in result, `expected notDerivable, got: ${JSON.stringify(result)}`)
    // The open case is named.
    assert(result.reason.length > 0)
})

Deno.test("deriveLaw: the IH misuse guard — no IH at a constructor head", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    declareNatOp(h, "constB", CONST_B_DEF)
    // constB's right identity direction is FALSE (constB(Succ(p), Zero) =
    // Zero() ≠ Succ(p)) — the engine must decline it, and the certificate
    // must NOT record an IH application at a constructor head.
    const constB = h.opRegistry.lookup("constB")!
    const result = deriveLaw(
        { kind: "identity", target: "constB", argument: ZERO_ARG },
        constB,
        h.registry,
        h.opRegistry,
        h.laws,
    )
    assert("derivable" in result, `expected notDerivable, got: ${JSON.stringify(result)}`)
    // The report names the open case (the honest edge).
    assert(result.reason.length > 0)
})

Deno.test("deriveLaw: the step budget is honored (budget exhaustion → residual)", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    declareNatOp(h, "addZero", ADD_ZERO_DEF)
    h.laws.declareLaw(
        { kind: "identity", target: "add", argument: ZERO_ARG },
        h.opRegistry,
        "primitive",
    )
    const addZero = h.opRegistry.lookup("addZero")!
    // A zero budget: no axiom/IH step may run — the Succ case (which needs
    // add's axiom) stays open, budget named.
    const result = deriveLaw(
        { kind: "identity", target: "addZero", argument: ZERO_ARG },
        addZero,
        h.registry,
        h.opRegistry,
        h.laws,
        0,
    )
    assert("derivable" in result, `expected notDerivable, got: ${JSON.stringify(result)}`)
    assert(result.reason.includes("budget"))
})

Deno.test("deriveLaw: an asserted law is never an axiom step (no laundering)", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    declareNatOp(h, "addZero", ADD_ZERO_DEF)
    // The SAME law, installed asserted: ineligible as an axiom.
    h.laws.declareLaw(
        { kind: "identity", target: "add", argument: ZERO_ARG },
        h.opRegistry,
        "asserted",
    )
    const addZero = h.opRegistry.lookup("addZero")!
    const result = deriveLaw(
        { kind: "identity", target: "addZero", argument: ZERO_ARG },
        addZero,
        h.registry,
        h.opRegistry,
        h.laws,
    )
    // The derivation declines (the only candidate axiom is ineligible) —
    // the honest residual, NOT a laundered discharge.
    assert("derivable" in result, `expected notDerivable, got: ${JSON.stringify(result)}`)
})

Deno.test("deriveLaw: a non-constructor argument term shape-rejects", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    const add = h.opRegistry.lookup("add")!
    const result = deriveLaw(
        { kind: "identity", target: "add", argument: "add(a, b)" },
        add,
        h.registry,
        h.opRegistry,
        h.laws,
    )
    assert("derivable" in result, `expected notDerivable, got: ${JSON.stringify(result)}`)
    assert(result.reason.includes("constructor"))
})

// ── Routing (end-to-end through declareCheckedLaw) ───────────────────────────

Deno.test("routing: identity: Zero on add installs discharged with a certificate", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    const add = h.opRegistry.lookup("add")!
    // The PRE-GATE regime routes residual (the gate is a post-residual
    // upgrade inside declareCheckedLaw, not part of screeningRegime).
    assertEquals(
        screeningRegime({ kind: "identity", target: "add", argument: ZERO_ARG }, add),
        "residual",
    )
    const outcome = declareCheckedLaw(
        { kind: "identity", target: "add", argument: ZERO_ARG },
        h.opRegistry,
        h.laws,
        h.eval_,
        undefined,
        { registry: h.registry },
    )
    assertEquals(outcome.regime, "derivable")
    assertEquals(outcome.law.provenance, "discharged")
    assert(outcome.derivation !== undefined)
    assertEquals(outcome.derivation!.axiomsUsed.length, 0)
})

Deno.test("routing: the fallback — commutative on add installs asserted via the screen", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    const outcome = declareCheckedLaw(
        { kind: "commutative", target: "add" },
        h.opRegistry,
        h.laws,
        h.eval_,
        undefined,
        { registry: h.registry },
    )
    // The engine declined; the residual screen ran; the law installs
    // asserted, and the reported regime names the mechanism that produced
    // the outcome.
    assertEquals(outcome.regime, "residual")
    assertEquals(outcome.law.provenance, "asserted")
    assertEquals(outcome.derivation, undefined)
})

Deno.test("routing: the falsified residual throws LawError (constB's identity)", () => {
    const h = natHarness()
    declareNatOp(h, "constB", CONST_B_DEF)
    assertThrows(
        () =>
            declareCheckedLaw(
                { kind: "identity", target: "constB", argument: ZERO_ARG },
                h.opRegistry,
                h.laws,
                h.eval_,
                undefined,
                { registry: h.registry },
            ),
        LawError,
    )
})

Deno.test("routing: a lawless axiom base declines to the residual screen", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    declareNatOp(h, "addZero", ADD_ZERO_DEF)
    // add carries NO laws here: addZero's identity-right at Succ needs
    // add's identity as an axiom, and the axiom base is empty — the
    // derivation declines (not a falsification: the claim is true, the
    // screen below passes it). The claim falls to the residual screen,
    // which exercises it and installs asserted.
    const outcome = declareCheckedLaw(
        { kind: "identity", target: "addZero", argument: ZERO_ARG },
        h.opRegistry,
        h.laws,
        h.eval_,
        undefined,
        { registry: h.registry },
    )
    assertEquals(outcome.regime, "residual")
    assertEquals(outcome.law.provenance, "asserted")
    assertEquals(outcome.derivation, undefined)
    // The screen DID exercise the claim (the concrete redundancy).
    assert(outcome.instances > 0)
})

Deno.test("routing: a registry-free caller keeps residual routing (additive union)", () => {
    const h = natHarness()
    declareNatOp(h, "add", ADD_DEF)
    // Without the registries threaded, the derivable arm never runs — the
    // claim routes residual and screens, exactly as before this PBI.
    const outcome = declareCheckedLaw(
        { kind: "identity", target: "add", argument: ZERO_ARG },
        h.opRegistry,
        h.laws,
        h.eval_,
    )
    assertEquals(outcome.regime, "residual")
    assertEquals(outcome.law.provenance, "asserted")
    assertEquals(outcome.derivation, undefined)
})

// ── Helpers (the test-local defShape access) ─────────────────────────────────

function readDefShapeFor(
    op: OpSig & { definition: string },
    h: { registry: TypeRegistry; opRegistry: OpRegistry },
    overrideDefinition?: string,
): DefShape {
    const effective = overrideDefinition === undefined
        ? op
        : ({ ...op, definition: overrideDefinition } as OpSig & { definition: string })
    return readDefShape(effective as Parameters<typeof readDefShape>[0], h.registry, h.opRegistry)
}

function readDefShapeRaw(
    h: {
        registry: TypeRegistry
        opRegistry: OpRegistry
        tc: LCTypeCheck
        nat: import("../src/core/types.ts").DataType
    },
    definition: string,
): DefShape {
    const opRegistry = h.opRegistry
    // A fresh probe op per call: Ω's declaration order makes reusing one
    // probe impossible (a second declare would be a duplicate), and a reused
    // probe would read its FIRST definition forever. The arity is the
    // definition's lambda-chain length (well-formedness enforces the
    // agreement — declaring the honest shape).
    const paramCount = (definition.match(/\\[a-zA-Z_][a-zA-Z0-9_]*:/g) ?? []).length
    const name = `shapeProbe${opRegistry.all().length}`
    opRegistry.declare(
        new OpSig(
            name,
            Array.from({ length: paramCount }, () => h.nat),
            h.nat,
            definition,
        ),
        h.tc.opWellFormedness,
    )
    return readDefShape(opRegistry.lookup(name)!, h.registry, opRegistry)
}

// The ScreeningRegime union's new arm is part of the public surface.
const _regimeArm: ScreeningRegime = "derivable"
void _regimeArm
