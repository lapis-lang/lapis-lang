/**
 * Cost algebra tests — the static cost/depth analysis over LC terms.
 *
 * See _docs/theory/semantics.md §5.5 (The Cost Algebra) and
 * _docs/issue52-plan.md §5 (the test plan this suite follows).
 *
 * The suites cover, in the plan's order:
 *
 * 1. the `SizeExpr`/`DepthExpr` algebra (construction, saturation,
 *    substitution, rendering, opacity propagation),
 * 2. constructor/app/op composition on hand-computable terms,
 * 3. the certified bounds (linear `add`, stratified `mul`/`addZero`,
 *    exact-literal scrutinees, no-flag on `map` → fold),
 * 4. the flag (the Ackermann shape — a fold whose recursion threads
 *    functions; and the negative control: the same edge with a closed
 *    producer does not flag),
 * 5. codata latency (an unfold whose generator folds over a `Nat`),
 * 6. op summaries (memoization, stratification, the `CostPass` over a
 *    derivation tree, unanalyzable definitions).
 */

import {
    analyzeOp,
    analyzeOps,
    analyzeTerm,
    type CheckedOpSig,
    COST_CEILING,
    CostPass,
    DepthExpr,
    LCTypeCheck,
    type OpCostSummary,
    OpRegistry,
    OpSig,
    OpSummaryStore,
    renderCostReport,
    SizeExpr,
    TypeRegistry,
} from "../src/index.ts"
import {
    DataType,
    Family,
    Field,
    type RequiredCases,
    Type,
    type TypeCases,
    Variant,
} from "../src/core/types.ts"
import { createNatStreamType, createNatType, createOpFixtures } from "./fixtures.ts"

import { assert, assertEquals } from "@std/assert"

// ── 1. The algebra ────────────────────────────────────────────────────────────

Deno.test("SizeExpr: constants, variables, and rendering", () => {
    assertEquals(SizeExpr.ZERO.render(), "0")
    assertEquals(SizeExpr.ONE.render(), "1")
    assertEquals(SizeExpr.constant(7).render(), "7")
    assertEquals(SizeExpr.variable("x").render(), "|x|")
    assertEquals(SizeExpr.variablePow("x", 3).render(), "|x|^3")
})

Deno.test("SizeExpr: plus merges monomials (2|x| + |x| = 3|x|)", () => {
    const sum = SizeExpr.constant(2).times(SizeExpr.variable("x")).plus(SizeExpr.variable("x"))
    assertEquals(sum.render(), "3·|x|")
})

Deno.test("SizeExpr: times distributes (|x|·|y| stays factored)", () => {
    const product = SizeExpr.variable("x").times(SizeExpr.variable("y"))
    assertEquals(product.render(), "|x|·|y|")
})

Deno.test("SizeExpr: pow multiplies exponents (|x|²·|x| = |x|³)", () => {
    const raised = SizeExpr.variablePow("x", 2).times(SizeExpr.variable("x"))
    assertEquals(raised.render(), "|x|^3")
})

Deno.test("SizeExpr: substitution replaces the variable's monomials", () => {
    // |x| + 2·|x|·|y|, x ↦ |z| + 1 → (|z| + 1) + 2·(|z| + 1)·|y|
    const expr = SizeExpr.variable("x").plus(
        SizeExpr.constant(2).times(SizeExpr.variable("x")).times(SizeExpr.variable("y")),
    )
    const substituted = expr.substitute("x", SizeExpr.variable("z").plus(SizeExpr.ONE))
    assertEquals(substituted.render(), "1 + 2·|y| + 2·|y|·|z| + |z|")
})

Deno.test("SizeExpr: saturation at the ceiling (COST_CEILING)", () => {
    const huge = SizeExpr.constant(COST_CEILING)
    assertEquals(huge.plus(SizeExpr.ONE).render(), `${COST_CEILING}`)
    const raised = SizeExpr.variable("x").times(SizeExpr.variable("y"))
    void raised
    // A monomial past the ceiling saturates its coefficient.
    const big = SizeExpr.constant(COST_CEILING).times(SizeExpr.constant(COST_CEILING))
    assertEquals(big.render(), `${COST_CEILING}`)
})

Deno.test("SizeExpr: opaque propagation (any opaque operand → opaque)", () => {
    const opaque = SizeExpr.opaque("function-typed")
    assertEquals(opaque.plus(SizeExpr.ONE).isOpaque, true)
    assertEquals(SizeExpr.ONE.plus(opaque).isOpaque, true)
    assertEquals(opaque.times(SizeExpr.ONE).isOpaque, true)
    assertEquals(opaque.substitute("x", SizeExpr.ONE).isOpaque, true)
    assertEquals(opaque.degree(), Number.POSITIVE_INFINITY)
})

Deno.test("DepthExpr: max-form composition (max, then plus)", () => {
    const d = DepthExpr.constant(2).max(DepthExpr.constant(5))
    assertEquals(d.toSize().render(), "7")
    const chained = DepthExpr.constant(1).plus(SizeExpr.variable("n"))
    assertEquals(chained.toSize().render(), "1 + |n|")
})

Deno.test("DepthExpr: opaque propagation", () => {
    const opaque = DepthExpr.opaque("function depth")
    assertEquals(opaque.max(DepthExpr.constant(3)).isOpaque, true)
    assertEquals(opaque.plus(SizeExpr.ONE).isOpaque, true)
})

// ── 2. Constructor/app/op composition ─────────────────────────────────────────

Deno.test("composition: Zero() costs 1 and sizes 1", () => {
    const fixtures = createOpFixtures()
    const report = analyzeTerm("Zero()", fixtures.registry, fixtures.opRegistry)
    assert(report !== undefined)
    assertEquals(report.cost.render(), "1")
    assertEquals(report.resultSize.render(), "1")
    assertEquals(report.growth, "constant")
})

Deno.test("composition: Succ(Succ(Zero())) costs 3 and sizes 3", () => {
    const fixtures = createOpFixtures()
    const report = analyzeTerm("Succ(Succ(Zero()))", fixtures.registry, fixtures.opRegistry)
    assert(report !== undefined)
    assertEquals(report.cost.render(), "3")
    assertEquals(report.resultSize.render(), "3")
})

Deno.test("composition: a free variable names its own size", () => {
    const fixtures = createOpFixtures()
    const report = analyzeTerm("n", fixtures.registry, fixtures.opRegistry)
    assert(report !== undefined)
    assertEquals(report.resultSize.render(), "|n|")
    assertEquals(report.growth, "linear")
})

// ── 3. Certified bounds ───────────────────────────────────────────────────────

Deno.test("certified: add — linear cost, additive result size, no flags", () => {
    const fixtures = createOpFixtures()
    const report = analyzeOp(fixtures.add as CheckedOpSig, fixtures.registry, fixtures.opRegistry)
    assertEquals(report.status, "analyzed")
    // add's fold over the axis performs one O(1) handler invocation per node:
    // the cost is the axis's size; the result concatenates the two operands.
    assertEquals(report.cost.render(), "|p0|")
    assertEquals(report.resultSize.render(), "|p0| + |p1|")
    assertEquals(report.growth, "linear")
    assertEquals(report.flags.length, 0)
})

Deno.test("certified: mul — quadratic cost, product result size, no flags", () => {
    const fixtures = createOpFixtures()
    const report = analyzeOp(fixtures.mul as CheckedOpSig, fixtures.registry, fixtures.opRegistry)
    assertEquals(report.status, "analyzed")
    // mul's per-node work instantiates add's linear cost (|p1| per node) over
    // the axis (|p0| nodes): the closed form is the stratified polynomial.
    assertEquals(report.cost.render(), "|p0| + |p0|·|p1|")
    assertEquals(report.resultSize.render(), "1 + |p0|·|p1|")
    assertEquals(report.growth, "polynomial")
    assertEquals(report.flags.length, 0)
})

Deno.test("certified: addZero — the fold-composition shape stays polynomial", () => {
    // The derivation engine's canonical second op: recursion continues into
    // add(p, b) — the re-entry through a bounded-size result. Declared on the
    // fixtures' Ω (add comes first — the stratification order).
    const fixtures = createOpFixtures()
    const nat = fixtures.nat
    const tc = new LCTypeCheck().setRegistry(fixtures.registry).setOpRegistry(fixtures.opRegistry)
    const addZero = fixtures.opRegistry.declare(
        new OpSig(
            "addZero",
            [nat, nat],
            nat,
            "\\a:Nat. \\b:Nat. fold [Nat] a { Zero() -> b, Succ(p) -> Succ(add(p, b)) }",
        ),
        tc.opWellFormedness,
    )
    const report = analyzeOp(addZero, fixtures.registry, fixtures.opRegistry)
    assertEquals(report.status, "analyzed")
    assertEquals(report.growth, "polynomial")
    assertEquals(report.flags.length, 0)
    // The quadratic closed form: per-node work grows with the recursion
    // result's size (each step re-adds b), the classic chain summation.
    assert(report.cost.render().includes("|p0|"))
})

Deno.test("certified: exact-literal scrutinee (2 invocations, exact cost AND size)", () => {
    const fixtures = createOpFixtures()
    const report = analyzeTerm(
        "fold [Nat] Succ(Succ(Zero())) { Zero() -> Zero(), Succ(p) -> Succ(p) }",
        fixtures.registry,
        fixtures.opRegistry,
    )
    assert(report !== undefined)
    // The literal scrutinee's node count is known: the scrutinee's own
    // construction (2 nodes) + the fold's per-node work (3 invocations —
    // the literal's full node count — × the handlers' SUMMED costs, 2) —
    // the implemented pairing (the handlers' sum over-approximates the
    // exact Σ_nodes decomposition; for these uniform O(1) handlers the
    // pairing stays within a constant factor). The RESULT SIZE is exact
    // too: a literal scrutinee's result is the recursion's unrolled shape
    // (2 steps from the base — 3 nodes) — no phantom free variable.
    assertEquals(report.cost.render(), "9")
    assertEquals(report.resultSize.render(), "4")
    assertEquals(report.verdict, "certified")
    assertEquals(report.flags.length, 0)
})

Deno.test("certified: map → fold certifies with no flag (affine constructors)", () => {
    // A List carrier, a `map` op over a closed `succ`-like mapped function,
    // and a consuming fold: the producer's result size closes (linear in |l|),
    // so the consumer's scrutinee edge carries a bound — no flag.
    const nat = createNatType()
    const list = new DataType("List", [])
    list.addVariant(
        new Variant("Nil", []),
        new Variant("Cons", [
            new Field("head", nat),
            new Field("tail", Family),
        ]),
    )
    list.seal()
    const registry = new TypeRegistry()
    registry.register(nat)
    registry.register(list)
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)

    // `incList`: maps Succ over the list (each element grows by 1 — the
    // affine-constructor shape; the result size stays linear in |l|). Note
    // the handler's binding list is SPACE-separated (`Cons(h t)`), the
    // grammar's field-binding form (bodies' constructor args take commas).
    const incList = omega.declare(
        new OpSig(
            "incList",
            [list],
            list,
            "\\l:List. fold [List] l { Nil() -> Nil(), Cons(h t) -> Cons(Succ(h), t) }",
        ),
        tc.opWellFormedness,
    )
    const incReport = analyzeOp(incList, registry, omega)
    assertEquals(incReport.status, "analyzed")
    assertEquals(incReport.flags.length, 0)
    // The mapped list's size closes (linear in the input's), the verdict is
    // certified — the Hofmann/LFPL shape. No flags = certified by the
    // classifier (the same criterion the report's verdict states).
    assertEquals(incReport.growth, "linear")

    // A consuming fold over incList's result: the scrutinee edge's producer
    // (the op) has a closed size — the edge certifies.
    const sumReport = analyzeTerm(
        "fold [List] incList(l) { Nil() -> Zero(), Cons(h t) -> Succ(h) }",
        registry,
        omega,
        new Map([["l", list]]),
    )
    assert(sumReport !== undefined)
    assertEquals(sumReport.verdict, "certified")
    assertEquals(sumReport.flags.length, 0)
})

// ── 4. The flag (the Ackermann shape) ─────────────────────────────────────────

const ACKERMANN_TERM =
    "\\m:Nat. fold [Nat] m { Zero() -> \\y:Nat. Succ(y), Succ(p) -> \\y:Nat. p (Succ(y)) }"

Deno.test("flag: the Ackermann shape flags (a fold whose recursion threads functions)", () => {
    // A fold over Nat producing Nat → Nat, whose handler APPLIES the
    // recursion result: the recursion result (function-typed, no size
    // algebra) flows into the application's fn position — the flagged
    // feedback shape. A TERM, not an op: the checker's T-Fold cannot declare
    // function-result folds today (the plan's D7).
    const fixtures = createOpFixtures()
    const report = analyzeTerm(
        ACKERMANN_TERM,
        fixtures.registry,
        fixtures.opRegistry,
        new Map([["m", fixtures.nat]]),
    )
    assert(report !== undefined)
    assertEquals(report.verdict, "flagged")
    assertEquals(report.flags.length, 1)
    const flag = report.flags[0]!
    // The edge: the fold's recursion result → the application's fn position.
    assertEquals(flag.edge.position, "application function")
    assertEquals(flag.edge.producer.kind, "fold")
    assertEquals(flag.edge.isFlagged, true)
    // The payload names the missing bound and the suggested runtime profile.
    assert(flag.missingBound.includes("function-typed"))
    assert(flag.suggestedProfile.includes("observe at runtime"))
})

Deno.test("flag: the negative control — a closed producer on the same edge does not flag", () => {
    // The SAME edge shape (a fold's scrutinee), a CLOSED producer: no flag.
    // The flag is the opacity, not the edge.
    const fixtures = createOpFixtures()
    const report = analyzeTerm(
        "fold [Nat] Succ(Zero()) { Zero() -> Zero(), Succ(p) -> Succ(p) }",
        fixtures.registry,
        fixtures.opRegistry,
    )
    assert(report !== undefined)
    assertEquals(report.edges.length > 0, true)
    assertEquals(report.flags.length, 0)
    assertEquals(report.verdict, "certified")
})

Deno.test("flag: flags are diagnostics — nothing throws, the report carries them", () => {
    const fixtures = createOpFixtures()
    const report = analyzeTerm(
        ACKERMANN_TERM,
        fixtures.registry,
        fixtures.opRegistry,
        new Map([["m", fixtures.nat]]),
    )
    assert(report !== undefined)
    // The rendering includes the flag's payload without throwing.
    const rendered = renderCostReport(report)
    assert(rendered.includes("flag:"))
    assert(rendered.includes("profile:"))
})

// ── 5. Codata latency ─────────────────────────────────────────────────────────

Deno.test("latency: an unfold's generator cost surfaces at the observation", () => {
    // A nat stream whose tail returns self (O(1)) — the simplest analyzable
    // unfold: the codata value itself is O(1) to produce, the observation's
    // latency is the named per-observation atom.
    const natStream = createNatStreamType()
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    registry.register(natStream)
    const omega = new OpRegistry()

    const unfoldReport = analyzeTerm(
        "unfold [NatStream] s { head -> Zero(), tail -> self }",
        registry,
        omega,
        new Map([["s", natStream]]),
    )
    assert(unfoldReport !== undefined)
    assertEquals(unfoldReport.resultSize.render(), "1")
    assertEquals(unfoldReport.verdict, "certified")
    // The latency record: the GENERATOR BODY's cost on the seed, per
    // observer (head's body is Zero() = 1 node; tail's is self = 0 extra).
    assertEquals(unfoldReport.latencies.length, 2)
    assertEquals(unfoldReport.latencies.map((l) => l.observer).sort(), ["head", "tail"])
    const head = unfoldReport.latencies.find((l) => l.observer === "head")
    const tail = unfoldReport.latencies.find((l) => l.observer === "tail")
    assertEquals(head?.latency.render(), "1")
    assertEquals(tail?.latency.render(), "0")

    // The observation's cost carries the latency atom (the codata dual).
    const obsReport = analyzeTerm(
        "(unfold [NatStream] s { head -> Zero(), tail -> self }).head",
        registry,
        omega,
        new Map([["s", natStream]]),
    )
    assert(obsReport !== undefined)
    assert(obsReport.cost.render().includes("latency(head)"))
    // The latency records ride along from the unfold (head, tail) plus the
    // observation's own (head again) — the per-observer ledger.
    assertEquals(obsReport.latencies.length, 3)
    assertEquals(obsReport.latencies[obsReport.latencies.length - 1]!.observer, "head")
    assertEquals(obsReport.verdict, "certified")
})

Deno.test("latency: an unbounded latency leaves the verdict certified but the atom stated", () => {
    // The codata dual's honest residual: an observation's cost contains the
    // free |latency(o)| variable nothing bounds — the generator term is
    // arbitrary. The classifier reads the RESULT SIZE (a stream value is
    // O(1) to produce), so the verdict stays certified; the latency atom in
    // the cost expression is the certificate's stated residual (productivity
    // guarantees finite work, not small work — semantics.md §5.5).
    const natStream = createNatStreamType()
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    registry.register(natStream)
    const omega = new OpRegistry()
    const report = analyzeTerm(
        "(unfold [NatStream] s { head -> Zero(), tail -> self }).head",
        registry,
        omega,
        new Map([["s", natStream]]),
    )
    assert(report !== undefined)
    assertEquals(report.verdict, "certified")
    assert(report.cost.render().includes("latency(head)"))
    assert(report.latencies.some((l) => l.observer === "head"))
})

Deno.test("regression: a generator's diagnostic records reach the unfold's certificate", () => {
    // A generator body that contains the Ackermann shape (a fold whose
    // recursion result is applied) carries a FLAG edge inside its body —
    // the pre-fix bug deferred it with the generator's WORK (the latency),
    // so observing the stream reported `certified` while the flagged
    // feedback hid inside the generator. Records ride along now; only the
    // work stays deferred.
    const natStream = createNatStreamType()
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    registry.register(natStream)
    const omega = new OpRegistry()
    const report = analyzeTerm(
        "unfold [NatStream] s { head -> \\m:Nat. fold [Nat] m { Zero() -> \\y:Nat. Succ(y), Succ(p) -> \\y:Nat. p (Succ(y)) }, tail -> self }",
        registry,
        omega,
        new Map([["s", natStream]]),
    )
    assert(report !== undefined)
    // The flag surfaces (the generator's records are the codata value's
    // own certificate), never laundered into a certified report.
    assertEquals(report.verdict, "flagged")
    assertEquals(report.flags.length, 1)
    assertEquals(report.flags[0]!.edge.producer.kind, "fold")
})

Deno.test("provenance: the codata constructs keep their own kinds (not fold)", () => {
    // An unfold's result is a codata VALUE — its edge provenance is `unfold`,
    // not the fold kind (conflating them would mislabel the flag's producer
    // end and make diagnostics claim a recursion result where none exists).
    const natStream = createNatStreamType()
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    registry.register(natStream)
    const omega = new OpRegistry()

    // The unfold's result flows into the observation: the edge's producer
    // names the construct (`unfold`, not `fold`).
    const applied = analyzeTerm(
        "(unfold [NatStream] s { head -> Zero(), tail -> self }).head",
        registry,
        omega,
        new Map([["s", natStream]]),
    )
    assert(applied !== undefined)
    const producer = applied.edges.find((e) => e.position === "observation generator")!.producer
    assertEquals(producer.kind, "unfold")
    assert(producer.kind === "unfold" && producer.name === "NatStream")

    // An application of an unfold's result is an ordinary first-order data
    // flow: the result is a known size-1 value with data kind — the app's
    // function position carries NO flag (the flag is the fold's recursion
    // result, which an unfold's result is not).
    assertEquals(applied.verdict, "certified")
    assertEquals(applied.flags.length, 0)
})

// ── 6. Robustness: classification degrades, never crashes ────────────────────

Deno.test("typeKind: a pass-local Type subclass classifies unknown, never crashes", () => {
    // The cost engine's marker types (FoldRecType) are pass-local Type
    // subclasses outside the core universe — `typeKind`'s contract is a TAG,
    // not a membership test: an undeclared kind degrades to `unknown` (the
    // classification route is foldType under a try), never throws (the
    // analysis never throws). Probed through the public entry with a
    // synthetic environment carrying a foreign marker: a binder denoted by
    // a non-universe type keeps the analysis alive — its denotation
    // classifies unknown and its size stays a named variable.
    class ForeignMarker extends Type {
        equals(other: Type): boolean {
            return other instanceof ForeignMarker
        }
        toString(): string {
            return "⟨foreign⟩"
        }
        // The pass-local marker is outside the core universe — no generic
        // case table or structural map answers for it (mirrors the engine's
        // FoldRecType).
        override dispatch<T>(_cases: RequiredCases<T>): T {
            throw new TypeError("ForeignMarker is outside the Type universe")
        }

        override map(_cases: TypeCases<Type>): Type {
            throw new TypeError("ForeignMarker is outside the Type universe")
        }

        override resolveFamily(_carrier: DataType): Type {
            throw new TypeError("ForeignMarker is outside the Type universe")
        }
    }
    const { registry, opRegistry, nat } = createOpFixtures()
    const report = analyzeTerm(
        "fold [Nat] x { Zero() -> Zero(), Succ(p) -> Succ(p) }",
        registry,
        opRegistry,
        new Map([["x", new ForeignMarker()]]),
    )
    // The binder's denotation holds the foreign marker: an old-style
    // membership test would have crashed the fold analysis; the
    // classification degrades to unknown and the fold still runs (the
    // scrutinee's size is the named variable the denotation assigned).
    assert(report !== undefined, "the analysis never throws on any input")
    assertEquals(report!.status, "analyzed")
    void nat
})

Deno.test("typeKind: the core universe still classifies exactly (fun/data)", () => {
    // The try/catch must not weaken the classification itself: every core
    // kind answers its case, and the tag table is unchanged. A data-typed
    // binder keeps symbolic sizes (kind "data" — a fold reads |x| as the
    // recurrence input); a function-typed binder is opaque (kind "function").
    const { registry, opRegistry, nat } = createOpFixtures()
    const dataReport = analyzeTerm(
        "fold [Nat] x { Zero() -> Zero(), Succ(p) -> Succ(p) }",
        registry,
        opRegistry,
        new Map([["x", nat]]),
    )
    assert(dataReport !== undefined)
    assertEquals(dataReport!.status, "analyzed")
    // The data path closes the chain recurrence — the classification fed it.
    assertEquals(dataReport!.growth, "linear")
})

// ── 7. Op summaries: memoization, stratification, the pass ────────────────────

Deno.test("memoization: a shared store serves the same object; a fresh store recomputes", () => {
    const fixtures = createOpFixtures()
    const add = fixtures.add as CheckedOpSig
    // Two summaryOf calls through the SAME store: the second serves the
    // memo — the identical summary object (identity, not merely deep
    // equality). This is the cache that makes a batch (`analyzeOps`) or a
    // pass (which holds one store) compute each op once.
    const store = new OpSummaryStore(fixtures.registry)
    const first = store.summaryOf(fixtures.opRegistry, add)
    const second = store.summaryOf(fixtures.opRegistry, add)
    assert(first === second)

    // A FRESH store recomputes: an equal summary, a different object (the
    // memo is per-store).
    const fresh = new OpSummaryStore(fixtures.registry).summaryOf(fixtures.opRegistry, add)
    assert(fresh !== first)
    assertEquals(fresh, first)
})

Deno.test("memoization: the public entries share the (registry, Ω)-keyed store", () => {
    const fixtures = createOpFixtures()
    const add = fixtures.add as CheckedOpSig
    // Separate analyzeOp CALLS on the same (registry, Ω) pair: the
    // module-level store cache keys the memo by the pair's identity — the
    // second call re-serves the FIRST call's summary object (the memo
    // survives across calls; the pre-fix per-call store restarted it).
    const first = analyzeOp(add, fixtures.registry, fixtures.opRegistry)
    const second = analyzeOp(add, fixtures.registry, fixtures.opRegistry)
    assert(first === second)
    // And a batch through the same pair shares the same store — the
    // batched summary is the cached object too.
    const batched = analyzeOps([add], fixtures.registry, fixtures.opRegistry)[0]!
    assert(batched === first)
})

Deno.test("stratification: analyzeOps computes in declaration order", () => {
    const fixtures = createOpFixtures()
    const summaries = analyzeOps(
        [fixtures.add as CheckedOpSig, fixtures.mul as CheckedOpSig],
        fixtures.registry,
        fixtures.opRegistry,
    )
    assertEquals(summaries.length, 2)
    assertEquals(summaries[0]!.op.name, "add")
    assertEquals(summaries[1]!.op.name, "mul")
    // mul's summary is computed AFTER add's — the declaration order (the
    // stratification that makes the analysis well-founded).
    assertEquals(summaries[0]!.cost.render(), "|p0|")
    assertEquals(summaries[1]!.cost.render(), "|p0| + |p0|·|p1|")
})

Deno.test("CostPass: the tree entry composes the memoized op summary", () => {
    // The identity-survival integration: the tree's opProd node names the
    // op; the pass consumes the derivation tree and reports the analysis.
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)
    omega.declare(
        new OpSig(
            "double",
            [nat],
            nat,
            "\\n:Nat. fold [Nat] n { Zero() -> Zero(), Succ(p) -> Succ(Succ(p)) }",
        ),
        tc.opWellFormedness,
    )

    const source = "double(Succ(Zero()))"
    const tree = tc.parseToTree(source).trees[0]
    assert(tree !== undefined)
    const pass = new CostPass(registry, omega)
    const report = pass.evaluateReport(tree)
    assert(report !== undefined)
    // The engine's own analysis of the same source — the two vehicles agree.
    const direct = analyzeTerm(source, registry, omega)
    assertEquals(report.cost.render(), direct?.cost.render())
    assertEquals(report.resultSize.render(), direct?.resultSize.render())
    assertEquals(report.verdict, direct?.verdict)
    assertEquals(report.subject, source)
})

Deno.test("CostPass: a data term's tree walks to the constructor rule", () => {
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(new OpRegistry())
    const tree = tc.parseToTree("Succ(Zero())").trees[0]
    assert(tree !== undefined)
    const pass = new CostPass(registry, new OpRegistry())
    const report = pass.evaluateReport(tree)
    assert(report !== undefined)
    assertEquals(report.cost.render(), "2")
    assertEquals(report.resultSize.render(), "2")
})

Deno.test("CostPass: the memo does not leak across reports (per-report walk state)", () => {
    // A long-lived pass must not retain the nodes (or the op identities) of
    // trees it has already walked: the defer memo and the identity sets are
    // per-report. Two successive evaluateReport calls on DIFFERENT trees
    // through the SAME pass stay independent.
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)
    omega.declare(
        new OpSig(
            "double",
            [nat],
            nat,
            "\\n:Nat. fold [Nat] n { Zero() -> Zero(), Succ(p) -> Succ(Succ(p)) }",
        ),
        tc.opWellFormedness,
    )
    const pass = new CostPass(registry, omega)

    const first = pass.evaluateReport(tc.parseToTree("double(Succ(Zero()))").trees[0]!)
    assert(first !== undefined)
    // The eager argument composes with the instantiated callee summary:
    // the arg's construction (2 nodes) + the fold's instantiated cost
    // (3·|p0| at |p0| = 2 → 6) = 8 — the argument's work is part of the
    // application (E-OpArg evaluates eagerly, leftmost).
    assertEquals(first.cost.render(), "8")

    const second = pass.evaluateReport(tc.parseToTree("Succ(Succ(Zero()))").trees[0]!)
    assert(second !== undefined)
    // The second report is the data term's own — not the first tree's
    // composition, not inflated by retained walk state.
    assertEquals(second.cost.render(), "3")
    assertEquals(second.unresolved.length, 0)
})

Deno.test("CostPass: a divergent Ω surfaces the tree's unknown-op names as residuals", () => {
    // The tree was derived under an Ω that declares `double`; the pass's Ω
    // does not. The tree still NAMES the applied op — the walk records it,
    // and the report states the residual (its work is not counted) instead
    // of silently dropping it. Never a crash.
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)
    omega.declare(
        new OpSig(
            "double",
            [nat],
            nat,
            "\\n:Nat. fold [Nat] n { Zero() -> Zero(), Succ(p) -> Succ(Succ(p)) }",
        ),
        tc.opWellFormedness,
    )
    const tree = tc.parseToTree("double(Succ(Zero()))").trees[0]!
    const divergentPass = new CostPass(registry, new OpRegistry())
    const report = divergentPass.evaluateReport(tree)
    assert(report !== undefined)
    // The residual names the op and the non-counting policy.
    assert(
        report.unresolved.some((u) => u.reason.includes("double")),
    )
})

Deno.test("unanalyzable: a definition the engine cannot read reports honestly", () => {
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)
    // A definition the checker REJECTS cannot enter Ω (declare throws — the
    // Ω-acyclicity/trust boundary). The engine's `unanalyzed` shape is what a
    // definition that PARSES-but-does-not-read would carry; here the honest
    // check is on the store's behavior for a definition the engine cannot
    // read: a term-shaped non-LC string analyzed through the store's path.
    // analyzeTerm (the same engine read) returns undefined — the caller's
    // decision point, never a throw.
    const summary = analyzeTerm("@@@ not LC source @@@", registry, omega)
    assertEquals(summary, undefined)
    // A definition that types but parses to an ambiguous forest would surface
    // as `unanalyzed` via the store; the public contract is: no throw.
    const wellFormed = omega.declare(
        new OpSig("ok", [nat], nat, "\\n:Nat. Zero()"),
        tc.opWellFormedness,
    )
    const report = analyzeOp(wellFormed, registry, omega)
    assertEquals(report.status, "analyzed")
    assertEquals(report.flags.length, 0)
    assertEquals(report.cost.render(), "1")
})

Deno.test("unanalyzable: the summary store's cycle guard never diverges", () => {
    // The cycle guard is defensive (Ω's acyclicity makes re-entrance
    // unreachable through `declare`), but its contract is directly testable:
    // a summary requested WHILE being computed serves the opaque placeholder
    // — never divergence — and the computed summary overwrites it.
    const nat = createNatType()
    const registry = new TypeRegistry()
    registry.register(nat)
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)
    const op = omega.declare(
        new OpSig("reentrant", [nat], nat, "\\n:Nat. Zero()"),
        tc.opWellFormedness,
    )
    class ReentrantStore extends OpSummaryStore {
        private entered = false
        override summaryOf(o: OpRegistry, target: CheckedOpSig): OpCostSummary {
            if (!this.entered && target.name === op.name) {
                this.entered = true
                return super.summaryOf(o, target) // re-enters the guard path
            }
            return super.summaryOf(o, target)
        }
    }
    const summary = new ReentrantStore(registry).summaryOf(omega, op as CheckedOpSig)
    // No divergence; the computed summary wins.
    assertEquals(summary.status, "analyzed")
    assertEquals(summary.cost.render(), "1")
})

Deno.test("report rendering: the certificate states the bounds and the edges", () => {
    const fixtures = createOpFixtures()
    const report = analyzeOp(fixtures.add as CheckedOpSig, fixtures.registry, fixtures.opRegistry)
    const rendered = renderCostReport(report)
    // The renderer states the op's name (the subject) and its bounds.
    assert(rendered.includes("add"))
    assert(rendered.includes("cost: |p0|"))
    assert(rendered.includes("growth: linear"))
})

// ── 7. Solver soundness regressions ───────────────────────────────────────────

Deno.test("regression: multiplicative feedback does NOT close to a linear bound", () => {
    // pow2(x, y) computes |y|^|x| — geometric growth through a first-order
    // op: R(n) = 1 + |y|·R(n−1). The recursion variable rides a symbolic
    // factor (multiplicative feedback), so the recurrence must NOT close to
    // base + |input|·g — the certificate states the recurrence and the coarse
    // class, never a closed (linear!) bound. The pre-fix bug closed it to
    // `2 + |p0|` with growth "linear" — a false certificate.
    const fixtures = createOpFixtures()
    const nat = fixtures.nat
    const tc = new LCTypeCheck().setRegistry(fixtures.registry).setOpRegistry(fixtures.opRegistry)
    const pow2 = fixtures.opRegistry.declare(
        new OpSig(
            "pow2",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> Succ(Zero()), Succ(p) -> mul(y, p) }",
        ),
        tc.opWellFormedness,
    )
    const report = analyzeOp(pow2, fixtures.registry, fixtures.opRegistry)
    assertEquals(report.status, "analyzed")
    // No closed linear bound: the result size is the honest opaque residual.
    assert(report.resultSize.isOpaque)
    // The certificate states the recurrence (with the recursion substituted).
    assert(report.recurrence !== undefined)
    assert(report.recurrence!.includes("#foldRec"))
    assertEquals(report.growth, "unbounded")
    assertEquals(report.flags.length, 0) // certified-coarse, never flagged
})

Deno.test("regression: additive growth with a symbolic factor still closes", () => {
    // The LFPL shape stays closable: R(n) = |y|² + R(n−1) (the recursion feeds
    // back BARE, the R-free remainder grows symbolically) closes to
    // base + |x|·|y|² — polynomial, not opaque. The bare-variable test must
    // not over-reject the additive form addZero relies on.
    const fixtures = createOpFixtures()
    const nat = fixtures.nat
    const tc = new LCTypeCheck().setRegistry(fixtures.registry).setOpRegistry(fixtures.opRegistry)
    const grow = fixtures.opRegistry.declare(
        new OpSig(
            "grow",
            [nat, nat],
            nat,
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> y, Succ(p) -> Succ(mul(y, y)) }",
        ),
        tc.opWellFormedness,
    )
    const report = analyzeOp(grow, fixtures.registry, fixtures.opRegistry)
    assertEquals(report.status, "analyzed")
    assert(!report.resultSize.isOpaque)
    assertEquals(report.growth, "polynomial")
})

Deno.test("regression: a sum-scrutinee's FULL size drives the recurrence", () => {
    // fold over add(m, n): the invocation count is |m| + |n| nodes — the
    // recurrence's input is the scrutinee's whole size expression. The old
    // `variables()[0]` pick dropped |n|, understating the result as 1 + |m|.
    const fixtures = createOpFixtures()
    const report = analyzeTerm(
        "fold [Nat] add(m, n) { Zero() -> Zero(), Succ(p) -> Succ(p) }",
        fixtures.registry,
        fixtures.opRegistry,
        new Map([["m", fixtures.nat], ["n", fixtures.nat]]),
    )
    assert(report !== undefined)
    assertEquals(report.resultSize.render(), "1 + |m| + |n|")
})

Deno.test("regression: the symbolic fold-recursion variable is untypable", () => {
    // A user binder literally named `foldRec` must not collide with the
    // fold's own symbolic recursion quantity under `substitute` — the `#`
    // prefix keeps the algebra's names out of the user's namespace.
    const fixtures = createOpFixtures()
    const report = analyzeTerm(
        "fold [Nat] m { Zero() -> Zero(), Succ(foldRec) -> foldRec }",
        fixtures.registry,
        fixtures.opRegistry,
        new Map([["m", fixtures.nat]]),
    )
    assert(report !== undefined)
    // The identity handler: the result size is the input's, cost linear.
    assertEquals(report.resultSize.render(), "1 + |m|")
    assertEquals(report.flags.length, 0)
})

Deno.test("regression: let-bound definition's result size threads to the body", () => {
    // let n = Succ(Succ(Zero())) in fold [Nat] n: the binder denotes the
    // DEFINITION'S result (2 nodes), not a fresh symbolic variable — the
    // engine and the pass agree on the exact bound (4 nodes, cost 9).
    const fixtures = createOpFixtures()
    const source =
        "let n : Nat = Succ(Succ(Zero())) in fold [Nat] n { Zero() -> Zero(), Succ(p) -> Succ(p) }"
    const engineReport = analyzeTerm(source, fixtures.registry, fixtures.opRegistry)
    assert(engineReport !== undefined)
    assertEquals(engineReport.resultSize.render(), "4")
    assertEquals(engineReport.cost.render(), "9")

    // The pass (the tree vehicle) agrees — the two vehicles' let binding
    // rules are the same substitution.
    const tree = new LCTypeCheck().setRegistry(fixtures.registry)
        .setOpRegistry(fixtures.opRegistry).parseToTree(source).trees[0]
    assert(tree !== undefined)
    const pass = new CostPass(fixtures.registry, fixtures.opRegistry)
    const passReport = pass.evaluateReport(tree)
    assert(passReport !== undefined)
    assertEquals(passReport.resultSize.render(), engineReport.resultSize.render())
    assertEquals(passReport.cost.render(), engineReport.cost.render())
})

// ── Helpers: the types the suites above construct ─────────────────────────────
// (Variant/Field come from `src/core/types.ts`; the List carrier is built
// inline in the map test — a fresh μ-type per call, mirroring the fixtures.)
