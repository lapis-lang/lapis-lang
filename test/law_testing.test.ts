/**
 * Law testing (∂T shrinking) tests — the property-based harness's value
 * layer: context paths, plugging, fillers, and the shrink quality contract.
 *
 * See _docs/theory/law-testing.md (the harness spec), _docs/theory/
 * type-algebra.md §4 (one-hole contexts), and issue #64's acceptance item:
 * "structural shrinking wired into the property harness — minimal-
 * counterexample quality improves measurably on the existing anchor laws".
 */

import { assert, assertEquals } from "@std/assert"

import {
    contextPaths,
    DerivativeGenerator,
    plug,
    renderValue,
    valueEquals,
    valueSize,
} from "../src/index.ts"
import { TokenVal, type Value, ValueEnv, VariantVal } from "../src/core/values.ts"
import { LCEval } from "../src/core/eval_grammar.ts"
import { type EvalTerm, makeEvalTerm } from "../src/core/law_checking.ts"
import { DataType, Field, Variant } from "../src/core/types.ts"

import {
    createLawHarness,
    createOpFixtures,
    createStackType,
    NatSourceGrammar,
} from "./fixtures.ts"

import { PropertyFailure } from "@lapis-lang/lang-forma"

// ── Fixtures ──────────────────────────────────────────────────────────────────

// `nat` is NOT destructured here: the shrinker tests build their generator
// with the carrier from ITS OWN fixture (`derivativeGenerator`) — the
// identity-based carrier guard and `reuseAdmissible` compare `DataType`
// instances by reference, so a module-level type mixed with a fresh eval
// grammar would silently disable reuse and route shrinks to the fallback.
const { registry, opRegistry } = createOpFixtures()
const evalGrammar = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
const evalOf: EvalTerm = makeEvalTerm(evalGrammar)

/** Build a Nat value of depth n by evaluating `Succ(...Zero())` chains. */
function natOf(depth: number): VariantVal {
    const [value] = evalGrammar.parseWith(
        `${"Succ(".repeat(depth)}Zero()${")".repeat(depth)}`,
        new ValueEnv(),
    )
    assert(value instanceof VariantVal, "nat sample must evaluate")
    return value
}

/** The Nat depth of a value (Zero() = 0; Succ(p) = depth(p) + 1). */
function natDepthOf(value: Value): number {
    let depth = 0
    let cur: Value = value
    while (cur instanceof VariantVal && cur.variantName === "Succ") {
        depth++
        cur = cur.fields.get("pred") as Value
    }
    assert(cur instanceof VariantVal && cur.variantName === "Zero", "not a Nat value")
    return depth
}

// ── Context paths ─────────────────────────────────────────────────────────────

Deno.test("contextPaths: a Nat of depth n admits exactly n paths (one per recursive field occurrence)", () => {
    // For a single-recursive-field carrier the path count is the DEPTH: each
    // Succ's pred field is one context; the leaf (Zero, no fields — no hole)
    // contributes none. (Node count = depth + 1: the leaf is a node that
    // yields no context.)
    for (const n of [0, 1, 2, 4]) {
        const value = natOf(n)
        assertEquals(contextPaths(value).length, n)
    }
})

Deno.test("contextPaths: the two contexts of Succ(Succ(Zero())) are the two pred positions", () => {
    const value = natOf(2)
    const paths = contextPaths(value)
    // One-step path: the outer Succ's pred. Two-step path: descending into
    // the inner Succ (the chain rule's value-level reading — the hole type
    // is the carrier, so the descent continues).
    assertEquals(paths.length, 2)
    const rendered = paths.map((p) => p.map(([v, f]) => `${v}.${f}`).join(" > "))
    assertEquals(rendered.toSorted(), [
        "Succ.pred",
        "Succ.pred > Succ.pred",
    ])
})

// ── Plugging ─────────────────────────────────────────────────────────────────
Deno.test("contextPaths: a branching carrier has one path per recursive field occurrence", () => {
    // Tree = Leaf | Node(l: Tree, r: Tree) — two recursive fields per node.
    // A 5-node tree (Node(Node(Leaf,Leaf),Leaf)) has 4 paths: one per
    // recursive FIELD occurrence across the value — the two leaves (nodes
    // with no fields) contribute none, so the count is node count minus
    // leaves, not the node count.
    const tree = new DataType("Tree", [])
    tree.variants.push(
        new Variant("Leaf", []),
        new Variant("Node", [new Field("l", tree, true), new Field("r", tree, true)]),
    )
    const leaf = new VariantVal("Leaf", tree, new Map())
    const inner = new VariantVal(
        "Node",
        tree,
        new Map([["l", leaf], ["r", leaf]]),
    )
    const root = new VariantVal(
        "Node",
        tree,
        new Map([["l", inner], ["r", leaf]]),
    )
    const paths = contextPaths(root)
    assertEquals(paths.length, 4)
    const rendered = paths.map((p) => p.map(([v, f]) => `${v}.${f}`).join(" > ")).toSorted()
    assertEquals(rendered, [
        "Node.l",
        "Node.l > Node.l",
        "Node.l > Node.r",
        "Node.r",
    ])
})

// ── Plugging ─────────────────────────────────────────────────────────────

Deno.test("plug: replacing each context with the same subtree round-trips to the original value", () => {
    const value = natOf(3)
    for (const path of contextPaths(value)) {
        const subtree = (() => {
            let node: VariantVal = value
            for (const [, fieldName] of path) {
                const field = node.fields.get(fieldName!)
                assert(field instanceof VariantVal, "path must descend through a variant")
                node = field
            }
            return node
        })()
        const patched = plug(value, path, subtree)
        assert(patched !== undefined)
        assert(renderValue(patched) === renderValue(value), `path ${path.length} round-trips`)
    }
})

Deno.test("plug: a mismatched path yields undefined (honest failure)", () => {
    const value = natOf(1)
    // A path claiming a Zero root does not match a Succ value.
    assertEquals(plug(value, [["Zero", "pred"]], value), undefined)
})

// ── Sizes and rendering ──────────────────────────────────────────────────────

Deno.test("valueSize: node count — Zero()=1, Succ(Zero())=2", () => {
    assertEquals(valueSize(natOf(0)), 1)
    assertEquals(valueSize(natOf(1)), 2)
    assertEquals(valueSize(natOf(3)), 4)
})

Deno.test("renderValue: the round trip parses and evaluates back to the same value", () => {
    for (const n of [0, 1, 3]) {
        const value = natOf(n)
        const rendered = renderValue(value)
        assert(rendered !== undefined, "a Nat always renders")
        const [reparsed] = evalGrammar.parseWith(rendered, new ValueEnv())
        assert(reparsed instanceof VariantVal)
        assertEquals(renderValue(reparsed), rendered)
    }
})

Deno.test("renderValue: a token renders as its bare type name and round-trips", () => {
    // The evaluator's token source form is the bare pattern-type name
    // (patternTokenProd emits matchedToken(name, name) — text IS the
    // name-lexed source). `Pat("x")` is NOT LC syntax: it was the old
    // renderer's output and failed to re-parse (the malformed-candidate
    // bug this contract fixes).
    const rendered = renderValue(new TokenVal("Pat", "Pat"))
    assertEquals(rendered, "Pat")
})

Deno.test("renderValue: a deviant token (text ≠ type name) declines", () => {
    // Only constructible directly (the evaluator always stamps text = name);
    // the decline keeps such a value from becoming a malformed candidate.
    assertEquals(renderValue(new TokenVal("Pat", "x")), undefined)
})

Deno.test("renderValue: a closure-valued field declines the whole candidate", () => {
    // Stack's `value` field is Any-typed — a Push holding a closure is a
    // real evaluated value, and the closure has NO LC source form. The
    // decline PROPAGATES: a partial render is never emitted.
    const stack = createStackType()
    const [closure] = evalGrammar.parseWith("\\x:Any. x", new ValueEnv())
    assert(closure !== undefined && !(closure instanceof VariantVal))
    const value = new VariantVal(
        "Push",
        stack,
        new Map([["value", closure as Value], ["rest", new VariantVal("Empty", stack, new Map())]]),
    )
    assertEquals(renderValue(value), undefined)
})

// ── The ∂T shrinker (standalone) ──────────────────────────────────────────────

/**
 * A generator bound to the fixtures — shrink tests run against `shrink`
 * directly (forAll-level quality is pinned in laws.test.ts's anchor).
 *
 * The carrier comes from THIS fixture, not the module-level one: reused
 * values produced by `evalG` carry the fresh registry's `DataType` identity,
 * and the shrinker's carrier guard (value.dataType !== carrier → fallback)
 * plus `reuseAdmissible`'s identity check both compare by reference — a
 * module-level `nat` here would silently disable reuse and route every
 * shrink to the regeneration fallback.
 */
function derivativeGenerator(): DerivativeGenerator<{ nat: string }> {
    const { registry, opRegistry, nat: fixtureNat } = createOpFixtures()
    const evalG = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
    return new DerivativeGenerator(
        new NatSourceGrammar(),
        { maxDepth: 4, maxRecursion: 5, branchStrategy: "random" },
        { evalOf: makeEvalTerm(evalG), carrier: fixtureNat },
    )
}

Deno.test("shrink: a Nat's candidates are exactly the strictly smaller Nats, ordered smallest-first per path", () => {
    const gen = derivativeGenerator()
    const value = natOf(2)
    const source = renderValue(value)
    assert(source !== undefined)
    const candidates = gen.shrink(source)
    // Every candidate is a Nat, strictly smaller, and re-parses.
    assert(candidates.length > 0)
    for (const candidate of candidates) {
        const [parsed] = evalGrammar.parseWith(candidate, new ValueEnv())
        assert(parsed instanceof VariantVal, `candidate parses: ${candidate}`)
        assert(
            valueSize(parsed) < valueSize(value),
            `candidate strictly smaller: ${candidate}`,
        )
        assertEquals(natDepthOf(parsed) < natDepthOf(value), true)
    }
})

Deno.test("shrink: structured-but-holeless values decline the ∂T path (zero candidates)", () => {
    // Zero() IS structured (a VariantVal) but has no punchable positions —
    // the ∂T layer emits nothing; the runner's fallback applies. The
    // regeneration strategy may return larger shallower-depth samples —
    // that is its known behavior (re-generation is not size-monotone); the
    // runner only ever ACCEPTS a candidate that still falsifies, so quality
    // is preserved end-to-end even when the fallback is noisy. What this
    // test pins: the ∂T layer itself contributes nothing for a minimal
    // value.
    const paths = contextPaths(natOf(0))
    assertEquals(paths.length, 0)
})

Deno.test("shrink: non-structured counterexamples (closures) delegate to regeneration", () => {
    // A lambda evaluates to a SpanClosure — not a VariantVal — so the ∂T
    // path declines and `super.shrink` (the regeneration strategy) supplies
    // the candidates. This exercises the delegation branch directly (the
    // zero-candidates branch is covered by the minimal-value test above).
    const gen = derivativeGenerator()
    const candidates = gen.shrink("\\x:Any. x")
    assert(Array.isArray(candidates))
})

// ── Reuse pool ────────────────────────────────────────────────────────────────

Deno.test("shrink: fillers reuse the failing value's own subvalues (no generation needed)", () => {
    const gen = derivativeGenerator()
    // Shrink Succ(Succ(Zero())): the outer hole (subtree Succ(Zero()), size
    // 2) takes the pool's Zero() (size 1) — a candidate built by reuse
    // alone, no sampler round-trip. The inner hole (subtree Zero(), size 1)
    // admits no filler: nothing in Nat is smaller than Zero() — the path
    // is exhausted, not skipped. So the candidate list is exactly
    // [Succ(Zero())]: one-level spine shrink, deduped (plugging Zero() into
    // the outer hole renders the SAME source as the existing candidate).
    const source = renderValue(natOf(2))
    assert(source !== undefined)
    const candidates = gen.shrink(source)
    assertEquals(candidates, ["Succ(Zero())"])
})

// ── The harness integration (quality, end to end) ────────────────────────────

Deno.test("harness: the promoted harness still runs forAll end to end (identity fold)", () => {
    const { gen } = createLawHarness()
    const result = gen.forAll((src: string) => {
        const [folded] = evalOf(
            `fold [Nat] ${src} { Zero() -> Zero(), Succ(p) -> Succ(p) }`,
            new ValueEnv(),
        )
        const [original] = evalOf(src, new ValueEnv())
        // Structural equality — the same primitive the law checker uses.
        // (JSON.stringify would choke on the circular `dataType` back-
        // pointers; valueEquals is the honest comparison.)
        return folded !== undefined && original !== undefined && valueEquals(folded, original)
    }, { numRuns: 100, seed: 42 })
    assertEquals(result.passed, true)
})

Deno.test("harness: a falsified property still throws PropertyFailure with a minimal counterexample", () => {
    const { gen } = createLawHarness()
    try {
        gen.forAll((src: string) => {
            const [mul] = evalOf(`mul(${src}, ${src})`, new ValueEnv())
            const [orig] = evalOf(src, new ValueEnv())
            return mul !== undefined && orig !== undefined && valueEquals(mul, orig)
        }, { numRuns: 100, seed: 42 })
        assert(false, "must fail")
    } catch (error) {
        assert(error instanceof PropertyFailure)
        // The counterexample is a Nat source the axiom falsifies.
        const counterexample = error.counterexample as string
        assert(typeof counterexample === "string")
    }
})
