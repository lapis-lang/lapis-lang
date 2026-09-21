/**
 * Type algebra tests — `derivative(T)` (one-hole contexts).
 *
 * See _docs/theory/type-algebra.md §4. The rules are checked
 * structurally: sum over variants, Leibniz over fields, the μ-bound spelled
 * by `Family` as the hole, and the chain rule's one-level reading
 * for fields of other data types.
 */

import { assertEquals, assertThrows } from "@std/assert"

import { coefficients, type ContextSpec, derivative } from "../src/core/type_algebra.ts"
import { createPatternType } from "./fixtures.ts"
import {
    Any,
    CodataType,
    DataType,
    Family,
    Field,
    FunType,
    IntersectionType,
    NothingType,
    Observer,
    TokenType,
    Type,
    Variant,
} from "../src/core/types.ts"

// ── Fixtures ──────────────────────────────────────────────────────────────────

// ── The typed-immutability contract (two-phase construction) ─────────────────

Deno.test("seal: a post-seal addVariant/addObserver throws (the definition is closed)", () => {
    const t = new DataType("SealedProbe", [])
    t.addVariant(new Variant("Base", []))
    t.seal()
    assertThrows(
        () => t.addVariant(new Variant("Evil", [])),
        TypeError,
        "SealedProbe is sealed",
    )
    const c = new CodataType("SealedCodataProbe")
    c.addObserver(new Observer("head", Any))
    c.seal()
    assertThrows(
        () => c.addObserver(new Observer("tail", c)),
        TypeError,
        "SealedCodataProbe is sealed",
    )
})

Deno.test("seal: the frozen array rejects mutation even through a retained alias", () => {
    // The freeze is IN PLACE (not a copy-and-replace): a caller who kept a
    // reference to the pre-seal array cannot mutate the sealed type either.
    const preSealVariants = [new Variant("Base", [])]
    const t = new DataType("AliasProbe", preSealVariants)
    t.seal()
    assertThrows(
        () => preSealVariants.push(new Variant("Evil", [])),
        TypeError,
    )
    // The readonly getter exposes the same (now-frozen) array.
    assertEquals(t.variants.length, 1)
})

// ── Fixtures ──────────────────────────────────────────────────────────────────

/** `Bool = True | False` — a nullary-sum carrier. */
function bool(): DataType {
    const b = new DataType("Bool", [])
    b.addVariant(new Variant("True", []), new Variant("False", []))
    return b
}

/** `Nat = Zero | Succ(pred: Nat)` — the single-recursive-field carrier. */
function nat(): DataType {
    const n = new DataType("Nat", [])
    n.addVariant(new Variant("Zero", []), new Variant("Succ", [new Field("pred", Family)]))
    return n
}

/** `Pair(a: Bool, b: Bool)` — the two-field record (Leibniz's product). */
function pair(): DataType {
    const p = new DataType("Pair", [])
    p.addVariant(
        new Variant("MkPair", [new Field("a", bool()), new Field("b", bool())]),
    )
    return p
}

/** `Wrapped(inner: Nat)` — a field of another data type (chain-rule step). */
function wrapped(): DataType {
    const w = new DataType("Wrapped", [])
    w.addVariant(new Variant("MkWrapped", [new Field("inner", nat())]))
    return w
}

/** `Stack = Empty | Push(value: Any, rest: Stack)` — heterogeneous fields. */
function stack(): DataType {
    const s = new DataType("Stack", [])
    s.addVariant(
        new Variant("Empty", []),
        new Variant("Push", [new Field("value", Any), new Field("rest", Family)]),
    )
    return s
}

/**
 * `Fork = Leaf | ForkIt(left: Tree, right: Tree)` — two recursive fields in
 * one variant (both are μ-bound occurrences).
 */
function fork(): DataType {
    const t = new DataType("Fork", [])
    t.addVariant(
        new Variant("Leaf", []),
        new Variant("ForkIt", [new Field("left", Family), new Field("right", Family)]),
    )
    return t
}

/** A carrier with a comb parent: `NatPos` inherits `Nat`'s variants. */
function natPos(): DataType {
    const n = nat()
    const p = new DataType("NatPos", [new Variant("Top", [])], n)
    return p
}

function spec(
    variantName: string,
    fieldName: string,
    holeType: Type,
    surroundTypes: Type[],
): ContextSpec {
    return { variantName, fieldName, holeType, surroundTypes }
}

// ── The sum rule (nullary variants) ───────────────────────────────────────────

Deno.test("derivative: Bool → [] — a nullary sum has no field to punch", () => {
    assertEquals(derivative(bool()), [])
})

Deno.test("derivative: Nat → one spec — Succ's pred field is the μ-bound spelled as the hole", () => {
    const n = nat()
    assertEquals(derivative(n), [spec("Succ", "pred", n, [])])
})

Deno.test("derivative: two recursive fields in one variant → two specs (each a μ occurrence)", () => {
    const t = fork()
    assertEquals(derivative(t).length, 2)
    assertEquals(derivative(t), [
        spec("ForkIt", "left", t, [t]),
        spec("ForkIt", "right", t, [t]),
    ])
})

// ── Leibniz (the product rule) ────────────────────────────────────────────────

Deno.test("derivative: Pair(a: Bool, b: Bool) → two specs, each surrounding the other field", () => {
    const b = bool()
    const p = pair()
    // ∂(F · G) = ∂F · G + F · ∂G — read structurally: punching field a
    // leaves b as the surroundings, and vice versa. The fields are data
    // types, so the chain-rule reading (holeType = the field's type)
    // applies; the surroundings stay Bool.
    assertEquals(derivative(p), [
        spec("MkPair", "a", b, [b]),
        spec("MkPair", "b", b, [b]),
    ])
})

// ── The chain rule (one level) ────────────────────────────────────────────────

Deno.test("derivative: a field of another data type yields a spec whose holeType is that field's type", () => {
    const n = nat()
    const w = wrapped()
    assertEquals(derivative(w), [spec("MkWrapped", "inner", n, [])])
})

// ── Heterogeneous fields (the screen's unsampleable rules hold) ──────────────

Deno.test("derivative: Stack → only the recursive field yields a spec; Any contributes nothing", () => {
    const s = stack()
    assertEquals(derivative(s), [spec("Push", "rest", s, [Any])])
})

Deno.test("derivative: function-typed, Token, pattern, Nothing, and Any fields contribute no context", () => {
    const weird = new DataType("Weird", [])
    weird.addVariant(
        new Variant(
            "Mk",
            [
                new Field("fn", new FunType(bool(), nat())),
                new Field("tok", new TokenType()),
                new Field("pat", createPatternType("Pat", ["a+b"])),
                new Field("none", new NothingType()),
                new Field("any", Any),
                new Field("rec", Family),
            ],
        ),
    )
    // The unsampleable fields yield no specs of their own, but they DO join
    // the recursive field's surroundings (Leibniz: everything except the
    // hole, in field order).
    assertEquals(derivative(weird).length, 1)
    const [only] = derivative(weird)
    assertEquals(only.variantName, "Mk")
    assertEquals(only.fieldName, "rec")
    assertEquals(only.holeType, weird)
    assertEquals(only.surroundTypes.length, 5)
})

// ── Comb inheritance (the parent chain's variants are covered) ────────────────

Deno.test("derivative: comb inheritance — the parent chain's recursive fields are specs too", () => {
    const p = natPos()
    const specs = derivative(p)
    // Top (own variant, no fields) contributes nothing; the parent chain's
    // Succ field is the single context. The hole's type is the carrier the
    // derivative was taken OF (NatPos): a NatPos value's Succ field takes a
    // NatPos filler — the carrier, not the parent, is the comb's algebra.
    assertEquals(specs.length, 1)
    assertEquals(specs[0], spec("Succ", "pred", p, []))
})

// ── Determinism ───────────────────────────────────────────────────────────────

Deno.test("derivative: the spec order follows declaration order — reproducible shrink candidates", () => {
    const p = pair()
    assertEquals(derivative(p), derivative(p))
})

// ── Boundary: intersections ───────────────────────────────────────────────────

Deno.test("derivative: an intersection-headed carrier is a typed rejection (not a semiring operation)", () => {
    // `derivative` accepts a `DataType` only; the runtime guard inside
    // catches a mis-typed carrier reaching it through an unsound cast (an
    // intersection type is NOT a semiring operation — type-algebra.md §4.3).
    const intersection = new IntersectionType(bool(), nat())
    const mistyped = intersection as unknown as DataType
    assertThrows(() => derivative(mistyped), TypeError, "intersection")
})

// ── Coefficients (type-algebra.md §3 — certified screen coverage) ────────────

Deno.test("coefficients: Bool — the exact product count c₁ = 2, c₀ = 0", () => {
    const b = bool()
    assertEquals(coefficients(b, 3), [0, 2, 0, 0])
})

Deno.test("coefficients: Nat — the chain, one inhabitant per size cₙ = 1", () => {
    const n = nat()
    // Zero is size 1; each Succ adds one node. GF: T = x + x·T (the
    // fixpoint of the chain — a linear recurrence, the rational-GF family).
    assertEquals(coefficients(n, 5), [0, 1, 1, 1, 1, 1])
})

Deno.test("coefficients: Pair(a: Bool, b: Bool) — a record's exact count c₃ = 4", () => {
    const p = pair()
    // MkPair(a: Bool, b: Bool): 1 node + two Bool fields, each contributing
    // 2 size-1 inhabitants → 2·2 = 4 at size 3. The other sizes are 0.
    assertEquals(coefficients(p, 4), [0, 0, 0, 4, 0])
})

Deno.test("coefficients: NS (Zero | One(b: Bool) | Succ(p)) — both field values counted", () => {
    // The coefficient reading sees One(False()) — which the old depth
    // sampler never generated (it took the first field sample per variant).
    const ns = new DataType("NS", [])
    ns.addVariant(
        new Variant("Zero", []),
        new Variant("One", [new Field("b", bool())]),
        new Variant("Succ", [new Field("p", Family)]),
    )
    ns.seal()
    // Size 1: Zero. Size 2: One(True), One(False), Succ(Zero) → 3.
    // Size 3: Succ(One(True)), Succ(One(False)), Succ(Succ(Zero)) → 3.
    // Size 4: three Succ-chains → 3.
    assertEquals(coefficients(ns, 4), [0, 1, 3, 3, 3])
})

Deno.test("coefficients: Tree (Leaf | Node(l, r)) — the Catalan shape (the algebraic family)", () => {
    const t = new DataType("Tree", [])
    t.addVariant(
        new Variant("Leaf", []),
        new Variant("Node", [new Field("l", Family), new Field("r", Family)]),
    )
    t.seal()
    // GF: T = x + x·T² → the Catalan numbers, node-counted: sizes 1, 3, 5
    // hold 1, 1, 2 trees; even sizes hold none (a Node has two subtrees).
    // c₅ = 2: Node(Leaf, Node(Leaf, Leaf)) and its mirror.
    assertEquals(coefficients(t, 5), [0, 1, 0, 1, 0, 2])
})

Deno.test("coefficients: a mutually recursive pair with a base case converges", () => {
    // A = mkA(b: B) | baseA(), B = mkB(a: A). The system advances in
    // lockstep: each round every equation reads the others' PREVIOUS round,
    // so the minimal nonzero degree advances one step per round and the
    // fixpoint settles at the true truncated series.
    const a = new DataType("A", [])
    const b = new DataType("B", [])
    a.addVariant(new Variant("baseA", []), new Variant("mkA", [new Field("b", b)]))
    b.addVariant(new Variant("mkB", [new Field("a", a)]))
    a.seal()
    b.seal()
    // Size 1: baseA. Size 2: mkB(baseA). Size 3: mkA(mkB(baseA)). ...
    assertEquals(coefficients(a, 4), [0, 1, 0, 1, 0])
    assertEquals(coefficients(b, 4), [0, 0, 1, 0, 1])
})

Deno.test("coefficients: a strictly alternating system has NO inhabitants (honest zeros)", () => {
    // A = mkA(b: B), B = mkB(a: A) — no base case: every inhabitant would
    // need the other type at every depth, so both series are identically
    // zero. The fixpoint converges to the honest zeros (an unproductive
    // variant has no inhabitants, consistent with the sampler's drop).
    const a = new DataType("A", [])
    const b = new DataType("B", [])
    a.addVariant(new Variant("mkA", [new Field("b", b)]))
    b.addVariant(new Variant("mkB", [new Field("a", a)]))
    a.seal()
    b.seal()
    assertEquals(coefficients(a, 4), [0, 0, 0, 0, 0])
    assertEquals(coefficients(b, 4), [0, 0, 0, 0, 0])
})

Deno.test("coefficients: a variant with a function-typed field contributes 0", () => {
    const fnBox = new DataType("FnBox", [])
    fnBox.addVariant(
        new Variant("MkFnBox", [new Field("fn", new FunType(bool(), nat()))]),
    )
    // Function-typed fields have no finite vocabulary — the variant dies,
    // the same rule `construct` applies.
    assertEquals(coefficients(fnBox, 3), [0, 0, 0, 0])
})

Deno.test("coefficients: a recursive carrier with an Any field contributes only the chain", () => {
    // Stack = Empty | Push(value: Any, rest: Stack): Push's Any field
    // contributes the zero polynomial — but the variant itself still
    // exists (the product through fields is x·0·x·T = 0, so Push
    // contributes nothing). Only Empty counts.
    const s = stack()
    // GF: S = x (Empty) + x·0 (Push — zero annihilates the product).
    assertEquals(coefficients(s, 3), [0, 1, 0, 0])
})

Deno.test("coefficients: comb inheritance — the parent chain's variants are summed", () => {
    const p = natPos()
    // NatPos = Top | (Nat's Zero | Succ(pred)). The Succ field's hole type
    // is the carrier the derivative was taken of; for coefficients, the
    // recursive field's GF is the CARRIER's (NatPos) — the comb's algebra.
    // Size 1: Zero, Top → 2. Size 2+: one Succ-chain each.
    assertEquals(coefficients(p, 4), [0, 2, 2, 2, 2])
})

Deno.test("coefficients: a pattern type — the language equation (NatPat: cₙ = 10ⁿ)", () => {
    // The language-equation reading: `NatPat = [0-9]+` reads
    // L = P·P* — per length n there are 10ⁿ digit strings. The coefficient
    // is DERIVED from the pattern, not declared.
    const pat = createPatternType("NatPat", ["[0-9]+"])
    assertEquals(coefficients(pat, 3), [0, 10, 100, 1000])
})

Deno.test("coefficients: an empty pattern set has no inhabitants — all zeros", () => {
    const hollow = createPatternType("HollowPat", [])
    assertEquals(coefficients(hollow, 2), [0, 0, 0])
})

Deno.test("coefficients: k = 0 yields just c₀ (empty for every productive type)", () => {
    assertEquals(coefficients(nat(), 0), [0])
    assertEquals(coefficients(bool(), 0), [0])
})

Deno.test("coefficients: an intersection-headed carrier is a typed rejection", () => {
    const intersection = new IntersectionType(bool(), nat())
    const mistyped = intersection as unknown as DataType
    assertThrows(() => coefficients(mistyped, 2), TypeError, "intersection")
})

Deno.test("coefficients: a negative degree is a typed rejection", () => {
    assertThrows(() => coefficients(nat(), -1), RangeError)
})
