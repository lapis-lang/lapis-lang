/**
 * Type algebra tests — `derivative(T)` (one-hole contexts).
 *
 * See _docs/theory/type-algebra.md §4 and issue #64. The rules are checked
 * structurally: sum over variants, Leibniz over fields, the μ-bound spelled
 * by `Field.isRecursive` as the hole, and the chain rule's one-level reading
 * for fields of other data types.
 */

import { assertEquals, assertThrows } from "@std/assert"

import { type ContextSpec, derivative } from "../src/core/type_algebra.ts"
import {
    Any,
    DataType,
    Field,
    FunType,
    IntersectionType,
    NothingType,
    PatternDataType,
    TokenType,
    Type,
    Variant,
} from "../src/core/types.ts"

// ── Fixtures ──────────────────────────────────────────────────────────────────

/** `Bool = True | False` — a nullary-sum carrier. */
function bool(): DataType {
    const b = new DataType("Bool", [])
    b.variants.push(new Variant("True", []), new Variant("False", []))
    return b
}

/** `Nat = Zero | Succ(pred: Nat)` — the single-recursive-field carrier. */
function nat(): DataType {
    const n = new DataType("Nat", [])
    n.variants.push(new Variant("Zero", []), new Variant("Succ", [new Field("pred", n, true)]))
    return n
}

/** `Pair(a: Bool, b: Bool)` — the two-field record (Leibniz's product). */
function pair(): DataType {
    const p = new DataType("Pair", [])
    p.variants.push(
        new Variant("MkPair", [new Field("a", bool()), new Field("b", bool())]),
    )
    return p
}

/** `Wrapped(inner: Nat)` — a field of another data type (chain-rule step). */
function wrapped(): DataType {
    const w = new DataType("Wrapped", [])
    w.variants.push(new Variant("MkWrapped", [new Field("inner", nat())]))
    return w
}

/** `Stack = Empty | Push(value: Any, rest: Stack)` — heterogeneous fields. */
function stack(): DataType {
    const s = new DataType("Stack", [])
    s.variants.push(
        new Variant("Empty", []),
        new Variant("Push", [new Field("value", Any, false), new Field("rest", s, true)]),
    )
    return s
}

/**
 * `Fork = Leaf | ForkIt(left: Tree, right: Tree)` — two recursive fields in
 * one variant (both are μ-bound occurrences).
 */
function fork(): DataType {
    const t = new DataType("Fork", [])
    t.variants.push(
        new Variant("Leaf", []),
        new Variant("ForkIt", [new Field("left", t, true), new Field("right", t, true)]),
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
    weird.variants.push(
        new Variant(
            "Mk",
            [
                new Field("fn", new FunType(bool(), nat()), false),
                new Field("tok", new TokenType(), false),
                new Field("pat", new PatternDataType("Pat", ["a+b"]), false),
                new Field("none", new NothingType(), false),
                new Field("any", Any, false),
                new Field("rec", weird, true),
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
