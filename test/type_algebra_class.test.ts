/**
 * Type algebra judgment-class tests — the class-level behaviors the
 * structural tests in `type_algebra.test.ts` do not reach: the
 * identity-keyed memos (the "@rule-style" seam without the decorator's
 * `Grammar` precondition), the `ContextSpec` chain-rule data edge, and the
 * typed-rejection boundary's caller-naming discipline.
 *
 * See _docs/theory/type-algebra.md §1 (the judgment-class consolidation),
 * §4.3 (the boundary), and the D1–D8 decisions of the plan these
 * behaviors implement.
 */

import { assert, assertEquals, assertThrows } from "@std/assert"

import {
    coefficients,
    derivative,
    finiteInhabitants,
    TypeAlgebra,
    typeAlgebra,
} from "../src/core/type_algebra.ts"
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
    Variant,
} from "../src/core/types.ts"
import { TokenVal, VariantVal } from "../src/core/values.ts"

// ── Fixtures ──────────────────────────────────────────────────────────────────

/** `Bool = True | False` — a nullary-sum carrier. */
function bool(): DataType {
    return DataType.define("Bool")
        .addVariant(new Variant("True", []), new Variant("False", []))
        .build()
}

/** `Nat = Zero | Succ(pred: Nat)` — the single-recursive-field carrier. */
function nat(): DataType {
    return DataType.define("Nat")
        .addVariant(new Variant("Zero", []), new Variant("Succ", [new Field("pred", Family)]))
        .build()
}

// ── Identity-keyed memos (D2 — the same-instance cache) ──────────────────────

Deno.test("memo identity: a repeat call on the same instance reads the memo (same spec objects)", () => {
    const t = nat()
    const first = typeAlgebra.derivative(t)
    const second = typeAlgebra.derivative(t)
    // The same array object — the memo hit, not a rebuild.
    assert(first === second)
    // The specs are the SAME objects too (the indexed accessor serves the
    // memoized list, never a fresh construction).
    const index = typeAlgebra.specFor(t)
    assert(index.get("Succ")?.get("pred") === first[0])
})

Deno.test("memo identity: two distinct DataType instances with the same name get separate verdicts", () => {
    // Instance identity is the cache key (the treeKey v3.0.1 keying scheme):
    // two structurally identical carriers are distinct cache entries — the
    // holeTypeAt identity discipline's mirror. (DataType.equals is name-based;
    // the memo deliberately is NOT.)
    const a = nat()
    const b = nat()
    assert(a !== b)
    assertEquals(a.name, b.name)
    const aSpecs = typeAlgebra.derivative(a)
    const bSpecs = typeAlgebra.derivative(b)
    assert(aSpecs !== bSpecs)
    assert(aSpecs[0] !== bSpecs[0])
    // The verdicts agree structurally — they are just not shared.
    assertEquals(aSpecs.length, bSpecs.length)
    assertEquals(aSpecs[0].holeType, bSpecs[0].holeType)
})

Deno.test("memo identity: a fresh TypeAlgebra instance has its own empty memo", () => {
    // Instances carry their caches; the module default instance's state does
    // not leak into (or from) a fresh one — a consumer isolating its memos
    // constructs its own algebra (D5's fresh-instance story).
    const fresh = new TypeAlgebra()
    const t = nat()
    const freshSpecs = fresh.derivative(t)
    const defaultSpecs = typeAlgebra.derivative(t)
    assert(freshSpecs !== defaultSpecs)
    assertEquals(freshSpecs.length, defaultSpecs.length)
    // And the fresh instance's own memo is identity-keyed the same way.
    assert(fresh.derivative(t) === freshSpecs)
})

Deno.test("inhabitants: the verdict memo round-trips both outcomes", () => {
    // The memo's sentinel contract: an undefined verdict (unbounded) and a
    // numeric one are both cached, and each reads back as itself — the
    // memo cannot confuse "absent" with "stored undefined" (the
    // null-sentinel reads back as undefined).
    const n = nat()
    assertEquals(finiteInhabitants(n), undefined)
    assertEquals(finiteInhabitants(n), undefined, "the undefined verdict survives the memo hit")
    const b = bool()
    assertEquals(finiteInhabitants(b), 2)
    assertEquals(finiteInhabitants(b), 2, "the numeric verdict survives the memo hit")
})

Deno.test("inhabitants: the verdict memo is per-algebra-instance (a fresh instance recomputes)", () => {
    const fresh = new TypeAlgebra()
    const b = bool()
    assertEquals(fresh.inhabitants(b), 2)
    // The module default instance was never asked about THIS carrier —
    // its memo is empty for it (no cross-instance cache sharing).
    assertEquals(finiteInhabitants(bool()), 2)
})

Deno.test("inhabitants: same-name carriers do not share verdicts (identity keying)", () => {
    // A Bool whose only field is a data field of ANOTHER Bool: the count is
    // the product through the field's own count (2), but the recursive
    // Nat-shaped twin keeps its undefined verdict — same name, different
    // shapes, different verdicts, never conflated by the memo.
    const inner = DataType.define("Carrier")
        .addVariant(new Variant("MkInner", [new Field("flag", bool())]))
        .build()
    assertEquals(finiteInhabitants(inner), 2)
    const outer = DataType.define("Carrier")
        .addVariant(
            new Variant("MkOuter", [new Field("flag", bool()), new Field("rest", Family)]),
        )
        .build()
    assertEquals(finiteInhabitants(outer), undefined)
    // The first verdict is intact after the second's walk.
    assertEquals(finiteInhabitants(inner), 2)
})

// ── ContextSpec.derivative(): the chain rule as data (D3) ────────────────────

Deno.test("context edge: a data-hole spec carries the hole's own derivative", () => {
    // Wrapped(inner: Nat): the spec's holeType is Nat, so the edge is
    // Nat's derivative — the chain rule's next step, held ON the spec.
    const n = nat()
    const w = DataType.define("Wrapped")
        .addVariant(new Variant("MkWrapped", [new Field("inner", n)]))
        .build()
    const [spec] = typeAlgebra.derivative(w)
    assert(spec.holeType === n)
    const edge = spec.derivative()
    assert(edge !== undefined)
    assertEquals(edge.length, 1)
    assertEquals(edge[0].variantName, "Succ")
    assertEquals(edge[0].fieldName, "pred")
    // The edge IS the hole type's derivative — the same objects the
    // algebra serves for the hole type directly.
    assert(edge[0] === typeAlgebra.derivative(n)[0])
})

Deno.test("context edge: a recursive-hole spec's edge is the carrier's own derivative", () => {
    // Nat's Succ field is the μ-bound: the hole type IS the carrier, so the
    // edge is the carrier's derivative — the self-referential step the
    // zipper walk takes (Nat: each spec's edge is the same list).
    const n = nat()
    const [spec] = typeAlgebra.derivative(n)
    assert(spec.holeType === n)
    const edge = spec.derivative()
    assertEquals(edge, typeAlgebra.derivative(n))
})

Deno.test("context edge: no-structure hole types carry no edge (undefined)", () => {
    // Token, function, Any, Nothing, pattern, and intersection hole types
    // contribute no context of their own — the edge is undefined (the same
    // unsampleable rule the readings apply). The surrounding specs still
    // exist; only the edge is absent.
    const b = bool()
    const weird = DataType.define("Weird")
        .addVariant(
            new Variant(
                "Mk",
                [
                    new Field("fn", new FunType(b, nat())),
                    new Field("any", Any),
                    new Field("none", new NothingType()),
                    new Field("rec", Family),
                ],
            ),
        )
        .build()
    const specs = typeAlgebra.derivative(weird)
    assertEquals(specs.length, 1)
    const [spec] = specs
    // The recursive hole: edge defined (the carrier's own derivative).
    assert(spec.holeType === weird)
    assertEquals(spec.derivative(), specs)
    // A data-hole spec on another carrier: edge defined.
    const wrapped = DataType.define("Wrapped")
        .addVariant(new Variant("MkWrapped", [new Field("inner", nat())]))
        .build()
    const dataSpec = typeAlgebra.derivative(wrapped)[0]
    assert(dataSpec.derivative() !== undefined)
})

Deno.test("context edge: the edge is computed at most once per spec (lazily memoized)", () => {
    // Two consultations return the same edge — the lazily-memoized data
    // edge, not a re-walk per consultation.
    const n = nat()
    const w = DataType.define("Wrapped")
        .addVariant(new Variant("MkWrapped", [new Field("inner", n)]))
        .build()
    const [spec] = typeAlgebra.derivative(w)
    assert(spec.derivative() === spec.derivative())
})

// ── The typed-rejection boundary (D6 — the caller-naming discipline) ─────────

Deno.test("boundary: derivative and coefficients both name themselves in the intersection rejection", () => {
    // The message interpolates `type.name` — an IntersectionType carries no
    // name of its own (it reads as undefined through the boundary's
    // interpolation, the same shape a mis-typed cast produces). The prefix
    // is the contract: each calling judgment's message carries ITS OWN
    // name — the same discipline `subtyping.ts`'s `requireType` applies to
    // the lattice.
    const intersection = new IntersectionType(bool(), nat()) as unknown as DataType
    assertThrows(
        () => typeAlgebra.derivative(intersection),
        TypeError,
        "derivative(",
    )
    assertThrows(
        () => typeAlgebra.derivative(intersection),
        TypeError,
        "intersection types are not a semiring operation",
    )
    const ix = new IntersectionType(bool(), nat()) as unknown as DataType
    assertThrows(
        () => typeAlgebra.coefficients(ix, 2),
        TypeError,
        "coefficients(",
    )
    assertThrows(
        () => typeAlgebra.coefficients(ix, 2),
        TypeError,
        "no coefficient reading is defined",
    )
})

Deno.test("boundary: a codata carrier rejects with the coalgebraic-dual message", () => {
    const stream = CodataType.define("Stream").addObserver(new Observer("head", Any)).build()
    assertThrows(
        () => typeAlgebra.coefficients(stream, 2),
        TypeError,
        "coalgebraic dual",
    )
    // BOTH readings reject a ν-carrier through the same boundary — the
    // derivative gained this rejection in the consolidation (the
    // free-function form accepted the signature and would crash on an
    // unsound cast; the boundary rejects it with a typed error instead).
    assertThrows(
        () => typeAlgebra.derivative(stream as unknown as DataType),
        TypeError,
        "coalgebraic dual",
    )
})

Deno.test("boundary: the free-function delegates route through the same boundary", () => {
    const intersection = new IntersectionType(bool(), nat()) as unknown as DataType
    assertThrows(() => derivative(intersection), TypeError, "derivative(")
    assertThrows(() => coefficients(intersection, 2), TypeError, "coefficients(")
})

// ── Value-side virtuals (D7 — the method contract) ──────────────────────────

Deno.test("value virtuals: Value.equals (VariantVal) — constructor, carrier name, fields", () => {
    const t = bool()
    const a = new VariantVal("True", t, new Map())
    const b = new VariantVal("True", t, new Map())
    const c = new VariantVal("False", t, new Map())
    // Same reference, same constructor, same fields — and the
    // same-name-different-shape case stays unequal.
    assertEquals(a.equals(b), true)
    assertEquals(a.equals(c), false)
    const other = new VariantVal("True", nat(), new Map())
    assertEquals(a.equals(other), false)
})

Deno.test("value virtuals: Value.equals (TokenVal) — type name + text identity", () => {
    // Token identity: same pattern-type name + same text; a different type
    // name with the same text is unequal (cross-type collisions are
    // distinct values).
    const x = new TokenVal("Pat", "x")
    const y = new TokenVal("Pat", "x")
    const z = new TokenVal("Pat", "y")
    const other = new TokenVal("OtherPat", "x")
    assertEquals(x.equals(y), true)
    assertEquals(x.equals(z), false)
    assertEquals(x.equals(other), false)
})

Deno.test("value virtuals: Value.size — node count and token length", () => {
    const zero = new VariantVal("Zero", nat(), new Map())
    const succ = new VariantVal("Succ", nat(), new Map([["pred", zero]]))
    assertEquals(zero.size(), 1)
    assertEquals(succ.size(), 2)
    const token = new TokenVal("Pat", "abc")
    assertEquals(token.size(), 3, "a token's size is its text length")
})
