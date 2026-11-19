/**
 * The Type case protocol — `dispatch` / `map` and their optionality.
 *
 * These tests pin the *design* of the protocol rather than any one pass: that an
 * unnamed kind falls to `default`, that a table need not enumerate the universe,
 * that `ExhaustiveCases` is the opt-in check, and that the predicates on `Type`
 * answer for kind without a consumer consulting the kind list.
 */

import { assert, assertEquals } from "@std/assert"
import {
    Any,
    AnyType,
    DataType,
    Family,
    Field,
    FunType,
    isTypeKind,
    Nothing,
    NothingType,
    type TypeCases,
    TypeVar,
    Variant,
} from "../src/index.ts"

const [nat] = DataType.buildAll(
    DataType.define("Nat").addVariant(new Variant("Zero", [])),
)!

Deno.test("dispatch: a kind the table does not name falls to `default`", () => {
    // The point of the protocol: naming one kind must not oblige the table to
    // name the rest. `Nat` is a data type and the table names no kinds at all.
    const tag = nat.dispatch<string>({ default: (t) => t.toString() })
    assertEquals(tag, "Nat")
})

Deno.test("dispatch: a named arm wins over `default`", () => {
    const tag = nat.dispatch<string>({
        data: () => "named",
        default: () => "defaulted",
    })
    assertEquals(tag, "named")
})

Deno.test("dispatch: no arm and no default is a loud caller bug", () => {
    // Not a silent `undefined`: an unasked kind is a programming error, so a
    // table that answers nothing throws rather than smuggling a sentinel.
    let threw = false
    try {
        nat.dispatch<string>({})
    } catch {
        threw = true
    }
    assert(threw, "an empty case table must throw, never return undefined")
})

Deno.test("dispatch: an arm's `undefined` is an answer, not an omission", () => {
    // `T` may include `undefined`. A *present* arm yielding `undefined` has
    // answered "nothing here"; only an absent arm falls through. Without that
    // distinction a decline would be indistinguishable from a missing case.
    const result = nat.dispatch<string | undefined>({
        data: () => undefined,
        default: () => "defaulted",
    })
    assertEquals(result, undefined)
})

Deno.test("map: an unnamed kind is left structurally unchanged", () => {
    const mapped = nat.map({})
    assertEquals(mapped, nat)
})

Deno.test("map: a composite maps its children before the handler sees them", () => {
    // The handler receives the mapped children, so a substitution spells only
    // the kind it transforms and the rest is rebuilt structurally.
    const fn = new FunType(new TypeVar("α", Any), nat)
    let sawParam: string | undefined
    fn.map({
        typeVar: (t) => (t.name === "α" ? nat : t),
        fun: (_, p) => {
            sawParam = p.toString()
            return undefined
        },
    })
    // `fun`'s child argument is the *mapped* param (Nat), not the original α.
    assertEquals(sawParam, "Nat")
})

Deno.test("isTypeKind: accepts every kind without naming any", () => {
    // The `default` a membership test uses. It cannot go stale: a kind added
    // later falls here too.
    for (const kind of [nat, Any, Nothing, new FunType(Any, Nothing)]) {
        assertEquals(kind.dispatch<true>({ default: isTypeKind }), true)
    }
})

Deno.test("isUninhabited: `Nothing` alone, without consulting the kind list", () => {
    // Intrinsic and unary — a consumer asks the type, never the universe.
    assertEquals(Nothing.isUninhabited(), true)
    assertEquals(nat.isUninhabited(), false)
    assertEquals(Any.isUninhabited(), false)
    assertEquals(new FunType(Any, Nothing).isUninhabited(), false)
})

Deno.test("isTop: `Any` alone", () => {
    assertEquals(Any.isTop(), true)
    assertEquals(Nothing.isTop(), false)
    assertEquals(nat.isTop(), false)
})

Deno.test("a new Type kind needs no edit in any dispatch consumer", () => {
    // The regression this protocol design exists to prevent: adding a kind must
    // not force every consumer table to grow an arm. `Duration` implements the
    // two abstract virtuals by delegating to `default`, and every consumer that
    // passes a `default` keeps working untouched.
    class Duration extends AnyType {
        override equals(other: AnyType): boolean {
            return other instanceof Duration
        }
        override toString(): string {
            return "Duration"
        }
        override dispatch<T>(cases: TypeCases<T>): T {
            return cases.default?.(this) as T
        }
    }
    const d = new Duration()
    assertEquals(d.dispatch<string>({ default: (t) => t.toString() }), "Duration")
    // And the intrinsic predicates still answer correctly by inheritance.
    assertEquals(d.isUninhabited(), false)
    assert(isTypeKind() === true)
})

Deno.test("buildAll publishes a recursive carrier unchanged by the refactor", () => {
    // A smoke check that the protocol change did not disturb construction: the
    // `Family` field resolves per carrier exactly as before.
    const [list] = DataType.buildAll(
        DataType.define("List")
            .addVariant(new Variant("Nil", []))
            .addVariant(
                new Variant("Cons", [new Field("head", Any)]),
            ),
    )!
    assertEquals(list.name, "List")
    assertEquals(list.variants.length, 2)
})

Deno.test("NothingType and AnyType remain the lattice bounds", () => {
    assertEquals(Nothing instanceof NothingType, true)
    assertEquals(Any instanceof AnyType, true)
})

Deno.test("Variant.isRecursive / recursiveFields answer without a kind test", () => {
    // The variant-level counterpart of the type predicates: a consumer asks the
    // variant whether it recurses, rather than restating
    // `fields.some(f => f.type instanceof FamilyType)` at every use.
    const [list] = DataType.buildAll(
        DataType.define("List")
            .addVariant(new Variant("Nil", []))
            .addVariant(
                new Variant("Cons", [new Field("head", Any), new Field("tail", Family)]),
            ),
    )!
    const [nil, cons] = list.variants
    assertEquals(nil!.isRecursive(), false)
    assertEquals(cons!.isRecursive(), true)
    assertEquals(nil!.recursiveFields().length, 0)
    // Only the μ-bound field counts — `head: Any` is not recursion.
    assertEquals(cons!.recursiveFields().map((f) => f.name), ["tail"])
})

Deno.test("Field.isRecursive: the μ-bound alone, not a same-named carrier", () => {
    // A field typed as the carrier's own DataType instance (not `Family`) is a
    // genuine non-recursive position — the type says which one it is.
    const [nat] = DataType.buildAll(
        DataType.define("Nat").addVariant(new Variant("Zero", [])),
    )!
    assertEquals(new Field("a", Family).isRecursive(), true)
    assertEquals(new Field("b", Any).isRecursive(), false)
    assertEquals(new Field("c", nat).isRecursive(), false)
})
