/**
 * Surface grammar tests — the layout rules (`surface-grammar.md` §7) and the
 * declaration/expression productions (§3, §4.1, §5.1).
 *
 * These are the *structural* tests. The pipeline's semantic behaviour is in
 * `surface_elaborate.test.ts`.
 */

import { assertEquals } from "@std/assert"
import {
    type CaseArm,
    type DataDecl,
    type FoldDecl,
    type MapDecl,
    SurfaceParse,
    type VariantDecl,
} from "../src/index.ts"

/** Parse a program, failing the test when it does not parse. */
function parse(source: string) {
    const program = new SurfaceParse().parseProgram(source)
    if (program === undefined) throw new Error(`did not parse:\n${source}`)
    return program
}

/** Whether a program parses. */
function parses(source: string): boolean {
    return new SurfaceParse().parseProgram(source) !== undefined
}

/** The single `data` declaration of a program. */
function dataOf(source: string): DataDecl {
    const [decl] = parse(source).declarations
    assertEquals(decl?.kind, "data")
    return decl as DataDecl
}

/** A declaration's variant items. */
function variantsOf(decl: DataDecl): VariantDecl[] {
    return decl.items.filter((i): i is VariantDecl => i.kind === "variantDecl")
}

/** A declaration's fold item. */
function foldOf(decl: DataDecl): FoldDecl {
    const [fold] = decl.items.filter((i): i is FoldDecl => i.kind === "foldDecl")
    if (fold === undefined) throw new Error("no fold declaration")
    return fold
}

// ── Layout: L1 exactness (§7) ────────────────────────────────────────────────

Deno.test("Layout L1: a body at the declared column parses", () => {
    assertEquals(parses("data Stack\n    Empty\n"), true)
})

Deno.test("Layout L1: a body one space short is rejected", () => {
    assertEquals(parses("data Stack\n   Empty\n"), false)
})

Deno.test("Layout L1: a body one space long is rejected", () => {
    assertEquals(parses("data Stack\n     Empty\n"), false)
})

Deno.test("Layout L1: a tab-indented body is rejected", () => {
    // The indent unit is four spaces, not a tab — L1 pins the unit.
    assertEquals(parses("data Stack\n\tEmpty\n"), false)
})

Deno.test("Whitespace: a tab is not whitespace between tokens", () => {
    // Spaces only, so a file cannot mix the two. A tab would make the column a
    // matter of the reader's tab width, which L1's exact indentation cannot
    // survive.
    assertEquals(parses("data Stack\n    Push\tvalue: Any\n"), false)
})

Deno.test("Whitespace: a tab is not trailing whitespace on a line", () => {
    assertEquals(parses("data Stack\n    Empty\t\n"), false)
})

Deno.test("Whitespace: a tab on an otherwise blank line is rejected", () => {
    assertEquals(parses("data Stack\n\t\n    Empty\n"), false)
})

Deno.test("Whitespace: a tab inside a comment is accepted", () => {
    // A comment's content is free text (§2.4) — the ban is on code position.
    assertEquals(parses("data Stack\n    Empty\n/* a\tb */\n"), true)
})

Deno.test("Whitespace: a tab inside a trailing comment is accepted", () => {
    assertEquals(parses("data Stack\n    Empty            /* a\tb */\n"), true)
})

Deno.test("Comments: a trailing comment may follow code or abut it", () => {
    // `surface-syntax.md` §1.4's result annotation, whose own example is
    // `Color Red toHex            /* "#FF0000" */`.
    assertEquals(parses(`data Color\n    Red            /* "#FF0000" */\n`), true)
    assertEquals(parses("data Stack\n    Empty/* note */\n"), true)
})

Deno.test("Whitespace: a tab inside a line comment is accepted", () => {
    assertEquals(parses("data Stack\n    Empty /* a\tb */\n"), true)
})

Deno.test("Layout L1: an unindented body is rejected", () => {
    assertEquals(parses("data Stack\nEmpty\n"), false)
})

Deno.test("Layout L1: a declaration cannot itself be indented", () => {
    // Declarations are top-level (§4) — the top level is column 0.
    assertEquals(parses("    data Stack\n        Empty\n"), false)
})

Deno.test("Layout L2: CRLF line endings are accepted", () => {
    assertEquals(parses("data Stack\r\n    Empty\r\n"), true)
})

Deno.test("Layout L2: a missing trailing newline is rejected", () => {
    assertEquals(parses("data Stack\n    Empty"), false)
})

Deno.test("Layout L2: blank lines between body items are consumed", () => {
    const decl = dataOf("data Stack\n    Empty\n\n    Push value: Any rest: Family\n")
    assertEquals(variantsOf(decl).map((v) => v.name), ["Empty", "Push"])
})

Deno.test("Layout L2: comment-only lines between body items are consumed", () => {
    const decl = dataOf("data Stack\n    Empty\n/* a comment */\n    Push value: Any\n")
    assertEquals(variantsOf(decl).map((v) => v.name), ["Empty", "Push"])
})

Deno.test("Comments: nested block comments are balanced by counting", () => {
    assertEquals(parses("data Stack\n    Empty\n/* a /* b */ c */\n"), true)
})

Deno.test("Comments: an unterminated comment is rejected", () => {
    assertEquals(parses("data Stack\n    Empty\n/* a\n"), false)
})

// ── `data` declarations (§4.1) ───────────────────────────────────────────────

Deno.test("dataDecl: a bare declaration with no variants has an empty body", () => {
    // `dataBodyItem+` requires at least one item, so this is a rejection.
    assertEquals(parses("data Stack\n"), false)
})

Deno.test("dataDecl: the head is a PascalCase name", () => {
    assertEquals(dataOf("data Stack\n    Empty\n").name, "Stack")
})

Deno.test("dataDecl: a camelCase declaration name is rejected", () => {
    assertEquals(parses("data stack\n    Empty\n"), false)
})

Deno.test("variantDecl: a zero-field variant", () => {
    const [variant] = variantsOf(dataOf("data Stack\n    Empty\n"))
    assertEquals(variant?.name, "Empty")
    assertEquals(variant?.fields.length, 0)
})

Deno.test("variantDecl: fields are recorded positionally in declaration order", () => {
    const decl = dataOf("data Stack\n    Push value: Any rest: Family\n")
    const [variant] = variantsOf(decl)
    assertEquals(variant?.fields.map((f) => f.name), ["value", "rest"])
    assertEquals(variant?.fields[0]?.type, { kind: "atom", name: "Any" })
    assertEquals(variant?.fields[1]?.type, { kind: "atom", name: "Family" })
})

Deno.test("variantDecl: a field type may not be a function type (§3.8)", () => {
    // `atomType` is the whole type grammar, so there is no `->` production for a
    // field type to use. A function value is only an operation reference
    // (§3.6.1), so a function *type* would describe a value no surface form can
    // build — the grammar does not admit one in the first place.
    assertEquals(parses("data Box\n    Wrap f: Any -> Any\n"), false)
})

Deno.test("variantDecl: a lowercase type name is rejected (§3.8)", () => {
    // There are no type variables, permanently — `a` is not a type.
    assertEquals(parses("data Box\n    Wrap a: a\n"), false)
})

Deno.test("dataDecl: the optional `<: Parent` clause parses", () => {
    const decl = dataOf("data Stack <: List\n    Empty\n")
    assertEquals(decl.parent, "List")
})

// ── `fold` declarations (§5.1) ───────────────────────────────────────────────

const STACK = `data Stack
    Empty
    Push value: Any rest: Family
    fold size <in: Stack, out: Any>
        Empty -> nil
        Push _ rest -> rest
`

Deno.test("foldDecl: the name, spec, and arms parse", () => {
    const fold = foldOf(dataOf(STACK))
    assertEquals(fold.name, "size")
    assertEquals(fold.arms.length, 2)
    assertEquals(fold.arms.map((a: CaseArm) => a.head.variant), ["Empty", "Push"])
})

Deno.test("foldDecl: the spec's `in` and `out` carry types, not expressions", () => {
    const fold = foldOf(dataOf(STACK))
    const inEntry = fold.spec?.entries.find((e) => e.key === "in")
    const outEntry = fold.spec?.entries.find((e) => e.key === "out")
    assertEquals(inEntry, { key: "in", kind: "type", type: { kind: "atom", name: "Stack" } })
    assertEquals(outEntry, { key: "out", kind: "type", type: { kind: "atom", name: "Any" } })
})

Deno.test("foldDecl: a bare flag spec entry parses", () => {
    const fold = foldOf(dataOf(`data Box
    Wrap x: Any
    fold f <para>
        Wrap x -> x
`))
    assertEquals(fold.spec?.entries, [{ key: "para", kind: "flag" }])
})

Deno.test("foldDecl: an `aux` spec entry carries a `#name` reference", () => {
    const fold = foldOf(dataOf(`data Box
    Wrap x: Any
    fold f <aux: #other>
        Wrap x -> x
`))
    assertEquals(fold.spec?.entries, [{ key: "aux", kind: "aux", name: "other" }])
})

Deno.test("foldDecl: a typed spec entry has exactly one derivation", () => {
    // The value's shape follows the key (§3.7's table), so `in: Box` has one
    // production to match. A key-blind alternation gave it two — `Box` is a
    // declared-type name *and* a variant reference — which doubled every forest
    // that declared a spec while yielding the same AST.
    const { forest } = new SurfaceParse().parseToTree(`data Box
    Wrap x: Box
    fold m <in: Box, out: Box>
        Wrap x -> x
`)
    assertEquals(forest.size, 1)
})

Deno.test("foldDecl: a non-type `in:` value is a parse failure, never an expression", () => {
    // `in` carries a type and nothing else. Before the value production was
    // key-driven, `(Any -> Any)` fell through to the expression alternative and
    // was silently accepted as a type entry — the hole that let a function type
    // reach a spec at all.
    assertEquals(
        parses("data Box\n    Wrap x: Box\n    fold m <in: 5>\n        Wrap x -> x\n"),
        false,
    )
})

Deno.test("foldDecl: every `properties:` law spelling is a parse failure (§12.35)", () => {
    // This pins a *known gap*, not a desired behaviour. `properties` carries a
    // `recordLiteral` (§3.6) and no such production exists, so the corpus's law
    // examples cannot be written. The test exists so the gap cannot close — or
    // change shape — silently: closing #122 must flip these assertions.
    const law = (value: string) =>
        parses(
            `data Box\n    Wrap x: Box\n    fold m <out: Box, properties: ${value}>\n        Wrap x -> x\n`,
        )
    // The corpus's canonical comma-separated flag list.
    assertEquals(law("(commutative, associative)"), false)
    // A relational law naming a declared operation.
    assertEquals(law("(distributive: #add)"), false)
    // A law carrying a value term.
    assertEquals(law("(identity: (Num N: 0))"), false)
    // The empty law set.
    assertEquals(law("()"), false)
    // And the one form that *does* parse is not a flag list: it is a paren over
    // an ordinary expression, which is exactly the conflation #122 must fix.
    const fold = foldOf(dataOf(`data Box
    Wrap x: Box
    fold m <out: Box, properties: (commutative)>
        Wrap x -> x
`))
    assertEquals(
        fold.spec?.entries.find((e) => e.key === "properties"),
        {
            key: "properties",
            kind: "expr",
            value: { kind: "paren", inner: { kind: "opRef", name: "commutative" } },
        },
    )
})

Deno.test("foldDecl: arms sit at column 8, not 4 or 12", () => {
    const at = (column: number) =>
        parses(
            `data Stack\n    Empty\n    fold f\n${" ".repeat(column)}Empty -> nil\n`,
        )
    assertEquals(at(8), true)
    assertEquals(at(4), false)
    assertEquals(at(12), false)
})

Deno.test("foldDecl: an arm head's wildcard binding is recorded", () => {
    const fold = foldOf(dataOf(STACK))
    const push = fold.arms.find((a) => a.head.variant === "Push")
    assertEquals(push?.head.bindings, ["_", "rest"])
})

Deno.test("foldDecl: a wildcard arm head is recorded without a variant", () => {
    const fold = foldOf(dataOf(`data Stack
    Empty
    fold f
        Empty -> nil
        _ -> nil
`))
    assertEquals(fold.arms[1]?.head.variant, undefined)
})

Deno.test("foldDecl: an indented (column-12) arm body parses", () => {
    const fold = foldOf(dataOf(`data Stack
    Empty
    fold f
        Empty ->
            nil
`))
    assertEquals(fold.arms.length, 1)
})

Deno.test("foldDecl: a contract clause parses with its bindings and body", () => {
    const fold = foldOf(dataOf(`data Stack
    Empty
    fold size <out: Any>
        ensures: self old result | result
        Empty -> nil
`))
    assertEquals(fold.contractClauses.length, 1)
    assertEquals(fold.contractClauses[0]?.kind, "ensures")
    assertEquals(fold.contractClauses[0]?.bindings, ["self", "old", "result"])
})

Deno.test("foldDecl: a contract clause body may be indented at column 12", () => {
    const fold = foldOf(dataOf(`data Stack
    Empty
    fold size <out: Any>
        ensures: self old result |
            result
        Empty -> nil
`))
    assertEquals(fold.contractClauses.length, 1)
    assertEquals(fold.contractClauses[0]?.bindings, ["self", "old", "result"])
})

// ── Expressions (§3) ────────────────────────────────────────────────────────

/** Parse an expression by wrapping it as a fold arm body. */
function exprOf(source: string) {
    const fold = foldOf(dataOf(`data Stack
    Empty
    fold f
        Empty -> ${source}
`))
    return fold.arms[0]?.body
}

Deno.test("expr: a literal is a literal", () => {
    assertEquals(exprOf("42"), { kind: "lit", text: "42" })
})

Deno.test("expr: a bare camelCase name is an operation reference", () => {
    assertEquals(exprOf("double"), { kind: "opRef", name: "double" })
})

Deno.test("expr: a bare PascalCase name is a variant reference", () => {
    assertEquals(exprOf("Empty"), { kind: "variantRef", name: "Empty" })
})

Deno.test("expr: a qualified variant reference records the qualifier", () => {
    assertEquals(exprOf("Stack Empty"), {
        kind: "variantRef",
        qualifier: "Stack",
        name: "Empty",
    })
})

Deno.test("expr: a construction records its named fields in order", () => {
    assertEquals(exprOf("Push value: nil rest: Empty"), {
        kind: "construction",
        variant: "Push",
        fields: [
            { key: "value", value: { kind: "lit", text: "nil" } },
            { key: "rest", value: { kind: "variantRef", name: "Empty" } },
        ],
    })
})

Deno.test("expr: a two-field construction has exactly one derivation", () => {
    // §3.3's greedy collection: every `key: value` pair after a construction
    // head belongs to that construction. Letting a field's value absorb the next
    // pair gives the input a second reading (`value: (nil rest: Empty)`), and the
    // two readings are structurally distinct objects — they do not collapse in
    // the forest, so a `Set` of one is the only proof of an unambiguous parse.
    const { forest } = new SurfaceParse().parseToTree(`data Stack
    Empty
    Push value: Any rest: Family
    fold f
        Empty -> Push value: nil rest: Empty
`)
    assertEquals(forest.size, 1)
})

Deno.test("expr: a nested construction must be parenthesized", () => {
    // The corpus always writes one this way:
    // `Cons head: 1 rest: (Cons head: 2 rest: Nil)`.
    const expr = exprOf("Push value: 1 rest: (Push value: 2 rest: Empty)")
    assertEquals(expr?.kind, "construction")
    assertEquals(expr?.kind === "construction" ? expr.fields.length : 0, 2)
})

Deno.test("expr: a qualified construction records the qualifier", () => {
    const expr = exprOf("Stack Push value: nil")
    assertEquals(expr, {
        kind: "construction",
        qualifier: "Stack",
        variant: "Push",
        fields: [{ key: "value", value: { kind: "lit", text: "nil" } }],
    })
})

Deno.test("expr: binary calls are one flat, left-associative level (§3.1)", () => {
    // `1 + 2 * 3` parses as `(1 + 2) * 3` — there is no precedence ladder.
    assertEquals(exprOf("1 + 2 * 3"), {
        kind: "binop",
        op: "*",
        lhs: {
            kind: "binop",
            op: "+",
            lhs: { kind: "lit", text: "1" },
            rhs: { kind: "lit", text: "2" },
        },
        rhs: { kind: "lit", text: "3" },
    })
})

Deno.test("expr: parentheses re-open the chain (§3.3)", () => {
    assertEquals(exprOf("1 * (2 + 3)"), {
        kind: "binop",
        op: "*",
        lhs: { kind: "lit", text: "1" },
        rhs: {
            kind: "paren",
            inner: {
                kind: "binop",
                op: "+",
                lhs: { kind: "lit", text: "2" },
                rhs: { kind: "lit", text: "3" },
            },
        },
    })
})

Deno.test("expr: a keyword send records a key/arg part", () => {
    assertEquals(exprOf("rest size: nil"), {
        kind: "call",
        receiver: { kind: "opRef", name: "rest" },
        parts: [{ key: "size", value: { kind: "lit", text: "nil" } }],
        messages: [],
    })
})

Deno.test("expr: a unary postfix send records messages", () => {
    assertEquals(exprOf("Empty not"), {
        kind: "call",
        receiver: { kind: "variantRef", name: "Empty" },
        parts: [],
        messages: ["not"],
    })
})

Deno.test("expr: `self` is a reference, not an operation", () => {
    assertEquals(exprOf("self"), { kind: "ref", name: "self" })
})

Deno.test("expr: `aux name` records the reference form", () => {
    assertEquals(exprOf("aux depth"), { kind: "ref", name: "aux depth" })
})

// ── Program shape (§4) ──────────────────────────────────────────────────────

Deno.test("program: multiple declarations parse in order", () => {
    const program = parse(`data A
    X
data B
    Y
`)
    assertEquals(program.declarations.map((d) => d.kind), ["data", "data"])
    assertEquals(program.declarations.map((d) => (d as DataDecl).name), ["A", "B"])
})

// ── `map` declarations (§5.3) ───────────────────────────────────────────────

/** A declaration's `map` item. */
function mapOf(decl: DataDecl): MapDecl {
    const [map] = decl.items.filter((i): i is MapDecl => i.kind === "mapDecl")
    if (map === undefined) throw new Error("no map declaration")
    return map
}

Deno.test("mapDecl: the body is FIELD-keyed, not variant-keyed (§5.3)", () => {
    // A map names fields and binds each transform's own parameter; it does not
    // name variants. That is what distinguishes it from a fold — the recursion
    // through `Family` fields is automatic, and only a map is eligible for
    // pipeline fusion.
    const map = mapOf(dataOf(`data Box
    Nil
    Cons head: Any rest: Family
    map double <out: Family>
        head x -> (x + 1)
`))
    assertEquals(map.name, "double")
    assertEquals(map.transforms.map((t) => t.field), ["head"])
    assertEquals(map.transforms[0]?.param, "x")
})

Deno.test("mapDecl: several transforms are recorded in source order", () => {
    const map = mapOf(dataOf(`data Pair
    MakePair first: Any second: Any
    map widen <out: Family>
        first x -> x
        second y -> y
`))
    assertEquals(map.transforms.map((t) => t.field), ["first", "second"])
    assertEquals(map.transforms.map((t) => t.param), ["x", "y"])
})

Deno.test("mapDecl: the spec carries the result type", () => {
    const map = mapOf(dataOf(`data Box
    Nil
    map double <out: Family>
        value x -> x
`))
    assertEquals(
        map.spec?.entries.find((e) => e.key === "out"),
        { key: "out", kind: "type", type: { kind: "atom", name: "Family" } },
    )
})

Deno.test("mapDecl: a transform takes no lambda form", () => {
    // `head x -> (x + 1)` binds the field's current value to `x` — the arm shape,
    // so a transform needs no anonymous binder.
    const map = mapOf(dataOf(`data Box
    Nil
    map double <out: Family>
        head x -> (x + 1)
`))
    assertEquals(map.transforms[0]?.body.kind, "paren")
})
