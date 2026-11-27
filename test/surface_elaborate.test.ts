/**
 * Surface elaboration tests — the full pipeline: source → AST → resolved →
 * elaborated → type-checked and evaluated by the *core's* one-pass grammar.
 *
 * The load-bearing assertion is the end-to-end one: a surface program that the
 * core accepts, type-checks, and evaluates. Everything between is scaffolding
 * for that.
 */

import { assert, assertEquals } from "@std/assert"
import {
    type DataDecl,
    DataType,
    elaborateProgram,
    Field,
    formatResolutionErrors,
    FunType,
    LCEval,
    LCTypeCheck,
    resolveProgram,
    SurfaceParse,
    type Type,
    TypeEnv,
    Variant,
} from "../src/index.ts"
import { Any, Family, ValueEnv } from "../src/index.ts"

/** Run the pipeline over a source string, throwing on any stage's failure. */
function pipeline(source: string) {
    const program = new SurfaceParse().parseProgram(source)
    if (program === undefined) throw new Error(`did not parse:\n${source}`)
    const resolved = resolveProgram(program)
    if (!resolved.ok) throw new Error(formatResolutionErrors(resolved.errors))
    return { program, ...resolved, ...elaborateProgram(program) }
}

/** Type-check a core term against the elaborated registry. */
function typesOf(source: string, registry: Parameters<LCTypeCheck["setRegistry"]>[0]) {
    return [...new LCTypeCheck().setRegistry(registry).parseWith(source, new TypeEnv())]
}

/** Evaluate a core term against the elaborated registry. */
function evalOf(source: string, registry: Parameters<LCEval["setRegistry"]>[0]) {
    return [...new LCEval().setRegistry(registry).parseWith(source, new ValueEnv())]
}

const STACK = `data Stack
    Empty
    Push value: Any rest: Family
`

// ── The registry ─────────────────────────────────────────────────────────────

Deno.test("elaborate: a `data` declaration produces one registered type", () => {
    const { types, registry } = pipeline(STACK)
    assertEquals(types.length, 1)
    assertEquals(types[0]?.name, "Stack")
    assertEquals(registry.lookup("Stack"), types[0])
})

Deno.test("elaborate: variants and their fields survive elaboration", () => {
    const { types } = pipeline(STACK)
    const stack = types[0]!
    assertEquals(stack.allVariants().map((v) => v.name), ["Empty", "Push"])
    assertEquals(stack.findVariant("Push")?.fields.map((f) => f.name), ["value", "rest"])
})

Deno.test("elaborate: `Family` becomes the μ-bound, not a named type", () => {
    const { types } = pipeline(STACK)
    assertEquals(types[0]?.findVariant("Push")?.fields[1]?.type, Family)
})

Deno.test("elaborate: the elaborated type equals its DataTypeBuilder equivalent", () => {
    // The parsed-and-elaborated declaration and the hand-built fixture must agree
    // structurally, which is what proves the surface pipeline produces the same
    // type the builder API does.
    const { types } = pipeline(STACK)
    const built = DataType.define("Stack")
        .addVariant(
            new Variant("Empty", []),
            new Variant("Push", [new Field("value", Any), new Field("rest", Family)]),
        )
        .build()

    const elaborateShape = types[0]!
    assertEquals(elaborateShape.name, built.name)
    assertEquals(
        elaborateShape.allVariants().map((v) => v.name),
        built.allVariants().map((v) => v.name),
    )
    for (const variant of built.allVariants()) {
        const mine = elaborateShape.findVariant(variant.name)!
        assertEquals(mine.fields.map((f) => f.name), variant.fields.map((f) => f.name))
        assertEquals(
            mine.fields.map((f) => f.type.toString()),
            variant.fields.map((f) => f.type.toString()),
        )
    }
})

// ── Core interoperation (§2.3's decision) ────────────────────────────────────

Deno.test("elaborate: the elaborated registry type-checks a construction", () => {
    const { registry } = pipeline(STACK)
    assert(typesOf("Empty()", registry).length === 1)
    assert(typesOf("Push(Empty(), Empty())", registry).length === 1)
})

Deno.test("elaborate: the elaborated registry rejects a wrong arity", () => {
    const { registry } = pipeline(STACK)
    assertEquals(typesOf("Push(Empty())", registry).length, 0)
})

// ── Fold elaboration (§3.1) ──────────────────────────────────────────────────

const STACK_TOP = `data Stack
    Empty
    Push value: Any rest: Family
    fold top <in: Stack, out: Stack>
        Empty -> Empty
        Push x rest -> rest
`

Deno.test("elaborate: a fold becomes an operation with the spec's types", () => {
    const { operations, types } = pipeline(STACK_TOP)
    assertEquals(operations.length, 1)
    const [op] = operations
    assertEquals(op?.name, "top")
    assertEquals(op?.paramTypes.length, 1)
    assertEquals(op?.paramTypes[0], types[0])
    assertEquals(op?.resultType, types[0])
})

Deno.test("elaborate: the fold's definition is core concrete syntax", () => {
    const { operations } = pipeline(STACK_TOP)
    // The core separates a handler's bindings with spaces and its handlers with
    // commas; a zero-field variant is a nullary construction.
    assertEquals(
        operations[0]?.definition,
        "\\e:Stack. fold [Stack] e { Empty() -> Empty(), Push(x rest) -> rest }",
    )
})

Deno.test("elaborate: the fold's definition type-checks in the core", () => {
    const { operations, registry } = pipeline(STACK_TOP)
    const forest = typesOf(operations[0]?.definition ?? "", registry)
    assertEquals(forest.length, 1)
    assertEquals(forest[0]?.toString(), "(Stack → Stack)")
})

Deno.test("elaborate: the fold evaluates through the core", () => {
    const { operations, registry } = pipeline(STACK_TOP)
    const def = operations[0]?.definition ?? ""
    const value = evalOf(`(${def}) Push(Empty(), Empty())`, registry)[0]
    assert(value !== undefined)
    assertEquals((value as { variantName?: string }).variantName, "Empty")
})

Deno.test("elaborate: a fold's arm bindings are positional in field order", () => {
    // `Fill x y` binds `x` to field `a` and `y` to field `b`, so returning `x`
    // must yield `a`'s value. The fixture distinguishes the fields: `Empty` and
    // `Push(…)` are different variants, so a swapped binding shows up as the
    // other value rather than as the same one.
    const { operations, registry } = pipeline(`data Box
    Empty
    Fill a: Any b: Any
    fold first <in: Box, out: Any>
        Empty -> Empty
        Fill x y -> x
`)
    const def = operations[0]?.definition ?? ""
    const value = evalOf(`(${def}) Fill(Empty(), Push(Empty(), Empty()))`, registry)[0]
    // An `EvalErrorValue` is a *value*: asserting only that the forest is
    // non-empty would pass on a failed evaluation.
    assert(value !== undefined)
    assertEquals((value as { variantName?: string }).variantName, "Empty")
})

Deno.test("elaborate: `Self` means the declaring type, not the μ-bound", () => {
    // `Self` in a spec is the declaring type — what makes `Num add <in: Self,
    // out: Self>` return its operand's type. `Family` is a *different*
    // reference: the μ-bound α, written in field position.
    const { operations, types } = pipeline(`data N
    Z
    fold id <in: Self, out: Self>
        Z -> Z
`)
    const op = operations[0]!
    assertEquals(op.paramTypes[0], types[0])
    assertEquals(op.resultType, types[0])
})

Deno.test("elaborate: `Family` in a field stays the μ-bound", () => {
    const { types } = pipeline(STACK)
    assertEquals(types[0]?.findVariant("Push")?.fields[1]?.type, Family)
})

Deno.test("elaborate: an operation's declared signature agrees with its definition", () => {
    // The `Ω` seal requires a definition to type as `paramTypes → resultType`.
    // A surface elaboration that produces both must therefore be self-consistent,
    // and only an assertion comparing them can catch a divergence — the
    // definition type-checking on its own says nothing about the declaration.
    for (
        const source of [
            STACK_TOP,
            `data N
    Z
    fold id <in: Self, out: Self>
        Z -> Z
`,
        ]
    ) {
        const { operations, registry } = pipeline(source)
        const op = operations[0]!
        const inferred = typesOf(op.definition, registry)
        assertEquals(inferred.length, 1)
        const expected = op.paramTypes.reduce<Type>(
            (acc, param) => new FunType(param, acc),
            op.resultType,
        )
        assertEquals(inferred[0]?.toString(), expected.toString())
    }
})

// ── Resolution failures ─────────────────────────────────────────────────────

/** The reasons resolution reports for a source string. */
function reasonsOf(source: string): string[] {
    const program = new SurfaceParse().parseProgram(source)
    if (program === undefined) return ["parse-failure"]
    return resolveProgram(program).errors.map((e) => e.reason)
}

Deno.test("resolve: `Family` cannot name a declaration", () => {
    assertEquals(reasonsOf("data Family\n    Empty\n"), ["reserved-declaration-name"])
})

Deno.test("resolve: `Self` cannot name a declaration", () => {
    assertEquals(reasonsOf("data Self\n    Empty\n"), ["reserved-declaration-name"])
})

Deno.test("resolve: a duplicate declaration is reported", () => {
    assertEquals(reasonsOf("data A\n    X\ndata A\n    Y\n"), ["duplicate-declaration"])
})

Deno.test("resolve: a duplicate variant within a type is reported", () => {
    assertEquals(reasonsOf("data A\n    X\n    X\n"), ["duplicate-variant"])
})

Deno.test("resolve: an undeclared type name is rejected, never minted", () => {
    // The surface has no type variables, so a typo has no legitimate reading.
    assertEquals(reasonsOf("data Box\n    Wrap x: Natt\n"), ["unknown-type"])
})

Deno.test("resolve: a function-typed FIELD is not even parseable", () => {
    // No surface form inhabits one — a function value is *only* an operation
    // reference (`grammar.ts`'s `primary`). A type is `atomType` and nothing
    // more (§3.8), so the `->` never reaches resolution: there is no function
    // type to reject, which is stronger than rejecting it later.
    assertEquals(
        reasonsOf("data Box\n    Wrap f: Any -> Any\n"),
        ["parse-failure"],
    )
})

Deno.test("resolve: a function-typed SPEC entry is not even parseable", () => {
    // A spec entry is a declared *signature*, and no operation takes a function
    // value: a map's transform is written as the transform itself (an arm body
    // bound to a field), not passed in. §3.8's `atomType` therefore has no
    // arrow, in this position either.
    assertEquals(
        reasonsOf(`data Box
    Wrap x: Any
    fold m <in: (Any -> Any), out: Any>
        Wrap x -> x
`),
        ["parse-failure"],
    )
})

Deno.test("resolve: `Token` is not a spellable surface type", () => {
    // `Token` belongs to Lapis Core alone — a pattern fold's handler binds it
    // under the fixed name `match`, and a program consumes that binding rather
    // than writing the type (`prelude.md` §2.1). An unknown name must be
    // rejected, and `Token` is not an exception.
    assertEquals(reasonsOf("data Box\n    Wrap x: Token\n"), ["unknown-type"])
})

Deno.test("elaborate: a declaration is never captured by a same-named core type", () => {
    // A user type taking a language-defined name must resolve to *its own*
    // declaration. `Token` is the one core type a surface name could otherwise
    // shadow, so declaring it is the sharp case.
    const { types } = pipeline(`data Token
    Wrap x: Any
data Uses
    Hold t: Token
`)
    const declared = types.find((t) => t.name === "Token")
    const uses = types.find((t) => t.name === "Uses")
    const field = uses?.allVariants()[0]?.fields[0]
    assert(declared !== undefined)
    assert(field !== undefined)
    assertEquals(field.type, declared)
})

Deno.test("elaborate: a fold over a user's `data Token` type-checks", () => {
    // End to end, because the name-capture defect only showed up here: the
    // elaborated text mentions `Token`, and the core resolves that to the user's
    // registration rather than to the core-owned `@Token`.
    const { operations, registry } = pipeline(`data Token
    Empty
    Wrap x: Any
    fold size <in: Token, out: Any>
        Empty -> Empty
        Wrap x -> x
`)
    const op = operations[0]!
    assert(!op.definition.includes("@Token"), "a user type must not elaborate to @Token")
    assertEquals(typesOf(op.definition, registry).map(String), ["(Token → Any)"])
})

Deno.test("resolve: a fold arm naming a non-existent variant is reported", () => {
    assertEquals(
        reasonsOf(`data A
    X
    fold f <out: Any>
        Y -> nil
`),
        ["unknown-variant"],
    )
})

Deno.test("resolve: an arm binding fewer names than the variant has fields is reported", () => {
    assertEquals(
        reasonsOf(`data A
    X a: Any b: Any
    fold f <out: Any>
        X only -> only
`),
        ["arity-mismatch"],
    )
})

Deno.test("resolve: a wildcard arm is reported until comb inheritance lands", () => {
    assertEquals(
        reasonsOf(`data A
    X
    fold f <out: Any>
        X -> nil
        _ -> nil
`),
        ["wildcard-arm"],
    )
})

Deno.test("resolve: a well-formed program reports nothing", () => {
    assertEquals(reasonsOf(STACK_TOP), [])
})

// ── Constructor position ───────────────────────────────────────────────
//
// A constructor is a `pascalIdent` in expression position, and it is the one
// naming position `unknown-type` cannot reach: a type name is checked at its
// annotation, but a construction names its variant inside a body. These are the
// cases that used to elaborate with `errors: []`.

/** A fold over a two-field type, so a construction can be spelled in the body. */
const withBody = (body: string) =>
    `data P
    P1
    P2 x: Any y: Any
    fold f <out: Any>
        P1 -> ${body}
`

Deno.test("resolve: a bare construction naming no declared variant is rejected", () => {
    assertEquals(
        reasonsOf(`data P
    P1
    fold f <out: Any>
        P1 -> TotallyUnknown
`),
        ["unknown-constructor"],
    )
})

Deno.test("resolve: a construction inside a field position is walked", () => {
    // The walk is recursive: `TotallyUnknown` is the *value* of a field here, not
    // the body itself. `P2` is the two-field variant, so only the inner name is
    // at fault.
    assertEquals(
        reasonsOf(`data P
    P1
    P2 x: Any y: Any
    fold f <out: Any>
        P1 -> (P2 x: TotallyUnknown y: P1)
`),
        ["unknown-constructor"],
    )
})

Deno.test("resolve: a bare construction declared by two unrelated types is ambiguous", () => {
    const errors = resolveProgram(
        new SurfaceParse().parseProgram(`data A
    Same
data B
    Same
    fold f <out: Any>
        Same -> (Same)
`)!,
    ).errors
    assertEquals(errors.map((e) => e.reason), ["ambiguous-constructor"])
    // The diagnostic must name *both* candidates, or it cannot tell the author
    // which qualification to write.
    assert(errors[0]?.message.includes("A"), errors[0]?.message)
    assert(errors[0]?.message.includes("B"), errors[0]?.message)
})

Deno.test("resolve: a qualifier naming no declaration is rejected", () => {
    assertEquals(
        reasonsOf(`data P
    P1
    fold f <out: Any>
        P1 -> (Ghost One)
`),
        ["bad-qualifier"],
    )
})

Deno.test("resolve: a qualifier naming a type that declares no such variant is rejected", () => {
    assertEquals(
        reasonsOf(`data A
    One
    fold f <out: Any>
        One -> (A Two)
`),
        ["bad-qualifier"],
    )
})

Deno.test("resolve: a construction may name its fields in any order", () => {
    // Field names bind by name, so the written order carries no meaning: the
    // caller names each slot, and a reordered construction is the same
    // constructor. Elaboration emits the declared order (asserted below, where a
    // transposition would be visible).
    assertEquals(reasonsOf(withBody("(P2 y: P1 x: P1)")), [])
})

Deno.test("elaborate: a reordered construction emits the declared field order", () => {
    // The fields have different types, so a transposition cannot hide: `A1` is an
    // `A` and `B1` is a `B`. Writing `y:` before `x:` must still emit `(A1(), B1())`
    // — declaration order — never `(B1(), A1())`.
    const { operations } = pipeline(`data A
    A1
data B
    B1
data P
    P2 x: A y: B
    fold f <out: Any>
        P2 a b -> (P2 y: B1 x: A1)
`)
    assertEquals(
        operations[0]?.definition,
        "\\e:P. fold [P] e { P2(a b) -> (P2(A1(), B1())) }",
    )
})

Deno.test("resolve: a construction with an undeclared field is rejected", () => {
    assertEquals(reasonsOf(withBody("(P2 bogus: P1 y: P1)")), ["selector-mismatch"])
})

Deno.test("resolve: a construction naming one field twice is rejected", () => {
    assertEquals(reasonsOf(withBody("(P2 x: P1 x: P1)")), ["selector-mismatch"])
})

Deno.test("resolve: a construction omitting a field is rejected", () => {
    assertEquals(reasonsOf(withBody("(P2 x: P1)")), ["selector-mismatch"])
})

Deno.test("resolve: an inherited variant is not ambiguous", () => {
    // A child re-declaring an inherited variant narrows it (comb inheritance), so
    // the two declarations are one constructor. The prelude's own
    // `IntList <: List` is this shape; flagging it would make the prelude
    // unelaboratable.
    const program = new SurfaceParse().parseProgram(`data List
    Nil
    Cons head: Any rest: Family
data IntList <: List
    Cons head: Any rest: Family
`)!
    const { table, errors } = resolveProgram(program)
    assertEquals(table.ambiguousVariants.size, 0)
    assertEquals([...table.variants.get("Cons") ?? []], ["List", "IntList"])
    assertEquals(errors.map((e) => e.reason), [])
})

Deno.test("resolve: an unrelated third declarer keeps an inherited name ambiguous", () => {
    // The ancestry skip must not become a blanket amnesty: `Other` has no lineage
    // relation to either, so bare `Cons` still names two constructors.
    const program = new SurfaceParse().parseProgram(`data List
    Nil
    Cons head: Any rest: Family
data IntList <: List
    Cons head: Any rest: Family
data Other
    Cons
`)!
    assertEquals([...resolveProgram(program).table.ambiguousVariants], ["Cons"])
})

Deno.test("resolve: a contract clause's body is walked", () => {
    // Clause bodies parse but are not otherwise resolved; a constructor in one
    // is still this pass's to resolve.
    assertEquals(
        reasonsOf(`data P
    P1
    fold f
        demands: guard | Ghost
        P1 -> P1
`),
        ["unknown-constructor"],
    )
})

Deno.test("resolve: a `map` transform's body is walked", () => {
    assertEquals(
        reasonsOf(`data P
    P2 x: Any y: Any
    map m
        x x -> Ghost
`),
        ["unknown-constructor"],
    )
})

Deno.test("resolve: a constructor in any expression position is walked", () => {
    // `binop`, `unary`, a call's receiver, a call's part, and parentheses — a
    // constructor can appear anywhere an expression can. Each body names one
    // undeclared constructor, so each yields exactly one diagnostic.
    for (
        const body of [
            "(Ghost add P1)",
            "Ghost negate",
            "Ghost add: P1",
            "((Ghost))",
        ]
    ) {
        assertEquals(reasonsOf(withBody(body)), ["unknown-constructor"], body)
    }
})

Deno.test("resolve: a well-formed construction still reports nothing", () => {
    // The no-false-positive half: a correctly qualified or unambiguous
    // construction, a reordered one, and an arm binding that happens to share a
    // variant's name.
    assertEquals(reasonsOf(withBody("(P2 x: P1 y: P1)")), [])
    assertEquals(reasonsOf(withBody("(P2 y: P1 x: P1)")), [])
    assertEquals(reasonsOf(withBody("P P2 y: P1 x: P1")), [])
    assertEquals(reasonsOf(withBody("P1")), [])
})

// ── Declaration independence ────────────────────────────────────────────────

Deno.test("elaborate: a type may refer to a type declared after it", () => {
    // The surface has no declaration ordering rule, so resolution is
    // whole-program and elaboration builds every declaration in one group.
    const { types } = pipeline(`data Uses
    Wrap inner: Later
data Later
    Done
`)
    assertEquals(types.map((t) => t.name), ["Uses", "Later"])
    assertEquals(types[0]?.findVariant("Wrap")?.fields[0]?.name, "inner")
})

// ── Elaboration has a verdict ───────────────────────────────────────────────
//
// The pipeline's contract is "elaborate, then the core checks"
// (`elaboration.md` §1.2). These tests assert the second half happens *inside*
// elaboration: an operation whose definition does not type as its declared
// signature is reported, and never enters `Ω`.

/** Run the pipeline and return the elaboration verdict — no throwing. */
function elaborateVerdictOf(source: string) {
    const program = new SurfaceParse().parseProgram(source)
    if (program === undefined) throw new Error(`did not parse:\n${source}`)
    return elaborateProgram(program)
}

Deno.test("elaborate: a fold whose `in:` disagrees with its definition is rejected", () => {
    // The signature comes from the spec (`in: B`) and the definition from the
    // arms plus the declaring type (`\e:Holder.`), so the two describe
    // different operations. The emitted text type-checks on its own — a
    // `Holder → Any` term is perfectly well typed — which is why only a verdict
    // that compares the definition against the *declared* signature catches it.
    const result = elaborateVerdictOf(`data N
    Z
data B
    T
data Holder
    H
    fold pick <in: B, out: B>
        H -> T
`)
    assertEquals(result.ok, false)
    assertEquals(result.errors.map((e) => e.reason), ["not-well-formed"])
    assertEquals(result.errors[0]?.operation, "pick")
    // The message names the disagreement, or the author cannot tell what to fix.
    assert(result.errors[0]?.message.includes("B"), result.errors[0]?.message)
    assert(result.errors[0]?.message.includes("Holder"), result.errors[0]?.message)
})

Deno.test("elaborate: a rejected operation never enters `Ω`", () => {
    // The property that matters: `ElaborationResult.operations` and the `Ω`
    // entry are the same judgement, so a caller cannot install what was
    // reported. A rejected operation is *absent*, not an unchecked entry.
    const result = elaborateVerdictOf(`data B
    T
data Holder
    H
    fold pick <in: B, out: B>
        H -> T
`)
    assertEquals(result.opRegistry.lookup("pick"), undefined)
    assertEquals(result.operations.length, 0)
    // The types are still published — the failure is per-operation.
    assertEquals(result.registry.lookup("Holder"), result.types.find((t) => t.name === "Holder"))
})

Deno.test("elaborate: a well-formed fold enters `Ω`", () => {
    const result = elaborateVerdictOf(STACK_TOP)
    assertEquals(result.ok, true)
    assertEquals(result.errors, [])
    const sealed = result.opRegistry.lookup("top")
    assert(sealed !== undefined)
    assertEquals(sealed.name, "top")
    assertEquals(sealed.definition, result.operations[0]?.definition)
})

Deno.test("elaborate: the verdict is per-operation, not per-program", () => {
    // One bad declaration must not make its siblings unusable: the good fold
    // elaborates and installs, the bad one is named in `errors`.
    const result = elaborateVerdictOf(`data B
    T
data Holder
    H
    fold good <in: Self, out: Self>
        H -> H
    fold bad <in: B, out: Any>
        H -> H
`)
    assertEquals(result.ok, false)
    assertEquals(result.errors.map((e) => e.operation), ["bad"])
    assertEquals(result.operations.map((o) => o.name), ["good"])
    assert(result.opRegistry.lookup("good") !== undefined)
    assertEquals(result.opRegistry.lookup("bad"), undefined)
})

Deno.test("elaborate: an operation the core cannot install is `not-well-formed`", () => {
    // A recursive fold's body names itself, which `Ω`'s acyclicity rule rejects
    // — an operation may only reference operations declared before it. The
    // failure surfaces against the operation rather than being emitted as text
    // that no consumer could install.
    const result = elaborateVerdictOf(`data Stack
    Empty
    Cons value: Any rest: Family
    fold size <in: Self, out: Any>
        Empty -> Empty
        Cons v r -> (r size)
`)
    assertEquals(result.ok, false)
    assertEquals(result.errors.map((e) => e.reason), ["not-well-formed"])
    assertEquals(result.errors[0]?.operation, "size")
})

// ── AST shape ───────────────────────────────────────────────────────────────

Deno.test("pipeline: the AST is what the passes consume, not the token tree", () => {
    const program = new SurfaceParse().parseProgram(STACK)!
    const decl = program.declarations[0] as DataDecl
    // One declaration, two variants — the AST sees each production exactly once,
    // unlike the `DerivationTree`, whose repeated productions nest.
    assertEquals(decl.items.filter((i) => i.kind === "variantDecl").length, 2)
})

Deno.test("pipeline: `parseToTree` still yields trees for diagnostics and unparsing", () => {
    const { trees } = new SurfaceParse().parseToTree(STACK)
    assert(trees.length >= 1)
    assertEquals(trees[0]?.source, STACK)
})
