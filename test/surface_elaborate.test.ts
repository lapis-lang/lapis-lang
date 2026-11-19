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
    // The #97 acceptance criterion, proven here first: the parsed-and-elaborated
    // declaration and the hand-built fixture must agree structurally.
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

Deno.test("resolve: `Family` cannot name a declaration (#101)", () => {
    assertEquals(reasonsOf("data Family\n    Empty\n"), ["reserved-declaration-name"])
})

Deno.test("resolve: `Self` cannot name a declaration (#101)", () => {
    assertEquals(reasonsOf("data Self\n    Empty\n"), ["reserved-declaration-name"])
})

Deno.test("resolve: a duplicate declaration is reported", () => {
    assertEquals(reasonsOf("data A\n    X\ndata A\n    Y\n"), ["duplicate-declaration"])
})

Deno.test("resolve: a duplicate variant within a type is reported", () => {
    assertEquals(reasonsOf("data A\n    X\n    X\n"), ["duplicate-variant"])
})

Deno.test("resolve: an undeclared type name is rejected, never minted (#116)", () => {
    // The surface has no type variables, so a typo has no legitimate reading.
    assertEquals(reasonsOf("data Box\n    Wrap x: Natt\n"), ["unknown-type"])
})

Deno.test("resolve: a function-typed FIELD is not even parseable", () => {
    // No surface form inhabits one — a function value is *only* an operation
    // reference (`surface-grammar.md` §3.6.1). A type is `atomType` and nothing
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
    // The §12.13 class: a user type taking a language-defined name must resolve
    // to *its own* declaration. `Token` is the one core type a surface name could
    // otherwise shadow, so declaring it is the sharp case.
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

Deno.test("resolve: a wildcard arm is reported until comb inheritance lands (#86)", () => {
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
