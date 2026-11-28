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
    VariantVal,
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
    fold top <out: Stack>
        Empty -> Empty
        Push value rest -> rest
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
        "\\e:Stack. fold [Stack] e { Empty() -> Empty(), Push(value rest) -> rest }",
    )
})

Deno.test("elaborate: the fold's definition type-checks in the core", () => {
    const { operations, registry } = pipeline(STACK_TOP)
    const forest = typesOf(operations[0]?.definition ?? "", registry)
    assertEquals(forest.length, 1)
    assertEquals(forest[0]?.toString(), "(Stack → Stack)")
})

// ── A fold's `in:` is its second parameter ──────────────────────────────────
//
// The carrier is always the first parameter, so `in:` adds one and the
// definition is a lambda per declared parameter. The parameter's name comes from
// the machinery name read from a body — the curried lambda, never a handler
// binding, because the core's `E-Fold` supplies values for the variant's fields
// only.

const NAT_PICK = `data Nat
    Zero
    Succ pred: Family
    fold pick <in: Self, out: Self>
        Zero -> in
        Succ pred -> in
`

Deno.test("elaborate: `in:` adds a second parameter after the carrier", () => {
    const { operations, types } = pipeline(NAT_PICK)
    const op = operations[0]!
    assertEquals(op.paramTypes.length, 2)
    assertEquals(op.paramTypes[0], types[0])
    assertEquals(op.paramTypes[1], types[0])
})

Deno.test("elaborate: an `in:` parameter is a curried lambda, not a handler binding", () => {
    // The binding list holds the variant's fields only. The parameter appears in
    // the lambdas and in the bodies, never inside `Zero(…)` — a handler binding
    // for it would be a position `E-Fold` never fills. The emitted name is the
    // core-legal spelling of the surface keyword, which the core reserves.
    const { operations } = pipeline(NAT_PICK)
    assertEquals(
        operations[0]?.definition,
        "\\e:Nat. \\in_:Nat. fold [Nat] e { Zero() -> in_, Succ(pred) -> in_ }",
    )
})

Deno.test("elaborate: a fold with `in:` installs, types and evaluates", () => {
    // The load-bearing property: the two-parameter signature and the two-lambda
    // definition agree, so the operation enters `Ω` and runs. A one-lambda
    // emission would fail the verdict instead — `Nat → Nat` against the declared
    // `Nat → Nat → Nat`.
    const { operations, registry, opRegistry } = pipeline(NAT_PICK)
    assertEquals(operations.length, 1)
    assertEquals(opRegistry.lookup("pick")?.paramTypes.length, 2)

    const def = operations[0]!.definition
    const value = evalOf(`(${def}) Zero() Succ(Zero())`, registry)[0]
    assert(value !== undefined)
    assertEquals((value as { variantName?: string }).variantName, "Succ")
})

Deno.test("resolve: an arm may not bind more names than the variant has fields", () => {
    // The `in:` value is read from the body, so a head binding beyond the field
    // count names a slot the emitted handler does not have — and the emitter,
    // which keeps only the variant's fields, would drop it silently.
    assertEquals(
        reasonsOf(`data Box
    Empty
    Fill a: Any b: Any
    fold f <out: Any>
        Empty extra -> Empty
        Fill a b extra -> a
`),
        ["arity-mismatch", "arity-mismatch"],
    )
})

Deno.test("resolve: an arm head cannot bind the machinery's `in`", () => {
    // `in` is read from the body like `self`, and it is a keyword, so an arm
    // head cannot bind it at all — the declaration fails to parse.
    assertEquals(
        reasonsOf(`data Box
    Empty
    fold f <in: Any, out: Any>
        Empty in -> in
`),
        ["parse-failure"],
    )
})

Deno.test("resolve: `in` cannot name a variant field", () => {
    // With `in` a keyword it is un-nameable, so the collision between a field and
    // the fold's extra argument cannot arise.
    assertEquals(
        reasonsOf(`data Foo
    Bar in: Any
`),
        ["parse-failure"],
    )
})

Deno.test("elaborate: the emitted `in` binder is hygienic against the fields", () => {
    // A field may be named `in_` — an ordinary identifier — so the binder is
    // chosen to avoid colliding with it. A fixed name would shadow the field and
    // change what `in_` means between the head and the body.
    const { operations } = pipeline(`data P
    Z
    M in_: Any a: Any
    fold f <in: Self, out: Any>
        Z -> in
        M in_ a -> in_
`)
    assertEquals(
        operations[0]?.definition,
        "\\e:P. \\in__:P. fold [P] e { Z() -> in__, M(in_ a) -> in_ }",
    )
})

Deno.test("resolve: a fold declaring `in:` binds nothing extra in the head", () => {
    // The `in:` value is machinery-supplied, so an arm whose head names only the
    // fields is complete — `Empty` has no fields, so an empty head is correct.
    assertEquals(
        reasonsOf(`data Box
    Empty
    fold f <in: Any, out: Any>
        Empty -> Empty
`),
        [],
    )
})

Deno.test("resolve: every arm must name the `in:` parameter the same", () => {
    // One lambda encloses the whole fold, so two names for it would leave one
    // unbound in the arms that use it — and it is a keyword, so neither arm can
    // name it at all.
    assertEquals(
        reasonsOf(`data N
    Z
    S pred: Family
    fold f <in: Self, out: Self>
        Z other -> other
        S p alt -> p
`),
        ["arity-mismatch", "arity-mismatch"],
    )
})

Deno.test("resolve: a spec record may not repeat a key", () => {
    // `specRecord` is a keyword list and `specType` reads the first match, so a
    // second `in:` would be dropped with no diagnostic — and it is exactly the
    // spelling an author reaches for when trying to declare a second operand.
    assertEquals(
        reasonsOf(`data N
    Z
    fold f <in: Self, in: Self, out: Self>
        Z -> Z
`),
        ["duplicate-spec-key"],
    )
})

Deno.test("elaborate: the fold evaluates through the core", () => {
    const { operations, registry } = pipeline(STACK_TOP)
    const def = operations[0]?.definition ?? ""
    const value = evalOf(`(${def}) Push(Empty(), Empty())`, registry)[0]
    assert(value !== undefined)
    assertEquals((value as { variantName?: string }).variantName, "Empty")
})

Deno.test("elaborate: a fold's arm bindings follow the declaration's field order", () => {
    // `Fill a b` binds the position, so returning `a` must yield the first
    // field's value. The fixture distinguishes the fields: `Empty` and
    // `Push(…)` are different variants, so a transposed head shows up as the
    // other value rather than as the same one.
    const { operations, registry } = pipeline(`data Box
    Empty
    Fill a: Any b: Any
    fold first <out: Any>
        Empty -> Empty
        Fill a b -> a
`)
    const def = operations[0]?.definition ?? ""
    const value = evalOf(`(${def}) Fill(Empty(), Push(Empty(), Empty()))`, registry)[0]
    // An `EvalErrorValue` is a *value*: asserting only that the forest is
    // non-empty would pass on a failed evaluation.
    assert(value !== undefined)
    assertEquals((value as { variantName?: string }).variantName, "Empty")
})

Deno.test("elaborate: an arm reads the field its binding names", () => {
    // The end-to-end property behind the name rule. Both fields hold a `Nat` of
    // a different magnitude, so reading the wrong slot changes the *value* and
    // a transposition cannot hide behind two equal fields. The emitted handler
    // keeps the surface names, so a reader of the core text sees the same
    // binding the author wrote.
    const source = (selected: string) =>
        `data Nat
    Zero
    Succ pred: Family

data M
    X a: Nat b: Nat
    fold pick <out: Nat>
        X a b -> ${selected}
`
    const magnitude = (value: unknown): number => {
        if (!(value instanceof VariantVal)) throw new Error("not a variant")
        return value.variantName === "Zero" ? 0 : 1 + magnitude([...value.fields.values()][0])
    }
    const pick = (selected: string, term: string) => {
        const { operations, registry, opRegistry } = pipeline(source(selected))
        assertEquals(operations[0]?.definition, `\\e:M. fold [M] e { X(a b) -> ${selected} }`)
        const forest = [
            ...new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
                .parseWith(term, new ValueEnv()),
        ]
        // A second derivation of the same term would still yield a value, so the
        // forest's size is what proves the parse was unambiguous.
        assertEquals(forest.length, 1)
        return magnitude(forest[0])
    }

    // `X(Zero(), Succ(Zero()))` is `a = 0`, `b = 1`.
    assertEquals(pick("a", "#pick(X(Zero(), Succ(Zero())))"), 0)
    assertEquals(pick("b", "#pick(X(Zero(), Succ(Zero())))"), 1)
})

Deno.test("elaborate: `Self` means the declaring type, not the μ-bound", () => {
    // `Self` in a spec is the declaring type — what makes `Num add <in: Self,
    // out: Self>` return its operand's type. The carrier is the *first*
    // parameter and `in: Self` adds a second of the same type, so both are the
    // declaring type. `Family` is a *different* reference: the μ-bound α,
    // written in field position.
    const { operations, types } = pipeline(`data N
    Z
    fold id <in: Self, out: Self>
        Z -> in
`)
    const op = operations[0]!
    assertEquals(op.paramTypes.length, 2)
    assertEquals(op.paramTypes[0], types[0])
    assertEquals(op.paramTypes[1], types[0])
    assertEquals(op.resultType, types[0])
})

Deno.test("elaborate: `Family` in a field stays the μ-bound", () => {
    const { types } = pipeline(STACK)
    assertEquals(types[0]?.findVariant("Push")?.fields[1]?.type, Family)
})

// ── A fold's declared `out:` is its result ──────────────────────────────────
//
// The σ fixpoint's seed is a join operand, so a carrier-seeded fixpoint made
// every non-carrier `out:` infer `Any` and fail the elaboration verdict with
// `returns Any, which is not <: Bool`. The fold's declared result must be the
// one it reports, or no predicate operation can enter Ω.

const BOOL_NAT = `data Bool
    True
    False

data Nat
    Zero
    Succ pred: Family
    fold isZero <out: Bool>
        Zero -> True
        Succ pred -> False
`

Deno.test("elaborate: a non-carrier `out:` installs and keeps its declared type", () => {
    const { operations, types, opRegistry } = pipeline(BOOL_NAT)
    assertEquals(operations.length, 1)
    const op = operations[0]!
    // The declaration and the registry must agree; comparing the declaration
    // alone would pass even if the *definition* had inferred something else.
    assertEquals(op.resultType.toString(), "Bool")
    assertEquals(opRegistry.lookup("isZero")?.resultType.toString(), "Bool")
    // The carrier is still the parameter — the seed change must not have
    // narrowed the fold's domain. Looked up by name so the assertion does not
    // depend on the declaration order in the fixture.
    const nat = types.find((t) => t.name === "Nat")
    assertEquals(op.paramTypes.length, 1)
    assertEquals(op.paramTypes[0], nat)
})

Deno.test("elaborate: a non-carrier fold's definition types as declared", () => {
    // End to end: the emitted text, checked by the core against the same
    // registry Ω was built from. This is the property the verdict depends on —
    // asserting only the declared signature would not catch a definition that
    // inferred `Any` while claiming `Bool`.
    const { operations, registry } = pipeline(BOOL_NAT)
    const forest = typesOf(operations[0]?.definition ?? "", registry)
    assertEquals(forest.length, 1)
    assertEquals(forest[0]?.toString(), "(Nat → Bool)")
})

// ── An omitted `out:` is inferred from the arms ─────────────────────────────
//
// A fold need not answer "what is my result?". The σ fixpoint already computes
// the LUB of the arm bodies, so the answer is read off the emitted term rather
// than substituted with `Any`. `Any` is never a default: it is `<:` every
// declared type, so a silent `Any` accepts any use and hides a disagreement.

const inferred = (arms: string, spec = "") => {
    const program = new SurfaceParse().parseProgram(`data Bool
    True
    False

data Nat
    Zero
    Succ pred: Family
    fold f ${spec}
${arms}
`)
    if (program === undefined) throw new Error("fixture did not parse")
    return elaborateProgram(program)
}

Deno.test("elaborate: an omitted `out:` infers the arms' common type", () => {
    // Both arms are `Nat`, so the fold is `Nat → Nat` — not `Nat → Any`.
    const result = inferred("        Zero -> Zero\n        Succ pred -> pred")
    assertEquals(result.ok, true)
    assertEquals(result.operations[0]?.resultType.toString(), "Nat")
})

Deno.test("elaborate: an omitted `out:` infers a non-carrier type", () => {
    // The case a carrier-based guess cannot reach: the arms are `Bool` while the
    // carrier is `Nat`.
    const result = inferred("        Zero -> True\n        Succ pred -> False")
    assertEquals(result.ok, true)
    assertEquals(result.operations[0]?.resultType.toString(), "Bool")
})

Deno.test("elaborate: an omitted `out:` whose arms disagree is rejected", () => {
    // `Nat` and `Bool` have no common supertype below `Any`, so the LUB is
    // `Any` — and an inferred `Any` would accept every use of `f`, including
    // uses the author cannot have meant. The author must say which they want.
    const result = inferred("        Zero -> True\n        Succ pred -> Zero")
    assertEquals(result.ok, false)
    assertEquals(result.operations.length, 0)
    assertEquals(result.errors.length, 1)
    assert(result.errors[0]?.message.includes("no common type"))
    assert(result.errors[0]?.message.includes("out: Any"))
})

Deno.test("elaborate: an explicit `out: Any` allows disagreeing arms", () => {
    // The escape hatch: naming `Any` is a decision, and a decision is honoured.
    // This is what distinguishes the rule from "divergence is illegal".
    const result = inferred("        Zero -> True\n        Succ pred -> Zero", "<out: Any>")
    assertEquals(result.ok, true)
    assertEquals(result.operations[0]?.resultType.toString(), "Any")
})

Deno.test("elaborate: an `Any`-typed arm is a legal inferred result", () => {
    // The other way an inference lands on `Any`, and it is honest: `Push`'s
    // `value` field IS `Any`, so the fold really does return `Any`. Without this
    // distinction the rule would reject a fold whose arms agree.
    const program = new SurfaceParse().parseProgram(`data Stack
    Empty
    Push value: Any rest: Family
    fold f
        Empty -> Empty
        Push v r -> v
`)!
    const result = elaborateProgram(program)
    assertEquals(result.ok, true)
    assertEquals(result.operations[0]?.resultType.toString(), "Any")
})

// ── A declared `out:` is a premise on every arm ─────────────────────────────

Deno.test("elaborate: an arm that does not produce `out:` is named", () => {
    // The diagnostic half. The signature/definition verdict also rejects this,
    // but it sees the fixpoint's `Any` — the join of `Bool` and `Nat` — and can
    // only say "returns Any", naming neither the case nor the type. Checking the
    // arms first makes the message point at the mistake.
    const result = inferred("        Zero -> True\n        Succ pred -> pred", "<out: Bool>")
    assertEquals(result.ok, false)
    assertEquals(result.errors.length, 1)
    const message = result.errors[0]?.message ?? ""
    assert(message.includes('"Succ"'), `expected the arm named: ${message}`)
    assert(message.includes("Bool"), `expected the declared type: ${message}`)
    assert(message.includes("Nat"), `expected the produced type: ${message}`)
})

Deno.test("elaborate: a fold whose arms all produce `out:` still installs", () => {
    // The no-false-positive half: the premise must not reject a correct fold.
    const result = inferred("        Zero -> True\n        Succ pred -> False", "<out: Bool>")
    assertEquals(result.ok, true)
    assertEquals(result.operations[0]?.resultType.toString(), "Bool")
})

Deno.test("elaborate: an operation's declared signature agrees with its definition", () => {
    // The `Ω` seal requires a definition to type as `paramTypes → resultType`.
    // A surface elaboration that produces both must therefore be self-consistent,
    // and only an assertion comparing them can catch a divergence — the
    // definition type-checking on its own says nothing about the declaration.
    //
    // The second fixture is the multi-parameter case: one lambda per declared
    // parameter, so a one-lambda emission shows up here as `N → N` against the
    // declared `N → N → N`.
    for (
        const source of [
            STACK_TOP,
            `data N
    Z
    fold id <in: Self, out: Self>
        Z -> in
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
    fold size <out: Any>
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

Deno.test("resolve: an arm head that renames its fields is reported", () => {
    // The head is a pattern over the declaration, so a binding is that field's
    // own name. A rename binds a name the variant does not declare, and the
    // emitted handler — which is positional — would read a different field.
    assertEquals(
        reasonsOf(`data A
    X a: Any b: Any
    fold f <out: Any>
        X x y -> x
`),
        ["field-name-mismatch"],
    )
})

Deno.test("resolve: an arm head that transposes its fields is reported", () => {
    // The count matches, so only a positional name check catches this. The
    // emitted handler keeps the written names and binds them positionally, so
    // the body would read field `b` while naming field `a`.
    assertEquals(
        reasonsOf(`data A
    X a: Any b: Any
    fold f <out: Any>
        X b a -> a
`),
        ["field-name-mismatch"],
    )
})

Deno.test("resolve: an arm head naming one field twice is reported", () => {
    // Right count, wrong binding: field `b` is never named, so the emitted
    // handler rebinds `a` over it.
    assertEquals(
        reasonsOf(`data A
    X a: Any b: Any
    fold f <out: Any>
        X a a -> a
`),
        ["field-name-mismatch"],
    )
})

Deno.test("resolve: an arm head binding the fields' names is accepted", () => {
    assertEquals(
        reasonsOf(`data A
    X a: Any b: Any
    fold f <out: Any>
        X a b -> a
`),
        [],
    )
})

Deno.test("resolve: `_` discards a field at any position", () => {
    // `_` is the only binding that is not a name: it discards the field instead
    // of binding it, so it is legal wherever a field's name is.
    for (const head of ["X a _ -> a", "X _ b -> b", "X _ _ -> a"]) {
        assertEquals(
            reasonsOf(`data A
    X a: Any b: Any
    fold f <out: Any>
        ${head}
`),
            [],
            head,
        )
    }
})

Deno.test("resolve: a field-name mismatch names the position, field, and binding", () => {
    // The message has to say which slot is wrong, or an author with a
    // multi-field variant cannot find the transposition.
    const [error] = resolveProgram(
        new SurfaceParse().parseProgram(`data A
    X a: Any b: Any
    fold f <out: Any>
        X b a -> a
`)!,
    ).errors
    assert(error !== undefined)
    assertEquals(error.reason, "field-name-mismatch")
    assert(error.message.includes("position 1"), error.message)
    assert(error.message.includes("`b`"), error.message)
    assert(error.message.includes("`a`"), error.message)
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
        P2 x y -> (P2 y: B1 x: A1)
`)
    assertEquals(
        operations[0]?.definition,
        "\\e:P. fold [P] e { P2(x y) -> (P2(A1(), B1())) }",
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

Deno.test("elaborate: a fold whose body does not produce its declared `out:` is rejected", () => {
    // The signature comes from the spec (`out: B`) and the definition from the
    // arms, so the two can describe different operations. The emitted text
    // type-checks on its own — an `Any`-valued arm makes the fold `Any` — which
    // is why only a verdict comparing the definition against the *declared*
    // signature catches it.
    const result = elaborateVerdictOf(`data N
    Z
data B
    T
data Holder
    H
    fold pick <in: B, out: B>
        H other -> other
`)
    assertEquals(result.ok, false)
    assertEquals(result.errors.map((e) => e.reason), ["not-well-formed"])
    assertEquals(result.errors[0]?.operation, "pick")
    // The message names the disagreement, or the author cannot tell what to fix.
    assert(result.errors[0]?.message.includes("B"), result.errors[0]?.message)
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
        H other -> other
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
    // elaborates and installs, the bad one is named in `errors`. `bad` returns
    // `Holder` where `B` is declared — a mismatch the carrier-seeded σ can
    // neither mask nor manufacture.
    const result = elaborateVerdictOf(`data B
    T
data Holder
    H
    fold good <out: Self>
        H -> H
    fold bad <out: B>
        H -> H
`)
    assertEquals(result.ok, false)
    assertEquals(result.errors.map((e) => e.operation), ["bad"])
    assertEquals(result.operations.map((o) => o.name), ["good"])
    assert(result.opRegistry.lookup("good") !== undefined)
    assertEquals(result.opRegistry.lookup("bad"), undefined)
})

Deno.test("elaborate: an operation the core cannot install is `not-well-formed`", () => {
    // A **self-call** names an operation from inside its own body, which `Ω`'s
    // acyclicity rule rejects — an operation may only reference operations
    // declared before it. The failure surfaces against the operation rather
    // than being emitted as text that no consumer could install. Structural
    // recursion is a different shape: it never names itself, so it installs.
    const result = elaborateVerdictOf(`data Stack
    Empty
    Cons value: Any rest: Family
    fold size <out: Any>
        Empty -> Empty
        Cons v r -> (r size)
`)
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

// ── A fold whose result is not its carrier ──────────────────────────────────
//
// The capture parse that locates an arm's body span is a scan, not the fold's
// typing judgement: `evalFoldFixpoint` re-parses the body under the real σ. A
// scan that binds a recursive `Family` field to the CARRIER decides the question
// anyway — a body reading that field under any other σ is rejected before the
// fixpoint runs, so a fold into a non-carrier type cannot be stated from source.

const SIZE_LIST = `data Nat
    Zero
    Succ pred: Family

data List
    Nil
    Cons head: Nat rest: Family

    fold size <out: Nat>
        Nil -> Zero
        Cons head rest -> Succ pred: rest
`

Deno.test("elaborate: a fold whose result is not its carrier installs", () => {
    // `rest` holds the folded sub-list — a Nat under the fold's σ — so
    // `Succ pred: rest` is well typed. The scan must reach that verdict without
    // deciding it: the emitted text and the declared signature are what agree.
    const result = pipeline(SIZE_LIST)
    assertEquals(result.operations.length, 1)
    assertEquals(result.opRegistry.lookup("size")?.resultType.toString(), "Nat")
    assertEquals(
        result.operations[0]?.definition,
        "\\e:List. fold [List] e { Nil() -> Zero(), Cons(head rest) -> Succ(rest) }",
    )
})

Deno.test("elaborate: a non-carrier size computes by structural recursion", () => {
    // The end-to-end property: not "the emission is the right string" but the
    // operation type-checks and evaluates at each size. The recursion is the
    // fold's own induction — no arm names `size`.
    const { registry, opRegistry } = pipeline(SIZE_LIST)

    /** A `Nat` value read back as its unary magnitude. */
    const magnitude = (value: unknown): number => {
        if (!(value instanceof VariantVal)) throw new Error("not a variant")
        return value.variantName === "Zero" ? 0 : 1 + magnitude([...value.fields.values()][0])
    }
    const size = (term: string) => {
        const [value] = [
            ...new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
                .parseWith(term, new ValueEnv()),
        ]
        return value === undefined ? undefined : magnitude(value)
    }

    assertEquals(size("#size(Nil())"), 0)
    assertEquals(size("#size(Cons(Zero(), Nil()))"), 1)
    assertEquals(size("#size(Cons(Zero(), Cons(Zero(), Nil())))"), 2)
})

// ── Operation application ───────────────────────────────────────────────────
//
// A unary send is the surface's application form (`surface-syntax.md` §2.3):
// `recv name` eliminates its receiver and applies the operation to it, so a
// send inside a body is how one declared operation is used from another. The
// emitted text is the core's sigilled application, `#name(arg)`.

const APPLY = `data Nat
    Zero
    Succ pred: Family

data List
    Nil
    Cons head: Nat rest: Family

    fold size <out: Nat>
        Nil -> Zero
        Cons head rest -> Succ pred: rest

data Box
    B inner: List

    fold sizeOf <out: Nat>
        B inner -> inner size
`

Deno.test("elaborate: a unary send applies the named operation to its receiver", () => {
    // `inner size` is an application, not a field read: `size` is a declared
    // operation taking the receiver as its carrier argument. The sent name is
    // rendered with the operation sigil, which is what makes it a core
    // application rather than a bare identifier.
    const { operations } = pipeline(APPLY)
    const sizeOf = operations.find((op) => op.name === "sizeOf")
    assertEquals(sizeOf?.definition, "\\e:Box. fold [Box] e { B(inner) -> #size(inner) }")
})

Deno.test("elaborate: an operation applied from a body types and computes", () => {
    // The end-to-end property. Both operations install, and the outer one's
    // result is the inner one's on the field — so the send reached the core as
    // an application and ran.
    const { operations, registry, opRegistry } = pipeline(APPLY)
    assertEquals(operations.map((op) => op.name).sort(), ["size", "sizeOf"])

    /** A `Nat` value read back as its unary magnitude. */
    const magnitude = (value: unknown): number => {
        if (!(value instanceof VariantVal)) throw new Error("not a variant")
        return value.variantName === "Zero" ? 0 : 1 + magnitude([...value.fields.values()][0])
    }
    const sizeOf = (term: string) => {
        const [value] = [
            ...new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
                .parseWith(term, new ValueEnv()),
        ]
        return value === undefined ? undefined : magnitude(value)
    }

    assertEquals(sizeOf("#sizeOf(B(Nil()))"), 0)
    assertEquals(sizeOf("#sizeOf(B(Cons(Zero(), Nil())))"), 1)
    assertEquals(sizeOf("#sizeOf(B(Cons(Zero(), Cons(Zero(), Nil()))))"), 2)
})

// ── Structural recursion ────────────────────────────────────────────────────
//
// A data fold is bottom-up (`lc.md` §5.2): a recursive `Family` field arrives at
// its arm already folded to the fold's result, so an arm that rebuilds a
// constructor around it recurses without naming the operation. That is the only
// recursion spelling the surface has — a self-call is the one `Ω`'s acyclicity
// rule rejects.

const PRELUDE_ADD = `data Nat
    Zero
    Succ pred: Family

    fold add <in: Self, out: Self>
        Zero -> in
        Succ pred -> Succ pred: pred
`

Deno.test("elaborate: structural recursion installs without a self-call", () => {
    // `Succ pred: pred` rebuilds around the field, which holds the folded
    // predecessor — a Nat, which is the fold's σ. Nothing in the arm names
    // `add`, so the acyclicity rule has nothing to reject.
    const result = pipeline(PRELUDE_ADD)
    assertEquals(result.operations.map((op) => op.name), ["add"])
    assertEquals(
        result.operations[0]?.definition,
        "\\e:Nat. \\in_:Nat. fold [Nat] e { Zero() -> in_, Succ(pred) -> Succ(pred) }",
    )
    assert(result.opRegistry.lookup("add") !== undefined)
})

Deno.test("elaborate: a structurally recursive operation computes its sum", () => {
    // The semantic property, not just the emission: `add` is addition. A
    // definition that dropped the recursive field would install and type and
    // still be wrong, so the assertion is on the value.
    const { operations, registry, opRegistry } = pipeline(PRELUDE_ADD)

    /** A `Nat` value read back as its unary magnitude. */
    const magnitude = (value: unknown): number => {
        if (!(value instanceof VariantVal)) throw new Error("not a variant")
        return value.variantName === "Zero" ? 0 : 1 + magnitude([...value.fields.values()][0])
    }
    const add = (left: number, right: number) => {
        const numeral = (n: number): string => n === 0 ? "Zero()" : `Succ(${numeral(n - 1)})`
        const [value] = [
            ...new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
                .parseWith(`#add(${numeral(left)}, ${numeral(right)})`, new ValueEnv()),
        ]
        return value === undefined ? undefined : magnitude(value)
    }

    assertEquals(operations.length, 1)
    assertEquals(add(0, 0), 0)
    assertEquals(add(0, 1), 1)
    assertEquals(add(1, 1), 2)
    assertEquals(add(2, 3), 5)
})
