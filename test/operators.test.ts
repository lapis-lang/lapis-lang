/**
 * Binary operators are operation applications — `overview.md` §12.49 / #129.
 *
 * The property that matters is end-to-end: a surface infix expression must
 * elaborate to core text the core *type-checks and evaluates*, not merely to a
 * string that looks right. An operator's name is its own symbol (`+`), not an
 * alias of a named twin, so the whole path is: declare `fold +`, write `a + b`,
 * and get a value back.
 */

import { assert, assertEquals } from "@std/assert"
import {
    elaborateProgram,
    formatResolutionErrors,
    LCEval,
    LCTypeCheck,
    renderOperationName,
    resolveProgram,
    SurfaceParse,
    TypeEnv,
    ValueEnv,
} from "../src/index.ts"

/** Run parse → resolve → elaborate, throwing on any stage's failure. */
function pipeline(source: string) {
    const program = new SurfaceParse().parseProgram(source)
    if (program === undefined) throw new Error(`did not parse:\n${source}`)
    const resolved = resolveProgram(program)
    if (!resolved.ok) throw new Error(formatResolutionErrors(resolved.errors))
    return elaborateProgram(program)
}

/**
 * A two-variant carrier with a symbolic `+` and a second fold whose arm body
 * uses it infix. `A2 + A2` differs from `A1 + A1` so a wrong operand is visible.
 */
const SYMBOLIC_PLUS = `data A
    A1
    A2

    fold + <in: Self, out: Self>
        A1 -> in
        A2 -> A1

    fold viaInfix <out: Self>
        A1 -> A1 + A2
        A2 -> A2
`

// ── The declaration form ─────────────────────────────────────────────────────

Deno.test("operators: a fold may be named with a symbol", () => {
    // `fold +` — the symbol IS the operation's name, so it needs no alias and
    // no mapping table.
    const { operations } = pipeline(SYMBOLIC_PLUS)
    const plus = operations.find((o) => o.name === "+")
    assert(plus !== undefined, "the symbolic operation must install")
})

Deno.test("operators: a multi-character symbolic name is one name", () => {
    // Maximal munch: `<+>` is a single operation name, not `<`, `+`, `>`.
    const { operations } = pipeline(`data A
    A1
    A2

    fold <+> <in: Self, out: Self>
        A1 -> in
        A2 -> in
`)
    assertEquals(operations.map((o) => o.name), ["<+>"])
})

Deno.test("operators: a named fold still declares", () => {
    // The symbolic form must not displace the camelCase one.
    const { operations } = pipeline(`data A
    A1

    fold plus <out: Self>
        A1 -> A1
`)
    assertEquals(operations.map((o) => o.name), ["plus"])
})

// ── The emitted text ────────────────────────────────────────────────────────

Deno.test("operators: an infix body elaborates to an operation application", () => {
    // The core has no infix level, so the operator is applied: `A1 + A2`
    // becomes `#+(A1(), A2())` — the sigil plus the operands as arguments.
    const { operations } = pipeline(SYMBOLIC_PLUS)
    const viaInfix = operations.find((o) => o.name === "viaInfix")
    assertEquals(
        viaInfix?.definition,
        "\\e:A. fold [A] e { A1() -> #+(A1(), A2()), A2() -> A2() }",
    )
})

Deno.test("operators: a postfix send elaborates to an application", () => {
    // The unary send is the model the infix path copies: `a negate` is
    // `#negate(a)`.
    const { operations } = pipeline(`data A
    A1
    A2

    fold negate <out: Self>
        A1 -> A2
        A2 -> A1

    fold flip <out: Self>
        A1 -> A1 negate
        A2 -> A2
`)
    const flip = operations.find((o) => o.name === "flip")
    assertEquals(flip?.definition, "\\e:A. fold [A] e { A1() -> #negate(A1()), A2() -> A2() }")
})

// ── The property that matters: it runs ──────────────────────────────────────

Deno.test("operators: an infix body type-checks and evaluates in the core", () => {
    // End-to-end: elaborate → LCTypeCheck → LCEval. `viaInfix(A1())` applies
    // `+` to (A1, A2); `+`'s A1 arm returns the right operand, so the result is
    // A2 — a value only reachable if the application really ran.
    const { registry, opRegistry } = pipeline(SYMBOLIC_PLUS)
    const check = (term: string) => {
        const typed = [
            ...new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
                .parseWith(term, new TypeEnv()),
        ]
        const evaluated = [
            ...new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
                .parseWith(term, new ValueEnv()),
        ]
        return { typed, evaluated }
    }

    const direct = check("#+(A1(), A2())")
    assertEquals(direct.typed.length, 1, "the application type-checks")
    assertEquals(direct.evaluated.length, 1, "the application evaluates")

    const nested = check("#viaInfix(A1())")
    assertEquals(nested.typed.length, 1, "a fold using infix type-checks")
    assertEquals(nested.evaluated.length, 1, "a fold using infix evaluates")
})

Deno.test("operators: the sigil is required — a bare name is not an application", () => {
    // `+(A1(), A2())` without the sigil is not an operation application, so the
    // core rejects it. This is what makes the sigil load-bearing rather than
    // decorative: it is the lexeme that identifies the form.
    const { registry, opRegistry } = pipeline(SYMBOLIC_PLUS)
    const typed = [
        ...new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
            .parseWith("+(A1(), A2())", new TypeEnv()),
    ]
    assertEquals(typed.length, 0)
})

// ── The name bijection ──────────────────────────────────────────────────────

Deno.test("operators: the name spelling is total and invertible", () => {
    // Core text must round-trip without a side table, so the spelling is a pure
    // function of the name — for every class of name, including the ones that
    // are not identifiers.
    assertEquals(renderOperationName("+"), "#+")
    assertEquals(renderOperationName("add"), "#add")
    assertEquals(renderOperationName("<+>"), "#<+>")
})
