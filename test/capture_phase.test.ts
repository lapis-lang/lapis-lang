/**
 * The evaluator's capture phase — a body parsed only to learn its SPAN.
 *
 * A lambda/fold/unfold/cofold body is captured as a span and replayed later via
 * `_forward` under the real environment (the higher-order attribute mechanism).
 * The capture itself must not compute: the span is a semantic action's second
 * argument, so the action runs, and an application left live would be performed
 * during the capture as well as on replay.
 *
 * The load-bearing case is a self-recursive operation, whose arms call it. A
 * live application during the capture re-enters the operation before any value
 * descends, so the recursion never reaches its base case.
 */

import { assert, assertEquals } from "@std/assert"
import {
    DataType,
    Family,
    Field,
    LCEval,
    OpRegistry,
    OpSig,
    TypeRegistry,
    ValueEnv,
    Variant,
} from "../src/index.ts"
import type { Value } from "../src/index.ts"

// ── Fixtures ─────────────────────────────────────────────────────────────────

/** `Nat = Zero | Succ pred: Family`. */
function natType(): DataType {
    return DataType.define("Nat")
        .addVariant(
            new Variant("Zero", []),
            new Variant("Succ", [new Field("pred", Family)]),
        )
        .build()
}

/**
 * A registry plus Ω holding `id` and one operation whose definition is given.
 *
 * The operation is installed directly rather than through `declare`, because
 * `Ω`'s acyclicity check rejects a self-referential definition. This file is
 * about what the EVALUATOR does with such a definition once it is in `Ω`, so the
 * declaration rules are deliberately out of the way.
 */
function harness(name: string, definition: string) {
    const nat = natType()
    const registry = new TypeRegistry()
    registry.register(nat)

    const opRegistry = new OpRegistry()
    const permissive = { checkDefinition: () => undefined }
    opRegistry.declare(new OpSig("id", [nat], nat, "\\x:Nat. x"), permissive)

    // A self-referential definition cannot pass `declare` (Ω's acyclicity
    // rule). Install it over an acyclic definition of the same signature, which
    // is the state a caller sees once that rule is replaced.
    opRegistry.declare(
        new OpSig(name, [nat], nat, "\\x:Nat. x"),
        permissive,
    )
    const installed = opRegistry.lookup(name)!
    Object.defineProperty(installed, "definition", { value: definition })

    return {
        nat,
        registry,
        opRegistry,
        evaluator: new LCEval().setRegistry(registry).setOpRegistry(opRegistry),
    }
}

/** A value as source-shaped text, for readable assertions. */
function render(value: Value): string {
    const v = value as unknown as {
        variantName?: string
        fields?: Map<string, Value>
    }
    if (v.variantName === undefined) return String(value)
    const fields = [...(v.fields?.values() ?? [])].map(render)
    return `${v.variantName}(${fields.join(", ")})`
}

/** Evaluate `source` to exactly one value and render it. */
function evaluate(ev: LCEval, source: string): string {
    const results = [...ev.parseWith(source, new ValueEnv())]
    assertEquals(results.length, 1, `expected one result for ${source}`)
    return render(results[0]!)
}

// ── Counted invocations ──────────────────────────────────────────────────────

/**
 * Evaluate `source` and report how many times an operation DEFINITION was
 * applied (E-Op), not merely referenced.
 *
 * Counting applications is what distinguishes "the arm was selected" from "the
 * arm's body was parsed": a body that is captured rather than run cannot apply
 * an operation, so a dead arm's count must match a body with no call at all.
 */
function applications(ev: LCEval, source: string): number {
    const proto = Object.getPrototypeOf(ev) as {
        evalOp: (...args: unknown[]) => unknown
    }
    const original = proto.evalOp
    let count = 0
    proto.evalOp = function (this: unknown, ...args: unknown[]) {
        count++
        return original.apply(this, args)
    }
    try {
        evaluate(ev, source)
    } finally {
        proto.evalOp = original
    }
    return count
}

// ── The span capture must not apply ──────────────────────────────────────────

Deno.test("capture: a recursive operation terminates on its base case", () => {
    // E-Fold selects ONE handler; the recursive call lives in the `Succ` arm,
    // which a `Zero()` scrutinee never enters. Before the capture phase was
    // inert this ran forever, because the capture applied `down` to itself
    // before any value had descended.
    const { evaluator: ev } = harness(
        "down",
        "\\e:Nat. fold [Nat] e { Zero() -> Zero(), Succ(pred) -> down(pred) }",
    )
    assertEquals(evaluate(ev, "down(Zero())"), "Zero()")
})

Deno.test("capture: a recursive operation descends and returns", () => {
    const { evaluator: ev } = harness(
        "down",
        "\\e:Nat. fold [Nat] e { Zero() -> Zero(), Succ(pred) -> down(pred) }",
    )
    // Three successors still bottom out at `Zero()`, so the descent is real
    // rather than a single step that happens to be correct.
    assertEquals(evaluate(ev, "down(Succ(Succ(Succ(Zero()))))"), "Zero()")
})

Deno.test("capture: an unreachable arm's operation is never applied", () => {
    // The two bodies differ only in an operation call inside the `Succ` arm.
    // `main(Zero())` never selects that arm, so the two must cost the same.
    const quiet = harness(
        "main",
        "\\e:Nat. fold [Nat] e { Zero() -> Zero(), Succ(pred) -> Zero() }",
    )
    const calling = harness(
        "main",
        "\\e:Nat. fold [Nat] e { Zero() -> Zero(), Succ(pred) -> id(pred) }",
    )
    assertEquals(
        applications(calling.evaluator, "main(Zero())"),
        applications(quiet.evaluator, "main(Zero())"),
        "an unselected fold arm must not apply an operation",
    )
})

Deno.test("capture: the selected arm's operation IS applied", () => {
    // The negative control for the test above: the same call in the arm the
    // scrutinee actually selects must run, or the capture would have made
    // applications inert everywhere rather than only while capturing.
    const quiet = harness(
        "main",
        "\\e:Nat. fold [Nat] e { Zero() -> Zero(), Succ(pred) -> Zero() }",
    )
    const calling = harness(
        "main",
        "\\e:Nat. fold [Nat] e { Zero() -> id(Zero()), Succ(pred) -> Zero() }",
    )
    assert(
        applications(calling.evaluator, "main(Zero())") >
            applications(quiet.evaluator, "main(Zero())"),
        "a selected fold arm must apply its operation",
    )
})

// ── The capture must still replay ────────────────────────────────────────────

Deno.test("capture: a fold arm body referencing a field computes", () => {
    // The replay path: the arm's binding must reach the re-parsed body under
    // the ambient environment, not the capture-phase one.
    const { evaluator: ev } = harness(
        "peel",
        "\\e:Nat. fold [Nat] e { Zero() -> Zero(), Succ(pred) -> pred }",
    )
    assertEquals(evaluate(ev, "peel(Succ(Zero()))"), "Zero()")
})

Deno.test("capture: a lambda body computes when applied", () => {
    const { evaluator: ev } = harness(
        "apply",
        "\\x:Nat. x",
    )
    assertEquals(evaluate(ev, "apply(Zero())"), "Zero()")
})
