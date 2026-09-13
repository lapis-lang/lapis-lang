/**
 * Operation symbols tests — verify the Ω environment (OpRegistry), the
 * `op(t₁, ..., tₙ)` term form (opProd), T-Op (typing), and E-Op (evaluation).
 *
 * See _docs/theory/lc.md §2.2 (op form), §2.4 (Ω), §3 (E-Op/E-OpArg), §5 (T-Op).
 */

import {
    type DerivationNode,
    EvalErrorValue,
    LCEval,
    LCTypeCheck,
    OpDeclarationError,
    OpRegistry,
    OpSig,
} from "../src/index.ts"
import { Nothing, TypeEnv } from "../src/core/types.ts"
import { type Value, ValueEnv, VariantVal } from "../src/core/values.ts"
import { createOpFixtures, createTestFixtures } from "./fixtures.ts"

import { assert, assertEquals, assertThrows } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry, opRegistry, nat, stream, bool } = createOpFixtures()

/** Type-check `src` under Γ with the op fixtures, returning the forest. */
function typeForestOf(src: string, gamma: TypeEnv = new TypeEnv()): Set<unknown> {
    return new LCTypeCheck()
        .setRegistry(registry)
        .setOpRegistry(opRegistry)
        .parseWith(src, gamma)
}

/** Evaluate `src` under ρ with the op fixtures, returning the forest. */
function evalForestOf(src: string, rho: ValueEnv = new ValueEnv()): Set<unknown> {
    return new LCEval()
        .setRegistry(registry)
        .setOpRegistry(opRegistry)
        .parseWith(src, rho)
}

/** Count the Succ links in a Nat value (its numeric depth). */
function natDepth(val: unknown): number {
    let depth = 0
    let cur: Value = val as Value
    while (cur instanceof VariantVal && cur.variantName === "Succ") {
        depth++
        cur = cur.fields.get("pred")!
    }
    return depth
}

// ── Ω: declaration checks ─────────────────────────────────────────────────────

Deno.test("Ω: declare accepts an acyclic chain (mul references earlier add)", () => {
    // createOpFixtures declares add then mul (mul references add) — if the
    // acyclicity check rejected valid chains, fixture construction would throw.
    const { opRegistry } = createOpFixtures()
    assertEquals(opRegistry.lookup("add") !== undefined, true)
    assertEquals(opRegistry.lookup("mul") !== undefined, true)
})

Deno.test("Ω: declare rejects self-reference", () => {
    const ops = new OpRegistry()
    const bad = new OpSig("loop", [nat, nat], nat, "loop(a, b)")
    assertThrows(() => ops.declare(bad), OpDeclarationError)
})

Deno.test("Ω: declare rejects forward reference", () => {
    const ops = new OpRegistry()
    const bad = new OpSig("early", [nat, nat], nat, "late(a, b)")
    assertThrows(() => ops.declare(bad), OpDeclarationError)
})

Deno.test("Ω: declare rejects the cyclic A↔B pair", () => {
    const ops = new OpRegistry()
    const a = new OpSig("opA", [nat, nat], nat, "opB(x, y)")
    const b = new OpSig("opB", [nat, nat], nat, "opA(x, y)")
    assertThrows(() => ops.declare(a), OpDeclarationError)
    assertThrows(() => ops.declare(b), OpDeclarationError)
})

// ── Acyclicity scan: lexical scope and exclusions ─────────────────────────────
//
// The dependency check is a lexical scan, not a token-level one (declare runs
// before parsing infrastructure exists). These tests pin its exactness claim:
// what it must match, what it must ignore, and that a missed exclusion fails
// loudly (rejected declaration), never silently.

Deno.test("Ω: the scan's exclusions — built-in call forms are not op references", () => {
    // `match(pₖ)` is a language-level call form (lc.md §2.2, T-Pattern), not
    // an operation. A definition using it must declare cleanly.
    const ops = new OpRegistry()
    ops.declare(
        new OpSig("usesMatch", [nat], nat, 'match("[0-9]+")'),
    )
    assertEquals(ops.lookup("usesMatch") !== undefined, true)
})

Deno.test("Ω: the scan's lexical boundaries — what is not an op application", () => {
    const ops = new OpRegistry()
    // These definition shapes contain no genuine op references; each must
    // declare cleanly (a phantom match would reject the declaration).

    // Variable application is whitespace-delimited — `f (x)` is not `f(x)`:
    // the whitespace breaks the ident-then-tight-paren shape.
    ops.declare(
        new OpSig("wsApp", [nat], nat, "\\x:Nat. \\f:Nat -> Nat. f (x)"),
    )
    // Variant construction is PascalCase — Zero() is not an op call, and the
    // lookbehind prevents the mid-identifier phantom (`ero(`) that a naive
    // lowercase-tail match would produce.
    ops.declare(new OpSig("variantUse", [nat], nat, "Zero()"))
    // A bare variable mention (no paren) is not an application: `myOp` alone
    // does not report a dependency on an op of that name.
    ops.declare(
        new OpSig("bareVar", [nat], nat, "\\x:Nat. \\myOp:Nat. myOp"),
    )
    assertEquals(ops.all().length, 3, "all three must declare cleanly")
})

Deno.test("Ω: the scan still catches genuine op references inside definitions", () => {
    // The exclusions must not over-suppress: a real op application in a
    // definition still requires the referenced op to be declared earlier.
    const ops = new OpRegistry()
    assertThrows(
        () => ops.declare(new OpSig("refsUnknown", [nat], nat, "unknownOp(x)")),
        OpDeclarationError,
        "not declared earlier",
    )
    // And once declared, the reference is accepted (acyclic chain).
    ops.declare(new OpSig("known", [nat], nat, "\\x:Nat. x"))
    ops.declare(new OpSig("refsKnown", [nat], nat, "known(x)"))
    assertEquals(ops.lookup("refsKnown") !== undefined, true)
})

Deno.test("Ω: declare rejects a duplicate operation name", () => {
    const ops = new OpRegistry()
    ops.declare(new OpSig("dup", [nat], nat, "Zero()"))
    assertThrows(
        () => ops.declare(new OpSig("dup", [nat], nat, "Zero()")),
        OpDeclarationError,
    )
})

Deno.test("Ω: declare rejects a PascalCase operation name", () => {
    const ops = new OpRegistry()
    assertThrows(
        () => ops.declare(new OpSig("Add", [nat, nat], nat, "Zero()")),
        OpDeclarationError,
    )
})

Deno.test("Ω: an operation may be named with a reserved word", () => {
    // The op form's tight paren is positionally disjoint from every keyword
    // position (all whitespace-delimited), so keyword-named operations are
    // declaraable and appliable — `fold(a, b)` is an op application.
    const ops = new OpRegistry()
    ops.declare(new OpSig("fold", [nat, nat], nat, "\\x:Nat. \\y:Nat. x"))
    assertEquals(ops.lookup("fold") !== undefined, true)
})

Deno.test("namespaces: a keyword-named op is positionally disjoint from the keyword forms", () => {
    // `fold(a, b)` — tight paren — is the op application (the registry
    // gate resolves the reading; the keyword form needs `fold [T]`).
    const ops = new OpRegistry()
    ops.declare(new OpSig("fold", [nat, nat], nat, "\\x:Nat. \\y:Nat. x"))

    // Typing: the op form type-checks.
    const typed = new LCTypeCheck()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("fold(Zero(), Zero())", new TypeEnv())
    assert(typed.size === 1, "the tight-paren op form must type-check")
    assertEquals([...typed][0], nat)

    // Evaluation: the op form computes as the definition.
    const evald = new LCEval()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("fold(Zero(), Zero())", new ValueEnv())
    assert(evald.size === 1, "the op form must evaluate")
    const [val] = evald
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Zero")

    // The keyword form still parses as the fold (whitespace-delimited).
    const foldForm = new LCTypeCheck()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith(
            "fold [Nat] Zero() { Zero() -> Zero(), Succ(p) -> Succ(p) }",
            new TypeEnv(),
        )
    assert(foldForm.size === 1, "the fold form must still parse unambiguously")
    assertEquals([...foldForm][0], nat)
})

// ── T-Op: typing ──────────────────────────────────────────────────────────────

Deno.test("T-Op: add(Zero(), Zero()) has type Nat", () => {
    const result = typeForestOf("add(Zero(), Zero())")
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, nat)
})

Deno.test("T-Op: add(Succ(Zero()), Zero()) has type Nat", () => {
    const result = typeForestOf("add(Succ(Zero()), Zero())")
    assert(result.size === 1, "should have exactly one parse")
    const [type] = result
    assertEquals(type, nat)
})

Deno.test("T-Op: arity mismatch is rejected (add takes 2 args)", () => {
    const result = typeForestOf("add(Zero())")
    assertEquals(result.size, 0, "a 1-arg application of a 2-arg op must be rejected")
})

Deno.test("T-Op: argument type mismatch is rejected", () => {
    // Bool is not <: Nat — the second argument violates the signature.
    const ops = new OpRegistry()
    ops.declare(new OpSig("add", [nat, nat], nat, "\\x:Nat. \\y:Nat. x"))
    const result = new LCTypeCheck()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("add(Zero(), True())", new TypeEnv())
    assertEquals(result.size, 0, "a Bool argument to add must be rejected")
})

Deno.test("T-Op: unknown operation does not parse as an op application", () => {
    // `unknownOp` is not in Ω — opProd's gate rejects, and the term falls
    // through to variable application, which fails (unbound variable).
    const result = typeForestOf("unknownOp(Zero(), Zero())")
    assertEquals(result.size, 0, "an undeclared op name must not type-check")
})

Deno.test("T-Op: subsumption — a Nat argument satisfies a Nat parameter", () => {
    // The premise is arg <: σᵢ (checked field-wise, like T-App's domain).
    // A Nat argument to add : Nat → Nat → Nat is accepted via S-Refl.
    const result = typeForestOf("add(x, Zero())", new TypeEnv().extend("x", nat))
    assert(result.size === 1, "a Nat argument must be accepted")
})

Deno.test("T-Op: Nothing argument propagates to the application type", () => {
    // An eagerly-evaluated arg of type Nothing makes the application
    // uninhabited (principle of explosion) — in either argument position.
    const first = typeForestOf("add(x, Zero())", new TypeEnv().extend("x", Nothing))
    assert(first.size === 1, "should have exactly one parse")
    assertEquals([...first][0], Nothing, "Nothing in the first arg propagates")

    const second = typeForestOf("add(Zero(), x)", new TypeEnv().extend("x", Nothing))
    assert(second.size === 1, "should have exactly one parse")
    assertEquals([...second][0], Nothing, "Nothing in the second arg propagates")
})

Deno.test("T-Op: a Nothing arg does not mask an arg type error", () => {
    // x : Nothing (arg 0), b : Bool (arg 1) — Bool is not <: Nat, so the
    // premise fails and the application is ill-typed (rejected), not Nothing:
    // a genuine type error must never be masked by Nothing propagation.
    const gamma = new TypeEnv().extend("x", Nothing).extend("b", bool)
    const result = typeForestOf("add(x, b)", gamma)
    assertEquals(result.size, 0, "the type error must win over Nothing propagation")
})

// ── E-Op: evaluation ──────────────────────────────────────────────────────────

Deno.test("E-Op: add(Zero(), Zero()) evaluates to Zero", () => {
    const result = evalForestOf("add(Zero(), Zero())")
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Zero")
})

Deno.test("E-Op: add computes as if let-bound (2 + 1 = 3)", () => {
    // two = Succ(Succ(Zero())); one = Succ(Zero()); add(two, one) = 3 succs
    const result = evalForestOf("add(Succ(Succ(Zero())), Succ(Zero()))")
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(natDepth(val), 3)
})

Deno.test("E-Op: mul references add by name (acyclic chain computes)", () => {
    // mul(2, 2) = 4
    const result = evalForestOf("mul(Succ(Succ(Zero())), Succ(Succ(Zero())))")
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(natDepth(val), 4)
})

Deno.test("E-Op: nested op application — add inside add's argument", () => {
    // add(add(1, 1), 1) = 3
    const result = evalForestOf(
        "add(add(Succ(Zero()), Succ(Zero())), Succ(Zero()))",
    )
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(natDepth(val), 3)
})

Deno.test("E-Op: escaping closure — op returning a function, applied later", () => {
    // add is declared first; mkAdder (referencing add) second — acyclic.
    const ops = new OpRegistry()
    ops.declare(new OpSig("add", [nat, nat], nat, "\\x:Nat. \\y:Nat. x"))
    ops.declare(
        new OpSig("mkAdder", [nat], nat, "\\x:Nat. \\y:Nat. add(x, y)"),
    )

    // Application requires whitespace in LC (`f x`, never `f(x)`): the
    // closure escapes the op and is applied later, in the main input.
    const result = new LCEval()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("mkAdder(Succ(Zero())) (Succ(Zero()))", new ValueEnv())
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Succ")
})

Deno.test("E-OpArg: arguments evaluate leftmost (strictness)", () => {
    // Both arguments are op applications themselves — evaluation must reduce
    // them to values before the definition applies (E-OpArg, structural).
    const result = evalForestOf("add(add(Zero(), Zero()), add(Zero(), Zero()))")
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Zero")
})

// ── Codata across the definition window ───────────────────────────────────────
//
// The definition window swaps `_input` to the definition source; a codata
// value crossing the window (in either direction) carries generator spans
// that index into its OWN input, so observations must re-parse against
// `SpanCodataVal.input` — the codata dual of the escaping-closure case.

Deno.test("E-Op: an op returning an unfold stays observable after the window", () => {
    // The codata value escapes the definition window; the observation happens
    // later, in the main input. (The let-bound equivalent works; so must this.)
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "mkStream",
            [nat],
            stream,
            "\\x:Nat. unfold [Stream] x { head -> Zero(), tail -> self }",
        ),
    )
    const result = new LCEval()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("(mkStream(Zero())).head", new ValueEnv())
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Zero")
})

Deno.test("E-Op: a codata argument stays observable inside the definition window", () => {
    // The codata value is built in the main input and passed INTO the op;
    // its generator spans are main-absolute. The observation re-parses against
    // the value's input, not the definition text currently in `_input`.
    const ops = new OpRegistry()
    ops.declare(new OpSig("headOf", [stream], nat, "\\s:Stream. s.head"))
    const result = new LCEval()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith(
            "headOf((unfold [Stream] Succ(Zero()) { head -> Succ(Zero()), tail -> self }))",
            new ValueEnv(),
        )
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Succ")
})

Deno.test("E-Op: codata crosses two definition windows (chained ops)", () => {
    // mkStream builds the value in its definition window; headOf observes it
    // in a different definition window — the spans never index either
    // definition, only the codata value's own input.
    const ops = new OpRegistry()
    ops.declare(
        new OpSig(
            "mkStream",
            [nat],
            stream,
            "\\x:Nat. unfold [Stream] x { head -> Zero(), tail -> self }",
        ),
    )
    ops.declare(new OpSig("headOf", [stream], nat, "\\s:Stream. s.head"))
    const result = new LCEval()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("headOf(mkStream(Zero()))", new ValueEnv())
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Zero")
})

Deno.test("E-Cofold: handler body resolves enclosing-scope variables", () => {
    // The cofold's handler body references the enclosing lambda's `y` — the
    // handler env must extend the ambient scope, symmetrically with E-Fold.
    const result = new LCEval()
        .setRegistry(registry)
        .parseWith(
            "(\\y:Nat. cofold [Stream] (unfold [Stream] Zero() { head -> Zero(), tail -> self }) { head(h) -> y }) (Zero())",
            new ValueEnv(),
        )
    assert(result.size === 1, "should have exactly one result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(val.variantName, "Zero")
})

// ── Identity survival ─────────────────────────────────────────────────────────

Deno.test("identity-survival: opProd nodes are retained in the derivation tree", () => {
    // The named form must survive parsing — the whole point of op symbols.
    // parseToTree retains @rule productions; opProd is one, so the tree
    // contains a labeled opProd node covering the application's span.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const { forest, trees } = tc.parseToTree("add(Zero(), Zero())")
    assert(forest.size === 1)
    assert(trees.length === 1)

    // The tree contains an opProd node covering the full application.
    const opNodes: DerivationNode[] = []
    const walk = (node: DerivationNode) => {
        if (node.label === "opProd") opNodes.push(node)
        for (const child of node.children) walk(child)
    }
    walk(trees[0]!.root)
    assertEquals(opNodes.length >= 1, true, "opProd node must be retained")
    assertEquals(opNodes.some((n) => n.span.start === 0 && n.span.end === 19), true)
})

Deno.test("identity-survival: two applications of the same op are recognizable", () => {
    // Both occurrences parse through opProd with the same op name — the
    // structural identity an optimizer needs (contrast: the let-bound
    // anonymous-fold encoding loses the identity under E-Let inlining).
    // Assert application spans rather than counting nodes — the engine's
    // left-recursion resolution duplicates ancestor labels in the tree, so
    // node counts are not a stable identity signal.
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const src = "add(add(Zero(), Zero()), add(Zero(), Zero()))"
    const { trees } = tc.parseToTree(src)
    assert(trees.length === 1)

    // Each op application contributes an opProd node at its own span: the
    // outer application and the two inner applications.
    const spans: string[] = []
    const walk = (node: DerivationNode) => {
        if (node.label === "opProd") {
            spans.push(`${node.span.start},${node.span.end}`)
        }
        for (const child of node.children) walk(child)
    }
    walk(trees[0]!.root)
    assertEquals(spans.includes("0,45"), true, "outer op application retained")
    assertEquals(spans.includes("4,23"), true, "first inner op application retained")
    assertEquals(spans.includes("25,44"), true, "second inner op application retained")
})

// ── Namespace disambiguation ──────────────────────────────────────────────────

Deno.test("namespaces: a let-bound add is still applicable with whitespace", () => {
    // `add (a)` with whitespace is variable application, not an op application.
    // The op form requires the tight paren; shadowing stays possible. The
    // let-bound add must be a function (Nat → Nat) so application type-checks.
    const result = typeForestOf(
        "let add:Nat -> Nat = \\x:Nat. x in add (Zero())",
    )
    assert(result.size === 1, "variable application with spacing must still work")
})

Deno.test("namespaces: op application is not variable application", () => {
    // add(Zero(), Zero()) with the tight paren is the op form — the let-bound
    // shadow does not capture it.
    const result = typeForestOf(
        "let add:Any = \\x:Nat. x in add(Zero(), Zero())",
    )
    assert(result.size === 1, "the op form must type-check regardless of shadowing")
    const [type] = result
    assertEquals(type, nat, "the op application yields the op's result type")
})

// ── Generative tests unaffected ────────────────────────────────────────────────

Deno.test("generative: an empty OpRegistry keeps opProd inert", () => {
    // The counterexample-search tests build grammars from createTestFixtures
    // (no op registry). opProd must not fire there — the gate is the lookup.
    const { registry: reg } = createTestFixtures()
    const tc = new LCTypeCheck().setRegistry(reg)
    const result = tc.parseWith("Empty()", new TypeEnv())
    assert(result.size === 1, "existing parses must be unaffected")
})

// ── E-Op determinism: the definition window fails loudly ─────────────────────
//
// The window's parses are internal — the caller never sees its forest — so
// evalOp requires exactly one parse result at each step. An empty or
// ambiguous parse is an EvalErrorValue naming the op, never a silent pick.

Deno.test("E-Op: an unparseable definition is a diagnosable error, not silence", () => {
    // The definition isn't valid LC — the window's parse is empty, and the
    // error names the op (the caller sees one eval-error value, not an
    // unexplained empty top-level forest).
    const ops = new OpRegistry()
    ops.declare(new OpSig("broken", [nat], nat, "%%% not a term"))
    const result = new LCEval()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("broken(Zero())", new ValueEnv())
    assert(result.size === 1, "exactly one error value, not a mysterious empty forest")
    const [val] = result
    assert(val instanceof EvalErrorValue)
    assert(
        val.message.includes("broken") && val.message.includes("no results"),
        `the error must name the op and the failure: got "${val.message}"`,
    )
})

Deno.test("E-Op: a non-function definition is a diagnosable error", () => {
    // The definition parses but evaluates to a non-closure (arity 0 body):
    // the first application step hits the not-a-function guard. The error
    // names the op and the step.
    const ops = new OpRegistry()
    ops.declare(new OpSig("notFn", [nat], nat, "Zero()"))
    const result = new LCEval()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("notFn(Zero())", new ValueEnv())
    assert(result.size === 1, "exactly one error value")
    const [val] = result
    assert(val instanceof EvalErrorValue)
    assert(
        val.message.includes("notFn") && val.message.includes("not a function"),
        `the error must name the op and the step: got "${val.message}"`,
    )
})

Deno.test("E-Op: arity mismatch against the signature is a diagnosable error", () => {
    const ops = new OpRegistry()
    ops.declare(new OpSig("add2", [nat, nat], nat, "\\x:Nat. \\y:Nat. x"))
    const result = new LCEval()
        .setRegistry(registry)
        .setOpRegistry(ops)
        .parseWith("add2(Zero())", new ValueEnv())
    assert(result.size === 1, "exactly one error value")
    const [val] = result
    assert(val instanceof EvalErrorValue)
    assert(
        val.message.includes("add2") && val.message.includes("2 arguments"),
        `the error must state the expected arity: got "${val.message}"`,
    )
})

Deno.test("E-Op: a well-formed definition still evaluates deterministically", () => {
    // The guards must not reject legitimate op application: the standard
    // fixture op evaluates to exactly one value.
    const result = evalForestOf("add(Succ(Zero()), Succ(Zero()))")
    assert(result.size === 1, "deterministic single result")
    const [val] = result
    assert(val instanceof VariantVal)
    assertEquals(natDepth(val), 2)
})
