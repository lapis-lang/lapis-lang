/**
 * Shared test fixtures — factory functions for fresh type definitions and
 * registries.
 *
 * Every test file imports from here instead of manually reconstructing the
 * same types. New types get added once.
 *
 * Factories construct fresh `DataType`/`CodataType` instances per call so that
 * parallel test execution or test ordering cannot cause cross-test
 * interference via shared mutable singletons.
 */

import { TypeRegistry, type Value } from "../src/index.ts"
import { Any, CodataType, DataType, Field, Observer, Variant } from "../src/core/types.ts"
import { LCTypeCheck } from "../src/core/typing_grammar.ts"
import { type EvalTerm, makeEvalTerm } from "../src/core/law_checking.ts"
import { LCEval } from "../src/core/eval_grammar.ts"
import { OpRegistry, OpSig } from "../src/core/ops.ts"
import { ValueEnv } from "../src/core/values.ts"
import {
    char,
    Grammar,
    literal,
    or,
    type Parser,
    rule,
    seq,
    type ValueGenerator,
} from "@lapis-lang/lang-forma"

// ── Type factories ────────────────────────────────────────────────────────────

/** Constructs a fresh `Stack` data type with `Empty`/`Push` variants. */
export function createStackType(): DataType {
    const stack = new DataType("Stack", [])
    stack.variants.push(
        new Variant("Empty", []),
        new Variant("Push", [
            new Field("value", Any, false),
            new Field("rest", stack, true),
        ]),
    )
    return stack
}

/** Constructs a fresh `Queue` data type with `Empty`/`Enq` variants. */
export function createQueueType(): DataType {
    const queue = new DataType("Queue", [])
    queue.variants.push(
        new Variant("Empty", []),
        new Variant("Enq", [
            new Field("value", Any, false),
            new Field("rest", queue, true),
        ]),
    )
    return queue
}

/** Constructs a fresh `Nat` data type with `Zero`/`Succ` variants. */
export function createNatType(): DataType {
    const nat = new DataType("Nat", [])
    nat.variants.push(
        new Variant("Zero", []),
        new Variant("Succ", [new Field("pred", nat, true)]),
    )
    return nat
}

/** Constructs a fresh `Bool` data type with `True`/`False` variants. */
export function createBoolType(): DataType {
    const bool = new DataType("Bool", [])
    bool.variants.push(
        new Variant("True", []),
        new Variant("False", []),
    )
    return bool
}

/** Constructs a fresh `Stream` codata type with `head`/`tail` observers. */
export function createStreamType(): CodataType {
    const stream = new CodataType("Stream")
    stream.observers.push(
        new Observer("head", Any, false),
        new Observer("tail", stream, true),
    )
    return stream
}

/**
 * Constructs a fresh `NatStream` codata type — a stream whose `head`
 * observes a `Nat` (unlike `Stream`, whose head is `Any`).
 *
 * Used by the op tests where an operation's declared signature must state
 * what the definition actually returns: `headOf` over a `NatStream` honestly
 * types as `[NatStream] → Nat`.
 */
export function createNatStreamType(): CodataType {
    const natStream = new CodataType("NatStream")
    const nat = createNatType()
    natStream.observers.push(
        new Observer("head", nat, false),
        new Observer("tail", natStream, true),
    )
    return natStream
}

// ── Registry factory ──────────────────────────────────────────────────────────

/** Fresh type instances, alongside a registry that references most of them. */
export interface TestFixtures {
    registry: TypeRegistry
    stack: DataType
    /** Not registered in `registry` (see `createTestFixtures` note). */
    queue: DataType
    nat: DataType
    bool: DataType
    stream: CodataType
}

/**
 * Creates a fresh `TypeRegistry` with freshly constructed type instances.
 *
 * Returns the registry and the type instances so tests can use the exact
 * registered instances in `assertEquals` comparisons.
 *
 * NOTE: `queue` is intentionally NOT registered — it shares the `Empty`
 * variant name with `stack`, which would clash in the registry's variant
 * reverse-lookup index. It is only useful for subtyping lattice tests
 * (join/meet/isSubtype) that don't need a registry.
 */
export function createTestFixtures(): TestFixtures {
    const stack = createStackType()
    const queue = createQueueType()
    const nat = createNatType()
    const bool = createBoolType()
    const stream = createStreamType()

    const registry = new TypeRegistry()
    registry.register(stack)
    registry.register(nat)
    registry.register(bool)
    registry.register(stream)

    return { registry, stack, queue, nat, bool, stream }
}

// ── Operation fixtures (Ω) ────────────────────────────────────────────────────

/** Fresh type instances + an `OpRegistry` (Ω) with `add`/`mul` on `Nat`. */
export interface OpTestFixtures {
    registry: TypeRegistry
    opRegistry: OpRegistry
    nat: DataType
    /** Registered in `registry` — for codata-through-window tests. */
    stream: CodataType
    /** Registered in `registry` — for argument-mismatch tests. */
    bool: DataType
    add: OpSig
    mul: OpSig
}

/**
 * Creates a fresh type registry (`Nat`, `NatStream`, `Bool`) and an
 * `OpRegistry` declaring `add` and `mul` — both folds over `Nat`, with
 * LC-source definitions that the declare-time well-formedness check
 * validates against their signatures.
 *
 * `add` is declared first; `mul`'s definition references `add` (an acyclic
 * chain — declaration-order stratification). The definitions are ordinary LC
 * concrete syntax: `add` recurses via the fold's recursive binding, and
 * `mul` applies the earlier-declared `add` by name.
 *
 * `NatStream` (not the `Any`-headed `Stream`) is registered so that op
 * signatures over codata can be stated honestly.
 *
 * `createTestFixtures` is intentionally unchanged — the generative tests
 * (`counterexamples.test.ts`) build grammars from it and must not see the
 * op productions fire (an empty `OpRegistry` keeps `opProd` inert).
 */
export function createOpFixtures(): OpTestFixtures {
    const nat = createNatType()
    const stream = createNatStreamType()
    const bool = createBoolType()

    const registry = new TypeRegistry()
    registry.register(nat)
    registry.register(stream)
    registry.register(bool)

    // The checker shares the registry and the Ω being built: a definition
    // referencing an earlier operation (mul → add) type-checks against it.
    // Declare in dependency order.
    const opRegistry = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)

    const add = opRegistry.declare(
        new OpSig(
            "add",
            [nat, nat],
            nat,
            // add = fold over x: Zero → y; Succ(p) → Succ(p).
            // The fold's recursive binding p IS add(pred(x), y) — the recursion is
            // the fold itself, so the definition never references add by name
            // (which the Ω-acyclicity rule would reject).
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> y, Succ(p) -> Succ(p) }",
        ),
        tc.opWellFormedness,
    )

    const mul = opRegistry.declare(
        new OpSig(
            "mul",
            [nat, nat],
            nat,
            // mul = fold over x: Zero → Zero; Succ(p) → add(y, p).
            // p IS mul(pred(x), y); the handler references the earlier-declared
            // add by name — an acyclic chain (declaration-order stratification).
            "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() -> Zero(), Succ(p) -> add(y, p) }",
        ),
        tc.opWellFormedness,
    )

    return { registry, opRegistry, nat, stream, bool, add, mul }
}

// ── Property-based law harness (forAll over a grammar) ────────────────────────

/**
 * A grammar whose generated values are LC **source strings** for `Nat`
 * values: `Zero()` | `Succ(nat)`.
 *
 * The law harness needs samples it can embed into law instances
 * (`mul(${src}, ${src})`) and evaluate through `LCEval` — so the semantic
 * action emits the concrete syntax itself. The `@rule` decoration on
 * `natProd` is load-bearing: it routes the production through lang-forma's
 * recursion-depth machinery, without which the generator's `Succ` branch
 * would infinitely recurse instead of respecting `maxRecursion`.
 *
 * This is the generator root the full `LCEval` grammar cannot provide:
 * random LC terms are overwhelmingly lambdas/applications (0 of 100
 * depth-4 samples evaluated to a data value), while the law schemas
 * quantify over operand values of a fixed type. The grammar IS the
 * arbitrary — here specialized to the operand carrier `Nat`.
 */
class NatSourceGrammar extends Grammar<{ nat: string }> {
    override start(): Parser<string> {
        return this.natProd()
    }

    @rule
    protected natProd(): Parser<string> {
        return or(
            seq(literal("Zero"), char("("), char(")")).map(() => "Zero()"),
            seq(literal("Succ"), char("("), this.natProd(), char(")"))
                .map(([, , inner]) => `Succ(${inner})`),
        )
    }
}

/** The two pieces a property-based law test needs, created together. */
export interface LawHarness {
    /** Generates `Nat` LC source strings (grammar-aware shrinking included). */
    gen: ValueGenerator<string>
    /** The op fixtures' evaluator — law instances evaluate through it. */
    evalOf: EvalTerm
}

/**
 * Creates the property-based law harness: a `Nat`-source generator bound to
 * the op fixtures' evaluator.
 *
 * Budgets: `maxRecursion` bounds the `Succ`-nesting depth (probes: 2 caps
 * at depth 1, 5 reaches depth 4); `branchStrategy: "random"` samples both
 * productions. `forAll` calls `sample` OUTSIDE its own try/catch — a
 * generation error would escape the property run, so the budgets must stay
 * comfortably within the grammar's ability to terminate (they do: every
 * path here is finite).
 */
export function createLawHarness(): LawHarness {
    const { registry, opRegistry } = createOpFixtures()
    const evalGrammar = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
    return {
        gen: new NatSourceGrammar().toGenerator({
            maxDepth: 4,
            maxRecursion: 5,
            branchStrategy: "random",
        }),
        evalOf: makeEvalTerm(evalGrammar),
    }
}

/**
 * A shared empty environment — `ValueEnv` is persistent (`extend` returns a
 * fresh instance; nothing mutates in place), so one instance is safely
 * reusable across every evaluation that binds nothing of its own.
 */
const SHARED_EMPTY_ENV = new ValueEnv()

/**
 * Evaluate a source string under a shared empty environment, returning its
 * first value — or `undefined` when nothing evaluates (an empty parse
 * forest).
 */
export function evalOne(evalOf: EvalTerm, source: string): Value | undefined {
    return evalOf(source, SHARED_EMPTY_ENV)[0]
}

/**
 * Stress tests are gated behind `SLOW_TESTS=1` so they do not slow down
 * regular CI builds. Run locally with `SLOW_TESTS=1 deno test --allow-env`.
 */
export const slowTestsEnabled = (() => {
    try {
        return Deno.env.get("SLOW_TESTS") === "1"
    } catch {
        // No env permission — skip the stress test.
        return false
    }
})()
