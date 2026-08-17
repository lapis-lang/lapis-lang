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

import { TypeRegistry } from "../src/index.ts"
import { Any, CodataType, DataType, Field, Observer, Variant } from "../src/core/types.ts"

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
