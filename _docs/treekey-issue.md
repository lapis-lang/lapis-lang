# zipper-grammar issue: `treeKey` fails for objects with non-enumerable state

## Summary

`@rule` parameterised methods cache per `(instance, method, treeKey(args))`. `treeKey` uses JSON
serialization to distinguish argument tuples. Objects with non-enumerable state (e.g., a private
`Map` field) serialize identically regardless of their actual content, causing the cache to return
stale results for different argument values.

## Reproduction

```typescript
import { Grammar, type Parser, rule } from "jsr:@lapis-lang/zipper-grammar@3.0.0"

class Env {
    private readonly bindings: Map<string, string>
    constructor(entries?: Map<string, string>) {
        this.bindings = entries ?? new Map()
    }
    extend(name: string, value: string): Env {
        const next = new Map(this.bindings)
        next.set(name, value)
        return new Env(next)
    }
    lookup(name: string): string | undefined {
        return this.bindings.get(name)
    }
}

class MyGrammar extends Grammar<{}> {
    override start() {
        return this.prod(new Env())
    }

    @rule
    prod(env: unknown): Parser<string> {
        const e = env as Env
        const val = e.lookup("x")
        if (val === undefined) return this.empty() as unknown as Parser<string>
        // Return a parser that produces the value
        return this.epsilon(val)
    }
}

const g = new MyGrammar()
// First call: env has x = "hello"
const env1 = new Env().extend("x", "hello")
const r1 = g._parseWith("hello", g.prod(env1))
// Second call: env has x = "world"
const env2 = new Env().extend("x", "world")
const r2 = g._parseWith("world", g.prod(env2))

// Expected: r1 = Set{"hello"}, r2 = Set{"world"}
// Actual: r1 = Set{"hello"}, r2 = Set{"hello"} (stale cache!)
```

## Root cause

`treeKey` (in `src/util/tree_key.ts`) serializes arguments to create a cache key for `@rule`
methods. For objects, it uses `JSON.stringify`, which:

1. Skips `Map`/`Set` (they serialize as `{}`)
2. Skips private fields (convention: underscore-prefixed or truly private via `#`)
3. Skips non-enumerable properties

This means two `Env` instances with completely different `Map` contents produce the same `treeKey`,
so the `@rule` cache returns the first result for all subsequent calls.

## Impact

Any `@rule` method that takes an object argument with non-enumerable state (e.g., a context
environment with a private `Map`) will have incorrect caching. This is the primary use case for
parameterised `@rule` methods — threading context (Γ, ρ) through grammar productions.

## Workaround

Add a unique enumerable property to each instance so `treeKey` distinguishes them:

```typescript
let counter = 0
class Env {
    readonly _id: number = ++counter
    private readonly bindings: Map<string, string>
    // ...
}
```

`JSON.stringify({_id: 1})` ≠ `JSON.stringify({_id: 2})`, so the cache distinguishes instances. This
works but is fragile — it relies on the implementation detail that `treeKey` uses JSON
serialization.

## Suggested fix

Option A: Use `WeakMap<object, string>` in `treeKey` to assign a unique ID to each object, instead
of JSON serialization. This distinguishes objects by identity, not by content. Downside: two
structurally equal but distinct objects would get different keys (but for context environments,
identity-based keying is correct — you don't want to share cache across different environment
instances even if they happen to have the same content).

Option B: Check if the object has a `toKey()` or `treeKey()` method and call it. This lets users
provide a custom key function. Downside: requires user awareness.

Option C: Use `Object.entries` instead of `JSON.stringify` to serialize enumerable properties, and
special-case `Map`/`Set` to serialize their contents. More robust but more complex.

**Recommendation: Option A** (WeakMap-based identity keying for objects). It's the simplest fix,
works for all objects without user intervention, and is correct for the primary use case (context
threading). The only downside (structurally equal objects getting different keys) is not a real
problem in practice — if you're creating new context objects, you want fresh cache entries.

## Environment

- zipper-grammar: 3.0.0
- Deno: 1.x (Ubuntu 24.04)
- Found during Lapis Core Calculus implementation (`TypeEnv` with private `Map<string, Type>`
  bindings)
