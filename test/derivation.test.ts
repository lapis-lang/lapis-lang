/**
 * Derivation tree + SemanticPass tests — verify v4.0.0's two-phase
 * parse-to-tree + tree-consuming pass architecture works with the LC grammar.
 */

import { type DerivationNode, LCAST, SemanticPass } from "../src/index.ts"
import { createTestFixtures } from "./fixtures.ts"

import { assert, assertEquals } from "@std/assert"

// ── Fixtures ─────────────────────────────────────────────────────────────────

const { registry } = createTestFixtures()

const ast = new LCAST().setRegistry(registry)

// ── Tests ─────────────────────────────────────────────────────────────────────

Deno.test("DerivationTree: parseToTree produces a tree with labeled nodes", () => {
    const { forest, trees } = ast.parseToTree("Empty()")
    assert(forest.size === 1)
    assert(trees.length === 1)
    const root = trees[0]!.root
    assert(root.label !== "")
    assert(root.span.end > root.span.start)
})

Deno.test("DerivationTree: tree for Push(Empty(), Empty()) has correct structure", () => {
    const { trees } = ast.parseToTree("Push(Empty(), Empty())")
    assert(trees.length === 1)
    const root = trees[0]!.root
    // Root should cover the full input
    assertEquals(root.span.start, 0)
    assertEquals(root.span.end, 22)
    // Should have children
    assert(root.children.length > 0)
})

Deno.test("SemanticPass: depth pass computes tree depth", () => {
    const { trees } = ast.parseToTree("Empty()")
    assert(trees.length === 1)

    class DepthPass extends SemanticPass<{ depth: number }> {
        protected override defaultHandler(
            _node: DerivationNode,
            childResults: readonly unknown[],
        ): unknown {
            if (childResults.length === 1) return childResults[0]
            return childResults.length > 0 ? 1 + Math.max(...(childResults as number[])) : 0
        }
    }

    const depth = new DepthPass().evaluate(trees[0]!)
    assert(typeof depth === "number")
    assert(depth >= 0)
})

Deno.test("SemanticPass: production count pass counts @rule nodes", () => {
    const { trees } = ast.parseToTree("Push(Empty(), Empty())")
    assert(trees.length === 1)

    class CountPass extends SemanticPass<{ count: number }> {
        private count = 0

        protected override defaultHandler(
            _node: DerivationNode,
            childResults: readonly unknown[],
        ): unknown {
            this.count++
            // Return the accumulated count from children (if any) or just this node
            const childSum = childResults.reduce((a: number, b: unknown) => a + (b as number), 0)
            return 1 + childSum
        }
    }

    const count = new CountPass().evaluate(trees[0]!)
    assert(typeof count === "number")
    assert(count > 0)
})
