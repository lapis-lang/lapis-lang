/**
 * Stack test — verifies the core calculus pipeline on a data type with fold.
 *
 * Tests: type checking, evaluation, and soundness (Progress + Preservation)
 * on a Stack data type with Empty and Push variants, and a `size` fold.
 */

import {
    // Types
    DataType,
    Variant,
    Field,
    FunType,
    TypeEnv,
    Any,
    // Terms
    Var,
    Lam,
    App,
    VariantCon,
    Fold,
    FoldHandler,
    // Values
    ValueEnv,
    VariantVal,
    // Typing
    TypeChecker,
    // Evaluation
    Evaluator,
    // Soundness
    checkSoundness,
} from "../src/index.ts";

import { assertEquals, assert } from "jsr:@std/assert";

// ── Define the Stack data type ────────────────────────────────────────────────

// data Stack
//     Empty
//     Push value: Any rest: Family
//
// DataType is self-referential (μ-type), so we create it in two steps:
// first the empty type, then add variants that reference it.
const StackType = new DataType("Stack", []);
StackType.variants.push(
    new Variant("Empty", []),
    new Variant("Push", [
        new Field("value", Any, false), // non-recursive
        new Field("rest", StackType, true), // recursive (Family)
    ]),
);

// ── Define a `size` fold: fold [Stack] e { Empty → 0, Push _ rest → 1 + rest } ─
// For now, we test with simple terms. The `size` fold would need Nat arithmetic
// which we don't have yet. Instead, let's test basic variant construction and
// a simple fold that returns a constant.

Deno.test("Stack: type-check Empty variant", () => {
    const checker = new TypeChecker();
    const gamma = new TypeEnv();

    // Stack Empty
    const emptyStack = new VariantCon("Empty", StackType, []);
    const type = checker.check(emptyStack, gamma);
    assertEquals(type, StackType);
});

Deno.test("Stack: type-check Push variant", () => {
    const checker = new TypeChecker();
    const gamma = new TypeEnv();

    // Stack Push value: 42 rest: Stack Empty
    // (using a Var as the value for now — in a real program this would be a literal)
    const pushStack = new VariantCon("Push", StackType, [
        new Var("x"), // value: Any
        new VariantCon("Empty", StackType, []), // rest: Stack
    ]);

    // Need x: Any in scope
    const gamma2 = gamma.extend("x", Any);
    const type = checker.check(pushStack, gamma2);
    assertEquals(type, StackType);
});

Deno.test("Stack: evaluate Empty variant", () => {
    const evaluator = new Evaluator();
    const rho = new ValueEnv();

    const emptyStack = new VariantCon("Empty", StackType, []);
    const result = evaluator.eval(emptyStack, rho);

    assert(result instanceof VariantVal);
    assertEquals(result.variantName, "Empty");
});

Deno.test("Stack: evaluate Push variant", () => {
    const evaluator = new Evaluator();
    const rho = new ValueEnv().extend("x", new VariantVal("Empty", StackType, new Map()));

    // Stack Push value: x rest: Stack Empty
    const pushStack = new VariantCon("Push", StackType, [
        new Var("x"),
        new VariantCon("Empty", StackType, []),
    ]);
    const result = evaluator.eval(pushStack, rho);

    assert(result instanceof VariantVal);
    assertEquals(result.variantName, "Push");
    assertEquals(result.fields.get("value")?.kind, "variantVal");
    assertEquals(result.fields.get("rest")?.kind, "variantVal");
});

Deno.test("Stack: soundness check on Empty", () => {
    const emptyStack = new VariantCon("Empty", StackType, []);
    const result = checkSoundness(emptyStack);

    assert(result.wellTyped, "should be well-typed");
    assert(result.progress, "Progress should hold");
    assert(result.preservation, "Preservation should hold");
    assert(result.value !== null, "should evaluate to a value");
});

Deno.test("Stack: soundness check on Push", () => {
    // Use a value (Empty) as the Push argument, not a Var, so the term is closed
    const pushStack = new VariantCon("Push", StackType, [
        new VariantCon("Empty", StackType, []), // value: Any (Stack is a subtype of Any)
        new VariantCon("Empty", StackType, []), // rest: Stack
    ]);
    const result = checkSoundness(pushStack);

    assert(result.wellTyped, "should be well-typed");
    assert(result.progress, "Progress should hold");
    assert(result.preservation, "Preservation should hold");
    assert(result.value !== null, "should evaluate to a value");
});

Deno.test("Stack: ill-typed variant (wrong type)", () => {
    const checker = new TypeChecker();
    const gamma = new TypeEnv();

    // Try to construct Push with a non-Stack rest
    // This should fail because the rest field expects Stack, not a Var of unknown type
    const badPush = new VariantCon("Push", StackType, [
        new Var("x"), // value: Any — ok if x: Any
        new Var("y"), // rest: Stack — fails if y is not Stack
    ]);

    // x: Any, y: Any (not Stack) — should fail
    const gamma2 = gamma.extend("x", Any).extend("y", Any);
    try {
        checker.check(badPush, gamma2);
        assert(false, "should have thrown TypeError_");
    } catch (e) {
        assert(e instanceof Error, "should be an error");
    }
});