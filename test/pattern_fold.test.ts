/**
 * Pattern-matched fold tests — the elimination form over pattern-matched data
 * types (T-FoldMatch / E-FoldMatch, lc.md §5.2b + §3.1).
 *
 * `fold [T] e { match("pᵢ") → tᵢ }` eliminates a `PatternDataType` token: the
 * handler head re-spells the constructor (`match("p")` — the same gate the
 * introduction form runs), the body references the fixed `match : Token`
 * binding, and evaluation dispatches the token to its handler by CANONICAL
 * pattern source. These tests pin the premises (carrier kind, scrutinee
 * subtype, exhaustiveness over canonical sources, handler-head carrier
 * membership), the one-pass join typing (no fixpoint — a PatternDataType has
 * no fields), the Nothing-propagation arm, the token dispatch (including the
 * bare-atom route's documented miss), the span replay of nested folds, and
 * the branch-ordering contract between the two fold forms.
 */

import {
    CostPass,
    DefinitionShapeError,
    EvalErrorValue,
    LCEval,
    LCTypeCheck,
    OpRegistry,
    readRejectedConstruct,
    TokenVal,
    TypeRegistry,
    ValueEnv,
} from "../src/index.ts"

import { FunType, Nothing, NothingType, TokenType, TypeEnv } from "../src/core/types.ts"

import { assert, assertEquals, assertThrows } from "@std/assert"

import { createNatType, createPatternType } from "./fixtures.ts"

// ── Fixtures ─────────────────────────────────────────────────────────────────

/** A harness: fresh registries + bound checker/evaluator per test. */
function patternHarness(
    types: { name: string; patterns: readonly string[] }[] = [
        { name: "NatPat", patterns: ["[0-9]+"] },
    ],
) {
    const registry = new TypeRegistry()
    for (const t of types) {
        registry.register(createPatternType(t.name, t.patterns))
    }
    const opRegistry = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ev = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
    return {
        registry,
        opRegistry,
        tc,
        ev,
    }
}

/** Type-check a source string; the single type or `undefined` (empty forest). */
function typeOfOne(
    h: ReturnType<typeof patternHarness>,
    source: string,
    gamma: TypeEnv = new TypeEnv(),
) {
    const results = [...h.tc.parseWith(source, gamma)]
    return results.length === 1 ? results[0] : undefined
}

/** Evaluate a source string; the single value or `undefined` (empty forest). */
function evalOne(
    h: ReturnType<typeof patternHarness>,
    source: string,
    rho: ValueEnv = new ValueEnv(),
) {
    const results = [...h.ev.parseWith(source, rho)]
    return results.length === 1 ? results[0] : undefined
}

/**
 * Parse to the checker's derivation tree, ASSERTING a singleton forest: an
 * empty parse is a test-fixture failure (the grammar rejected the source —
 * a syntax tweak, a registry gap), reported as such rather than surfacing
 * later as `trees[0]`'s undefined-index. The assertion runs BEFORE the
 * indexing, so the failure names the parse, not the consumer.
 */
function parseTree(tc: LCTypeCheck, source: string) {
    const { trees } = tc.parseToTree(source)
    assertEquals(trees.length, 1, `expected a singleton parse forest for: ${source}`)
    return trees[0]!
}

// ── T-FoldMatch: well-typed eliminations ─────────────────────────────────────

Deno.test("T-FoldMatch: single-handler fold types as the handler body's type", () => {
    const h = patternHarness()
    const result = typeOfOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[0-9]+") → \\y:Int. y }',
    )
    assert(result instanceof FunType)
})

Deno.test("T-FoldMatch: the handler body sees match : Token (the binding is live)", () => {
    const h = patternHarness()
    // The BODY IS the bare `match` variable — σ is the binding's own type:
    // Token. This pins the handler context extension (a body that cannot
    // compile without the binding): without `match : Token` in Γ the body is
    // an unbound variable and the fold rejects.
    const result = typeOfOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[0-9]+") → match }',
    )
    assert(result instanceof TokenType)
    // And a body referencing the binding at the WRONG position (a function
    // argument slot that wants a NatPat) rejects — the binding's type is
    // Token, not the carrier.
    assertEquals(
        typeOfOne(
            h,
            'fold [NatPat] match("[0-9]+") { match("[0-9]+") → (\\y:NatPat. y) match }',
        ),
        undefined,
    )
})

Deno.test("T-FoldMatch: multi-handler fold requires ONE common result type (lc.md §5.2b)", () => {
    const h = patternHarness([{ name: "NatPat", patterns: ["[0-9]+", "[0-9]*[02468]"] }])
    // lc.md §5.2b's rule: every handler body types as `Token → σ` for ONE σ —
    // NOT a lattice join. Two handlers whose bodies AGREE (both return the
    // token: Token) type as Token.
    const r1 = typeOfOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[0-9]+") → match, match("[0-9]*[02468]") → match }',
    )
    assert(r1 instanceof TokenType)
    // DIVERGENT bodies (one returns the token, one a function over it) reject
    // the fold — the branch is an empty forest, never a laundered `Any` (the
    // join-shaped acceptance the rule forbids). BOTH orders are pinned: the
    // common-type check starts at the FIRST handler's body, and either
    // direction of divergence must reject.
    assertEquals(
        typeOfOne(
            h,
            'fold [NatPat] match("[0-9]+") { match("[0-9]+") → match, match("[0-9]*[02468]") → \\m:Token. m }',
        ),
        undefined,
    )
    assertEquals(
        typeOfOne(
            h,
            'fold [NatPat] match("[0-9]+") { match("[0-9]+") → \\m:Token. m, match("[0-9]*[02468]") → match }',
        ),
        undefined,
    )
})

Deno.test("T-FoldMatch: exhaustiveness — a missing declared pattern rejects", () => {
    const h = patternHarness([{ name: "NatPat", patterns: ["[0-9]+", "[0-9]*[02468]"] }])
    // One handler for a two-pattern carrier: exhaustiveness fails.
    assertEquals(
        typeOfOne(
            h,
            'fold [NatPat] match("[0-9]+") { match("[0-9]+") → \\m:Token. m }',
        ),
        undefined,
    )
})

Deno.test("T-FoldMatch: canonical equivalence satisfies exhaustiveness", () => {
    const h = patternHarness([{ name: "NatPat", patterns: ["[0-9]+"] }])
    // The registered spelling [0123456789]+ and the handler's [0-9]+ normalize
    // to ONE canonical source — the handler satisfies the declared pattern.
    const result = typeOfOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[0123456789]+") → \\m:Token. m }',
    )
    assert(result instanceof FunType)
})

Deno.test("T-FoldMatch: an undeclared pattern in a handler head rejects", () => {
    const h = patternHarness()
    assertEquals(
        typeOfOne(
            h,
            'fold [NatPat] match("[0-9]+") { match("[a-z]+") → \\m:Token. m }',
        ),
        undefined,
    )
})

Deno.test("T-FoldMatch: a pattern owned by a different type rejects", () => {
    const h = patternHarness([
        { name: "NatPat", patterns: ["[0-9]+"] },
        { name: "WordPat", patterns: ["[a-z]+"] },
    ])
    // [a-z]+ is declared on WordPat, not on the fold's carrier NatPat — the
    // unmatchable head rejects the handler branch (and exhaustiveness fails).
    assertEquals(
        typeOfOne(
            h,
            'fold [NatPat] match("[0-9]+") { match("[a-z]+") → \\m:Token. m }',
        ),
        undefined,
    )
})

Deno.test("T-FoldMatch: wrong-kind annotation rejects (branch-reject, not a crash)", () => {
    const h = patternHarness()
    // The annotation resolves to a TypeVar (unregistered name) — neither the
    // pattern branch's gate nor the variant branch's accepts it: the branch
    // is a clean empty forest, never a throw out of the parse (the ordering
    // pin). A registered-codata carrier takes the same path (patternFoldProd
    // and foldProd both reject it); the TypeVar route is what this harness
    // can spell without a codata fixture.
    assertEquals(
        typeOfOne(
            h,
            'fold [Stream] match("[0-9]+") { match("[0-9]+") → \\m:Token. m }',
        ),
        undefined,
    )
})

Deno.test("T-FoldMatch: a scrutinee of the wrong type rejects", () => {
    const h = patternHarness()
    // A lambda scrutinee does not subtype the pattern carrier.
    assertEquals(
        typeOfOne(
            h,
            'fold [NatPat] \\x:Token. x { match("[0-9]+") → \\m:Token. m }',
        ),
        undefined,
    )
})

Deno.test("T-FoldMatch: a Nothing-typed scrutinee propagates Nothing (let-bound)", () => {
    const h = patternHarness()
    // Principle of explosion: the scrutinee's TYPE is Nothing. The
    // Nothing-typed scrutinee here is a variable whose Γ type is Nothing
    // (installed via the gamma — an actual Nothing VALUE cannot be written;
    // the checker's judgment carries the variable's type, the same shape
    // typing.test.ts's S-Bot test uses), so the PROPAGATION ARM fires — the
    // fold's result is Nothing, not the body type (Token).
    const gamma = new TypeEnv().extend("x", Nothing)
    const result = typeOfOne(
        h,
        'fold [NatPat] x { match("[0-9]+") → \\m:Token. m }',
        gamma,
    )
    assert(result instanceof NothingType)
    assertEquals(result.toString(), "Nothing")
})

Deno.test("T-FoldMatch: scrutinee of type Nothing propagates Nothing (annotation-driven)", () => {
    const h = patternHarness()
    // An op-free construction: a λ-parameter typed Nothing, the fold as the
    // body — the parameter's type IS Nothing, the scrutinee premise is
    // satisfied via Nothing <: NatPat, and the fold's result is Nothing (the
    // propagation arm fires, NOT the join). The codomain pins the arm: a join
    // of the body types would be Token (the body is `match`), never Nothing.
    const result = typeOfOne(
        h,
        'λx:Nothing. fold [NatPat] x { match("[0-9]+") → \\m:Token. m }',
    )
    assert(result instanceof FunType)
    // The codomain IS Nothing (the propagation arm), not the body type Token
    // (a join would give Token → Token as the fold's σ — the codomain here
    // would be Token → Token's own body, never Nothing).
    assert((result as FunType).result instanceof NothingType)
    assertEquals((result as FunType).result.toString(), "Nothing")
})

Deno.test("T-FoldMatch: zero-pattern carrier rejects (the empty-handler arm)", () => {
    const h = patternHarness([{ name: "EmptyPat", patterns: [] }])
    // A zero-pattern carrier is vacuously exhaustive but has no tokens — the
    // bare-atom scrutinee (whose gate accepts any registered pattern type's
    // name) reaches the judgment with ZERO handlers; the empty-handler arm
    // (spanHandlers.length === 0) rejects — a judgment over an empty handler
    // set has no σ to join.
    assertEquals(
        typeOfOne(
            h,
            "fold [EmptyPat] EmptyPat { }",
        ),
        undefined,
    )
})

Deno.test("T-FoldMatch: match shadows an outer binding inside the handler body", () => {
    const h = patternHarness()
    // `match` is bound at Token by the handler; an outer `match : NatPat →
    // NatPat` would type the body's `match` at the FUNCTION type — the result
    // being Token proves the handler's binding won (the extendCtx shadowing,
    // last-binding-wins). The body IS the bare `match` variable.
    const outer = new TypeEnv().extend(
        "match",
        new FunType(
            h.registry.lookup("NatPat")!,
            h.registry.lookup("NatPat")!,
        ),
    )
    const result = typeOfOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[0-9]+") → match }',
        outer,
    )
    assert(result instanceof TokenType)
})

// ── E-FoldMatch: evaluation ──────────────────────────────────────────────────

Deno.test("E-FoldMatch: the token dispatches to its handler and binds match", () => {
    const h = patternHarness()
    // The body IS the bare `match` variable: the value the fold returns is
    // the SCRUTINEE's own TokenVal, read through the extended environment —
    // this pins `extend("match", scrutinee)` (the binding machinery; a body
    // that ignored the binding would error on the unbound variable).
    const result = evalOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[0-9]+") → match }',
    )
    assert(result instanceof TokenVal)
    const tok = result as TokenVal
    assertEquals(tok.dataTypeName, "NatPat")
    assertEquals(tok.text, "[0-9]+")
})

Deno.test("E-FoldMatch: each declared pattern routes to its own handler (identity observed)", () => {
    const h = patternHarness([{ name: "NatPat", patterns: ["[0-9]+", "[0-9]*[02468]"] }])
    // lc.md §5.2b demands ONE common result type, so the two bodies cannot
    // return differently-TYPED results — the distinguishing observation is
    // the RETURNED TOKEN's text: each body produces a FRESH token whose
    // canonical source is its own head's pattern, so a first-handler-always
    // dispatch would return the [0-9]+ token for BOTH scrutinees and fail
    // the identity assertion below.
    const r1 = evalOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → match("[0-9]*[02468]") }',
    )
    const r2 = evalOne(
        h,
        'fold [NatPat] match("[0-9]*[02468]") { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → match("[0-9]*[02468]") }',
    )
    assert(r1 instanceof TokenVal)
    assert(r2 instanceof TokenVal)
    // The returned token NAMES THE FIRED ARM: the [0-9]+ scrutinee routes to
    // the [0-9]+ body, the [0-9]*[02468] scrutinee to its own.
    assertEquals((r1 as TokenVal).text, "[0-9]+")
    assertEquals((r2 as TokenVal).text, "[0-9]*[02468]")
})

Deno.test("E-FoldMatch: canonical spellings dispatch equally", () => {
    const h = patternHarness([{ name: "NatPat", patterns: ["[0-9]+"] }])
    // The scrutinee spells [0123456789]+; the handler head spells [0-9]+ —
    // both canonicalize to one source; the dispatch succeeds.
    const result = evalOne(
        h,
        'fold [NatPat] match("[0123456789]+") { match("[0-9]+") → \\m:Token. m }',
    )
    assert(result !== undefined)
    assert(!(result instanceof EvalErrorValue))
})

Deno.test("E-FoldMatch: a non-token scrutinee errors (not a crash)", () => {
    const h = patternHarness()
    const result = evalOne(
        h,
        'fold [NatPat] \\x:Token. x { match("[0-9]+") → \\m:Token. m }',
    )
    assert(result instanceof EvalErrorValue)
    const err = result as EvalErrorValue
    assert(err.message.startsWith("pattern fold scrutinee is not a TokenVal"))
})

Deno.test("E-FoldMatch: a token of a different type rejects the handler head", () => {
    const h = patternHarness([
        { name: "NatPat", patterns: ["[0-9]+"] },
        { name: "WordPat", patterns: ["[a-z]+"] },
    ])
    // The handler head names a WordPat pattern; the fold's carrier is NatPat
    // — the head gate's carrier premise rejects the branch (an unmatchable
    // head would corrupt exhaustiveness), so the source is an empty forest
    // on BOTH sides, not a value.
    const result = evalOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[a-z]+") → \\m:Token. m }',
    )
    assertEquals(result, undefined)
})

Deno.test("E-FoldMatch: a bare-atom token scrutinee misses the dispatch (documented asymmetry)", () => {
    const h = patternHarness()
    // The bare atom's TokenVal text is the TYPE NAME, not a pattern source —
    // no handler's canonical source equals "NatPat", so the dispatch is a
    // miss reported as the no-handler failure (the fold keys DECLARED
    // PATTERNS; the bare atom remains the type's value, not a constructor).
    const result = evalOne(
        h,
        'fold [NatPat] NatPat { match("[0-9]+") → \\m:Token. m }',
    )
    assert(result instanceof EvalErrorValue)
    const err = result as EvalErrorValue
    assert(err.message.startsWith("no handler for pattern:"))
})

Deno.test("E-FoldMatch: a nested fold's span replays under the ambient scope", () => {
    const h = patternHarness()
    // The inner fold's body produces a token; the outer fold dispatches on
    // it — the span-replay machinery's offset arithmetic holds for
    // fold-in-fold (the inner body replays, the outer body re-reads from ITS
    // span).
    const result = evalOne(
        h,
        'fold [NatPat] (fold [NatPat] match("[0-9]+") { match("[0-9]+") → match("[0-9]+") }) { match("[0-9]+") → \\m:Token. m }',
    )
    assert(result !== undefined)
    assert(!(result instanceof EvalErrorValue))
    // The outer body ran: its closure binds the inner fold's token.
    assert(result !== null && typeof result === "object")
})

Deno.test("E-FoldMatch: the bound match is the token value (a TokenVal)", () => {
    const h = patternHarness()
    // A body that produces the token itself: the closure's captured env
    // carries the binding (the outer fold's dispatch extended the ambient
    // scope with `match ↦ tok`).
    const result = evalOne(
        h,
        'fold [NatPat] match("[0-9]+") { match("[0-9]+") → match("[0-9]+") }',
    )
    assert(result instanceof TokenVal)
    const tok = result as TokenVal
    assertEquals(tok.dataTypeName, "NatPat")
    assertEquals(tok.text, "[0-9]+")
})

// ── The branch-ordering pin (the two fold forms) ─────────────────────────────

Deno.test("Branch ordering: a variant fold over a DataType still works", () => {
    // The two fold forms are lexically identical up to the type gate; the
    // pattern branch is ordered FIRST and rejects non-pattern carriers, and
    // the variant branch handles DataTypes — both sides must keep working
    // side by side.
    const registry = new TypeRegistry()
    registry.register(createNatType())
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(new OpRegistry())
    const ev = new LCEval().setRegistry(registry).setOpRegistry(new OpRegistry())
    const src = "\\x:Nat. \\y:Nat. fold [Nat] x { Zero() → y, Succ(p) → p }"
    const t = [...tc.parseWith(src, new TypeEnv())]
    assertEquals(t.length, 1)
    const v = [...ev.parseWith(src, new ValueEnv())]
    assertEquals(v.length, 1)
})

// ── The derivation fragment boundary ─────────────────────────────────────────

Deno.test("Derivation reader: a pattern fold is rejected loudly (the reader's own diagnostic)", () => {
    // The derivation fragment is a fold-skeleton language over VARIANT
    // carriers — the reader's `patternFold` action throws
    // DefinitionShapeError naming the construct (the loud rejection, never a
    // silent mis-read).
    //
    // The diagnostic is reached DIRECTLY (the `readRejectedConstruct` seam —
    // the derivation module's diagnostic surface): through `readDefShape` the
    // pre-scan's `match`-lexeme entry (REJECTED_CONSTRUCTS) always fires
    // first — a pattern fold necessarily contains the word `match` — so that
    // path's diagnostic is the pre-scan's, and this assertion would not
    // distinguish the reader's own action from it.
    assertThrows(
        () => readRejectedConstruct("patternFold", ["NatPat", "[0-9]+"]),
        DefinitionShapeError,
        "pattern-type elimination",
    )
})

// ── The cost pass ─────────────────────────────────────────────────────────────

Deno.test("CostPass: the pattern fold's records charge the FIRED handler", () => {
    const registry = new TypeRegistry()
    registry.register(createPatternType("NatPat", ["[0-9]+", "[0-9]*[02468]"]))
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)
    const pass = new CostPass(registry, omega)

    // Handler 0 is a cheap token; handler 1's body is a NESTED fold. The
    // scrutinee names [0-9]+ — the dispatch (by the token's per-pattern size
    // variable `token(T:<p>)`) must charge ONLY the cheap handler, regardless
    // of handler ORDER: the nested fold's cost (a third token production)
    // would appear in the sum otherwise.
    const cheapFirst = pass.evaluateReport(
        parseTree(
            tc,
            'fold [NatPat] match("[0-9]+") { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → fold [NatPat] match("[0-9]+") { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → match("[0-9]*[02468]") } }',
        ) as never,
    )
    const expensiveFirst = pass.evaluateReport(
        parseTree(
            tc,
            'fold [NatPat] match("[0-9]+") { match("[0-9]*[02468]") → fold [NatPat] match("[0-9]+") { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → match("[0-9]*[02468]") }, match("[0-9]+") → match("[0-9]+") }',
        ) as never,
    )
    // Both dispatch to the [0-9]+ handler: identical reports.
    assertEquals(cheapFirst?.cost.render(), expensiveFirst?.cost.render())
    // And the charge is the scrutinee's token (1) + the fired body's token (1).
    assertEquals(cheapFirst?.cost.render(), "2")
})

Deno.test("CostPass: the scrutinee's pattern decides the charge (the other handler fires too)", () => {
    const registry = new TypeRegistry()
    registry.register(createPatternType("NatPat", ["[0-9]+", "[0-9]*[02468]"]))
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)
    const pass = new CostPass(registry, omega)
    // The scrutinee names [0-9]*[02468] — the EXPENSIVE handler fires: the
    // charge is the scrutinee (1) + the fired body's own fold (scrutinee 1 +
    // body 1) = 3. A handlers[0]-style charge would report 2.
    const report = pass.evaluateReport(
        parseTree(
            tc,
            'fold [NatPat] match("[0-9]*[02468]") { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → fold [NatPat] match("[0-9]+") { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → match("[0-9]*[02468]") } }',
        ) as never,
    )
    assertEquals(report?.cost.render(), "3")
    // The dispatch edge's consumer names the pattern fold.
    assert(
        report?.edges.some((e: { consumer: { kind: string } }) => e.consumer.kind === "foldMatch"),
    )
})

Deno.test("CostPass: a token without per-pattern identity charges every handler conservatively", () => {
    const registry = new TypeRegistry()
    registry.register(createPatternType("NatPat", ["[0-9]+", "[0-9]*[02468]"]))
    const omega = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(omega)
    const pass = new CostPass(registry, omega)
    // The bare-atom route's token size variable is `token(T)` (no pattern
    // component) — no dispatch identity: the conservative charge covers both
    // handler bodies (scrutinee 1 + token 1 + the nested fold's 2) = 4.
    const report = pass.evaluateReport(
        parseTree(
            tc,
            'fold [NatPat] NatPat { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → fold [NatPat] match("[0-9]+") { match("[0-9]+") → match("[0-9]+"), match("[0-9]*[02468]") → match("[0-9]*[02468]") } }',
        ) as never,
    )
    assertEquals(report?.cost.render(), "4")
})
