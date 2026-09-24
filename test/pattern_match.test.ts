/**
 * Pattern-matched construction tests — the `match("p")` introduction form
 * (T-Pattern / E-Pattern, lc.md §5.1 + §2.3) over pattern-matched data types.
 *
 * Two introduction routes exist for a pattern type's token: the bare `Ident`
 * atom (T-Token — the registry-gated token, `patternTokenProd`) and the
 * explicit `match("p")` form (T-Pattern — the pattern-carrying constructor,
 * `patternMatchProd`). These tests pin the explicit form's premises (parse,
 * anchoring, declared-on-type), its evaluation to a `TokenVal`, the
 * interaction surface (op gate, reserved name, variable application), and the
 * sibling token atom's unchanged behavior.
 */

import {
    DefinitionShapeError,
    LCEval,
    LCTypeCheck,
    OpRegistry,
    OpSig,
    readDefShape,
    readRejectedConstruct,
    TokenVal,
    TypeRegistry,
    TypeRegistryError,
    ValueEnv,
} from "../src/index.ts"

import { Any, FunType, TypeEnv } from "../src/core/types.ts"

import { parsePattern } from "../src/core/pattern_lang.ts"

import { VariantVal } from "../src/core/values.ts"

import { assert, assertEquals, assertThrows } from "@std/assert"

import { createPatternType } from "./fixtures.ts"

// ── Fixtures ─────────────────────────────────────────────────────────────────

/** A harness: fresh registries + bound checker/evaluator per test. */
function patternHarness(
    types: { name: string; patterns: readonly string[] }[] = [
        { name: "NatPat", patterns: ["[0-9]+"] },
    ],
) {
    const registry = new TypeRegistry()
    const instances = types.map((t) => {
        const instance = createPatternType(t.name, t.patterns)
        registry.register(instance)
        return instance
    })
    const opRegistry = new OpRegistry()
    const tc = new LCTypeCheck().setRegistry(registry).setOpRegistry(opRegistry)
    const ev = new LCEval().setRegistry(registry).setOpRegistry(opRegistry)
    return {
        registry,
        opRegistry,
        tc,
        ev,
        typeOf: (name: string) => instances.find((t) => t.name === name)!,
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

// ── T-Pattern: well-typed introductions ──────────────────────────────────────

Deno.test('T-Pattern: match("[0-9]+") types as the declaring NatPat', () => {
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match("[0-9]+")'), h.typeOf("NatPat"))
})

Deno.test("T-Pattern: canonical comparison — an equivalent spelling of one class parses", () => {
    // The declared-vs-explicit comparison is CANONICAL (patternToString
    // normalization): the class renders as its collapsed ranges (`[0-9]`, not
    // `[0123456789]`), so two spellings of one class AST agree.
    const h = patternHarness([{ name: "DigitPat", patterns: ["[0123456789]"] }])
    assertEquals(typeOfOne(h, 'match("[0-9]")'), h.typeOf("DigitPat"))
})

Deno.test("T-Pattern: a distinct AST is NOT the declared pattern (rejected)", () => {
    // `0123456789` parses to a CONCAT of ten chars — a different AST (and a
    // different canonical source) from any declared class. No type declares
    // it. Likewise the declared `[0-9]+` is a PLUS of a class — a BARE class
    // `[0-9]` is a different pattern entirely.
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match("0123456789")'), undefined)
    assertEquals(typeOfOne(h, 'match("[0-9]")'), undefined)
})

Deno.test("T-Pattern: multiple pattern types resolve to the declaring type", () => {
    const h = patternHarness([
        { name: "NatPat", patterns: ["[0-9]+"] },
        { name: "EvenPat", patterns: ["[0-9]*[02468]"] },
    ])
    assertEquals(typeOfOne(h, 'match("[0-9]+")'), h.typeOf("NatPat"))
    assertEquals(typeOfOne(h, 'match("[0-9]*[02468]")'), h.typeOf("EvenPat"))
})

Deno.test("T-Pattern: a type reference pattern (<T>) is anchored and resolves", () => {
    // `<NatPat>` — a typeref pattern: anchored (it resolves to another
    // declared pattern), and declared on the referencing type.
    const h = patternHarness([
        { name: "NatPat", patterns: ["[0-9]+"] },
        { name: "RefPat", patterns: ["<NatPat>"] },
    ])
    assertEquals(typeOfOne(h, 'match("<NatPat>")'), h.typeOf("RefPat"))
})

// ── T-Pattern premises ───────────────────────────────────────────────────────

Deno.test("T-Pattern: an undeclared pattern is rejected (empty forest)", () => {
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match("[a-z]+")'), undefined)
})

Deno.test("T-Pattern: a pattern no registered type declares is rejected", () => {
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match("[0-9]+")'), h.typeOf("NatPat"))
    // With the pattern types unregistered, the gate has no owner to resolve
    // through — the branch declines.
    const emptyRegistry = new TypeRegistry()
    const bare = new LCTypeCheck().setRegistry(emptyRegistry)
    assertEquals([...bare.parseWith('match("[0-9]+")', new TypeEnv())].length, 0)
})

Deno.test("TypeRegistry: registration is final — a duplicate type name is rejected", () => {
    // The reverse indexes (variant/observer/pattern) are built incrementally
    // and keyed by NON-type names, so a same-named re-registration would
    // overwrite the `types` entry while the pattern index kept pointing at
    // the PRIOR instance — a stale pattern→type mapping no lookup could
    // surface. Registration is final (the OpRegistry.declare duplicate
    // policy): replacement is an error, not a hazard.
    const registry = new TypeRegistry()
    const first = createPatternType("Pat", ["[0-9]+"])
    registry.register(first)
    assertThrows(
        () => registry.register(createPatternType("Pat", ["[a-z]+"])),
        TypeRegistryError,
        "already registered",
    )
    // The FIRST registration stays authoritative — nothing was overwritten.
    assertEquals(registry.lookup("Pat"), first)
    assertEquals(registry.lookupPatternSource("[0-9]+"), first)
})

Deno.test("TypeRegistry: a duplicate across kinds is also rejected (same name, any kind)", () => {
    // The finality holds across kinds: a DataType, a CodataType, and a
    // DataType share the one name-keyed map.
    const registry = new TypeRegistry()
    const nat = createPatternType("NatPat", ["[0-9]+"])
    registry.register(nat)
    // Re-registering the SAME instance is also a duplicate (the name is
    // taken — idempotent registration is not offered, keeping the
    // first-declared-wins tie-break honest).
    assertThrows(
        () => registry.register(nat),
        TypeRegistryError,
    )
    // A distinct DataType with the same name — rejected too.
    assertThrows(
        () => registry.register(createPatternType("NatPat", ["[a-z]+"])),
        TypeRegistryError,
    )
})

Deno.test("TypeRegistry: a revised type set goes through a fresh registry", () => {
    // The supported replacement workflow: construct a new registry. The
    // pattern index keys map by identity per registry — the old registry's
    // indexes stay self-consistent, and the new one builds from scratch.
    const old = new TypeRegistry()
    const natV1 = createPatternType("NatPat", ["[0-9]+"])
    old.register(natV1)
    const fresh = new TypeRegistry()
    const natV2 = createPatternType("NatPat", ["[0-9]*"])
    fresh.register(natV2)
    // The fresh registry resolves the revised declaration, with no stale
    // entry from the old one.
    assertEquals(fresh.lookup("NatPat"), natV2)
    assertEquals(fresh.lookupPatternSource("[0-9]*"), natV2)
    assertEquals(fresh.lookupPatternSource("[0-9]+"), undefined)
    // And the old registry is unchanged (its own index, its own truth).
    assertEquals(old.lookup("NatPat"), natV1)
    assertEquals(old.lookupPatternSource("[0-9]+"), natV1)
})

Deno.test("T-Pattern: the anchoring check tolerates a (theoretically) empty concat", () => {
    // `parsePattern` never produces an empty concat (a concat node requires
    // at least one parsed atom — an exhausted source throws first), so the
    // anchoring walk's first-part read cannot crash in practice. The walk
    // nonetheless treats an empty concat as UNANCHORED (a pattern matching
    // nothing anchors nothing) rather than trusting the cross-module
    // invariant with a bare `!`. The gate is probed through the parser's
    // output: no reachable input builds an empty concat, so this pins the
    // DECLARED contract via the sibling shapes (the single-atom and
    // multi-part concats) and leaves the guard unexercised-but-documented.
    const h = patternHarness([
        { name: "TwoCharPat", patterns: ["ab"] },
        { name: "CharPat", patterns: ["a"] },
    ])
    // A multi-part concat anchors at its first part (the literal `a`).
    assertEquals(typeOfOne(h, 'match("ab")'), h.typeOf("TwoCharPat"))
    // A single-atom pattern parses to the ATOM itself (a passthrough, not a
    // 1-part concat) — the anchoring walk never even sees a concat here.
    assertEquals(typeOfOne(h, 'match("a")'), h.typeOf("CharPat"))
})

Deno.test("T-Pattern: an unanchored pattern is rejected", () => {
    // surface-syntax.md §1.3: a pattern must start with a specific literal or
    // class — the rejected shape is a leading `.` (any). The check descends
    // through the postfix wrappers to the FIRST ATOM: `Nat = [0-9]+` anchors
    // at its class (the canonical carrier), while a bare `.` has no specific
    // start atom.
    const h = patternHarness([
        { name: "NatPat", patterns: ["[0-9]+"] },
        // The unanchored shape IS declared on some type — the anchoring
        // premise, not the declared premise, rejects the term.
        { name: "AnyPat", patterns: ["."] },
    ])
    assertEquals(typeOfOne(h, 'match(".")'), undefined, "a leading `.` is unanchored")
    // The postfix wrappers are transparent: a star/plus/opt over a class
    // anchors at the class.
    const starH = patternHarness([
        { name: "StarPat", patterns: ["[0-9]*"] },
        { name: "OptPat", patterns: ["[0-9]?"] },
        { name: "PlusPat", patterns: ["[0-9]+"] },
    ])
    assertEquals(typeOfOne(starH, 'match("[0-9]*")'), starH.typeOf("StarPat"))
    assertEquals(typeOfOne(starH, 'match("[0-9]?")'), starH.typeOf("OptPat"))
    assertEquals(typeOfOne(starH, 'match("[0-9]+")'), starH.typeOf("PlusPat"))
    // But the bare token atom for the unanchored-declared type still works
    // (T-Token's premise is registry membership only — anchoring is
    // T-Pattern's premise).
    assertEquals(typeOfOne(h, "AnyPat"), h.typeOf("AnyPat"))
})

Deno.test("T-Pattern: a malformed pattern source is a rejection, not a throw", () => {
    // `[0-9` is an unterminated class — the parse error is caught by the
    // gate and the branch is rejected (empty forest), never thrown out of
    // the checker.
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match("[0-9")'), undefined)
})

Deno.test("T-Pattern: the empty pattern source is rejected", () => {
    // parsePattern rejects the empty pattern (a variant must consume at least
    // one character) — the gate rejects before the declaration check.
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match("")'), undefined)
})

Deno.test("T-Pattern: a pattern whose language nothing declares but text parses — canonical gate", () => {
    // A pattern must be declared CANONICALLY: the parsed AST's rendering must
    // match a declared pattern's rendering. An escaped-metacharacter spelling
    // of a declared class does not agree (`\\+` is a different AST from a
    // class) unless a type declares it that way.
    const h = patternHarness([{ name: "PlusPat", patterns: ["\\+"] }])
    assertEquals(typeOfOne(h, 'match("\\\\+")'), h.typeOf("PlusPat"))
})

Deno.test("TypeRegistry: the declared patterns are frozen (no post-registration drift)", () => {
    // The registry's pattern index is built once at registration; a mutable
    // declaration array would let a post-registration `patterns.push` /
    // splice drift the index from the type's own declaration (removed
    // patterns staying constructible, added patterns being rejected).
    // `DataType` freezes the array — a mutation attempt either throws
    // (strict mode) or silently no-ops, and the index stays consistent with
    // the type's declarations either way.
    const registry = new TypeRegistry()
    const nat = createPatternType("NatPat", ["[0-9]+"])
    registry.register(nat)
    // The frozen array: the type's declarations cannot be extended.
    const before = nat.patterns.length
    try {
        ;(nat.patterns as unknown as unknown[]).push(parsePattern("[a-z]+"))
    } catch {
        // Strict-mode throw is fine — either way the array is unchanged.
    }
    assertEquals(nat.patterns.length, before, "the declaration array is frozen")
    assertEquals(
        registry.lookupPatternSource("[a-z]+"),
        undefined,
        "the index did not see the (rejected) mutation",
    )
    assertEquals(
        registry.lookupPatternSource("[0-9]+"),
        nat,
        "the original declaration still resolves",
    )
    // The declared pattern itself is still constructible (no false decline).
    const h = patternHarness([{ name: "NatPat", patterns: ["[0-9]+"] }])
    assertEquals(typeOfOne(h, 'match("[0-9]+")'), h.typeOf("NatPat"))
})

// ── Concrete-syntax surface ──────────────────────────────────────────────────

Deno.test("T-Pattern: whitespace around the payload parses (ws is internal)", () => {
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match( "[0-9]+" )'), h.typeOf("NatPat"))
})

Deno.test("T-Pattern: a spaced paren is NOT the pattern form (tight paren)", () => {
    // `match ("…")` — space before the paren — is variable application (or an
    // unbound variable error), never the pattern form. The op form's
    // positional-disjointness discipline.
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match ("[0-9]+")'), undefined)
})

Deno.test("T-Pattern: an escaped delimiter quote parses and round-trips", () => {
    // `match("\"<Char>*\"")` — the pattern source `"<Char>*"` with the
    // delimiter quotes escaped. The payload is the pattern language's own
    // source (the quote chars are pattern literals here).
    //
    // The payload's `<Char>` parses as a TYPE REFERENCE (a `<Ident>`-shaped
    // span is the typeref syntax — not a literal), so the resolvability
    // premise requires `Char` to be a registered pattern type: the gate
    // rejects a pattern whose type references do not resolve (a token whose
    // language the registry cannot enumerate). The fixture registers it.
    const h = patternHarness([
        { name: "Char", patterns: ['[^"]'] },
        { name: "StringPat", patterns: ['"<Char>*"'] },
    ])
    const result = typeOfOne(h, 'match("\\"<Char>*\\"")')
    assertEquals(result, h.typeOf("StringPat"))
})

Deno.test("T-Pattern: a typeref to an unregistered pattern type is rejected", () => {
    // The resolvability premise (surface-syntax.md §1.3's type-reference
    // rule): a pattern's type references must resolve to registered pattern
    // types — recursively. `<Missing>` names no registered type, so the
    // gate rejects the term (an unresolvable reference would introduce a
    // token whose language the registry cannot enumerate — the constructor
    // would be accepted with an unknowable language).
    const h = patternHarness([{ name: "RefPat", patterns: ["<Missing>"] }])
    assertEquals(typeOfOne(h, 'match("<Missing>")'), undefined)
})

Deno.test("T-Pattern: a typeref to an UNANCHORED declared pattern is rejected", () => {
    // The transitive anchoring premise: a reference is anchored only when
    // its target's declared patterns are — `<AnyRefPat>` declares the
    // pattern `<AnyPat>` whose TARGET declares an unanchored pattern (`.`),
    // so the gate rejects the referencing term (the anchoring obligation
    // the declaration machinery skipped is owned here — the reference's
    // language is the target's, and the target's language is unanchored).
    const h = patternHarness([
        { name: "AnyPat", patterns: ["."] },
        { name: "AnyRefPat", patterns: ["<AnyPat>"] },
    ])
    assertEquals(typeOfOne(h, 'match("<AnyPat>")'), undefined)
    // The bare token atom for the unanchored-declared type still works
    // (T-Token's premise is registry membership only).
    assertEquals(typeOfOne(h, "AnyPat"), h.typeOf("AnyPat"))
})

Deno.test("T-Pattern: a typeref chain resolves transitively", () => {
    // A reference to a type whose OWN references resolve: the walk follows
    // the chain (cycle-safe — a self-reference is accepted once the type is
    // on the seen list, since its own patterns were validated at its gate
    // visit).
    const h = patternHarness([
        { name: "NatPat", patterns: ["[0-9]+"] },
        { name: "RefPat", patterns: ["<NatPat>"] },
        { name: "RefRefPat", patterns: ["<RefPat>"] },
    ])
    assertEquals(typeOfOne(h, 'match("<RefPat>")'), h.typeOf("RefRefPat"))
    assertEquals(typeOfOne(h, 'match("<NatPat>")'), h.typeOf("RefPat"))
})

Deno.test("T-Pattern: a variable named match is a variable (Γ gate)", () => {
    // `match` is a legal camelCase `ident`: a λ-bound `match` variable is an
    // ordinary variable reference, and its APPLICATION (`match "…"` with
    // whitespace) is variable application. The pattern form needs the tight
    // paren.
    const h = patternHarness()
    const bound = new TypeEnv().extend("match", h.typeOf("NatPat"))
    // `\match:NatPat. match` — the variable reference (not the pattern form,
    // which needs the paren).
    const result = typeOfOne(h, "\\match:NatPat. match", bound)
    assert(
        result instanceof FunType,
        "a λ-bound `match` types as the lambda's function type",
    )
    assertEquals(result?.result, h.typeOf("NatPat"))
})

// ── E-Pattern: evaluation ────────────────────────────────────────────────────

Deno.test('E-Pattern: match("[0-9]+") evaluates to the pattern token', () => {
    const h = patternHarness()
    const value = evalOne(h, 'match("[0-9]+")')
    assert(value instanceof TokenVal, "the value is a TokenVal")
    const token = value as TokenVal
    assertEquals(token.dataTypeName, "NatPat")
    // The token's text is the CANONICAL pattern source (patternToString —
    // the declared pattern's identity, lifted one level from the bare
    // atom's text = name). For an already-canonical spelling the two agree.
    assertEquals(token.text, "[0-9]+")
})

Deno.test("E-Pattern: equivalent spellings introduce EQUAL tokens (canonical text)", () => {
    // The token's text/size are the DECLARED pattern's canonical source, not
    // the caller's spelling: `match("[0123456789]")` and `match("[0-9]")`
    // against the same declaration introduce EQUAL tokens (same type name,
    // same canonical text, same size) — the constructor is the pattern, and
    // the pattern's identity is its canonical form.
    const h = patternHarness([{ name: "DigitPat", patterns: ["[0123456789]"] }])
    const a = evalOne(h, 'match("[0123456789]")') as TokenVal
    const b = evalOne(h, 'match("[0-9]")') as TokenVal
    assertEquals(a.text, b.text, "both carry the canonical source")
    assertEquals(a.text, "[0-9]", "the class renders as its collapsed ranges")
    assertEquals(a.size(), b.size(), "sizes agree (the canonical source's length)")
    assertEquals(a.equals(b), true)
})

Deno.test("E-Pattern: the token identity — two parses are equal values", () => {
    const h = patternHarness()
    const a = evalOne(h, 'match("[0-9]+")')
    const b = evalOne(h, 'match("[0-9]+")')
    assertEquals(a?.equals(b as TokenVal), true)
    // size = the canonical source's length (the token's text-length measure).
    assertEquals(a?.size(), "[0-9]+".length)
})

Deno.test("E-Pattern: the registry gate rejects an undeclared pattern", () => {
    const h = patternHarness()
    assertEquals(evalOne(h, 'match("[a-z]+")'), undefined)
    assertEquals(evalOne(h, 'match("[0-9")'), undefined, "malformed → rejection")
})

Deno.test("E-Pattern: the token round-trips through its rendered source", () => {
    // The renderSource contract: a match-introduced token renders as
    // `match("<pattern>")` (delimiter-escaped), and the render re-evaluates
    // to an equal token.
    const h = patternHarness()
    const value = evalOne(h, 'match("[0-9]+")')
    const rendered = (value as TokenVal).renderSource()
    assertEquals(rendered, 'match("[0-9]+")')
    const reparsed = evalOne(h, rendered!)
    assertEquals(reparsed?.equals(value!), true)
    // The bare-atom sibling renders its own form from the same registry.
    const atomRendered = (evalOne(h, "NatPat") as TokenVal).renderSource()
    assertEquals(atomRendered, "NatPat")
    const atomReparsed = evalOne(h, atomRendered!)
    assertEquals(atomReparsed?.equals(evalOne(h, "NatPat")!), true)
})

Deno.test("renderSource: a direct-constructed token with arbitrary text declines", () => {
    // The route decides: only a token produced by E-Pattern ("pattern"
    // route) renders the match form. A direct-constructed token whose text
    // is arbitrary matched data (the law checker enumerates matched TEXTS —
    // "42" — not pattern sources) has no source form: `match("42")` would
    // NOT re-evaluate (42 is not a declared pattern), and the round-trip
    // judgment never emits a partial render. This is the law_testing.test's
    // original decline contract, now route-qualified.
    const deviant = new TokenVal("NatPat", "42")
    assertEquals(deviant.renderSource(), undefined)
    // The escape-payload token (text = a pattern source) is also declined
    // on the default route — the route, not the text, decides.
    const notIntroduced = new TokenVal("NatPat", "[0-9]+")
    assertEquals(notIntroduced.renderSource(), undefined)
    // And a pattern-route token whose payload needs escaping round-trips
    // through the delimiter escapes.
    const hq = patternHarness([{ name: "StringPat", patterns: ['"<Char>*"'] }])
    const quoted = evalOne(hq, 'match("\\"<Char>*\\"")') as TokenVal
    assertEquals(quoted.renderSource(), 'match("\\"<Char>*\\"")')
    assertEquals(evalOne(hq, quoted.renderSource()!)?.equals(quoted), true)
})

Deno.test("E-Pattern: the bare token atom is unchanged (sibling regression guard)", () => {
    const h = patternHarness()
    // The bare Ident atom still types and evaluates as before.
    assertEquals(typeOfOne(h, "NatPat"), h.typeOf("NatPat"))
    const atomValue = evalOne(h, "NatPat")
    assert(atomValue instanceof TokenVal)
    assertEquals((atomValue as TokenVal).dataTypeName, "NatPat")
    assertEquals((atomValue as TokenVal).text, "NatPat")
})

// ── Interaction surface ──────────────────────────────────────────────────────

Deno.test("T-Pattern: `match(...)` is never an op application (Ω cannot hold the name)", () => {
    // The op gate is tried first (atomProd order) but Ω can never hold
    // `match` (BUILTIN_CALL_FORMS reservation) — the pattern branch owns the
    // form even with a populated Ω.
    const h = patternHarness()
    h.opRegistry.declare(
        new OpSig(
            "add",
            [h.typeOf("NatPat"), h.typeOf("NatPat")],
            h.typeOf("NatPat"),
            "\\x:NatPat. \\y:NatPat. y",
        ),
        h.tc.opWellFormedness,
    )
    assertEquals(typeOfOne(h, 'match("[0-9]+")'), h.typeOf("NatPat"))
})

Deno.test("T-Pattern: an op definition using match(...) declares and evaluates", () => {
    // The definition window (E-Op) opens over the definition source; the
    // pattern branch must parse inside it. `usesMatch` is the fixture the
    // acyclicity-scan tests have been declaring with a permissive checker —
    // now the REAL checker accepts it. The definition is the identity lambda
    // (arity 1) — the op's parameter flows through.
    const h = patternHarness()
    const natPat = h.typeOf("NatPat")
    const sig = h.opRegistry.declare(
        new OpSig("usesMatch", [natPat], natPat, "\\x:NatPat. x"),
        h.tc.opWellFormedness,
    )
    assertEquals(sig.name, "usesMatch")
    // A definition that USES the pattern form: a curried function whose body
    // is the match construction (the definition must type as
    // `paramTypes → resultType` — Ω well-formedness). The op
    // evaluates through the definition window to the token.
    const constSig = h.opRegistry.declare(
        new OpSig("mkToken", [natPat], natPat, '\\x:NatPat. match("[0-9]+")'),
        h.tc.opWellFormedness,
    )
    assertEquals(constSig.name, "mkToken")
    const value = evalOne(h, "mkToken(NatPat)")
    assert(value instanceof TokenVal, "the op's definition evaluates to the token")
    assertEquals((value as TokenVal).text, "[0-9]+")
})

Deno.test("T-Pattern: inside a lambda body the form types and evaluates", () => {
    // A lambda body containing the pattern form types as a function returning
    // the pattern type, and the applied closure evaluates to the token.
    const h = patternHarness()
    const fnType = typeOfOne(h, '\\x:Any. match("[0-9]+")')
    assert(fnType instanceof FunType, "the lambda types as a function")
    assertEquals(fnType?.result, h.typeOf("NatPat"))
    const applied = evalOne(h, '(\\x:Any. match("[0-9]+")) (NatPat)')
    assert(applied instanceof TokenVal, "the applied closure evaluates to the token")
    assertEquals((applied as TokenVal).text, "[0-9]+")
})

Deno.test("T-Pattern: an operand position premise failure rejects the enclosing term", () => {
    // A `match` form whose own premise fails rejects the enclosing let —
    // the sub-term is ill-typed, so the binding is (empty forest).
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'let x:NatPat = match("[a-z]+") in x'), undefined)
})

Deno.test("T-Pattern: a valid match form satisfies the let's declared type", () => {
    const h = patternHarness()
    const result = typeOfOne(h, 'let x:NatPat = match("[0-9]+") in x')
    assertEquals(result, h.typeOf("NatPat"))
})

Deno.test("T-Pattern: Any-typed annotation accepts the pattern type (subsumption)", () => {
    const h = patternHarness()
    const result = typeOfOne(h, 'let x:Any = match("[0-9]+") in x')
    assertEquals(result, Any)
})

Deno.test("T-Pattern: the derivation fragment rejects the construction", () => {
    // The fold-skeleton fragment admits no pattern constructors (the same
    // rejection the bare token atom takes): `matchedPattern` throws
    // DefinitionShapeError naming the form. The reader is reached through
    // `readDefShape` — the same public entry the derivation engine uses —
    // over a real op whose definition body is the match construction.
    // Ω's well-formedness accepts the definition (T-Pattern types the body),
    // so the shape error comes from the FRAGMENT's rejection, not the
    // declaration.
    const h = patternHarness()
    const natPat = h.typeOf("NatPat")
    h.opRegistry.declare(
        new OpSig("shapeProbe", [natPat], natPat, '\\n:NatPat. match("[0-9]+")'),
        h.tc.opWellFormedness,
    )
    const shapeError = assertThrows(
        () => readDefShape(h.opRegistry.lookup("shapeProbe")!, h.registry, h.opRegistry),
        DefinitionShapeError,
    )
    // The rejection names the construct — not a bare parse failure.
    assert(
        shapeError.message.includes("pattern-matched construction"),
        `the diagnostic names the form: ${shapeError.message}`,
    )
})

Deno.test("T-Pattern: the derivation diagnostic escapes the quoted payload (real reader)", () => {
    // The diagnostic quotes the RAW payload as LC SOURCE — the delimiter
    // characters (`"`, `\`) are escaped exactly as `TokenVal.renderSource`
    // escapes them, so the message shows the spelling the definition
    // carries and is re-parsable. A raw interpolation would close the
    // string at the first inner `"` — malformed and misleading.
    //
    // The REAL reader action is exercised (not a reimplementation): the
    // parse driver swallows per-branch action throws, so
    // `readRejectedConstruct` — the derivation module's diagnostic seam —
    // invokes `DerivationReader.matchedPattern` directly.
    const raw = '"<Char>*"'
    const error = assertThrows(
        () => readRejectedConstruct("pattern", ["Pat", raw]),
        DefinitionShapeError,
    )
    // The quoted payload renders escaped — the re-parsable spelling.
    assertEquals(
        error.message,
        'pattern-matched construction (`match("\\"<Char>*\\"")` — a pattern-type constructor)',
    )
    // A backslash-bearing payload escapes too.
    const backslash = assertThrows(
        () => readRejectedConstruct("pattern", ["Pat", "a\\b"]),
        DefinitionShapeError,
    )
    assertEquals(
        backslash.message,
        'pattern-matched construction (`match("a\\\\b")` — a pattern-type constructor)',
    )
    // A plain payload passes through unchanged (the common case stays
    // readable), and the bare-token diagnostic rides the same seam.
    const plain = assertThrows(
        () => readRejectedConstruct("pattern", ["Pat", "[0-9]+"]),
        DefinitionShapeError,
    )
    assertEquals(
        plain.message,
        'pattern-matched construction (`match("[0-9]+")` — a pattern-type constructor)',
    )
    const token = assertThrows(
        () => readRejectedConstruct("token", ["Pat", "Pat"]),
        DefinitionShapeError,
    )
    assertEquals(token.message, "matched token (`Pat` — a pattern-type atom)")
})

Deno.test("E-Pattern: the evaluator's value is distinct from a variant value", () => {
    // A token is not a VariantVal — the kinds stay distinct (the shrinker's
    // structured-value gate and the law checker's screens rely on it).
    const h = patternHarness()
    const value = evalOne(h, 'match("[0-9]+")')
    assert(!(value instanceof VariantVal))
})

Deno.test("T-Pattern: the checker and evaluator agree on the declared-pattern gate", () => {
    // Both grammars bound to the same registry: a term the checker rejects
    // the evaluator rejects too (the same registry identity, the same index).
    const h = patternHarness()
    assertEquals(typeOfOne(h, 'match("[a-z]+")') === undefined, true)
    assertEquals(evalOne(h, 'match("[a-z]+")') === undefined, true)
})
