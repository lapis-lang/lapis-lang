/**
 * LC Operation Symbols — the operation signature environment `Ω` and named
 * operation application support.
 *
 * See _docs/theory/lc.md §2.2, §2.4, §2.5 (Ω's conditions), §3 (E-Op/E-OpArg), §5.8 (T-Op).
 *
 *   Ω ::= ∅ | Ω, op:σ₁→...→σₙ→τ    operation signature (name ↦ argument/result types)
 *
 * `op(t₁, ..., tₙ)` is the application of a _named operation_ — the symbolic
 * identity of a fold declared in the surface language. It is _definitional_
 * sugar: `Ω` maps each operation name to its defining LC term, so the
 * application computes by applying the definition. The named form exists so
 * that operation identity survives `let`-inlining and substitution — an
 * optimizer can recognize two occurrences as the same algebraic operation,
 * which anonymous folds cannot express.
 *
 * ## Ω-acyclicity (declaration-order stratification)
 *
 * An operation may only reference operations declared **earlier** in `Ω`.
 * Every `op` application then terminates by induction on declaration order:
 * op _N_'s handlers call only ops _1..N-1_, each of which terminates on all
 * inputs by induction. Without the rule, a handler calling another operation
 * by name could cycle (`op A` calls `op B` calls `op A`), reintroducing
 * general recursion through `Ω` — termination would depend on a semantic
 * measure that is not syntactically visible.
 *
 * The check is a decidable dependency-graph condition, evaluated once per
 * declaration (stratification-class, the same family as Datalog's negation
 * stratification) — not a per-program semantic measure checker. It costs
 * nothing at evaluation time.
 *
 * ## Detection: lexical scan of the definition source
 *
 * In LC concrete syntax, a camelCase identifier immediately followed by `(` is
 * unambiguously a named operation application: variable application requires
 * whitespace (`f x`, never `f(x)`), and variant construction is PascalCase
 * (`Zero()`). The declaration-time check therefore scans the definition source
 * for that pattern and rejects references to operation names not already in
 * `Ω` (self-reference, forward reference, and cycles alike).
 *
 * The scan is **lexical, not token-level — by design and by necessity**:
 * `declare` runs before any parsing infrastructure exists (`Ω` is populated
 * before grammars are constructed — the grammar holds the registry), so the
 * check must be grammar-independent. This is exact for the current LC
 * concrete syntax, which has no string literals and no comments — the only
 * camelCase-ident-then-paren forms are op applications and the built-in
 * `match("p")` form (excluded below). If a future syntax revision adds string
 * literals, comments, or other call-shaped constructs, the exclusion list
 * (or the scan itself) must be updated — until then, every match the scan
 * reports is a genuine op application.
 */

import { FunType, type Type } from "./types.ts"

/**
 * The signature/definition well-formedness condition that a sealed operation
 * carries (lc.md §2.5, well-formedness): the definition types as
 * `paramTypes → resultType`.
 *
 * The registry cannot check this itself — checking requires the type checker,
 * and `ops.ts` cannot import it (cycle: `typing_grammar` → `grammar` →
 * `ops`). The check is therefore injected at declaration time (`declare`),
 * and the grammars accept **only sealed operations** (`CheckedOpSig`), making
 * the condition a type-level guarantee rather than a runtime convention.
 */
export interface OpWellFormedness {
    /**
     * Check that `definition` types as `paramTypes → resultType`. Return a
     * reason string when it does not; `undefined` when it does.
     */
    checkDefinition(op: OpSig): string | undefined
}

/**
 * An operation whose definition has been validated against its signature —
 * the definition types as `paramTypes → resultType` (lc.md §2.5, well-formedness).
 *
 * Produced exclusively by `OpRegistry.declare` (which runs the injected
 * well-formedness check); every entry the grammars read from `Ω` has this
 * type, so a signature/definition mismatch cannot enter Ω through the
 * public API. Unvalidated `OpSig`s remain constructible (for building
 * declarations to submit to `declare`) but cannot be installed.
 */
export interface CheckedOpSig extends OpSig {
    /** Marker: the well-formedness check has passed. */
    readonly checked: true
}

/** Brand a validated `OpSig` as checked (registry-internal). */
const brandChecked = (op: OpSig): CheckedOpSig => Object.assign(op, { checked: true as const })

/**
 * Language-level call forms — call-shaped (`name(...)`), camelCase, and part
 * of the language rather than members of `Ω`. A closed vocabulary, like the
 * law catalog: entries exist only when the grammar itself defines a call
 * form.
 *
 * Serves two coupled purposes, and the coupling is what makes each sound:
 *
 * - **Reserved from operation names** (`declare` rejects an op named with
 *   one). An op named `match` would be indistinguishable from the
 *   pattern-matched construction `match("p")` (lc.md §2.2, T-Pattern) —
 *   worse, once in Ω the `opProd` registry gate would shadow the language
 *   form for every subsequent parse. The same parseability rationale as the
 *   camelCase name-shape check: a name that cannot be a distinct op
 *   application cannot be an op name.
 * - **Excluded from the dependency scan** (`referencedOps`). Because the
 *   names are reserved from operations, an occurrence of `match(` in a
 *   definition is always the language form, never an op application — the
 *   exclusion can never suppress a genuine op reference.
 *
 * - `match` — the pattern-matched construction `match("p")`
 *   (lc.md §2.2, T-Pattern — `patternMatchProd`), introduced by the grammar's
 *   pattern gate, not an operation.
 */
const BUILTIN_CALL_FORMS: readonly string[] = ["match"]

// ── Operation names in core text: the `#` sigil ──────────────────────────────

/**
 * The sigil that marks a core-text operation application: `#add(a, b)`.
 *
 * Every operation application in core concrete syntax carries it, whether the
 * name is symbolic (`#+(a, b)`) or alphanumeric (`#add(a, b)`). One rule, so
 * `renderOperationName`/`parseOperationName` are total and mutually inverse
 * with no conditionals and no symbol table.
 *
 * **Why a sigil at all.** An operation's name is whatever the source declared
 * — `+` is a name in its own right, not an alias of `add` (`lc.md` §2.2: the
 * named form *is* "the symbolic identity of a fold"). Without a sigil, `+`
 * has no spelling in core text whose grammar admits only
 * identifiers, and `add(a, b)` is ambiguous with variable application until
 * the registry says otherwise. The sigil resolves both at the lexeme.
 *
 * **Why `#` and not a bracket form.** The sigil must be *unspellable from the
 * surface*: a name a user declaration can produce would let a program capture
 * core-owned vocabulary. No surface operator-character set contains `#`
 * (`surface-grammar.md` §2.3: contiguous runs of `+ - * / < > = ! ? & | , .`),
 * so `#+` and `#add` are outside the surface's name grammar. A bracketed form
 * like `(+)` is spellable the moment `(` and `)` join the operator set — and
 * every candidate bracket (`(` `)` `[` `]` `{` `}`) is core syntax, so
 * admitting it would overlap the operator alphabet with the delimiter
 * alphabet. The same reasoning spells the core-owned raw-text type `@Token`
 * (`lc.md` §2.1), which names `#name` as this sigil's precedent.
 *
 * **Why uniform.** The alternative — a sigil only on symbolic names — needs an
 * `isSymbolic` test at every text boundary (render, parse, gate, scan, and the
 * law machinery's interpolations), and each test is a place the two sides can
 * disagree. Uniform also buys a parse that does not consult `Ω`: the sigil
 * makes an operation application syntactically identifiable, whereas a bare
 * `name(args)` is one only when the registry already holds the name.
 *
 * **The surface's own `#`.** The surface uses `#` in two places — a spec
 * record's `aux #name` entry and a law argument's keyword-part reference
 * (`identity: #add`). Both denote an operation, so under this rule they are
 * the *same* form as an application rather than a third kind of thing
 * (`overview.md` §12.23 records the reference-vs-value distinction).
 */
export const OP_NAME_SIGIL = "#"

/**
 * The core-text spelling of an operation name — `add` → `#add`.
 *
 * Total and injective: distinct names never share a spelling, which is what
 * lets core text round-trip through a parser without a side table.
 */
export function renderOperationName(name: string): string {
    return `${OP_NAME_SIGIL}${name}`
}

/**
 * The operation name a core-text lexeme denotes — `#add` → `add`.
 *
 * Inverse of `renderOperationName`. Returns `undefined` for a lexeme without
 * the sigil, which is how the parser distinguishes an operation application
 * from variable application.
 */
export function parseOperationName(lexeme: string): string | undefined {
    return lexeme.startsWith(OP_NAME_SIGIL) ? lexeme.slice(OP_NAME_SIGIL.length) : undefined
}

/**
 * The characters a symbolic operation name may be built from
 * (`surface-grammar.md` §2.3). *
 * Two properties hold by choice, and both are load-bearing:
 *
 * - **Disjoint from the core's delimiters.** No character here is `(`, `)`,
 *   `[`, `]`, `{`, `}`, `:`, `\`, or whitespace, so a symbolic name can be
 *   written adjacent to the syntax that surrounds it. This is why the surface
 *   spec's prose mention of "grouping characters" (`surface-syntax.md` §2.1)
 *   is not implementable: admitting brackets would overlap the operator
 *   alphabet with the delimiter alphabet, and a maximal-munch run would then
 *   swallow the delimiters (`(+)` would lex as one name).
 * - **Disjoint from the sigil.** `#` is absent, so an operation name can never
 *   begin with the character that marks an application.
 */
export const SYMBOLIC_OP_CHARS: readonly string[] = [
    "+",
    "-",
    "*",
    "/",
    "<",
    ">",
    "=",
    "!",
    "?",
    "&",
    "|",
    ",",
    ".",
]

/**
 * Whether `c` may appear in a symbolic operation name.
 *
 * The one definition: the surface's operator lexeme and the core's
 * operation-name lexeme both read it, so the two alphabets cannot drift.
 */
export function isSymbolicOpChar(c: string): boolean {
    return SYMBOLIC_OP_CHARS.includes(c)
}

/**
 * Whether `name` is a well-formed operation name.
 *
 * Two disjoint classes, both of which are *names the surface can declare*:
 *
 * - **camelCase** — an identifier: `add`, `_aux`, `fold` (keywords are
 *   allowed; the op form's sigil and tight paren are positionally disjoint
 *   from every keyword position).
 * - **symbolic** — a contiguous run of `SYMBOLIC_OP_CHARS`: `+`, `<=`, `<+>`.
 *
 * Neither class admits a character that is core syntax (a bracket, a comma, a
 * dot, a colon), which is what keeps the emitted text parseable. A PascalCase
 * name is rejected because it would collide with the variant namespace.
 */
export function isOperationName(name: string): boolean {
    if (name === "") return false
    if (/^[a-z_][a-zA-Z0-9_]*$/.test(name)) return true
    return [...name].every(isSymbolicOpChar)
}

/**
 * Scan concrete-syntax source for named operation applications — the shared
 * op-reference scanner.
 *
 * An operation application is spelled with the sigil: `#add(a, b)`. The sigil
 * makes the scan **exact**, not approximate:
 *
 * - No other form in LC concrete syntax begins with `#`, so the pattern cannot
 *   match a variant construction (`Zero()`), a variable, or the name in a
 *   `@Token` type.
 * - Nothing must be excluded. `match("p")` is a language call form, not an
 *   operation, and it is not sigilled either — `BUILTIN_CALL_FORMS` therefore
 *   needs no special case here.
 * - Symbolic names need no separate treatment: `#+(a, b)` and `#add(a, b)`
 *   differ only in the characters between the sigil and the paren.
 *
 * **Quoted pattern sources are removed before matching.** A pattern's text is
 * not source code: `data Tag / pattern #\w+` declares text a token matches,
 * and a source containing `#name(` would otherwise be reported as an operation
 * reference. The scan strips double-quoted spans first, so its exactness does
 * not depend on which characters a pattern happens to use.
 *
 * **Why a lexical scan at all.** Ω's acyclicity check runs before parsing
 * infrastructure exists (`Ω` is populated before grammars are constructed), so
 * the check must be grammar-independent. The sigil is what makes a lexical
 * scan exact: the pattern is anchored by a character no other production uses.
 *
 * **Consumers:** `OpRegistry.declare`'s acyclicity check (the declaration-
 * order stratification). The derivation engine's axiom-base scan does NOT
 * use this function: it scans PARSED handler bodies at the term level
 * (`derivation.ts`'s `freeOps` — the ops an obligation's `op` applications
 * name), so the two scans operate at different levels (lexical source vs.
 * parsed terms). They agree because the reader parses exactly the concrete
 * syntax this scan recognizes.
 *
 * **Over-approximation risk:** none. The sigil is unambiguous, and the
 * character class is closed (no whitespace, no delimiters), so every match is
 * a genuine application.
 */
export function scanOpReferences(source: string): Set<string> {
    const referenced = new Set<string>()
    // A pattern's quoted source is text, not code (see the docblock).
    const unquoted = source.replace(/"(?:[^"\\]|\\.)*"/g, '""')
    // `#` then a maximal run of non-whitespace, non-delimiter characters, then `(`
    const opCall = /#([^\s(),[\]{}:;.\\]+)\(/g
    for (const match of unquoted.matchAll(opCall)) {
        const name = match[1]
        if (name !== undefined) referenced.add(name)
    }
    return referenced
}

// ── Operation signature ───────────────────────────────────────────────────────

/**
 * An operation signature: `op : σ₁ → ... → σₙ → τ`.
 *
 * The `definition` is the operation's defining LC term, as concrete-syntax
 * source. It is evaluated on demand (E-Op applies it to the argument values);
 * it is never inlined into the parse input, so the named form stays
 * recognizable to law-aware passes.
 */
export class OpSig {
    constructor(
        readonly name: string,
        readonly paramTypes: Type[],
        readonly resultType: Type,
        /** The defining LC term, as concrete-syntax source text. */
        readonly definition: string,
    ) {}

    /**
     * The full signature type `σ₁ → ... → σₙ → τ`.
     *
     * Not consumed by the core: T-Op checks the premises field-wise and E-Op
     * applies the definition, so neither needs the assembled function type.
     * It exists for the law machinery — law screening and derivation
     * discharge query an operation's signature as a single type (e.g. to
     * check that a `distributive:⊕` law's two operations have composable
     * signatures) — and for tools that print or compare signatures.
     */
    get signature(): Type {
        let result = this.resultType
        for (let i = this.paramTypes.length - 1; i >= 0; i--) {
            result = new FunType(this.paramTypes[i]!, result)
        }
        return result
    }
}

// ── Declaration errors ─────────────────────────────────────────────────────────

/**
 * A declaration failure: the operation name and the failed check's reason.
 * `declare` throws this on any failed check (name shape, built-in call
 * form, duplicate, acyclicity, well-formedness) — a rejected declaration is
 * an exceptional outcome for the caller, who stated the declaration as a
 * fact; the reason identifies the failed check.
 */
export class OpDeclarationError extends Error {
    constructor(
        readonly opName: string,
        readonly reason: string,
    ) {
        super(`operation "${opName}": ${reason}`)
        this.name = "OpDeclarationError"
    }
}

// ── The operation registry (Ω) ────────────────────────────────────────────────

/**
 * `Ω` — the operation signature environment. Maps operation names to their
 * signatures and defining terms, in declaration order.
 *
 * The registry is append-only: `declare` adds an operation at the end of the
 * declaration order, and the acyclicity check runs against the operations
 * already present. This makes `Ω` acyclic by construction.
 *
 * **The trust boundary:** every entry in `Ω` is a `CheckedOpSig` — its
 * definition has been validated against its signature (the definition types
 * as `paramTypes → resultType`). The validation is injected
 * (`OpWellFormedness`) because the registry cannot type-check itself
 * (`ops.ts` cannot import the type checker — that would be a cycle through
 * `grammar.ts`). The grammars read only checked entries, so T-Op's trust in
 * `resultType` and E-Op's execution of `definition` can never diverge —
 * without this check, a mismatched declaration would type-check as one
 * thing and evaluate as another, a Preservation violation through Ω.
 */
export class OpRegistry {
    private readonly ops = new Map<string, CheckedOpSig>()
    /** Declaration order — the stratification order for the acyclicity check. */
    private readonly order: string[] = []

    /**
     * Declare an operation: run every declaration-time check and install the
     * sealed operation. Returns the `CheckedOpSig` (branded, validated).
     *
     * Checks:
     *
     * 1. **Name shape** — an operation name the surface can declare:
     *    camelCase (matching the `opIdent` lexeme) or a symbolic run
     *    (`surface-grammar.md` §2.3). A PascalCase name is rejected because it
     *    would collide with the variant namespace and never parse as an op
     *    application. Reserved words are allowed: the op form's sigil and tight
     *    paren are positionally disjoint from every keyword position, so an
     *    operation named `fold` is appliable (`#fold(a, b)`).
     * 1b. **Built-in call forms** — `match` (and any future call form) are
     *    reserved from operation names: an op so named would be
     *    indistinguishable from the language form `match("p")`.
     * 2. **Duplicate** — redeclaring an operation name is rejected; the
     *    signature and definition would silently diverge.
     * 3. **Acyclicity** — the definition may only reference operations already
     *    declared in `Ω` (declaration-order stratification). Self-reference,
     *    forward reference, and cycles are all rejected here.
     * 4. **Well-formedness** — the definition types as
     *    `paramTypes → resultType`. Mandatory, not optional: an entry in `Ω`
     *    carries the guarantee. The checker is injected (see the class doc);
     *    a test or embedding that does not care about typing can inject a
     *    permissive checker explicitly.
     *
     * The definition is type-checked under the operations **already
     * declared** (acyclicity ran first), so a definition referencing an
     * earlier operation checks against it — declare in dependency order.
     *
     * @throws OpDeclarationError on any failed check.
     */
    declare(op: OpSig, wellFormedness: OpWellFormedness): CheckedOpSig {
        // 1. Name shape: camelCase or symbolic — the two classes the surface
        //    declares and the emitted core text parses.
        if (!isOperationName(op.name)) {
            throw new OpDeclarationError(
                op.name,
                "not a valid operation name — expected camelCase or a symbolic run " +
                    "(`surface-grammar.md` §2.3)",
            )
        }

        // 1b. Built-in call forms are reserved from operation names: an op
        //     named `match` would be indistinguishable from the language's
        //     `match("p")` form. The sigil disjoints an application from that
        //     form, but the bare name would still be ambiguous inside a spec
        //     record or a law argument, where `#name` denotes the operation.
        if (BUILTIN_CALL_FORMS.includes(op.name)) {
            throw new OpDeclarationError(
                op.name,
                "reserved for the built-in call form — an operation of this name would be " +
                    "indistinguishable from the language form",
            )
        }

        // 2. Duplicate: redeclaration is rejected.
        if (this.ops.has(op.name)) {
            throw new OpDeclarationError(op.name, "operation is already declared in Ω")
        }

        // 3. Acyclicity: the definition may only reference earlier operations.
        for (const referenced of scanOpReferences(op.definition)) {
            if (referenced === op.name) {
                throw new OpDeclarationError(
                    op.name,
                    "self-reference — an operation may only reference operations declared earlier in Ω",
                )
            }
            if (!this.ops.has(referenced)) {
                throw new OpDeclarationError(
                    op.name,
                    `references "${referenced}", which is not declared earlier in Ω ` +
                        "(forward reference or cycle — declaration-order stratification)",
                )
            }
        }

        // 4. Well-formedness: the definition types as the declared signature.
        //    T-Op trusts `resultType`; E-Op executes the raw `definition`;
        //    without this check a mismatched declaration type-checks as one
        //    thing and evaluates as another.
        const reason = wellFormedness.checkDefinition(op)
        if (reason !== undefined) {
            throw new OpDeclarationError(op.name, `definition is not well-formed: ${reason}`)
        }

        const sealed = brandChecked(op)
        this.ops.set(op.name, sealed)
        this.order.push(op.name)
        return sealed
    }

    /** Look up an operation by name (always a checked entry). */
    lookup(name: string): CheckedOpSig | undefined {
        return this.ops.get(name)
    }

    /** All declared operations, in declaration order (all checked). */
    all(): CheckedOpSig[] {
        return this.order.map((name) => this.ops.get(name)!)
    }
}
