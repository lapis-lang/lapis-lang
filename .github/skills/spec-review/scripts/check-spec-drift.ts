/**
 * Spec drift probe — the two defects this repository produces most, and that
 * the compiler cannot see.
 *
 * 1. **Type names taught but never declared.** Every PascalCase name in a type
 *    position in `_docs/`, checked against the built-ins, the types the corpus
 *    declares, and the types the fixtures register. This is the `Number` /
 *    `Boolean` / `Object` leak class: `atomType` mints a `TypeVar` for any
 *    unrecognized name, so the checker accepts them all (overview §12.18,
 *    §12.29, §12.31; issue #116).
 *
 * 2. **`data` bodies at a column the grammar does not admit.** L1 requires a
 *    body to be exactly one indent unit (4 spaces) deeper than its header.
 *
 * The probe is TEXTUAL and exhaustive where reading is not. Its output is a list
 * of CANDIDATES TO VERIFY, never findings: it cannot resolve a name declared in
 * another file, cannot tell a variant from a type, and cannot read EBNF.
 *
 * Run:
 *   deno run --allow-read .github/skills/spec-review/scripts/check-spec-drift.ts
 *   deno run --allow-read … --json
 */

// Deno globals only — no imports, so the probe runs from any directory with no
// lockfile, no network, and no dependency resolution.

const ROOT = Deno.cwd()

/**
 * Names that resolve without a declaration.
 *
 * `Any`/`Nothing` are the lattice bounds; `Family`/`Self` are the recursive
 * references — this mirrors `BUILTIN_TYPE_NAMES` in `src/surface/resolve.ts`.
 * `Token` is core-only: not surface-spellable, but it appears in core prose.
 */
const BUILTINS = new Set(["Any", "Nothing", "Family", "Self", "Token"])

/**
 * Capitalized words that appear in prose without ever being type names.
 *
 * A name that survives this list and the declaration checks is still only a
 * candidate. Erring toward silence keeps the probe's output worth reading.
 */

/** Read a directory's entries, or an empty list when it does not exist. */
function entriesOf(dir: string): Deno.DirEntry[] {
    try {
        return [...Deno.readDirSync(dir)]
    } catch {
        return []
    }
}

/** Read a file as text, or the empty string when it is unreadable. */
function readOrEmpty(path: string): string {
    try {
        return Deno.readTextFileSync(path)
    } catch {
        return ""
    }
}

/**
 * Every file under `dir` whose name ends with `suffix`, recursively.
 *
 * One walker for both probes, so the two agree on what "the corpus" means.
 */
function collect(dir: string, suffix: string, out: string[] = []): string[] {
    for (const entry of entriesOf(dir)) {
        const full = `${dir}/${entry.name}`
        if (entry.isDirectory) collect(full, suffix, out)
        else if (entry.name.endsWith(suffix)) out.push(full)
    }
    return out
}

/** A path relative to the repository root, for readable output. */
function rel(path: string): string {
    return path.startsWith(`${ROOT}/`) ? path.slice(ROOT.length + 1) : path
}

/**
 * The type names the corpus DECLARES — a `data Name` form in `_docs/` or
 * `examples/`.
 *
 * Variants are not types, so a name declared only as a variant is not accepted
 * here: the probe reports it as a candidate instead of silently approving it.
 */
function declaredTypes(): Map<string, string> {
    const declared = new Map<string, string>()
    const sources = [
        ...collect(`${ROOT}/_docs`, ".md"),
        ...collect(`${ROOT}/examples`, ".md"),
        ...collect(`${ROOT}/examples`, ".lapis"),
    ]
    for (const path of sources) {
        for (const match of readOrEmpty(path).matchAll(/^\s*data\s+([A-Z][A-Za-z0-9_]*)/gm)) {
            const name = match[1]!
            if (!declared.has(name)) declared.set(name, rel(path))
        }
    }
    return declared
}

/**
 * The type names `src/` and `test/` declare, via the builder API.
 *
 * `DataType.define("Stack")` and friends are declared types in every practical
 * sense — the test registry knows them — even where the docs never write the
 * `data` form.
 */
function fixtureTypes(): Set<string> {
    const declared = new Set<string>()
    for (const path of [...collect(`${ROOT}/src`, ".ts"), ...collect(`${ROOT}/test`, ".ts")]) {
        for (const m of readOrEmpty(path).matchAll(/\.define\(\s*"([A-Z][A-Za-z0-9_]*)"/g)) {
            declared.add(m[1]!)
        }
    }
    return declared
}

/**
 * The ```lapis fences of a markdown document, each with its starting line.
 *
 * Restricting to `lapis` is what makes the probe usable: prose and TypeScript
 * fences are not Lapis, so collecting type names from them yields dozens of
 * candidates that are all correct (`DataType`, `Field`, `CaseArm`, …) and
 * drown the handful that matter. The corpus is the `lapis` fences.
 */
function lapisBlocks(text: string): { line: number; body: string }[] {
    const blocks: { line: number; body: string }[] = []
    const lines = text.split("\n")
    let open: { line: number; body: string[] } | undefined
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i]!
        if (/^\s*```lapis\s*$/.test(line)) {
            open = { line: i + 1, body: [] }
            continue
        }
        if (/^\s*```\s*$/.test(line)) {
            if (open !== undefined) blocks.push({ line: open.line, body: open.body.join("\n") })
            open = undefined
            continue
        }
        if (open !== undefined) open.body.push(line)
    }
    return blocks
}

/**
 * Whether a line is a fold or unfold arm head: `Variant … -> …`.
 *
 * An arm is `armHead "->" armBody`, so the `->` is an *arm* arrow, not a type
 * arrow. `Leaf -> 0` puts `Leaf` before an arrow, and a probe that cannot tell
 * the two apart reports every variant as an undeclared type.
 */
function isArmHead(line: string): boolean {
    return /^\s*(?:[A-Z][A-Za-z0-9_]*\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*)*)?(?:->|→)/.test(line)
}

/**
 * Every PascalCase name used in a plausible TYPE position in a `lapis` block.
 *
 * The positions collected are a field or spec annotation (`name: Type`), the
 * result of a type arrow (`… -> Type`), a type whose arrow points right
 * (`Type ->`, only when something precedes it on the line), and a declared
 * parent (`data X <: Parent`).
 *
 * Two exclusions keep the output readable, and both are sound: bare PascalCase
 * in *expression* position is a variant reference, and an arm head's arrow is an
 * arm arrow rather than a type arrow. The probe consequently under-reports
 * rather than over-reports, which is the correct bias for a candidate list.
 */
function typePositionNames(text: string): Map<string, number[]> {
    const found = new Map<string, number[]>()
    const record = (name: string, line: number): void => {
        const lines = found.get(name) ?? []
        lines.push(line)
        found.set(name, lines)
    }

    const lines = text.split("\n")
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i]!
        const lineNo = i + 1
        // `field: Type` / `in: Type` / `out: Type`
        for (const m of line.matchAll(/[A-Za-z_][A-Za-z0-9_]*:\s*([A-Z][A-Za-z0-9_]*)/g)) {
            record(m[1]!, lineNo)
        }
        if (isArmHead(line)) continue
        // `Type -> …` — a type whose arrow points right.
        for (const m of line.matchAll(/([A-Z][A-Za-z0-9_]*)\s*(?:->|→)/g)) record(m[1]!, lineNo)
        // `… -> Type` — a result type.
        for (const m of line.matchAll(/(?:->|→)\s*([A-Z][A-Za-z0-9_]*)/g)) record(m[1]!, lineNo)
        // `data X <: Parent`
        for (const m of line.matchAll(/data\s+[A-Z][A-Za-z0-9_]*\s*<:\s*([A-Z][A-Za-z0-9_]*)/g)) {
            record(m[1]!, lineNo)
        }
    }
    return found
}

/**
 * The variant names the corpus DECLARES, as `PascalCase` heads of a `data`
 * body line.
 *
 * A variant is not a type: `Cons`, `Zero`, `Red`, and `Leaf` appear in
 * `field: Type` positions only when the corpus is teaching that a variant
 * constructs its carrier (`rest: Nil`). Excluding them is what makes the
 * unknown-name list short enough to read, and the exclusion is sound because a
 * variant reaching a genuine type position would be a different defect — a
 * carrier used where its constructor was meant.
 */
function variantNames(): Set<string> {
    const declared = new Set<string>()
    for (
        const path of [...collect(`${ROOT}/_docs`, ".md"), ...collect(`${ROOT}/examples`, ".md")]
    ) {
        for (const block of lapisBlocks(readOrEmpty(path))) {
            const lines = block.body.split("\n")
            let inDataBody = false
            for (const line of lines) {
                if (/^\s*data\s+[A-Z]/.test(line)) {
                    inDataBody = true
                    continue
                }
                if (inDataBody) {
                    const variant = line.match(
                        /^\s+([A-Z][A-Za-z0-9_]*)\s*(?:[A-Za-z_][A-Za-z0-9_]*:|$)/,
                    )
                    if (variant !== null) declared.add(variant[1]!)
                    // A dedent ends the body.
                    if (line.trim() !== "" && !/^\s/.test(line)) inDataBody = false
                }
            }
        }
    }
    return declared
}

// ── Probe 1: names taught but not declared ──────────────────────────────────

const declared = declaredTypes()
const fixtureDeclared = fixtureTypes()
const variants = variantNames()

const unknown = new Map<string, { file: string; lines: number[] }[]>()
for (const path of collect(`${ROOT}/_docs`, ".md")) {
    const file = rel(path)
    for (const block of lapisBlocks(readOrEmpty(path))) {
        for (const [name, lines] of typePositionNames(block.body)) {
            if (BUILTINS.has(name) || declared.has(name) || fixtureDeclared.has(name)) continue
            if (variants.has(name)) continue
            const sites = unknown.get(name) ?? []
            // Report absolute line numbers: the block's offset plus the match.
            sites.push({ file, lines: lines.slice(0, 3).map((l) => l + block.line) })
            unknown.set(name, sites)
        }
    }
}

// ── Probe 2: `data` bodies at a non-standard column ─────────────────────────

interface LayoutIssue {
    readonly file: string
    readonly line: number
    readonly name: string
    readonly bodyIndent: number
    readonly expected: number
}

const layoutIssues: LayoutIssue[] = []
for (const path of collect(`${ROOT}/_docs`, ".md")) {
    const file = rel(path)
    const lines = readOrEmpty(path).split("\n")
    let inFence = false
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i]!
        // Only fenced code blocks carry Lapis; prose is not a program.
        if (/^\s*```/.test(line)) {
            inFence = !inFence
            continue
        }
        if (!inFence) continue
        const header = line.match(/^(\s*)data\s+([A-Z][A-Za-z0-9_]*)/)
        if (header === null) continue
        const headerIndent = header[1]!.length
        const next = lines[i + 1] ?? ""
        // A blank line or a fence ends the comparison — there is no body to judge.
        if (next.trim() === "" || /^\s*```/.test(next)) continue
        const bodyIndent = next.match(/^(\s*)/)![1]!.length
        if (bodyIndent !== headerIndent + 4) {
            layoutIssues.push({
                file,
                line: i + 1,
                name: header[2]!,
                bodyIndent,
                expected: headerIndent + 4,
            })
        }
    }
}

// ── Report ──────────────────────────────────────────────────────────────────

const asJson = Deno.args.includes("--json")
const report = {
    unknownTypeNames: [...unknown.entries()]
        .sort((a, b) => a[0].localeCompare(b[0]))
        .map(([name, sites]) => ({ name, sites })),
    layoutIssues,
    declaredTypeCount: declared.size,
    fixtureTypeCount: fixtureDeclared.size,
    variantCount: variants.size,
}

if (asJson) {
    console.log(JSON.stringify(report, null, 2))
    Deno.exit(0)
}

console.log(`declared in _docs/ or examples/: ${declared.size}`)
console.log(`declared in src/ or test/:      ${fixtureDeclared.size}`)
console.log("")

if (report.unknownTypeNames.length === 0) {
    console.log("unknown type names: none")
} else {
    console.log(`unknown type names (${report.unknownTypeNames.length}) — candidates; verify each:`)
    for (const { name, sites } of report.unknownTypeNames) {
        const where = sites.slice(0, 2).map((s) => `${s.file}:${s.lines.join(",")}`).join("; ")
        const more = sites.length > 2 ? ` (+${sites.length - 2} more)` : ""
        console.log(`  ${name.padEnd(16)} ${where}${more}`)
    }
    console.log("")
    console.log("  Fine if it is a variant, a prelude type declared elsewhere, or a")
    console.log("  record field spelled PascalCase. A defect if nothing declares it —")
    console.log("  `atomType` accepts it silently and mints a rigid TypeVar.")
}

console.log("")
if (layoutIssues.length === 0) {
    console.log("data bodies at a non-standard column: none")
} else {
    console.log(`data bodies at a non-standard column (${layoutIssues.length}):`)
    for (const issue of layoutIssues) {
        console.log(
            `  ${issue.file}:${issue.line}  data ${issue.name} — body at ` +
                `${issue.bodyIndent}, expected ${issue.expected}`,
        )
    }
}
