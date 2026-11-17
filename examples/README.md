# Examples

Executable-fixture candidates: complete Lapis programs, one per file. The target state is that
`deno test` executes every file here and that the published docs _read_ them instead of retyping
them (PBI #95).

## Status: not yet runnable

Nothing here executes yet. Each file states its own blockers in a header comment. The current set:

| File              | Blocked by                                                                                                                                 |
| ----------------- | ------------------------------------------------------------------------------------------------------------------------------------------ |
| `quadratic.lapis` | #97 (no `data`/`fold` productions), #93 (`Number`, `sqrt`, `-`, `*`, `/` undeclared), #106 (no surface application), #107 (`aux` spelling) |

Do not add a file here that silently differs from what the docs show — either the file is the single
source the docs read, or it is not in this directory. Where the two currently disagree, the file is
authoritative and the doc needs a fix.

## Conventions

- **The top level is declarations only.** No definition form, no expression statements — a program
  is `declaration*`. Values worth showing are named at a call site and described by a trailing
  `/* … */` result annotation, which is a documentation-fragment device rather than source
  (`_docs/overview.md` §12.6, §12.21).
- **Header comment states the intended result and any contract**, so a future harness has something
  to check against. Contract clauses (`demands:`/`ensures:`) are the _checked_ way to claim a result
  in real code; trailing annotations are not checked by the language.
- **Note anything the prelude cannot yet spell.** An example that depends on an undeclared name is
  not wrong — it is the target — but the header must say so, or the file reads as a regression.
