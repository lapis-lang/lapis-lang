# TAPL Checkers — Reference Implementations

Typechecking implementations from Benjamin Pierce's _Types and Programming Languages_, downloaded
from <https://www.cis.upenn.edu/~bcpierce/tapl/checkers/>.

Each directory is an OCaml implementation with the same structure: `core.ml` (typing + evaluation),
`syntax.ml` (AST), `parser.mly` / `lexer.mll` (parser), `test.f` (example programs).

## Most Relevant to Lapis Core

### `fullfsub/` — F<: with Subtyping (TAPL Ch 26)

**The closest match to our type system.** Bounded quantification (`∀α<:σ.τ`), type abstraction
(`Λα<:σ. t`), type application (`t [τ]`), and the full subtyping algorithm. Our F_{<:μν} is this
plus μ/ν types.

- Compare: subtyping algorithm (`core.ml`) vs our `src/core/subtyping.ts`
- Compare: typing rules for `Λ`/`t[τ]` vs our planned T-TAbs/T-TApp

### `fullisorec/` — Iso-Recursive Types (TAPL Ch 20)

**Exactly our design decision.** Iso-recursive types use explicit `fold`/`unfold` operations rather
than silent unfolding. Direct comparison for our `Fold`/`Unfold` terms.

- Compare: `fold`/`unfold` typing rules vs our T-Fold/T-Unfold
- Compare: `fold`/`unfold` evaluation rules vs our E-Fold/E-Unfold

### `rcdsubbot/` — Records, Subtyping, Bot (TAPL Ch 15-16)

**Our subtyping lattice.** Width/depth subtyping on records, plus `Bot` (our `Nothing`) and `Top`
(our `Any`). Records map to our DataType/CodataType field subtyping.

- Compare: `Top`/`Bot` handling vs our `Any`/`Nothing`
- Compare: width/depth subtyping vs our S-Data-Width/S-Data-Depth

### `fullsub/` — Simply-Typed Lambda Calculus with Subtyping (TAPL Ch 15-16)

**Simpler subtyping baseline.** STLC + subtyping, no polymorphism. Good for understanding the
subtyping algorithm without F<: complexity.

## Useful for Later

### `fullfomsub/` — Fω with Subtyping (TAPL Ch 28)

Higher-kinded type constructors with subtyping. For when we add type-level functions (e.g.,
`Family`/`Self` as higher-kinded references).

### `fullequirec/` — Equi-Recursive Types (TAPL Ch 20)

The alternative we rejected. Equi-recursive types unfold silently — we chose explicit
`fold`/`unfold` instead. Useful to validate our design decision.

## License

These are from the TAPL supplementary materials, provided by Benjamin Pierce. They are for reference
and comparison only — not included in the Lapis build.
