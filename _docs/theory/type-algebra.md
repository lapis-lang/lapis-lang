# Type Algebra — Counting, Coefficients, and Derivatives of Lapis Types

> **Status:** Draft v0.1. This document grounds the law-discharge pipeline in the algebra of
> algebraic data types: generating functions for inhabitant counts, coefficient sequences for
> certified screen coverage, and derivatives (one-hole contexts) for structural shrinking. It
> extends [`lc.md`](./lc.md) §7 (Algebraic Equivalence) and [`semantics.md`](./semantics.md) §5.4
> (Law Checking); implementation anchor: `src/core/law_checking.ts`.

## 1. Overview

The algebra of ADTs (Taylor 2013; McBride 2001, "The Derivative of a Regular Type is its Type of
One-Hole Contexts"; Fiore & Leinster 2004) treats a type as a **combinatorial object**:

| Type form                | Algebra                | Counting                     |
| ------------------------ | ---------------------- | ---------------------------- |
| `Nothing` (bottom)       | $0$                    | no inhabitants               |
| nullary variant / unit   | $1$                    | one inhabitant               |
| variant set (sum)        | $T_1 + T_2 + \dots$    | sum of counts                |
| variant fields (product) | $T_1 \cdot T_2 \cdots$ | product of counts            |
| function field $σ → τ$   | $\tau^\sigma$          | exponential (unusable below) |
| recursion $T = F(T)$     | solve the equation     | series or closed form        |

Lapis already runs this algebra at the **term** level — the BMF calculus, fold-fusion, and the cost
decomposition of `semantics.md` §5.5 are generating-function reasoning in proof form. This document
is the **type-level** mirror: the same equations, read for _sizes_ and _contexts_ rather than
proofs.

Three readings of one equation, one module:

1. **Counting** — `|T|`, the total inhabitant count: decides the `finite` regime
   (`finiteInhabitants`, implemented).
2. **Coefficients** — $c_n$, the count of inhabitants of size $n$: certifies the residual screen's
   coverage ("all inhabitants of size ≤ 2 per position").
3. **Derivatives** — $\partial T$, the type of one-hole contexts: structural shrinking, paramorphism
   typing, live-observation evidence.

## 2. Counting: `|T|` as a decision procedure

### 2.1 The classifier

`finiteInhabitants(type)` (implemented, `law_checking.ts`) evaluates the generating function:

- A variant contributes the **product** over its fields; the variant set contributes the **sum**.
- A **recursive field** (`Family` position) makes the count undefined: $T = 1 + a\,T$ has no
  polynomial solution — a value may nest arbitrarily deep.
- A **function-typed field** makes it undefined: $\tau^\sigma$ has no finite vocabulary unless both
  ends are tiny, and no sampler can enumerate closures.
- An **`Any`-typed field** makes it undefined: the top type subsumes every type.
- A **field of another data type** contributes that type's count (the product threads through);
  parent-chain variants (comb inheritance) are summed in.
- Counts are **saturated** at the ceiling ($2^{17}$): a component past it returns ceiling+1, so deep
  record chains cannot overflow the number range while the caller's comparison still decides
  enumerability.

**Theorem (finiteness criterion — qualified).** For **productive** μ-types (those with at least one
non-recursive base variant), finitely inhabitable **iff acyclic** — no `Family` occurrence in its
own unfolding — and every field type is finitely inhabitable. Proof: acyclic productive types have
polynomial generating functions (the recursion is syntactically absent); cyclic productive types
have $T = F(T)$ with $T$ reachable from $F$'s product terms, hence infinitely many inhabitants of
unbounded size.

**Unproductive recursive types are the boundary of the first cut.** A definition like `Wrap(T)` — a
variant whose only field is recursive — has an _empty_ least fixpoint: no finite value inhabits it
(every value would need to wrap another, forever), yet the classifier reports `undefined`
("unbounded"). Treating every reachable recursive field as unbounded is therefore a **conservative
approximation, not an exact decision procedure**: it correctly identifies all truly-unbounded types
(no false "finite") but over-rejects unproductive recursive ones (false "unbounded") — they are
routed to the residual screen, where the screen then honestly reports no vocabulary (a Stream-like
carrier's sampler has no base case). Adding productivity analysis ("does the recursion have a base
case?") would refine this to an exact criterion; until then the conservative routing is the honest
choice — it never claims full coverage of a space it cannot enumerate. The classifier is
$O(\text{size of type declaration})$ with memoization.

### 2.2 Regime routing as arithmetic

The exhaustion cost of a law is $\prod_i |T_i|^{v_i}$ where $v_i$ is the number of schema variables
landing on operand position $i$. The docs' "~2²⁰ inhabitants" threshold is therefore sound **only
per schema arity**:

| Carrier             | identity ($v=1$) | commutative ($v=2$) | associative ($v=3$) |
| ------------------- | ---------------- | ------------------- | ------------------- |
| Bool (2)            | 2                | 4                   | 8                   |
| 2¹⁰-inhabitant enum | 2¹⁰              | 2²⁰ (at budget)     | 2³⁰ (residual)      |
| binary64 (2⁶⁴)      | 2⁶⁴ (never)      | never               | never               |

"Never" is structural-exhaustion-never: the `machineFinite` regime's sub-space specifications (§5)
make cells like binary64-identity dischargeable by certifying a declared subset — the sweep
arithmetic above then applies to the sub-space's certified size.

`screeningRegime` computes the **exact** sweep ($\prod_i |T_i|^{v_i} \times$
instances-per-assignment, saturated arithmetic) and routes `finite` only when it fits
`MAX_EXHAUSTION_INSTANCES`. The routing is a decision, not a guess: the estimate IS the sweep the
check will run (the same `assignments` enumeration).

### 2.3 Pattern types are always infinite

A pattern-matched data type (`PatternDataType`) is a regular language over the lexer alphabet. By
the Chomsky–Schützenberger theorem, every regular language has a **rational** generating function;
for `Nat = [0-9]+` the equation is $L = 1 + 10\,L$ (the geometric series $1/(1-a)$) — no closed
bound, hence no exhaustion, ever. This is the formal refutation of proof-by-exhaustion as a default
discharge for the pattern universe (`Rational`, `Complex`, `Nat`, `Int`, `String`): the classifier
returns "unbounded" for every one of them, permanently.

Pattern types get their counting from the **coefficient** reading instead (§3), and their discharge
from `machineFinite` encodings (§5) or derivation (§6) — never from exhaustion.

## 3. Coefficients: certified screen coverage

For a type $T$ with generating function $G_T(x) = \sum_n c_n x^n$, $c_n$ counts the inhabitants of
size $n$ (size = constructor-node count). The two carrier classes differ in the GF's form, and the
certification design must keep them apart:

- **Pattern types are regular languages** — by Chomsky–Schützenberger their GFs are **rational**:
  $c_n$ satisfies a _linear recurrence_ with constant coefficients, computable directly once the
  pattern's language equation is known (§2.3).
- **Recursive μ-types are generally NOT regular** — their GFs are _algebraic_, not rational. A
  branching recursive type such as `Tree = Leaf + Node(Tree, Tree)` has the Catalan generating
  function $T(x) = 1 + x\,T(x)^2$, whose coefficients satisfy a _quadratic recurrence_
  ($c_n = \sum_i c_i c_{n-1-i}$ — the Catalan numbers), not a linear one. A chain-recursive type
  (`List`) is the degenerate case: its GF $1/(1-a)$ is rational. So the coefficient-certification
  implementation needs at least algebraic-recurrence support (or per-type equation solving) before
  it can cover recursive μ-carriers; linear recurrences alone cover pattern types and
  chain-recursive carriers only.

The design (PBI #65) should state this split explicitly: rational GFs for pattern types
(Chomsky–Schützenberger), algebraic GFs for recursive μ-types (the Lagrange/implicit-function
reading of the type equation), and a per-type decision for which recurrence class the certification
machinery supports.

This upgrades the residual screen's evidence from an opaque instance count to a **certified
prefix**: a sweep bounded at depth 2 can state "checked all inhabitants of size ≤ 2 for each operand
position" — a theorem, not a vibe. The screen's existing machinery (`samplesFor` walks variants
depth-bounded) already enumerates exactly the $c_{\le 2}$ prefix; the missing piece is computing
$c_{\le 2}$ **independently** (from the type equation) and asserting the sweep's instance count
matches it. Coverage goes from "we checked N instances" to "we checked the first $k$ size classes,
containing exactly $c_0 + \dots + c_k$ inhabitants".

For pattern types, $c_n$ comes from the language equation: a pattern `p` with generating function
$P(x)$ (concatenation multiplies, alternation sums, Kleene star inverts $(1-P)$) gives the count of
matched strings of each length. The coefficient reading is what makes the pattern universe checkable
at bounded size even though it is unbounded in total (§2.3).

## 4. Derivatives: one-hole contexts

McBride's theorem: the formal derivative of a type's generating function is the type of its
**one-hole contexts** — the data structure with exactly one subvalue replaced by a hole.

### 4.1 The rules (implementation spec)

Differentiation is structural recursion over the `Type` AST (McBride 2001; Taylor Part III):

$$
\begin{aligned}
\partial_a\, \text{const} &= 0 & &\text{(no } a \text{ inside → no contexts)} \\
\partial_a (F + G) &= \partial_a F + \partial_a G &&\text{(sum rule)} \\
\partial_a (F \cdot G) &= \partial_a F \cdot G + F \cdot \partial_a G &&\text{(Leibniz)} \\
\partial_a\, a &= 1 &&\text{(the hole itself)} \\
\partial_a\, F(G(a)) &= \partial_a G \cdot \partial_G F &&\text{(chain rule)}
\end{aligned}
$$

**Implicit differentiation is the implementation key**: differentiate the μ-equation directly, never
solving for $T$ first. For $T(a) = 1 + a \cdot T(a)^2$:

$$\partial_a T = T^2 + 2aT \cdot \partial_a T \quad\Rightarrow\quad \partial_a T = T^2 \cdot L(2aT)$$

The tree context is "two subtrees plus a list of `(Bool, a, Tree)` steps back to the root" — no
division or quotient rule anywhere in the implementation, just structural recursion with the μ-bound
variable solved for linearly at its occurrence. The list case: $\partial L = L^2$ (the classic
zipper: reverse-prefix × suffix). The chain rule is what makes this correct for Lapis's
heterogeneous fields — a hole can sit deep inside a field's own structure.

### 4.2 Landing sites

1. **Structural shrinking.** `law-testing.md`'s `forAll` harness shrinks by re-generating at
   shallower depth. The ∂T alternative: plug a **smaller filler** into the hole — the counterexample
   shrinks along the actual value's structure, monotone toward a minimal falsifier, derived from the
   type rather than the generator. (The harness currently lives in `test/laws.test.ts`; promotion
   into `src/` rides on this.)

2. **`old` / paramorphism typing.** A paramorphic handler sees the raw pre-fold subnode (`old`) plus
   its surroundings. The surroundings are precisely what $\partial T$ decomposes into — Leibniz's
   "everything except the hole". The keyword stops being ad hoc: it is the one-hole context at the
   recursion point, and its type is derivable from the fold's functor.

3. **Live-observation evidence typing.** The runtime re-screening channel (`design-decisions.md`,
   Laws) accumulates evidence against `asserted` laws from actual usage. ∂T types that evidence:
   which contexts of actual values have been exercised, so coverage claims over the observation
   channel become quantified ("all one-hole contexts of shape ≤ k observed").

### 4.3 Boundary

- **Rose-shaped recursion** ($R = a \cdot L(R)$ — recursion _under a list field_) differentiates
  fine ($\partial R = L(R) \cdot L(a \cdot L(R)^2)$), but Lapis's `Field.isRecursive` marks direct
  `Family` positions only; nested recursion through _other_ types is a separate expressiveness
  decision. The derivative machinery covers exactly what the cage expresses; the chain rule states
  precisely what nested-recursion expressiveness would buy.
- **Intersections** are not a semiring operation; $\partial$ on `IntersectionType` is undefined here
  (the screen already treats intersected carriers as unsampleable — consistent).
- **Function-typed fields** have exponential GFs that blow up immediately; the existing
  `screenableDomain` rule is justified, not weakened, by the algebra.
- **Codata (ν)** is the coalgebraic dual — bounded observation stays bounded; nothing here touches
  ν.

## 5. machineFinite: encoding declarations (design)

The `machineFinite` regime (semantics.md §5.4) needs the encodings themselves declared — the bound
must be spec-able, not an implementation accident. Three declaration forms:

1. **Encoding declarations on data types** — a `data` type states its encoding family (`binary64`,
   `char-unicode`, `int-two-complement`), fixing `|T|` **as part of the language definition**
   (binary64 = exactly $2^{64}$, `Inf`/`NaN` as in-domain values). The classifier _reads_ the
   declared count; it never infers an encoding from the runtime representation.
2. **Sub-space specifications** — a law declaration may scope its claim ("all Floats in [-1, 1]"),
   so bounded enumeration **certifies the checked sub-space**: `discharged` for the sub-space,
   `asserted` beyond it. The certification is the claim.
3. **Alphabet declarations for Char-like types** — a fixed finite alphabet makes bounded-length
   string enumeration well-posed (the length bound rides on sized types, already a design decision
   for termination).

In type-algebra terms, an encoding declaration is just a **fixed `|T|` constant** the classifier
reads before its own structural analysis: binary64's GF is the constant $2^{64}$, and sub-space
specs restrict enumeration to a certified subset with the same sweep arithmetic as §2.2. This is the
discharge route for machine-finite _pattern_ carriers (`Float`, `Int`, `Char`) — the only route,
since §2.3 bars them from structural exhaustion forever.

## 6. Derivation: the BMF engine (design)

The `derivable` regime proves laws from primitive laws via fold-induction skeletons. The key
structural fact: **the induction motive is fixed by the functor** — the fold schema determines the
skeleton, so derivation is algorithmic (the cage's reason it beats general provers here).

The algebra-of-ADTs connection: fold-fusion and generating-function manipulation are the _same_
calculus. Taylor Part II's series expansions (list $= 1/(1-a)$, tree $= (1-\sqrt{1-4a})/2a$) and
BMF's calculational rules are the same move — reading the type equation pointwise instead of
structurally. A characterized handler fragment (handlers whose bodies call only primitive,
discharged operations in semantically essential ways) makes "derivable" decidable: the skeleton
generates the proof obligation, the primitive law set discharges it.

**Caution (Fiore–Leinster).** Algebraic manipulations that use subtraction/division (seven trees in
one) are only semiring-valid under specific conditions. Never auto-adopt a type-isomorphism rewrite
into `↝` from a raw algebraic derivation; isomorphisms admitted this way need an explicit pair of
total maps (`from`/`to`) checked against the calculus.

## 7. Implementation status and roadmap

| Piece                                      | Status                                                      |
| ------------------------------------------ | ----------------------------------------------------------- |
| `finiteInhabitants` (counting classifier)  | **implemented** (`law_checking.ts`)                         |
| Exact sweep routing (`screeningRegime`)    | **implemented** (`law_checking.ts`)                         |
| Exhaustion (`exhaustLaw` → `discharged`)   | **implemented** (`law_checking.ts`)                         |
| Zero-coverage rejection (declined screen)  | **implemented** (`screenLaw` outcome + reject)              |
| `Token` value form (`TokenVal`, T-Token)   | **implemented** (`values.ts`, `grammar.ts`)                 |
| Pattern sampling (token prefix, §2.3/§3)   | **implemented** (`patternSamples` in `law_checking.ts`)     |
| ∂T machinery (§4) — `derivative(T)`        | **implemented** (`type_algebra.ts`; `ContextSpec` shapes,   |
|                                            | implicit differentiation at the μ-bound)                    |
| ∂T-based structural shrinking              | **implemented** (`law_testing.ts`; `DerivativeGenerator`,   |
|                                            | regeneration as the fallback)                               |
| ∂T: `old`/paramorphism typing (§4.2)       | pending (stretch — needs the `old` language feature)        |
| ∂T: observation-channel evidence typing    | pending (stretch — needs the re-screening channel)          |
| Coefficient-certified screen coverage (§3) | pending (screen enumerates the size-1 prefix; GF check TBD) |
| Encoding declarations (§5)                 | pending (design above; `semantics.md` §5.4 note)            |
| BMF derivation engine (§6)                 | pending (awaits the handler-fragment characterization)      |

Ordering rationale: counting and routing landed first because they are the **decision procedures**
everything else consults; pattern-value support next (it unblocks the largest unserved universe);
coefficients and derivatives are refinements of mechanisms that already enumerate the right spaces.

## 8. References

- Chris Taylor, _The Algebra of Algebraic Data Types_, Parts I–III (2013) — the counting analogy,
  recursive-type equations, type derivatives.
- Conor McBride, _The Derivative of a Regular Type is its Type of One-Hole Contexts_ (2001) — ∂T =
  one-hole contexts; implicit differentiation.
- André Huet, _The Zipper_ (1997) — contexts as navigable structures.
- Flajolet & Sedgewick, _Analytic Combinatorics_ (2009) — generating functions for combinatorial
  classes; Chomsky–Schützenberger for regular languages.
- Fiore & Leinster, _Objects of categories as complex numbers_ (2004) — when algebraic manipulations
  are semiring-valid.
- Abbott, Altenkirch & Ghani, _Categories of containers_ / shapely types — the cost-decomposition
  anchor already cited in `semantics.md` §5.5.
