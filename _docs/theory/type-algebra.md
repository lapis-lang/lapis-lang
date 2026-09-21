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

Pattern types get their counting from the **coefficient** reading (§3), whose pattern arm is now the
**language-equation reading** (implemented, `pattern_lang.ts`): each pattern's AST states its
equation directly — character/class → count at length 1, concatenation → convolution, star →
$L = \varepsilon + P \cdot L$, plus → $P \cdot P^*$, optional → the $\varepsilon$-branch, type
reference → the referenced type's counts (memoized, cycles rejected loudly). For `Nat = [0-9]+` this
reads as $L = P \cdot L$ with $P$ = 10 chars — $c_n = 10^n$, exactly as the geometric series
$1/(1-a)$ says. Discharge is `machineFinite` sub-space sweeps (§5) or derivation (§6) — never
exhaustion.

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

The design (PBI #65, implemented) states this split explicitly: rational GFs for pattern types
(Chomsky–Schützenberger), algebraic GFs for recursive μ-types (the Lagrange/implicit-function
reading of the type equation), and a per-type decision for which recurrence class the certification
machinery supports. One mechanism covers both: the equations are iterated, never solved.

This upgrades the residual screen's evidence from an opaque instance count to a **certified
prefix**: "checked all inhabitants of size ≤ k per operand position — exactly N, verified". The
certificate's independence is the point: `coefficients(type, k)` reads the type equation directly (a
truncated fixpoint over `T(x) = Σ x·Π GF(field)`, in `type_algebra.ts`), while the screen enumerates
the size-≤ kᵢ class set (`inhabitantsUpToSize` in `law_checking.ts`) — a different method computing
the same count, asserted equal. A mismatch rejects the declaration loudly: an enumeration hole would
otherwise masquerade as full-prefix coverage. The certificate states the split (§3's
rational/algebraic division) but the implementation needs no per-type case analysis: chain carriers
satisfy linear recurrences, branching carriers quadratic ones, and the fixpoint solves both.
(Pattern types use the language-equation reading for the same coefficients (#62 implemented,
`pattern_lang.ts`) — the singleton fallback is gone; see §5.)

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
  fine ($\partial R = L(R) \cdot L(a \cdot L(R)^2)$), but Lapis's `Family`-typed fields mark direct
  μ-bound positions only; nested recursion through _other_ types is a separate expressiveness
  decision. The derivative machinery covers exactly what the cage expresses; the chain rule states
  precisely what nested-recursion expressiveness would buy.
- **Intersections** are not a semiring operation; $\partial$ on `IntersectionType` is undefined here
  (the screen already treats intersected carriers as unsampleable — consistent).
- **Function-typed fields** have exponential GFs that blow up immediately; the existing
  `screenableDomain` rule is justified, not weakened, by the algebra.
- **Codata (ν)** is the coalgebraic dual — bounded observation stays bounded; nothing here touches
  ν.

## 5. machineFinite: sub-space specifications (implemented)

The `machineFinite` regime (semantics.md §5.4) is now implemented for pattern carriers, on a single
declaration form:

**Sub-space specifications** — a law declaration may scope its claim ("all Ints with $|x| \le
2^{31}$"), so bounded enumeration **certifies the checked sub-space**: `discharged` for the
sub-space, `asserted` beyond it. The certification is the claim. A spec is a predicate over the
swept operand position, type-checked against the operand carrier, evaluated by the same total
evaluator as the law body; the enumeration materializes the carrier's strings (length-bounded,
budget-capped) and keeps exactly the members the predicate admits. The sweep's **visible extent** is
part of the certificate (`SubSpaceSweep`: the length bound reached and each scoped position's
admitted cardinality) — the claim is "discharged on strings of length ≤ N matching the scope", not
an unqualified `discharged`. An EMPTY filtered space rejects the declaration (a vacuous discharge is
almost never the scoped claim its author meant). Structural exhaustion stays permanently unavailable
to pattern carriers (§2.3); the sub-space sweep is the honest alternative.

**Rejected design: encoding declarations on data types.** The original design ( `type-algebra.md`
before the #62 rescope; semantics.md §5.4's note) proposed a `data` type stating its encoding family
(`binary64`, `char-unicode`, `int-two-complement`), fixing `|T|` as part of the language definition
(binary64 = exactly $2^{64}$, `Inf`/`NaN` as in-domain values). This is **dropped**: it contradicts
the token-value architecture. A pattern-matched type is a _lexeme space_ — its patterns constrain
the raw token text only; interpretation (which lexeme is a Float, which is an Int) belongs to the
fold layer, and machine-numerics trust is the `primitive` provenance tier's business. A `|T|`
constant read from a declaration would assert an encoding the pattern language cannot express
(`binary64`'s exact $2^{64}$ count is a property of the interleaved interpretation, not of any
lexeme set). The `alphabet` declaration form is likewise dropped for the same reason — the character
universe is instead a **one-line language fiat**: `.` and classes range over code points 0–127
(ASCII) for now; Unicode widening is a later, separate decision (surface-syntax.md §1.3).

In type-algebra terms, the sub-space sweep applies §2.2's sweep arithmetic to a **filtered
carrier**: the certified size is the sub-space's cardinality, which `exhaustLaw` knows exactly
because it enumerated it. This is the discharge route for machine-finite _pattern_ carriers (`Nat`,
`Int`, `Char`, user-declared pattern types) — the only route besides §6's derivation, since §2.3
bars them from structural exhaustion forever.

## 6. Derivation: the BMF engine (implemented — `src/core/derivation.ts`)

The `derivable` regime proves laws from primitive laws via fold-induction skeletons. The key
structural fact: **the induction motive is fixed by the functor** — the fold schema determines the
skeleton, so derivation is algorithmic (the cage's reason it beats general provers here).

The algebra-of-ADTs connection: fold-fusion and generating-function manipulation are the _same_
calculus. Taylor Part II's series expansions (list $= 1/(1-a)$, tree $= (1-\sqrt{1-4a})/2a$) and
BMF's calculational rules are the same move — reading the type equation pointwise instead of
structurally. A characterized handler fragment (handlers whose bodies call only primitive,
discharged operations in semantically essential ways) makes "derivable" decidable: the skeleton
generates the proof obligation, the primitive law set discharges it.

**The characterization, operationally** (`derivation.ts`'s module doc is the record): a claim is
derivable iff the bounded engine closes every schema instance's every variant case — the fragment is
_defined_ by what the engine closes. The admitted definition shape: a lambda chain over the declared
parameters whose body is a fold over one of the parameters (the recursion axis), one handler per
axis variant, over a μ-type carrier. The move set: fold-computation unfolding (E-Fold at the
symbolic level), congruence, the induction hypothesis at recursion positions, and one-step axiom
instantiation from `primitive`/`discharged` laws — all bounded, no search, no backtracking. Scope
boundaries (first cut): intrinsic kinds only (`distributive` routes residual), pattern carriers
outside, one induction axis (`commutative` on Nat's `add` is the honest edge), and no type-level
rewrites (the caution below, honored structurally).

**Caution (Fiore–Leinster).** Algebraic manipulations that use subtraction/division (seven trees in
one) are only semiring-valid under specific conditions. Never auto-adopt a type-isomorphism rewrite
into `↝` from a raw algebraic derivation; isomorphisms admitted this way need an explicit pair of
total maps (`from`/`to`) checked against the calculus.

## 7. Implementation status and roadmap

| Piece                                                    | Status                                                    |
| -------------------------------------------------------- | --------------------------------------------------------- |
| `finiteInhabitants` (counting classifier)                | **implemented** (`law_checking.ts`)                       |
| Exact sweep routing (`screeningRegime`)                  | **implemented** (`law_checking.ts`)                       |
| Exhaustion (`exhaustLaw` → `discharged`)                 | **implemented** (`law_checking.ts`)                       |
| Zero-coverage rejection (declined screen)                | **implemented** (`screenLaw` outcome + reject)            |
| `Token` value form (`TokenVal`, T-Token)                 | **implemented** (`values.ts`, `grammar.ts`)               |
| Pattern sampling (token prefix, §2.3/§3)                 | **implemented** (`patternSamples` in `law_checking.ts`)   |
| ∂T machinery (§4) — `derivative(T)`                      | **implemented** (`type_algebra.ts`; `ContextSpec` shapes, |
|                                                          | implicit differentiation at the μ-bound)                  |
| ∂T-based structural shrinking                            | **implemented** (`law_testing.ts`; `DerivativeGenerator`, |
|                                                          | regeneration as the fallback)                             |
| ∂T: `old`/paramorphism typing (§4.2)                     | pending (stretch — needs the `old` language feature)      |
| ∂T: observation-channel evidence typing                  | pending (stretch — needs the re-screening channel)        |
| Coefficient-certified screen coverage (§3)               | **implemented** (`type_algebra.ts` `coefficients`;        |
| `law_checking.ts` `inhabitantsUpToSize` + certification) |                                                           |
| Pattern language-equation coefficients (§2.3/§3)         | **implemented** (`pattern_lang.ts` parse + counting;      |
|                                                          | `types.ts` AST patterns; `type_algebra.ts` pattern arm)   |
| Token size = text length (§3 certificates)               | **implemented** (`values.ts` `valueSize` token arm)       |
| Sub-space specifications + `machineFinite` (§5)          | **implemented** (`laws.ts` `LawDecl.subSpace` +           |
|                                                          | validation; `law_checking.ts` machineFinite arm +         |
|                                                          | `exhaustLaw` sub-space filtering)                         |
| Encoding declarations (§5)                               | **rejected** — contradicts the token architecture (§5)    |
| Sub-space surface syntax                                 | pending (core: structured `subSpace` field; the surface   |
|                                                          | form lands with the pattern-surface PBI)                  |
| BMF derivation engine (§6)                               | **implemented** (`derivation.ts` — the bounded,           |
|                                                          | search-free discharger; the fragment is defined by what   |
|                                                          | the engine closes; `commutative` on Nat's `add` stays     |
|                                                          | the honest edge)                                          |

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
