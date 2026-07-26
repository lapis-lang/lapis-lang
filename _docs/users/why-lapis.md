# Why Lapis?

> You write programs. You've debugged infinite loops, shipped code the compiler
> couldn't prove correct, and wished your optimizer understood what your code
> *meant*. This document is for you. It's short. It shows you one thing you
> can't do in any language you're using right now, and explains why Lapis can do
> it.

## The thing you can't do

You're writing a polynomial evaluator. You have a list of coefficients and a
value `x`, and you want to compute the result. The obvious way:

```
scale each coefficient by x, then sum them
```

In any language, that's two passes: one to scale, one to sum. An intermediate
list sits in memory between them. You know this. You've written it a hundred
times.

You also know — maybe from a textbook, maybe from a class — that there's a
better way: **Horner's rule**. Instead of scaling then summing, you fold from the
inside out, multiplying by `x` at each step:

$$c_0 + c_1 x + c_2 x^2 + \cdots = c_0 + x(c_1 + x(c_2 + \cdots))$$

One pass. No intermediate list. The textbook says "apply Horner's rule." Your
compiler doesn't, because it doesn't know that scaling distributes over
summing. That's a *law* — an algebraic fact about `*` and `+` — and your
compiler doesn't know your `*` and `+` obey it. In Haskell you can write the law
in a comment or a QuickCheck property. The compiler ignores it. In Scala you can
write a typeclass law. The compiler ignores it. In every language you've used,
the law is decoration, not structure.

**In Lapis, you declare the law, and the compiler applies Horner's rule for
you.** Automatically. Because it trusts the law — and it trusts it because the
language *enforces* that every operation is a fold, and every fold respects the
algebra.

Here's what that looks like:

```lapis
data NumList
    Nil
    Cons head: Number tail: Family

    fold sum <out: Number>
        Nil -> 0
        Cons head tail -> head + tail

    fold scaleEach <in: x Number, out: Family, properties: (distributive: sum)>
        Nil -> Family Nil
        Cons head tail -> Family Cons head: head * x tail: (tail x)

    merge scaledSum <#scaleEach, #sum>
```

Read that last line: `merge scaledSum <#scaleEach, #sum>`. That's the
specification — "scale each element, then sum." The `properties: (distributive: sum)`
on `scaleEach` is the law that says scaling distributes over summing. The
compiler verifies the law at declaration time (by testing it against generated
samples), then performs the fusion when it sees the `merge`. You wrote the
two-pass specification. The compiler calculated the one-pass program.

**That's the thing you can't do.** Not "Horner's rule" specifically — the
*general principle*: you declare algebraic laws, the compiler verifies them, and
it exploits them for optimization. Fusion, short-circuiting, cancellation — all
automatic, all from declared laws, all trusted because the language's structure
makes them trustworthy.

## Why Lapis can do it (and your language can't)

Two facts make it work, and neither is optional.

**Fact 1: Every operation is a fold (or an unfold).**

Lapis has no general recursion. No `fix`, no self-call, no `while`. The only way
to recurse is `fold` (consuming data, bottom-up, terminating) or `unfold`
(generating codata, top-down, productive). This means:

- **Every program terminates.** No infinite loops. No termination checker
  needed — the language doesn't have the recursion that causes non-termination.
- **Every operation has a known algebraic shape.** A fold is a homomorphism — it
  replaces constructors with operations. This shape is what makes laws
  *checkable*: the compiler can test `associative` or `distributive` against a
  fold because the fold's structure is fixed.

**Fact 2: Laws are declarations, not comments.**

When you write `properties: (associative, commutative, identity: Zero)`, that's
not a comment. It's a declaration the compiler:

1. **Verifies** — generates sample inputs and checks the law holds.
2. **Exploits** — when it sees `three add Zero`, the `identity: Zero` law fires
   and the fold is short-circuited without traversal.
3. **Fuses on** — when it sees `merge`, the `distributive` law authorizes
   single-pass fusion.

Your language can't do this because your language has general recursion. With
general recursion, the compiler can't trust law declarations — verifying that
an arbitrary recursive function is associative is undecidable. The enforcement
(fold/unfold only) is what makes the exploitation reliable. The cage is what
makes the key work.

## The tradeoff, stated honestly

You give up general recursion. That's the cost. No `while`, no `fix`, no
self-call. If you need to traverse a structure, you write a `fold`. If you need
to generate a stream, you write an `unfold`. If you need something that's
neither — a computation that doesn't follow the shape of a data type — you
can't write it directly. You have to find a structure that fits.

This sounds restrictive, and it is. But it's the same kind of restriction as
"no `goto`" — a restriction that *enables* something. Structured programming
removed `goto` and got loops you could reason about. Lapis removes general
recursion and gets folds you can *calculate with*. The restriction is the
feature.

And the payoff — laws the compiler trusts, optimizations the compiler performs
from declarations, programs derived from specifications by algebra — is
something no existing language offers. Haskell has laws but doesn't enforce
fold. Coal enforces fold but doesn't exploit laws. Lapis does both.

## What to read next

This document is the hook. The full story is in
[`rationale.md`](./rationale.md) — a narrative from `fold` (which you know)
through totality, laws, program calculation, data/codata duality, and into
Datalog and Prolog as special cases of the same structure.

If you want the formal treatment — the calculus, the typing rules, the
soundness argument — that's in [`theory/`](../theory/), starting with
[`theory/why-lapis.md`](../theory/why-lapis.md).

But if you just want to know whether this language is worth your time: the
`merge` example above is the answer. You declare the law. The compiler verifies
it. The optimization happens. That's the whole pitch.