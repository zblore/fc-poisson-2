# The Poisson conjecture is false: a Lean proof

A Lean 4 proof that the Poisson conjecture fails for two canonical pairs, and hence for every number of pairs from two up. It proves four statements from the file `Arxiv/math.0608009/PoissonConjecture.lean` in Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures), against their own definitions and under their own names:

- `poisson_conjecture.variants.dimension_two`;
- `poisson_conjecture.variants.dimension_three`, as the case n = 3 of the next one;
- `poisson_conjecture.variants.dimension_ge_two`;
- `poisson_conjecture`.

## The result

Take polynomials in 2n variables x₁, …, xₙ, y₁, …, yₙ over a field of characteristic zero, with the canonical Poisson bracket, so that {xᵢ, yⱼ} = 1 when i = j and 0 otherwise, {yᵢ, xⱼ} = −{xⱼ, yᵢ}, and {xᵢ, xⱼ} = {yᵢ, yⱼ} = 0. A Poisson endomorphism is a substitution that preserves this bracket. Adjamagbo and van den Essen (2007) conjectured that every Poisson endomorphism is invertible, and showed this sits in a chain with the Jacobian and Dixmier conjectures.

Levent Alpöge announced a counterexample to the Jacobian conjecture in three variables in July 2026, which refutes the Poisson conjecture for three pairs and more. Christopher D. Long then gave an explicit counterexample with only two pairs: "An Explicit Counterexample to the Rank-Two Poisson Conjecture", arXiv:2608.23777 (2026). It is four polynomials R, T, D, S in x, q, p, z with rational coefficients, of degree up to 23. His paper is an unrefereed preprint. He writes that the four-variable construction, including the correction term H, was produced in a session with ChatGPT 5.6 Sol, and that Claude Fable 5 supplied independent algebraic audits. His proof is by hand; two accompanying programs, one using SymPy and one using only Python's standard library, check its identities. This proof is an independent machine check.

A Lean proof over the rationals was reported in Formal Conjectures pull request [#5451](https://github.com/google-deepmind/formal-conjectures/pull/5451) (September 2026), which corrected the statement, but the pull request neither includes nor links that proof, and I could not find it. As far as I could find, this is the first published formal proof, and it covers every field of characteristic zero and every n ≥ 2. I searched GitHub and the Formal Conjectures pull requests on 26 Oct 2026.

## The proof

The proof follows Long's own route.

- **Coordinates.** Long works in the coordinates x, y, β, D₀, which are polynomials in x, q, p, z. In those coordinates R, T, S and D are small. The brackets of the four coordinates with each other are polynomials in the coordinates too (`poissonBracket_coord`).
- **A chain rule.** The bracket of two polynomials written in the coordinates is then a sum over the coordinate brackets (`poissonBracket_aeval`). This rests on a chain rule for partial derivatives of a substitution (`pderiv_aeval`), which Mathlib does not have yet.
- **Six identities.** That turns the six bracket conditions into six polynomial identities in four variables (`Identities.lean`). Each is checked by computing the derivatives symbolically and comparing the two sides at an arbitrary point of the field. This is how the rational coefficients in Long's polynomials (1/2, 1/3, 1/6, 3/10, 1/20) are handled.
- **Not surjective.** Long's points (0, 0, 1/24, −1/8) and (1, 2/3, 247/96, −89/64) have the same image (0, 1/8, 0, 0). So every polynomial in the image of the map takes the same value at both points, but x takes the values 0 and 1. So x is not in the image.
- **More pairs.** For n ≥ 2, act by Long's map on the first two pairs and by the identity on the rest. A retraction onto the first two pairs shows the padded map is still not surjective (`Padding.lean`).

The files:

- `Challenge.lean`: the four statements, for Palomar. It imports only Mathlib, so the three definitions they use are copied into it from Formal Conjectures, word for word. Palomar does not accept names like `Arxiv.«math.0608009».poisson_conjecture`, with its escaped `«math.0608009»`, so the theorems are stated in the namespace `PoissonConjecture`, with the same leaf names. The definitions keep Formal Conjectures' names, so the statements are the same. `Solution` proves them under both names.
- `Solution.lean`: imports the proof.
- `Poisson2/Defs.lean`: the same three definitions, copied from Formal Conjectures.
- `Poisson2/Bracket.lean`: basic lemmas about the bracket, copied from Formal Conjectures.
- `Poisson2/ChainRule.lean`: the chain rule and the bracket of substitutions.
- `Poisson2/Coordinates.lean`: Long's coordinates and their bracket table.
- `Poisson2/Identities.lean`: R, T, D, S and the six identities.
- `Poisson2/Main.lean`: the endomorphism, its Poisson property, and non-surjectivity.
- `Poisson2/Padding.lean`: renaming along canonical pairs, and the padding to any n ≥ 2.
- `Poisson2/FormalTarget.lean`: the four Formal Conjectures statements.

`lake comparator` checks that `Solution` proves exactly the statements of `Challenge.lean`, with the same definitions; with this repository's `comparator.json` it replays the proof through Lean's kernel and nanoda. CI runs it through `scripts/verify-comparator.sh`, copied unchanged from Palomar's template, which adds con-ron, the toolchain's second bundled independent kernel. Palomar's own pipeline, which `.github/workflows/palomar-preflight.yml` runs on a chosen commit, runs con-ron separately, in a version its maintainers pin, and is the check that decides acceptance. `Poisson2/FormalTarget.lean` proves the statements under Formal Conjectures' names too, and checks in Lean that both sets of names have the same statements at every universe level. `scripts/check-fc-match.py` checks the other link: that `Challenge.lean` is Formal Conjectures' three definitions and four statements, character for character, and nothing else. With `--self-test` it also checks that altered copies of `Challenge.lean` (a changed universe, an extra hypothesis, a shadowing definition, and others) and of `Poisson2/FormalTarget.lean` fail. `audit/Axioms.lean` checks that the proofs use only `propext`, `Classical.choice` and `Quot.sound`, and it fails if that ever changes. `audit/Control.lean` checks that the audit would catch a `sorry` (an unproved statement reports `sorryAx`), specialises the result to the rationals, and checks the bracket sign and Long's common image (0, 1/8, 0, 0).

## Building

It needs Lean v4.35.0-rc3 and Mathlib at commit `5e0c4e52`.

```
lake exe cache get
lake build
lake env lean audit/Axioms.lean
lake env lean audit/Control.lean
python3 scripts/check-fc-match.py --self-test
```

The whole library builds in a few minutes. `scripts/verify-comparator.sh` runs `lake comparator` as Palomar's template does; it needs Linux, for its sandbox.

An earlier version (commit `d464ff4`) depended on Formal Conjectures directly, on Lean v4.33.1. This version has the same proofs, ported to Palomar's layout.

## How it was made

I used Claude Code to draft the Lean. I've checked every line myself and can explain all of it.

## About

I'm Zayn Blore. My main project is [csd-lean4](https://github.com/zblore/csd-lean4), the Lean library behind my work on Constraint-Surface Dynamics.
