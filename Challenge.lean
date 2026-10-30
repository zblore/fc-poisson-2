/-
Copyright 2026 The Formal Conjectures Authors.
Modifications copyright 2026 Zayn Blore.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The Poisson conjecture is false

The Poisson conjecture $PC_n$ (K. Adjamagbo and A. van den Essen, arXiv:math/0608009) asserts
that, over a field `K` of characteristic zero, every endomorphism of the `n`-th canonical Poisson
algebra is an automorphism. The canonical Poisson algebra is the polynomial algebra in the `2n`
variables `X (Sum.inl i)` and `X (Sum.inr i)`, with bracket `{X (Sum.inl i), X (Sum.inr i)} = 1`.

The four statements are Formal Conjectures' statements, with Formal Conjectures' leaf names:

* `poisson_conjecture.variants.dimension_two`: $PC_2$ is false (C. D. Long, arXiv:2608.23777);
* `poisson_conjecture.variants.dimension_ge_two`: $PC_n$ is false for every `n ≥ 2`;
* `poisson_conjecture.variants.dimension_three`: $PC_3$ is false;
* `poisson_conjecture`: the Poisson conjecture is false.

The three definitions below are copied verbatim from Formal Conjectures
(`google-deepmind/formal-conjectures`, commit `a6bf2bb646fc1926130c24781a3b3cf23d0ef288`):
`MvPolynomial.poissonBracket` from
`FormalConjecturesForMathlib/Algebra/MvPolynomial/PoissonBracket.lean`, and the other two from
`FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean`, as is the text of the four
statements. Formal Conjectures states them in the namespace `Arxiv.«math.0608009»`, but Palomar
does not accept escaped name components such as `«math.0608009»` in theorem names, so here they
are stated in the namespace `PoissonConjecture`. The definitions keep their Formal Conjectures
names, so the statements are the same terms. `Solution` also proves them under Formal
Conjectures' own names.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] [Fintype σ]

/-- The canonical Poisson bracket on `MvPolynomial (σ ⊕ σ) R`, given by
$\{f, g\} = \sum_{i} (\partial_{x_i} f \cdot \partial_{y_i} g
- \partial_{y_i} f \cdot \partial_{x_i} g)$ where $x_i$ (resp. $y_i$) is the variable
indexed by `Sum.inl i` (resp. `Sum.inr i`). -/
noncomputable def poissonBracket (f g : MvPolynomial (σ ⊕ σ) R) : MvPolynomial (σ ⊕ σ) R :=
  ∑ i : σ, (pderiv (Sum.inl i) f * pderiv (Sum.inr i) g -
    pderiv (Sum.inr i) f * pderiv (Sum.inl i) g)

end MvPolynomial

namespace Arxiv.«math.0608009»

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A `K`-algebra endomorphism `φ` of the polynomial algebra in $2n$ variables is an
endomorphism of the `n`-th canonical Poisson algebra $P_n(K)$ if it preserves the canonical
Poisson bracket. Following [AvdE07], Lemma 2, it is equivalent to require preservation on
the generators only, which is the form used here (the brackets of generators are constants,
so preserving and intertwining them agree). -/
def IsPoissonEndomorphism {n : ℕ}
    (φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K) : Prop :=
  ∀ v w, poissonBracket (φ (X v)) (φ (X w)) = poissonBracket (X v) (X w)

variable (K) in
/-- The Poisson Conjecture in dimension `n` ($PC_n$ in the notation of [AvdE07]): every
endomorphism of the `n`-th canonical Poisson algebra over `K` is an automorphism.
An endomorphism is an automorphism iff it is bijective, since the inverse of a bijective
algebra endomorphism preserving the Poisson bracket is again such. -/
def PoissonConjectureFor (n : ℕ) : Prop :=
  ∀ φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K,
    IsPoissonEndomorphism φ → Function.Bijective φ

end Arxiv.«math.0608009»

namespace PoissonConjecture

open Arxiv.«math.0608009»

variable {K : Type*} [Field K] [CharZero K]

/-- **The Poisson conjecture is false.** -/
theorem poisson_conjecture : ¬ ∀ n, PoissonConjectureFor K n := by
  sorry

/-- **The Poisson conjecture is false in dimension `2`** (Long 2026). -/
theorem poisson_conjecture.variants.dimension_two : ¬ PoissonConjectureFor K 2 := by
  sorry

/-- **The Poisson conjecture is false in dimension `3`.** -/
theorem poisson_conjecture.variants.dimension_three : ¬ PoissonConjectureFor K 3 := by
  sorry

/-- **The Poisson conjecture is false in every dimension `n ≥ 2`.** -/
theorem poisson_conjecture.variants.dimension_ge_two (n : ℕ) (hn : 2 ≤ n) :
    ¬ PoissonConjectureFor K n := by
  sorry

end PoissonConjecture
