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
# The definitions of Formal Conjectures' Poisson conjecture

Copied verbatim from Formal Conjectures (`google-deepmind/formal-conjectures`, commit
`a6bf2bb646fc1926130c24781a3b3cf23d0ef288`):

* `MvPolynomial.poissonBracket`, from
  `FormalConjecturesForMathlib/Algebra/MvPolynomial/PoissonBracket.lean`;
* `Arxiv.«math.0608009».IsPoissonEndomorphism` and `Arxiv.«math.0608009».PoissonConjectureFor`,
  from `FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean`.

`Challenge.lean` contains the same three definitions, character for character, so that the
statements checked by Palomar are Formal Conjectures' statements. `scripts/check-fc-match.py`
checks the copies against the Formal Conjectures sources.
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
