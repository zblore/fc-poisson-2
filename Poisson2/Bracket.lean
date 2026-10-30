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

public import Poisson2.Defs

/-!
# Basic lemmas about the canonical Poisson bracket

Copied from Formal Conjectures'
`FormalConjecturesForMathlib/Algebra/MvPolynomial/PoissonBracket.lean` (commit
`a6bf2bb646fc1926130c24781a3b3cf23d0ef288`). **Modified:** the definition is moved to
`Poisson2.Defs`, and in `poissonBracket_X_inl_inr` the deprecated `if_neg h` is replaced by
`ite_eq_right h`, the lemma it now abbreviates.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] [Fintype σ]

@[simp]
theorem poissonBracket_self (f : MvPolynomial (σ ⊕ σ) R) : poissonBracket f f = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [mul_comm, sub_self]

theorem poissonBracket_swap (f g : MvPolynomial (σ ⊕ σ) R) :
    poissonBracket f g = -poissonBracket g f := by
  rw [poissonBracket, poissonBracket, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp]
theorem poissonBracket_X_inl_inl (i j : σ) :
    poissonBracket (X (Sum.inl i) : MvPolynomial (σ ⊕ σ) R) (X (Sum.inl j)) = 0 :=
  Finset.sum_eq_zero fun k _ => by
    rw [pderiv_X_of_ne (show (Sum.inl j : σ ⊕ σ) ≠ Sum.inr k from by simp),
      pderiv_X_of_ne (show (Sum.inl i : σ ⊕ σ) ≠ Sum.inr k from by simp), mul_zero, zero_mul,
      sub_self]

@[simp]
theorem poissonBracket_X_inr_inr (i j : σ) :
    poissonBracket (X (Sum.inr i) : MvPolynomial (σ ⊕ σ) R) (X (Sum.inr j)) = 0 :=
  Finset.sum_eq_zero fun k _ => by
    rw [pderiv_X_of_ne (show (Sum.inr i : σ ⊕ σ) ≠ Sum.inl k from by simp),
      pderiv_X_of_ne (show (Sum.inr j : σ ⊕ σ) ≠ Sum.inl k from by simp), zero_mul, mul_zero,
      sub_self]

@[simp]
theorem poissonBracket_X_inl_inr [DecidableEq σ] (i j : σ) :
    poissonBracket (X (Sum.inl i) : MvPolynomial (σ ⊕ σ) R) (X (Sum.inr j)) =
      if i = j then 1 else 0 := by
  rw [poissonBracket, Finset.sum_eq_single i]
  · rw [pderiv_X_self, one_mul,
      pderiv_X_of_ne (show (Sum.inl i : σ ⊕ σ) ≠ Sum.inr i from by simp), zero_mul, sub_zero]
    rcases eq_or_ne i j with rfl | h
    · simp
    · rw [pderiv_X_of_ne (show (Sum.inr j : σ ⊕ σ) ≠ Sum.inr i from by simpa using Ne.symm h),
        ite_eq_right h]
  · intro k _ hk
    rw [pderiv_X_of_ne (show (Sum.inl i : σ ⊕ σ) ≠ Sum.inl k from by simpa using Ne.symm hk),
      pderiv_X_of_ne (show (Sum.inl i : σ ⊕ σ) ≠ Sum.inr k from by simp)]
    simp
  · simp

@[simp]
theorem poissonBracket_X_inr_inl [DecidableEq σ] (i j : σ) :
    poissonBracket (X (Sum.inr i) : MvPolynomial (σ ⊕ σ) R) (X (Sum.inl j)) =
      if i = j then -1 else 0 := by
  rw [poissonBracket_swap, poissonBracket_X_inl_inr]
  split_ifs with h₁ h₂ h₂ <;> simp_all [Ne.symm]

end MvPolynomial
