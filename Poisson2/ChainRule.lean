/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Poisson2.Bracket

/-!
# Chain rules for substitution

For `u : τ → MvPolynomial σ R` and `F : MvPolynomial τ R`, the partial derivatives of the
substitution `aeval u F` are given by the chain rule (`pderiv_aeval`). Consequently the canonical
Poisson bracket of two substitutions is determined by the brackets of the `u j`
(`poissonBracket_aeval`): it is the bracket "in the coordinates `u`".
-/

@[expose] public section

namespace Poisson2

open MvPolynomial

variable {R σ τ : Type*} [CommRing R]

/-- The chain rule for partial derivatives of a substitution. -/
theorem pderiv_aeval [Fintype τ] (u : τ → MvPolynomial σ R) (F : MvPolynomial τ R) (i : σ) :
    pderiv i (aeval u F) = ∑ j, aeval u (pderiv j F) * pderiv i (u j) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, pderiv_X, map_add,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, Pi.single_apply, apply_ite (aeval u),
      map_zero, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

/-- The canonical Poisson bracket of two substitutions, in terms of the brackets of the
substituted polynomials. -/
theorem poissonBracket_aeval [Fintype σ] [Fintype τ] (u : τ → MvPolynomial (σ ⊕ σ) R)
    (F G : MvPolynomial τ R) :
    poissonBracket (aeval u F) (aeval u G) =
      ∑ j, ∑ l, aeval u (pderiv j F) * aeval u (pderiv l G) * poissonBracket (u j) (u l) := by
  simp only [poissonBracket, pderiv_aeval, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := (Finset.univ : Finset σ))]
  conv_rhs => rw [Finset.sum_comm (s := (Finset.univ : Finset τ))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset σ))]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- To evaluate the bracket of two substitutions it suffices to know the brackets of the
coordinates as substitutions `aeval u (π j l)`, and to compute in `MvPolynomial τ R`. -/
theorem poissonBracket_aeval_eq_C [Fintype σ] [Fintype τ] (u : τ → MvPolynomial (σ ⊕ σ) R)
    (π : τ → τ → MvPolynomial τ R)
    (hπ : ∀ j l, poissonBracket (u j) (u l) = aeval u (π j l))
    (F G : MvPolynomial τ R) (c : R)
    (h : ∑ j, ∑ l, pderiv j F * pderiv l G * π j l = C c) :
    poissonBracket (aeval u F) (aeval u G) = C c := by
  rw [poissonBracket_aeval]
  simp only [hπ, ← map_mul, ← map_sum, h, aeval_C, algebraMap_eq]

end Poisson2
