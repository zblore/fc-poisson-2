/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Poisson2.ChainRule
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Long's source coordinates and their brackets

C. D. Long (arXiv:2608.23777, Sections 3 and 4) works in the polynomial coordinates
`(x, y, β, D₀)` on `K[x, q, p, z]`, where
`β = 3x²p + 2(1 - 3xq)z - 9q²`, `y = q - xβ/3` and `D₀ = (1 + 3xq)p/2 - 3q²z`.

In Formal Conjectures' indexing the variables are `x = X₁`, `q = X₂`, `p = X₃`, `z = X₄`, so
`{x, p} = {q, z} = 1`. Long's bracket has the opposite sign (`{p, x} = 1`). Every bracket below
is FC's `poissonBracket`.

The main result of this file, `poissonBracket_coord`, gives the brackets of the four coordinates
as polynomials in the coordinates themselves, with `Q = y + xβ/3` (which equals `q`).
-/

@[expose] public section

namespace Poisson2

open MvPolynomial

/-- Numerals have zero partial derivatives. -/
@[simp]
theorem pderiv_ofNat {S ι : Type*} [CommSemiring S] (i : ι) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial ι S) = 0 := by
  rw [← Nat.cast_ofNat]
  exact Derivation.map_natCast _ n

variable (K : Type*) [Field K]

/-- The variable `x = X₁`. -/
noncomputable def vx : MvPolynomial (Fin 2 ⊕ Fin 2) K := X (Sum.inl 0)

/-- The variable `q = X₂`. -/
noncomputable def vq : MvPolynomial (Fin 2 ⊕ Fin 2) K := X (Sum.inl 1)

/-- The variable `p = X₃`. -/
noncomputable def vp : MvPolynomial (Fin 2 ⊕ Fin 2) K := X (Sum.inr 0)

/-- The variable `z = X₄`. -/
noncomputable def vz : MvPolynomial (Fin 2 ⊕ Fin 2) K := X (Sum.inr 1)

/-- Long's `β = 3x²p + 2(1 - 3xq)z - 9q²`. -/
noncomputable def β : MvPolynomial (Fin 2 ⊕ Fin 2) K :=
  3 * vx K ^ 2 * vp K + 2 * (1 - 3 * vx K * vq K) * vz K - 9 * vq K ^ 2

/-- Long's `y = q - xβ/3`. -/
noncomputable def y : MvPolynomial (Fin 2 ⊕ Fin 2) K :=
  vq K - C (1 / 3) * vx K * β K

/-- Long's `D₀ = (1 + 3xq)p/2 - 3q²z`. -/
noncomputable def D₀ : MvPolynomial (Fin 2 ⊕ Fin 2) K :=
  C (1 / 2) * (1 + 3 * vx K * vq K) * vp K - 3 * vq K ^ 2 * vz K

/-- The source coordinates `(x, y, β, D₀)`. -/
noncomputable def u : Fin 4 → MvPolynomial (Fin 2 ⊕ Fin 2) K :=
  ![vx K, y K, β K, D₀ K]

/-- `Q = y + xβ/3` in the coordinate variables `X 0, X 1, X 2, X 3 = x, y, β, D₀`. -/
noncomputable def Qs : MvPolynomial (Fin 4) K := X 1 + C (1 / 3) * X 0 * X 2

/-- The bracket `{y, D₀}` in the coordinate variables. -/
noncomputable def brkYD : MvPolynomial (Fin 4) K :=
  -(3 * Qs K ^ 2 + C (1 / 6) * X 2 * (1 + 3 * X 0 * Qs K) +
    C (3 / 2) * X 0 * Qs K * (X 2 + 21 * Qs K ^ 2))

/-- The bracket `{β, D₀}` in the coordinate variables. -/
noncomputable def brkBD : MvPolynomial (Fin 4) K :=
  C (9 / 2) * Qs K * (X 2 + 21 * Qs K ^ 2)

/-- The bracket `{y, β}` in the coordinate variables. -/
noncomputable def brkYB : MvPolynomial (Fin 4) K :=
  2 - 6 * X 0 * X 1 - 3 * X 0 ^ 2 * X 2

/-- The brackets of the source coordinates, as polynomials in the coordinates. In FC's sign
convention the `x, y, β` entries are the negatives of Long's Proposition 6.2, and in the notation
of his Section 5 `{x, D₀} = A₃`, `{y, D₀} = −A₂` and `{β, D₀} = A₁`. -/
noncomputable def brk : Fin 4 → Fin 4 → MvPolynomial (Fin 4) K :=
  ![![0, -X 0 ^ 3, 3 * X 0 ^ 2, C (1 / 2) * (1 + 3 * X 0 * Qs K)],
    ![X 0 ^ 3, 0, brkYB K, brkYD K],
    ![-(3 * X 0 ^ 2), -brkYB K, 0, brkBD K],
    ![-(C (1 / 2) * (1 + 3 * X 0 * Qs K)), -brkYD K, -brkBD K, 0]]

variable [CharZero K]

-- The simp sets are shared by all sixteen cases, so some lemmas are unused in each case.
set_option linter.unusedSimpArgs false in
/-- **The bracket table.** The brackets of Long's source coordinates are polynomials in those
coordinates. -/
theorem poissonBracket_coord (j l : Fin 4) :
    poissonBracket (u K j) (u K l) = aeval (u K) (brk K j l) := by
  fin_cases j <;> fin_cases l <;>
  · simp only [u, brk, Fin.zero_eta, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp only [brkYB, brkYD, brkBD, Qs, map_add, map_sub, map_mul, map_neg, map_pow, map_one,
      map_zero, map_ofNat, aeval_X, aeval_C, algebraMap_eq, Fin.isValue, Matrix.cons_val,
      y, β, D₀, vx, vq, vp, vz]
    simp +decide only [poissonBracket, Fin.sum_univ_two, Derivation.leibniz,
      Derivation.leibniz_pow, map_add, map_sub, map_neg, pderiv_X, pderiv_C, pderiv_ofNat,
      Derivation.map_one_eq_zero, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      Fin.isValue, ↓reduceIte, smul_eq_mul, nsmul_eq_mul, mul_zero, zero_mul, mul_one, add_zero,
      zero_add, sub_zero, zero_sub, neg_zero, Nat.cast_ofNat, Nat.cast_one, Nat.reduceSub,
      pow_one]
    try
      apply MvPolynomial.funext
      intro e
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_one, map_zero, map_ofNat,
        eval_X, eval_C]
      ring

end Poisson2
