/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Poisson2.Coordinates

/-!
# Long's four polynomials and their brackets

Long's polynomials `R, T, D, S` (arXiv:2608.23777, Section 3), written in the coordinate
variables `X 0, X 1, X 2, X 3 = x, y, β, D₀` of `Poisson2.Coordinates`, with `u = xy`:

* `R = 2x - 3x²y - x³β`;
* `S = y + 3x(1 + u)²β + 3xy²(4 + 3u)`;
* `T = -((1 + u)³β + y²(1 + u)(4 + 3u)) / 2`;
* `D = D₀ + H`, where
  `H = y⁴(18u² + 78u + 125)/20 + 3βy²(u³ + 5u² + 10u - 5)/10 - β²(9u + 2)/6 - x²β³/6`.

The six identities below are Long's Theorem 5.2 in FC's sign convention, in which
`{R, D} = {T, S} = 1`.
-/

namespace Poisson2

open MvPolynomial

variable (K : Type*) [Field K]

/-- `u = xy` in the coordinate variables. -/
noncomputable def us : MvPolynomial (Fin 4) K := X 0 * X 1

/-- Long's `R`. -/
noncomputable def Rs : MvPolynomial (Fin 4) K := 2 * X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2

/-- Long's `S`. -/
noncomputable def Ss : MvPolynomial (Fin 4) K :=
  X 1 + 3 * X 0 * (1 + us K) ^ 2 * X 2 + 3 * X 0 * X 1 ^ 2 * (4 + 3 * us K)

/-- Long's `T`. -/
noncomputable def Ts : MvPolynomial (Fin 4) K :=
  C (-1 / 2) * ((1 + us K) ^ 3 * X 2 + X 1 ^ 2 * (1 + us K) * (4 + 3 * us K))

/-- Long's Hamiltonian correction `H`. -/
noncomputable def Hs : MvPolynomial (Fin 4) K :=
  C (1 / 20) * X 1 ^ 4 * (18 * us K ^ 2 + 78 * us K + 125) +
    C (3 / 10) * X 2 * X 1 ^ 2 * (us K ^ 3 + 5 * us K ^ 2 + 10 * us K - 5) -
    C (1 / 6) * X 2 ^ 2 * (9 * us K + 2) - C (1 / 6) * X 0 ^ 2 * X 2 ^ 3

/-- Long's `D = D₀ + H`. -/
noncomputable def Ds : MvPolynomial (Fin 4) K := X 3 + Hs K

/-- The bracket of two polynomials in the coordinate variables, computed from the table `brk`. -/
noncomputable def cbr (F G : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∑ j, ∑ l, pderiv j F * pderiv l G * brk K j l

variable [CharZero K]

/-- Shared proof of the six identities: expand the table, differentiate symbolically, evaluate
at an arbitrary point and compare in `K`. -/
macro (name := coordIdentity) "coord_identity" : tactic => `(tactic| (
  simp only [cbr, Fin.sum_univ_four, brk, brkYB, brkYD, brkBD, Qs, Fin.isValue,
    Matrix.cons_val, Rs, Ss, Ts, Hs, Ds, us]
  simp +decide only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, map_neg,
    pderiv_X, pderiv_C, pderiv_ofNat, Derivation.map_one_eq_zero, Pi.single_apply, Fin.isValue,
    ↓reduceIte, smul_eq_mul, nsmul_eq_mul, mul_zero, zero_mul, mul_one, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, Nat.cast_ofNat]
  apply MvPolynomial.funext
  intro e
  simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_one, map_zero, map_ofNat,
    eval_X, eval_C]
  ring))

set_option linter.unusedSimpArgs false

theorem cbr_R_T : cbr K (Rs K) (Ts K) = C 0 := by coord_identity

theorem cbr_R_D : cbr K (Rs K) (Ds K) = C 1 := by coord_identity

theorem cbr_R_S : cbr K (Rs K) (Ss K) = C 0 := by coord_identity

theorem cbr_T_D : cbr K (Ts K) (Ds K) = C 0 := by coord_identity

theorem cbr_T_S : cbr K (Ts K) (Ss K) = C 1 := by coord_identity

theorem cbr_D_S : cbr K (Ds K) (Ss K) = C 0 := by coord_identity

end Poisson2
