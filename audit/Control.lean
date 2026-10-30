/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Poisson2

/-!
# Controls

* The axiom audit would catch a `sorry`: `#print axioms` reports `sorryAx` for an unproved
  statement.
* The result specialises to the rationals.
* FC's bracket has `{X₁, X₃} = 1`, the sign the docstrings assume.
* Long's two points have the common image `(R, T, D, S) = (0, 1/8, 0, 0)` (his Theorem 1.1).
-/

open MvPolynomial Arxiv.«math.0608009» Poisson2

public theorem unproved : ¬ Arxiv.«math.0608009».PoissonConjectureFor ℚ 1 := by
  sorry

/-- info: 'unproved' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unproved

example : ¬ PoissonConjectureFor ℚ 2 :=
  Arxiv.«math.0608009».poisson_conjecture.variants.dimension_two

example : poissonBracket (X (Sum.inl 0) : MvPolynomial (Fin 2 ⊕ Fin 2) ℚ) (X (Sum.inr 0)) = 1 := by
  simp

/-- Long's common image `(0, 1/8, 0, 0)`, at the first point. -/
example : (fun v => aeval (P₁ ℚ) (φ ℚ (X v))) =
    Sum.elim ![(0 : ℚ), 1 / 8] ![0, 0] := by
  funext v
  rw [φ_X, ← AlgHom.comp_apply, comp_aeval]
  rcases v with v | v <;> fin_cases v <;>
    simp [F, Rs, Ts, Ds, Ss, Hs, us, u, P₁, vx, vq, vp, vz, β, y, D₀] <;> norm_num
