/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Poisson2.Identities

/-!
# The rank-two Poisson conjecture is false

Long's endomorphism `φ` of `K[x, q, p, z]` sends `X₁, X₂, X₃, X₄ = x, q, p, z` to `R, T, D, S`
(written here as polynomials in the source coordinates `x, y, β, D₀`).

* `isPoissonEndomorphism_φ`: `φ` preserves the canonical bracket on generators, by the six
  identities of `Poisson2.Identities` and the bracket table of `Poisson2.Coordinates`.
* `φ_not_surjective`: `X₁` is not in the image. The points `(0, 0, 1/24, -1/8)` and
  `(1, 2/3, 247/96, -89/64)` (Long, Theorem 1.1) have the same image (it is `(0, 1/8, 0, 0)`,
  checked in `audit/Control.lean`), so every polynomial in the image of `φ` takes the same value
  at both, while `X₁` takes `0` and `1`.

The statements `dimension_two` and `poisson_conjecture` are Formal Conjectures'
`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_two` and
`Arxiv.«math.0608009».poisson_conjecture`, up to `K` being explicit here; the exact restatements
are in `Poisson2.FormalTarget`.
-/

@[expose] public section

namespace Poisson2

open MvPolynomial Arxiv.«math.0608009»

variable (K : Type*) [Field K] [CharZero K]

/-- The images of the generators `X₁, X₂, X₃, X₄`, in the coordinate variables. -/
noncomputable def F : Fin 2 ⊕ Fin 2 → MvPolynomial (Fin 4) K :=
  Sum.elim ![Rs K, Ts K] ![Ds K, Ss K]

/-- Long's Poisson endomorphism of `K[x, q, p, z]`. -/
noncomputable def φ : MvPolynomial (Fin 2 ⊕ Fin 2) K →ₐ[K] MvPolynomial (Fin 2 ⊕ Fin 2) K :=
  aeval fun v => aeval (u K) (F K v)

omit [CharZero K] in
theorem φ_X (v : Fin 2 ⊕ Fin 2) : φ K (X v) = aeval (u K) (F K v) := aeval_X _ _

/-- A bracket identity in the coordinate variables gives the bracket of the images. -/
theorem bracket_of_cbr (G₁ G₂ : MvPolynomial (Fin 4) K) (c : K) (h : cbr K G₁ G₂ = C c) :
    poissonBracket (aeval (u K) G₁) (aeval (u K) G₂) = C c :=
  poissonBracket_aeval_eq_C (u K) (brk K) (poissonBracket_coord K) G₁ G₂ c h

/-- The six independent off-diagonal brackets of `R, T, D, S`; the other six follow by
antisymmetry. -/
theorem bracket_images :
    poissonBracket (aeval (u K) (Rs K)) (aeval (u K) (Ts K)) = 0 ∧
    poissonBracket (aeval (u K) (Rs K)) (aeval (u K) (Ds K)) = 1 ∧
    poissonBracket (aeval (u K) (Rs K)) (aeval (u K) (Ss K)) = 0 ∧
    poissonBracket (aeval (u K) (Ts K)) (aeval (u K) (Ds K)) = 0 ∧
    poissonBracket (aeval (u K) (Ts K)) (aeval (u K) (Ss K)) = 1 ∧
    poissonBracket (aeval (u K) (Ds K)) (aeval (u K) (Ss K)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
  | rw [bracket_of_cbr K _ _ _ (cbr_R_T K), map_zero]
  | rw [bracket_of_cbr K _ _ _ (cbr_R_D K), map_one]
  | rw [bracket_of_cbr K _ _ _ (cbr_R_S K), map_zero]
  | rw [bracket_of_cbr K _ _ _ (cbr_T_D K), map_zero]
  | rw [bracket_of_cbr K _ _ _ (cbr_T_S K), map_one]
  | rw [bracket_of_cbr K _ _ _ (cbr_D_S K), map_zero]

/-- **Long's map is a Poisson endomorphism.** -/
theorem isPoissonEndomorphism_φ : IsPoissonEndomorphism (φ K) := by
  obtain ⟨hRT, hRD, hRS, hTD, hTS, hDS⟩ := bracket_images K
  intro v w
  rw [φ_X, φ_X]
  rcases v with v | v <;> rcases w with w | w <;> fin_cases v <;> fin_cases w <;>
    simp only [F, Sum.elim_inl, Sum.elim_inr, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, poissonBracket_self,
      poissonBracket_X_inl_inl, poissonBracket_X_inr_inr, poissonBracket_X_inl_inr,
      poissonBracket_X_inr_inl, poissonBracket_swap (aeval (u K) (Ts K)) (aeval (u K) (Rs K)),
      poissonBracket_swap (aeval (u K) (Ds K)) (aeval (u K) (Rs K)),
      poissonBracket_swap (aeval (u K) (Ss K)) (aeval (u K) (Rs K)),
      poissonBracket_swap (aeval (u K) (Ds K)) (aeval (u K) (Ts K)),
      poissonBracket_swap (aeval (u K) (Ss K)) (aeval (u K) (Ts K)),
      poissonBracket_swap (aeval (u K) (Ss K)) (aeval (u K) (Ds K)),
      hRT, hRD, hRS, hTD, hTS, hDS] <;>
    simp

omit [CharZero K] in
/-- Evaluating an image of `φ` at a point only depends on the values of `R, T, D, S` there. -/
theorem aeval_φ (P : Fin 2 ⊕ Fin 2 → K) (g : MvPolynomial (Fin 2 ⊕ Fin 2) K) :
    aeval P (φ K g) = aeval (fun v => aeval P (φ K (X v))) g := by
  rw [φ, ← AlgHom.comp_apply, comp_aeval]
  simp only [aeval_X]

/-- The first point of Long's three-point fibre, `(x, q, p, z) = (0, 0, 1/24, -1/8)`. -/
noncomputable def P₁ : Fin 2 ⊕ Fin 2 → K := Sum.elim ![0, 0] ![1 / 24, -1 / 8]

/-- The second point of Long's three-point fibre, `(x, q, p, z) = (1, 2/3, 247/96, -89/64)`. -/
noncomputable def P₂ : Fin 2 ⊕ Fin 2 → K := Sum.elim ![1, 2 / 3] ![247 / 96, -89 / 64]

/-- `φ` takes the same value at the two points. -/
theorem aeval_φ_X_P₁_eq_P₂ (v : Fin 2 ⊕ Fin 2) :
    aeval (P₁ K) (φ K (X v)) = aeval (P₂ K) (φ K (X v)) := by
  rw [φ_X, ← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply, comp_aeval]
  rcases v with v | v <;> fin_cases v <;>
    simp [F, Rs, Ts, Ds, Ss, Hs, us, u, P₁, P₂, vx, vq, vp, vz, β, y, D₀] <;> norm_num

/-- **`φ` is not surjective**: `X₁` is not in its image. -/
theorem φ_not_surjective : ¬ Function.Surjective (φ K) := by
  intro h
  obtain ⟨g, hg⟩ := h (X (Sum.inl 0))
  have h₁ := congrArg (aeval (P₁ K)) hg
  have h₂ := congrArg (aeval (P₂ K)) hg
  rw [aeval_φ, funext (aeval_φ_X_P₁_eq_P₂ K), ← aeval_φ, h₂] at h₁
  simp [P₁, P₂] at h₁

/-- **The Poisson conjecture is false for two canonical pairs** (Long 2026). This is the
statement of Formal Conjectures' `poisson_conjecture.variants.dimension_two`, with `K`
explicit. -/
theorem dimension_two : ¬ PoissonConjectureFor K 2 := fun h =>
  φ_not_surjective K (h (φ K) (isPoissonEndomorphism_φ K)).2

/-- **The Poisson conjecture is false.** This is the statement of Formal Conjectures'
`poisson_conjecture`, with `K` explicit. -/
theorem poisson_conjecture : ¬ ∀ n, PoissonConjectureFor K n := fun h =>
  dimension_two K (h 2)

end Poisson2
