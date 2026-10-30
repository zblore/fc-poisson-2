/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Poisson2.Main

/-!
# Padding: the Poisson conjecture fails for every `n ≥ 2`

An embedding `e : σ ↪ τ` of index types sends canonical pairs to canonical pairs. A Poisson
endomorphism `φ` on the pairs indexed by `σ` extends to the pairs indexed by `τ`: on the image
of `e` act by `φ` (after renaming the variables), and elsewhere act as the identity.

* `padImg_bracket`: the extension preserves the canonical bracket on generators.
* `not_surjective_pad`: if `φ` is not surjective then neither is the extension. The proof uses a
  retraction `retract e` that intertwines the two maps.

With `Fin 2 ↪ Fin n` and Long's map this proves Formal Conjectures'
`poisson_conjecture.variants.dimension_ge_two` (Long, Corollary 8.1).
-/

@[expose] public section

namespace Poisson2

open MvPolynomial Arxiv.«math.0608009»

section Rename

variable {R σ τ : Type*} [CommRing R] (e : σ ↪ τ)

/-- The renaming of variables `Sum.map e e`, which sends canonical pairs to canonical pairs. -/
abbrev pairMap : σ ⊕ σ → τ ⊕ τ := Sum.map e e

theorem pairMap_injective : Function.Injective (pairMap e) :=
  Sum.map_injective.2 ⟨e.injective, e.injective⟩

theorem pderiv_rename_of_notMem {i : τ ⊕ τ} (hi : i ∉ Set.range (pairMap e))
    (p : MvPolynomial (σ ⊕ σ) R) : pderiv i (rename (pairMap e) p) = 0 := by
  classical
  refine pderiv_eq_zero_of_notMem_vars fun h => hi ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (vars_rename _ _ h)
  exact ⟨j, rfl⟩

theorem inr_notMem_of_inl {i : τ} (h : Sum.inl i ∉ Set.range (pairMap e)) :
    Sum.inr i ∉ Set.range (pairMap e) := by
  rintro ⟨j | j, hj⟩
  · exact Sum.inl_ne_inr hj
  · exact h ⟨Sum.inl j, by simpa [pairMap] using hj⟩

theorem inl_notMem_of_inr {i : τ} (h : Sum.inr i ∉ Set.range (pairMap e)) :
    Sum.inl i ∉ Set.range (pairMap e) := by
  rintro ⟨j | j, hj⟩
  · exact h ⟨Sum.inr j, by simpa [pairMap] using hj⟩
  · exact Sum.inr_ne_inl hj

/-- Renaming along canonical pairs commutes with the canonical bracket. -/
theorem poissonBracket_rename [Fintype σ] [Fintype τ] (f g : MvPolynomial (σ ⊕ σ) R) :
    poissonBracket (rename (pairMap e) f) (rename (pairMap e) g) =
      rename (pairMap e) (poissonBracket f g) := by
  classical
  have hinj := pairMap_injective e
  rw [poissonBracket, poissonBracket, map_sum,
    ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Sum.inl (e i) : τ ⊕ τ) = pairMap e (Sum.inl i) from rfl,
      show (Sum.inr (e i) : τ ⊕ τ) = pairMap e (Sum.inr i) from rfl]
    simp only [pderiv_rename hinj, map_sub, map_mul]
  · intro i _ hi
    have hl : Sum.inl i ∉ Set.range (pairMap e) := by
      rintro ⟨j | j, hj⟩
      · exact hi (Finset.mem_map.2 ⟨j, Finset.mem_univ _, Sum.inl_injective hj⟩)
      · exact Sum.inr_ne_inl hj
    simp only [pderiv_rename_of_notMem e hl, pderiv_rename_of_notMem e (inr_notMem_of_inl e hl),
      mul_zero, sub_zero]

/-- A variable outside the image of the renaming commutes with every renamed polynomial. -/
theorem poissonBracket_X_rename_of_notMem [Fintype τ] {v : τ ⊕ τ} (hv : v ∉ Set.range (pairMap e))
    (g : MvPolynomial (σ ⊕ σ) R) : poissonBracket (X v) (rename (pairMap e) g) = 0 := by
  classical
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases v with i | i
  · rw [pderiv_X_of_ne (by simp : (Sum.inl i : τ ⊕ τ) ≠ Sum.inr k), zero_mul, sub_zero]
    by_cases hki : k = i
    · subst hki
      rw [pderiv_rename_of_notMem e (inr_notMem_of_inl e hv), mul_zero]
    · rw [pderiv_X_of_ne (by simpa [eq_comm] using hki), zero_mul]
  · rw [pderiv_X_of_ne (by simp : (Sum.inr i : τ ⊕ τ) ≠ Sum.inl k), zero_mul, zero_sub,
      neg_eq_zero]
    by_cases hki : k = i
    · subst hki
      rw [pderiv_rename_of_notMem e (inl_notMem_of_inr e hv), mul_zero]
    · rw [pderiv_X_of_ne (by simpa [eq_comm] using hki), zero_mul]

end Rename

section Pad

variable {K : Type*} [Field K] {σ τ : Type*} (e : σ ↪ τ)
  (φ : MvPolynomial (σ ⊕ σ) K →ₐ[K] MvPolynomial (σ ⊕ σ) K)

open Classical in
/-- The images of the generators under the padded map: `φ` on the image of `e`, the identity
elsewhere. -/
noncomputable def padImg (v : τ ⊕ τ) : MvPolynomial (τ ⊕ τ) K :=
  if h : v ∈ Set.range (pairMap e) then rename (pairMap e) (φ (X h.choose)) else X v

theorem padImg_pairMap (w : σ ⊕ σ) :
    padImg e φ (pairMap e w) = rename (pairMap e) (φ (X w)) := by
  have h : pairMap e w ∈ Set.range (pairMap e) := ⟨w, rfl⟩
  rw [padImg, dite_eq_left h, pairMap_injective e h.choose_spec]

theorem padImg_of_notMem {v : τ ⊕ τ} (hv : v ∉ Set.range (pairMap e)) :
    padImg e φ v = X v :=
  dite_eq_right hv

/-- The padded map preserves the canonical bracket on generators. -/
theorem padImg_bracket [Fintype σ] [Fintype τ]
    (hφ : ∀ v w, poissonBracket (φ (X v)) (φ (X w)) = poissonBracket (X v) (X w))
    (v w : τ ⊕ τ) :
    poissonBracket (padImg e φ v) (padImg e φ w) = poissonBracket (X v) (X w) := by
  by_cases hv : v ∈ Set.range (pairMap e) <;> by_cases hw : w ∈ Set.range (pairMap e)
  · obtain ⟨v, rfl⟩ := hv
    obtain ⟨w, rfl⟩ := hw
    rw [padImg_pairMap, padImg_pairMap, poissonBracket_rename, hφ, ← poissonBracket_rename,
      rename_X, rename_X]
  · obtain ⟨v, rfl⟩ := hv
    rw [padImg_pairMap, padImg_of_notMem e φ hw, poissonBracket_swap,
      poissonBracket_X_rename_of_notMem e hw, ← rename_X (pairMap e) v, poissonBracket_swap,
      poissonBracket_X_rename_of_notMem e hw]
  · obtain ⟨w, rfl⟩ := hw
    rw [padImg_of_notMem e φ hv, padImg_pairMap, poissonBracket_X_rename_of_notMem e hv,
      ← rename_X (pairMap e) w, poissonBracket_X_rename_of_notMem e hv]
  · rw [padImg_of_notMem e φ hv, padImg_of_notMem e φ hw]

open Classical in
/-- A retraction onto the pairs indexed by `σ`: rename back on the image of `e`, and send the
other variables to `0`. -/
noncomputable def retract : MvPolynomial (τ ⊕ τ) K →ₐ[K] MvPolynomial (σ ⊕ σ) K :=
  aeval fun v => if h : v ∈ Set.range (pairMap e) then X h.choose else 0

theorem retract_X_pairMap (w : σ ⊕ σ) :
    retract (K := K) e (X (pairMap e w)) = X w := by
  have h : pairMap e w ∈ Set.range (pairMap e) := ⟨w, rfl⟩
  rw [retract, aeval_X, dite_eq_left h, pairMap_injective e h.choose_spec]

theorem retract_X_of_notMem {v : τ ⊕ τ} (hv : v ∉ Set.range (pairMap e)) :
    retract (K := K) e (X v) = 0 := by
  rw [retract, aeval_X, dite_eq_right hv]

theorem retract_rename (p : MvPolynomial (σ ⊕ σ) K) : retract e (rename (pairMap e) p) = p := by
  have : (retract e).comp (rename (pairMap e)) = AlgHom.id K (MvPolynomial (σ ⊕ σ) K) := by
    refine algHom_ext fun w => ?_
    rw [AlgHom.comp_apply, rename_X, retract_X_pairMap, AlgHom.id_apply]
  exact congrArg (· p) (congrArg DFunLike.coe this)

/-- The retraction intertwines the padded map with `φ`. -/
theorem retract_comp_pad :
    (retract e).comp (aeval (padImg e φ)) = φ.comp (retract e) := by
  refine algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, aeval_X]
  by_cases hv : v ∈ Set.range (pairMap e)
  · obtain ⟨w, rfl⟩ := hv
    rw [padImg_pairMap, retract_rename, retract_X_pairMap]
  · rw [padImg_of_notMem e φ hv, retract_X_of_notMem e hv, map_zero]

/-- If `φ` is not surjective, neither is the padded map. -/
theorem not_surjective_pad (hφ : ¬ Function.Surjective φ) :
    ¬ Function.Surjective
      (aeval (padImg e φ) : MvPolynomial (τ ⊕ τ) K →ₐ[K] MvPolynomial (τ ⊕ τ) K) := by
  intro h
  refine hφ fun p => ?_
  obtain ⟨q, hq⟩ := h (rename (pairMap e) p)
  refine ⟨retract e q, ?_⟩
  rw [← AlgHom.comp_apply, ← retract_comp_pad, AlgHom.comp_apply, hq, retract_rename]

end Pad

variable (K : Type*) [Field K] [CharZero K]

/-- **The Poisson conjecture is false for every `n ≥ 2`**: pad Long's rank-two map with identity
pairs. This is the statement of Formal Conjectures' `poisson_conjecture.variants.dimension_ge_two`,
with `K` explicit.
-/
theorem dimension_ge_two (n : ℕ) (hn : 2 ≤ n) : ¬ PoissonConjectureFor K n := fun h =>
  not_surjective_pad (Fin.castLEEmb hn) (φ K) (φ_not_surjective K)
    (h _ fun v w => by
      rw [aeval_X, aeval_X]
      exact padImg_bracket _ _ (isPoissonEndomorphism_φ K) v w).2

end Poisson2
