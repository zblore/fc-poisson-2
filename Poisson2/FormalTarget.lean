/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Poisson2.Padding

/-!
# The Formal Conjectures statements

`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_two`,
`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three`,
`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_ge_two` and
`Arxiv.«math.0608009».poisson_conjecture`, with Formal Conjectures' own hypotheses
(`{K : Type*} [Field K] [CharZero K]`). The `example`s check that the statements proved here
are definitionally the statements in Formal Conjectures (pinned in `lakefile.toml`).
-/

universe w

namespace Poisson2

open Arxiv.«math.0608009»

/-- Formal Conjectures' `poisson_conjecture.variants.dimension_two`. -/
theorem fc_dimension_two {K : Type*} [Field K] [CharZero K] : ¬ PoissonConjectureFor K 2 :=
  dimension_two K

/-- Formal Conjectures' `poisson_conjecture.variants.dimension_ge_two`. -/
theorem fc_dimension_ge_two {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 2 ≤ n) :
    ¬ PoissonConjectureFor K n :=
  dimension_ge_two K n hn

/-- Formal Conjectures' `poisson_conjecture.variants.dimension_three`: the case `n = 3` of
`dimension_ge_two`. (Formal Conjectures' docstring sketches a different proof, by the cotangent lift
of Alpöge's Jacobian counterexample.) -/
theorem fc_dimension_three {K : Type*} [Field K] [CharZero K] : ¬ PoissonConjectureFor K 3 :=
  fc_dimension_ge_two 3 (by norm_num)

/-- Formal Conjectures' `poisson_conjecture`. -/
theorem fc_poisson_conjecture {K : Type*} [Field K] [CharZero K] :
    ¬ ∀ n, PoissonConjectureFor K n :=
  poisson_conjecture K

example : type_of% @fc_dimension_two.{w} =
    type_of% @poisson_conjecture.variants.dimension_two.{w} :=
  rfl

example : type_of% @fc_dimension_three.{w} =
    type_of% @poisson_conjecture.variants.dimension_three.{w} :=
  rfl

example : type_of% @fc_dimension_ge_two.{w} =
    type_of% @poisson_conjecture.variants.dimension_ge_two.{w} :=
  rfl

example : type_of% @fc_poisson_conjecture.{w} =
    type_of% @Arxiv.«math.0608009».poisson_conjecture.{w} :=
  rfl

end Poisson2
