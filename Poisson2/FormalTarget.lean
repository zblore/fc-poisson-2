/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Poisson2.Padding

/-!
# The Formal Conjectures statements

`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_two`,
`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three`,
`Arxiv.«math.0608009».poisson_conjecture.variants.dimension_ge_two` and
`Arxiv.«math.0608009».poisson_conjecture`, with Formal Conjectures' names, binders and statements
(`{K : Type*} [Field K] [CharZero K]`).

Palomar does not accept escaped name components such as `«math.0608009»` in theorem names, so
`Challenge.lean` states the same four statements in the namespace `PoissonConjecture`, with
Formal Conjectures' leaf names. They are proved here too, from the ones above. The `example`s at
the end check that the two sets of names have the same statements at every universe level, so
Comparator's check of the `PoissonConjecture` names covers Formal Conjectures' names as well.
-/

@[expose] public section

namespace Arxiv.«math.0608009»

variable {K : Type*} [Field K] [CharZero K]

/-- **The Poisson conjecture is false.** -/
theorem poisson_conjecture : ¬ ∀ n, PoissonConjectureFor K n :=
  Poisson2.poisson_conjecture K

/-- **The Poisson conjecture is false in dimension `2`** (Long 2026). -/
theorem poisson_conjecture.variants.dimension_two : ¬ PoissonConjectureFor K 2 :=
  Poisson2.dimension_two K

/-- **The Poisson conjecture is false in dimension `3`**: the case `n = 3` of `dimension_ge_two`.
(Formal Conjectures' docstring sketches a different proof, by the cotangent lift of Alpöge's
Jacobian counterexample.) -/
theorem poisson_conjecture.variants.dimension_three : ¬ PoissonConjectureFor K 3 :=
  Poisson2.dimension_ge_two K 3 (by norm_num)

/-- **The Poisson conjecture is false in every dimension `n ≥ 2`.** -/
theorem poisson_conjecture.variants.dimension_ge_two (n : ℕ) (hn : 2 ≤ n) :
    ¬ PoissonConjectureFor K n :=
  Poisson2.dimension_ge_two K n hn

end Arxiv.«math.0608009»

namespace PoissonConjecture

open Arxiv.«math.0608009»

variable {K : Type*} [Field K] [CharZero K]

/-- **The Poisson conjecture is false.** -/
theorem poisson_conjecture : ¬ ∀ n, PoissonConjectureFor K n :=
  Arxiv.«math.0608009».poisson_conjecture

/-- **The Poisson conjecture is false in dimension `2`** (Long 2026). -/
theorem poisson_conjecture.variants.dimension_two : ¬ PoissonConjectureFor K 2 :=
  Arxiv.«math.0608009».poisson_conjecture.variants.dimension_two

/-- **The Poisson conjecture is false in dimension `3`.** -/
theorem poisson_conjecture.variants.dimension_three : ¬ PoissonConjectureFor K 3 :=
  Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three

/-- **The Poisson conjecture is false in every dimension `n ≥ 2`.** -/
theorem poisson_conjecture.variants.dimension_ge_two (n : ℕ) (hn : 2 ≤ n) :
    ¬ PoissonConjectureFor K n :=
  Arxiv.«math.0608009».poisson_conjecture.variants.dimension_ge_two n hn

end PoissonConjecture

section

universe w

example : type_of% @Arxiv.«math.0608009».poisson_conjecture.{w} =
    type_of% @PoissonConjecture.poisson_conjecture.{w} :=
  rfl

example : type_of% @Arxiv.«math.0608009».poisson_conjecture.variants.dimension_two.{w} =
    type_of% @PoissonConjecture.poisson_conjecture.variants.dimension_two.{w} :=
  rfl

example : type_of% @Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three.{w} =
    type_of% @PoissonConjecture.poisson_conjecture.variants.dimension_three.{w} :=
  rfl

example : type_of% @Arxiv.«math.0608009».poisson_conjecture.variants.dimension_ge_two.{w} =
    type_of% @PoissonConjecture.poisson_conjecture.variants.dimension_ge_two.{w} :=
  rfl

end
