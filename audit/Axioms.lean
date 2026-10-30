/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

import Poisson2

/-!
# Axioms of the main results

Fails if any main result comes to depend on anything beyond Lean's three standard axioms.
-/

/--
info: 'Arxiv.«math.0608009».poisson_conjecture' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Arxiv.«math.0608009».poisson_conjecture

/--
info: 'Arxiv.«math.0608009».poisson_conjecture.variants.dimension_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Arxiv.«math.0608009».poisson_conjecture.variants.dimension_two

/--
info: 'Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Arxiv.«math.0608009».poisson_conjecture.variants.dimension_three

/--
info: 'Arxiv.«math.0608009».poisson_conjecture.variants.dimension_ge_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Arxiv.«math.0608009».poisson_conjecture.variants.dimension_ge_two

/--
info: 'PoissonConjecture.poisson_conjecture' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonConjecture.poisson_conjecture

/--
info: 'PoissonConjecture.poisson_conjecture.variants.dimension_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonConjecture.poisson_conjecture.variants.dimension_two

/--
info: 'PoissonConjecture.poisson_conjecture.variants.dimension_three' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonConjecture.poisson_conjecture.variants.dimension_three

/--
info: 'PoissonConjecture.poisson_conjecture.variants.dimension_ge_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonConjecture.poisson_conjecture.variants.dimension_ge_two

/--
info: 'Poisson2.pderiv_aeval' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Poisson2.pderiv_aeval

/--
info: 'Poisson2.poissonBracket_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Poisson2.poissonBracket_rename
