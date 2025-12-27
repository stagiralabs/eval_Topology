import VerifiedAgora.tagger
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.GroupTheory.Archimedean
import Mathlib.Topology.Order.Basic

/-!
# Topology on archimedean groups and fields

In this file we prove the following theorems:

- `Rat.denseRange_cast`: the coercion from `ℚ` to a linear ordered archimedean field has dense
  range;

- `AddSubgroup.dense_of_not_isolated_zero`, `AddSubgroup.dense_of_no_min`: two sufficient conditions
  for a subgroup of an archimedean linear ordered additive commutative group to be dense;

- `AddSubgroup.dense_or_cyclic`: an additive subgroup of an archimedean linear ordered additive
  commutative group `G` with order topology either is dense in `G` or is a cyclic subgroup.
-/

open Set

/-- Rational numbers are dense in a linear ordered archimedean field. -/
@[target] theorem Rat.denseRange_cast {𝕜} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [Archimedean 𝕜] : DenseRange ((↑) : ℚ → 𝕜) := by sorry


namespace AddSubgroup

variable {G : Type*} [LinearOrderedAddCommGroup G] [TopologicalSpace G] [OrderTopology G]
  [Archimedean G]

/-- An additive subgroup of an archimedean linear ordered additive commutative group with order
topology is dense provided that for all positive `ε` there exists a positive element of the
subgroup that is less than `ε`. -/
@[target] theorem dense_of_not_isolated_zero (S : AddSubgroup G) (hS : ∀ ε > 0, ∃ g ∈ S, g ∈ Ioo 0 ε) :
    Dense (S : Set G) := by sorry


/-- Let `S` be a nontrivial additive subgroup in an archimedean linear ordered additive commutative
group `G` with order topology. If the set of positive elements of `S` does not have a minimal
element, then `S` is dense `G`. -/
theorem dense_of_no_min (S : AddSubgroup G) (hbot : S ≠ ⊥)
    (H : ¬∃ a : G, IsLeast { g : G | g ∈ S ∧ 0 < g } a) : Dense (S : Set G) := by
  refine S.dense_of_not_isolated_zero fun ε ε0 => ?_
  contrapose! H
  exact exists_isLeast_pos hbot ε0 (disjoint_left.2 H)

/-- An additive subgroup of an archimedean linear ordered additive commutative group `G` with order
topology either is dense in `G` or is a cyclic subgroup. -/
@[target] theorem dense_or_cyclic (S : AddSubgroup G) : Dense (S : Set G) ∨ ∃ a : G, S = closure {a} := by sorry


end AddSubgroup
