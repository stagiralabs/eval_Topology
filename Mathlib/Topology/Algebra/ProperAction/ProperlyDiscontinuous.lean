import VerifiedAgora.tagger
/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# When a proper action is properly discontinuous

This file proves that if a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the action is properly
discontinuous if and only if it is proper. This is in particular true if `X` is first-countable or
weakly locally compact.

## Main statement
* `properlyDiscontinuousSMul_iff_properSMul`: If a discrete group acts on a T2 space `X` such that
  `X × X` is compactly generated, and if the action is continuous in the second variable,
  then the action is properly discontinuous if and only if it is proper.

## Tags

grouup action, proper action, properly discontinuous, compactly generated
-/

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]

open Prod Set

/-- If a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the action is properly
discontinuous if and only if it is proper. This is in particular true if `X` is first-countable or
weakly locally compact.

There was an older version of this theorem which was changed to this one to make use
of the `CompactlyGeneratedSpace` typeclass. (since 2024-11-10) -/
@[target] theorem properlyDiscontinuousSMul_iff_properSMul [T2Space X] [DiscreteTopology G]
    [ContinuousConstSMul G X] [CompactlyGeneratedSpace (X × X)] :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X := by sorry
