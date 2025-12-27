import VerifiedAgora.tagger
/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Youle Fang, Jujian Zhang, Yuyang Zhao
-/
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# A profinite group is the projective limit of finite groups

We define the topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups.

## Main definitions

* `toFiniteQuotientFunctor` : The functor from `OpenNormalSubgroup P` to `FiniteGrp`
  sending an open normal subgroup `U` to `P ⧸ U`, where `P : ProfiniteGrp`.

* `toLimit` : The continuous homomorphism from a profinite group `P` to
  the projective limit of its quotients by open normal subgroups ordered by inclusion.

* `ContinuousMulEquivLimittoFiniteQuotientFunctor` : The `toLimit` is a
  `ContinuousMulEquiv`

## Main Statements

* `OpenNormalSubgroupSubClopenNhdsOfOne` : For any open neighborhood of `1` there is an
  open normal subgroup contained in it.

-/

universe u

open CategoryTheory IsTopologicalGroup

namespace ProfiniteGrp

instance (P : ProfiniteGrp) : SmallCategory (OpenNormalSubgroup P) :=
  Preorder.smallCategory (OpenNormalSubgroup ↑P.toProfinite.toTop)

/-- The functor from `OpenNormalSubgroup P` to `FiniteGrp` sending `U` to `P ⧸ U`,
where `P : ProfiniteGrp`. -/
def toFiniteQuotientFunctor (P : ProfiniteGrp) : OpenNormalSubgroup P ⥤ FiniteGrp where
  obj := fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
  map := fun fHK => FiniteGrp.ofHom (QuotientGroup.map _ _ (.id _) (leOfHom fHK))
  map_id _ := ConcreteCategory.ext <| QuotientGroup.map_id _
  map_comp f g := ConcreteCategory.ext <| (QuotientGroup.map_comp_map
    _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm

/-- The `MonoidHom` from a profinite group `P` to the projective limit of its quotients by
open normal subgroups ordered by inclusion -/
def toLimit_fun (P : ProfiniteGrp.{u}) : P →*
    limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  toFun p := by sorry


@[target] lemma toLimit_fun_continuous (P : ProfiniteGrp.{u}) : Continuous (toLimit_fun P) := by sorry


/-- The morphism in the category of `ProfiniteGrp` from a profinite group `P` to
the projective limit of its quotients by open normal subgroups ordered by inclusion -/
def toLimit (P : ProfiniteGrp.{u}) : P ⟶
    limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp) := by sorry


/-- An auxiliary result, superseded by `toLimit_surjective` -/
@[target] theorem denseRange_toLimit (P : ProfiniteGrp.{u}) : DenseRange (toLimit P) := by sorry


theorem toLimit_surjective (P : ProfiniteGrp.{u}) : Function.Surjective (toLimit P) := by
  have : IsClosed (Set.range P.toLimit) :=
    P.toLimit.hom.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← closure_eq_iff_isClosed.mpr this,
    Dense.closure_eq (denseRange_toLimit P)]

@[target] theorem toLimit_injective (P : ProfiniteGrp.{u}) : Function.Injective (toLimit P) := by sorry


/-- The topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups -/
noncomputable def continuousMulEquivLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) :
    P ≃ₜ* (limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)) := {
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨toLimit_injective P, toLimit_surjective P⟩)
    P.toLimit.hom.continuous_toFun) with
  map_mul' := (toLimit P).hom.map_mul' }

instance isIso_toLimit (P : ProfiniteGrp.{u}) : IsIso (toLimit P) := by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact ⟨toLimit_injective P, toLimit_surjective P⟩

/-- The isomorphism in the category of profinite group between a profinite group and
the projective limit of its quotients by open normal subgroups -/
noncomputable def isoLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) :
    P ≅ (limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)) :=
  ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivLimittoFiniteQuotientFunctor P)

end ProfiniteGrp
