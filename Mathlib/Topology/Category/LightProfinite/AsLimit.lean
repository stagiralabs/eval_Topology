import VerifiedAgora.tagger
/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightProfinite.Basic
/-!
# Light profinite sets as limits of finite sets.

We show that any light profinite set is isomorphic to a sequential limit of finite sets.

The limit cone for `S : LightProfinite` is `S.asLimitCone`, the fact that it's a limit is
`S.asLimit`.

We also prove that the projection and transition maps in this limit are surjective.

-/

noncomputable section

open CategoryTheory Limits CompHausLike

namespace LightProfinite

universe u

variable (S : LightProfinite.{u})

/-- The functor `ℕᵒᵖ ⥤ FintypeCat` whose limit is isomorphic to `S`. -/
abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := by sorry


/-- An abbreviation for `S.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := by sorry


/--
A cone over `S.diagram` whose cone point is isomorphic to `S`.
(Auxiliary definition, use `S.asLimitCone` instead.)
-/
def asLimitConeAux : Cone S.diagram := by sorry


/-- An auxiliary isomorphism of cones used to prove that `S.asLimitConeAux` is a limit cone. -/
def isoMapCone : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone := by sorry


/--
`S.asLimitConeAux` is indeed a limit cone.
(Auxiliary definition, use `S.asLimit` instead.)
-/
def asLimitAux : IsLimit S.asLimitConeAux :=
  let hc : IsLimit (lightToProfinite.mapCone S.asLimitConeAux) :=
    S.toLightDiagram.isLimit.ofIsoLimit S.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

/-- A cone over `S.diagram` whose cone point is `S`. -/
def asLimitCone : Cone S.diagram where
  pt := by sorry


/-- `S.asLimitCone` is indeed a limit cone. -/
def asLimit : IsLimit S.asLimitCone := by sorry


/-- A bundled version of `S.asLimitCone` and `S.asLimit`. -/
def lim : Limits.LimitCone S.diagram := by sorry


/-- The projection from `S` to the `n`th component of `S.diagram`. -/
abbrev proj (n : ℕ) : S ⟶ S.diagram.obj ⟨n⟩ := S.asLimitCone.π.app ⟨n⟩

@[target] lemma lightToProfinite_map_proj_eq (n : ℕ) : lightToProfinite.map (S.proj n) =
    (lightToProfinite.obj S).asLimitCone.π.app _ := by sorry


@[target] lemma proj_surjective (n : ℕ) : Function.Surjective (S.proj n) := by sorry


/-- An abbreviation for the `n`th component of `S.diagram`. -/
abbrev component (n : ℕ) : LightProfinite := by sorry


/-- The transition map from `S_{n+1}` to `S_n` in `S.diagram`. -/
abbrev transitionMap (n : ℕ) :  S.component (n+1) ⟶ S.component n :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

/-- The transition map from `S_m` to `S_n` in `S.diagram`, when `m ≤ n`. -/
abbrev transitionMapLE {n m : ℕ} (h : n ≤ m) : S.component m ⟶ S.component n :=
  S.diagram.map ⟨homOfLE h⟩

@[target] lemma proj_comp_transitionMap (n : ℕ) :
    S.proj (n + 1) ≫ S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩ = S.proj n := by sorry


lemma proj_comp_transitionMap' (n : ℕ) : S.transitionMap n ∘ S.proj (n + 1) = S.proj n := by
  rw [← S.proj_comp_transitionMap n]
  rfl

@[target] lemma proj_comp_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    S.proj m ≫ S.diagram.map ⟨homOfLE h⟩ = S.proj n := by sorry


lemma proj_comp_transitionMapLE' {n m : ℕ} (h : n ≤ m) :
    S.transitionMapLE h ∘ S.proj m  = S.proj n := by
  rw [← S.proj_comp_transitionMapLE h]
  rfl

@[target] lemma surjective_transitionMap (n : ℕ) : Function.Surjective (S.transitionMap n) := by sorry


@[target] lemma surjective_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (S.transitionMapLE h) := by sorry


end LightProfinite
