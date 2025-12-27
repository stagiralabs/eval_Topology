import VerifiedAgora.tagger
/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHaus.Limits
import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
/-!

# Effective epimorphisms in `CompHaus`

This file proves that `EffectiveEpi`, `Epi` and `Surjective` are all equivalent in `CompHaus`.
As a consequence we deduce from the material in
`Mathlib.Topology.Category.CompHausLike.EffectiveEpi` that `CompHaus` is `Preregular`
and `Precoherent`.

We also prove that for a finite family of morphisms in `CompHaus` with fixed
target, the conditions jointly surjective, jointly epimorphic and effective epimorphic are all
equivalent.

## Projects

- Define regular categories, and show that `CompHaus` is regular.
- Define coherent categories, and show that `CompHaus` is actually coherent.

-/

universe u

open CategoryTheory Limits CompHausLike

namespace CompHaus

open List in
theorem effectiveEpi_tfae
    {B X : CompHaus.{u}} (π : X ⟶ B) :
    TFAE
    [ EffectiveEpi π
    , Epi π
    , Function.Surjective π
    ] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 → 1 := fun hπ ↦ ⟨⟨effectiveEpiStruct π hπ⟩⟩
  tfae_finish

instance : Preregular CompHaus :=
  preregular fun _ _ _ ↦ ((effectiveEpi_tfae _).out 0 2).mp

example : Precoherent CompHaus.{u} := inferInstance

-- TODO: prove this for `Type*`
open List in
@[target] theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ] := by sorry


theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Finite α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

end CompHaus
