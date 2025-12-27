import VerifiedAgora.tagger
/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected compact Hausdorff spaces.

## Overview

This file defines the type `Stonean` of all extremally (note: not "extremely"!)
disconnected compact Hausdorff spaces, gives it the structure of a large category,
and proves some basic observations about this category and various functors from it.

The Lean implementation: a term of type `Stonean` is a pair, considering of
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`,
in the sense of category theory (i.e., such that morphisms out of the object
can be lifted along epimorphisms).

## Main definitions

* `Stonean` : the category of extremally disconnected compact Hausdorff spaces.
* `Stonean.toCompHaus` : the forgetful functor `Stonean ⥤ CompHaus` from Stonean
  spaces to compact Hausdorff spaces
* `Stonean.toProfinite` : the functor from Stonean spaces to profinite spaces.

## Implementation

The category `Stonean` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/
universe u

open CategoryTheory
open scoped Topology

/-- `Stonean` is the category of extremally disconnected compact Hausdorff spaces. -/
abbrev Stonean := CompHausLike (fun X ↦ ExtremallyDisconnected X)

namespace CompHaus

/-- `Projective` implies `ExtremallyDisconnected`. -/
instance (X : CompHaus.{u}) [Projective X] : ExtremallyDisconnected X := by
  apply CompactT2.Projective.extremallyDisconnected
  intro A B _ _ _ _ _ _ f g hf hg hsurj
  let A' : CompHaus := CompHaus.of A
  let B' : CompHaus := CompHaus.of B
  let f' : X ⟶ B' := CompHausLike.ofHom _ ⟨f, hf⟩
  let g' : A' ⟶ B' := CompHausLike.ofHom _ ⟨g,hg⟩
  have : Epi g' := by
    rw [CompHaus.epi_iff_surjective]
    assumption
  obtain ⟨h, hh⟩ := Projective.factors f' g'
  refine ⟨h, h.hom.2, ?_⟩
  ext t
  apply_fun (fun e => e t) at hh
  exact hh

/-- `Projective` implies `Stonean`. -/
@[simps!]
def toStonean (X : CompHaus.{u}) [Projective X] :
    Stonean where
  toTop := by sorry


end CompHaus

namespace Stonean

/-- The (forgetful) functor from Stonean spaces to compact Hausdorff spaces. -/
abbrev toCompHaus : Stonean.{u} ⥤ CompHaus.{u} := by sorry


/-- The forgetful functor `Stonean ⥤ CompHaus` is fully faithful. -/
abbrev fullyFaithfulToCompHaus : toCompHaus.FullyFaithful := by sorry


open CompHausLike

instance (X : Type*) [TopologicalSpace X]
    [ExtremallyDisconnected X] : HasProp (fun Y ↦ ExtremallyDisconnected Y) X :=
  ⟨(inferInstance : ExtremallyDisconnected X)⟩

/-- Construct a term of `Stonean` from a type endowed with the structure of a
compact, Hausdorff and extremally disconnected topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : Stonean := by sorry


instance (X : Stonean.{u}) : ExtremallyDisconnected X := X.prop

/-- The functor from Stonean spaces to profinite spaces. -/
abbrev toProfinite : Stonean.{u} ⥤ Profinite.{u} := by sorry


/--
A finite discrete space as a Stonean space.
-/
def mkFinite (X : Type*) [Finite X] [TopologicalSpace X] [DiscreteTopology X] : Stonean where
  toTop := by sorry


/--
A morphism in `Stonean` is an epi iff it is surjective.
-/
@[target] lemma epi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by sorry

  classical
  let g : Y ⟶ mkFinite (ULift (Fin 2)) := TopCat.ofHom
    ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
  let h : Y ⟶ mkFinite (ULift (Fin 2)) := TopCat.ofHom ⟨fun _ => ⟨1⟩, continuous_const⟩
  have H : h = g := by
    rw [← cancel_epi f]
    ext x
    apply ULift.ext -- why is `ext` not doing this automatically?
    change 1 = ite _ _ _ -- why is `dsimp` not getting me here?
    rw [if_neg]
    refine mt (hVU ·) ?_ -- what would be an idiomatic tactic for this step?
    simpa only [U, Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      using exists_apply_eq_apply f x
  apply_fun fun e => (e y).down at H
  change 1 = ite _ _ _ at H -- why is `dsimp at H` not getting me here?
  rw [if_pos hyV] at H
  exact one_ne_zero H

/-- Every Stonean space is projective in `CompHaus` -/
instance instProjectiveCompHausCompHaus (X : Stonean) : Projective (toCompHaus.obj X) where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected (toCompHaus.obj X).toTop := X.prop
    have hf : Function.Surjective f := by rwa [← CompHaus.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.continuous f.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

/-- Every Stonean space is projective in `Profinite` -/
instance (X : Stonean) : Projective (toProfinite.obj X) where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected (toProfinite.obj X) := X.prop
    have hf : Function.Surjective f := by rwa [← Profinite.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.continuous f.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

/-- Every Stonean space is projective in `Stonean`. -/
instance (X : Stonean) : Projective X where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.toTop := X.prop
    have hf : Function.Surjective f := by rwa [← Stonean.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.continuous f.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

end Stonean

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is a Stonean space equipped with an epimorphism
  down to `X` (see `CompHaus.presentation.π` and `CompHaus.presentation.epi_π`). It is a
  "constructive" witness to the fact that `CompHaus` has enough projectives. -/
noncomputable
def presentation (X : CompHaus) : Stonean where
  toTop := by sorry


/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentation.π (X : CompHaus) : Stonean.toCompHaus.obj X.presentation ⟶ X := by sorry


/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance presentation.epi_π (X : CompHaus) : Epi (π X) :=
  (projectivePresentation X).epi

/-- The underlying `CompHaus` of a `Stonean`. -/
abbrev _root_.Stonean.compHaus (X : Stonean) := by sorry


/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is a Stonean space, `f : X ⟶ Y` an epi in `CompHaus` and `e : Z ⟶ Y` is arbitrary, then
`lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It exists because
`Z` is a projective object in `CompHaus`.
-/
noncomputable
def lift {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Z.compHaus ⟶ X := by sorry


@[target] lemma lift_lifts {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by sorry


lemma Gleason (X : CompHaus.{u}) :
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    show ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X.toTop, inferInstance⟩
    show Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCompHaus

end CompHaus

namespace Profinite

/-- If `X` is profinite, `presentation X` is a Stonean space equipped with an epimorphism down to
    `X` (see `Profinite.presentation.π` and `Profinite.presentation.epi_π`). -/
noncomputable
def presentation (X : Profinite) : Stonean where
  toTop := (profiniteToCompHaus.obj X).projectivePresentation.p.toTop
  prop := (profiniteToCompHaus.obj X).presentation.prop

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentation.π (X : Profinite) : Stonean.toProfinite.obj X.presentation ⟶ X :=
  (profiniteToCompHaus.obj X).projectivePresentation.f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance presentation.epi_π (X : Profinite) : Epi (π X) := by
  have := (profiniteToCompHaus.obj X).projectivePresentation.epi
  rw [CompHaus.epi_iff_surjective] at this
  rw [epi_iff_surjective]
  exact this

/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is a Stonean space, `f : X ⟶ Y` an epi in `Profinite` and `e : Z ⟶ Y` is arbitrary,
then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It is
`CompHaus.lift e f` as a morphism in `Profinite`.
-/
noncomputable
def lift {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Stonean.toProfinite.obj Z ⟶ X := Projective.factorThru e f

@[simp, reassoc]
lemma lift_lifts {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y)
    [Epi f] : lift e f ≫ f = e := by simp [lift]

@[target] lemma projective_of_extrDisc {X : Profinite.{u}} (hX : ExtremallyDisconnected X) :
    Projective X := by sorry


end Profinite
