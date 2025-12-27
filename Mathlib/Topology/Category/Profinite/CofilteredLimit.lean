import VerifiedAgora.tagger
/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
import Mathlib.Topology.Category.TopCat.Limits.Konig

/-!
# Cofiltered limits of profinite sets.

This file contains some theorems about cofiltered limits of profinite sets.

## Main Results

- `exists_isClopen_of_cofiltered` shows that any clopen set in a cofiltered limit of profinite
  sets is the pullback of a clopen set from one of the factors in the limit.
- `exists_locally_constant` shows that any locally constant function from a cofiltered limit
  of profinite sets factors through one of the components.
-/

namespace Profinite

open CategoryTheory Limits

universe u v

variable {J : Type v} [SmallCategory J] [IsCofiltered J] {F : J ⥤ Profinite.{max u v}} (C : Cone F)

/-- If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
a clopen set in one of the terms in the limit.
-/
theorem exists_isClopen_of_cofiltered {U : Set C.pt} (hC : IsLimit C) (hU : IsClopen U) :
    ∃ (j : J) (V : Set (F.obj j)), IsClopen V ∧ U = C.π.app j ⁻¹' V := by
  -- First, we have the topological basis of the cofiltered limit obtained by pulling back
  -- clopen sets from the factors in the limit. By continuity, all such sets are again clopen.
  have hB := TopCat.isTopologicalBasis_cofiltered_limit.{u, v} (F ⋙ Profinite.toTopCat)
      (Profinite.toTopCat.mapCone C) (isLimitOfPreserves _ hC) (fun j => {W | IsClopen W}) ?_
      (fun i => isClopen_univ) (fun i U1 U2 hU1 hU2 => hU1.inter hU2) ?_
  rotate_left
  · intro i
    change TopologicalSpace.IsTopologicalBasis {W : Set (F.obj i) | IsClopen W}
    apply isTopologicalBasis_isClopen
  · rintro i j f V (hV : IsClopen _)
    exact ⟨hV.1.preimage ((F ⋙ toTopCat).map f).hom.continuous,
      hV.2.preimage ((F ⋙ toTopCat).map f).hom.continuous⟩
    -- Porting note: `<;> continuity` fails
  -- Using this, since `U` is open, we can write `U` as a union of clopen sets all of which
  -- are preimages of clopens from the factors in the limit.
  obtain ⟨S, hS, h⟩ := hB.open_eq_sUnion hU.2
  clear hB
  let j : S → J := fun s => (hS s.2).choose
  let V : ∀ s : S, Set (F.obj (j s)) := fun s => (hS s.2).choose_spec.choose
  have hV : ∀ s : S, IsClopen (V s) ∧ s.1 = C.π.app (j s) ⁻¹' V s := fun s =>
    (hS s.2).choose_spec.choose_spec

  -- Since `U` is also closed, hence compact, it is covered by finitely many of the
  -- clopens constructed in the previous step.
  have hUo : ∀ (i : ↑S), IsOpen ((fun s ↦ (C.π.app (j s)) ⁻¹' V s) i) := by
    intro s
    exact (hV s).1.2.preimage (C.π.app (j s)).hom.continuous
  have hsU : U ⊆ ⋃ (i : ↑S), (fun s ↦ C.π.app (j s) ⁻¹' V s) i := by
    dsimp only
    rw [h]
    rintro x ⟨T, hT, hx⟩
    refine ⟨_, ⟨⟨T, hT⟩, rfl⟩, ?_⟩
    dsimp only
    rwa [← (hV ⟨T, hT⟩).2]
  have := hU.1.isCompact.elim_finite_subcover (fun s : S => C.π.app (j s) ⁻¹' V s) hUo hsU
  -- Porting note: same remark as after `hB`
  -- We thus obtain a finite set `G : Finset J` and a clopen set of `F.obj j` for each
  -- `j ∈ G` such that `U` is the union of the preimages of these clopen sets.
  obtain ⟨G, hG⟩ := this
  -- Since `J` is cofiltered, we can find a single `j0` dominating all the `j ∈ G`.
  -- Pulling back all of the sets from the previous step to `F.obj j0` and taking a union,
  -- we obtain a clopen set in `F.obj j0` which works.
  classical
  obtain ⟨j0, hj0⟩ := IsCofiltered.inf_objs_exists (G.image j)
  let f : ∀ s ∈ G, j0 ⟶ j s := fun s hs => (hj0 (Finset.mem_image.mpr ⟨s, hs, rfl⟩)).some
  let W : S → Set (F.obj j0) := fun s => if hs : s ∈ G then F.map (f s hs) ⁻¹' V s else Set.univ
  -- Conclude, using the `j0` and the clopen set of `F.obj j0` obtained above.
  refine ⟨j0, ⋃ (s : S) (_ : s ∈ G), W s, ?_, ?_⟩
  · apply isClopen_biUnion_finset
    intro s hs
    dsimp [W]
    rw [dif_pos hs]
    exact ⟨(hV s).1.1.preimage (F.map _).hom.continuous,
      (hV s).1.2.preimage (F.map _).hom.continuous⟩
  · ext x
    constructor
    · intro hx
      simp_rw [W, Set.preimage_iUnion, Set.mem_iUnion]
      obtain ⟨_, ⟨s, rfl⟩, _, ⟨hs, rfl⟩, hh⟩ := hG hx
      refine ⟨s, hs, ?_⟩
      rwa [dif_pos hs, ← Set.preimage_comp, ← CompHausLike.coe_comp, C.w]
    · intro hx
      simp_rw [W, Set.preimage_iUnion, Set.mem_iUnion] at hx
      obtain ⟨s, hs, hx⟩ := hx
      rw [h]
      refine ⟨s.1, s.2, ?_⟩
      rw [(hV s).2]
      rwa [dif_pos hs, ← Set.preimage_comp, ← CompHausLike.coe_comp, C.w] at hx

@[target] theorem exists_locallyConstant_fin_two (hC : IsLimit C) (f : LocallyConstant C.pt (Fin 2)) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) (Fin 2)), f = g.comap (C.π.app _).hom := by sorry

  classical
  use j, LocallyConstant.ofIsClopen hV
  apply LocallyConstant.locallyConstant_eq_of_fiber_zero_eq
  simp only [Fin.isValue, Functor.const_obj_obj, LocallyConstant.coe_comap, Set.preimage_comp,
    LocallyConstant.ofIsClopen_fiber_zero]
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [← h]

open Classical in
@[target] theorem exists_locallyConstant_finite_aux {α : Type*} [Finite α] (hC : IsLimit C)
    (f : LocallyConstant C.pt α) : ∃ (j : J) (g : LocallyConstant (F.obj j) (α → Fin 2)),
      (f.map fun a b => if a = b then (0 : Fin 2) else 1) = g.comap (C.π.app _).hom := by sorry


@[target] theorem exists_locallyConstant_finite_nonempty {α : Type*} [Finite α] [Nonempty α]
    (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _).hom := by sorry

  classical
  let ι : α → α → Fin 2 := fun a b => if a = b then 0 else 1
  let σ : (α → Fin 2) → α := fun f => if h : ∃ a : α, ι a = f then h.choose else default
  refine ⟨j, gg.map σ, ?_⟩
  ext x
  simp only [Functor.const_obj_obj, LocallyConstant.coe_comap, LocallyConstant.map_apply,
    Function.comp_apply]
  dsimp [σ]
  have h1 : ι (f x) = gg (C.π.app j x) := by
    change f.map (fun a b => if a = b then (0 : Fin 2) else 1) x = _
    rw [h]
    rfl
  have h2 : ∃ a : α, ι a = gg (C.π.app j x) := ⟨f x, h1⟩
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [dif_pos h2]
  apply_fun ι
  · rw [h2.choose_spec]
    exact h1
  · intro a b hh
    have hhh := congr_fun hh a
    dsimp [ι] at hhh
    rw [if_pos rfl] at hhh
    split_ifs at hhh with hh1
    · exact hh1.symm
    · exact False.elim (bot_ne_top hhh)

/-- Any locally constant function from a cofiltered limit of profinite sets factors through
one of the components. -/
@[target] theorem exists_locallyConstant {α : Type*} (hC : IsLimit C) (f : LocallyConstant C.pt α) :
    ∃ (j : J) (g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _).hom := by sorry


end Profinite
