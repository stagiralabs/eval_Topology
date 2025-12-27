import VerifiedAgora.tagger
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Topology.Bornology.Basic

/-!
# Bornology structure on products and subtypes

In this file we define `Bornology` and `BoundedSpace` instances on `α × β`, `Π i, π i`, and
`{x // p x}`. We also prove basic lemmas about `Bornology.cobounded` and `Bornology.IsBounded`
on these types.
-/


open Set Filter Bornology Function

open Filter

variable {α β ι : Type*} {π : ι → Type*} [Bornology α] [Bornology β]
  [∀ i, Bornology (π i)]

instance Prod.instBornology : Bornology (α × β) where
  cobounded' := (cobounded α).coprod (cobounded β)
  le_cofinite' :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite

instance Pi.instBornology : Bornology (∀ i, π i) where
  cobounded' := Filter.coprodᵢ fun i => cobounded (π i)
  le_cofinite' := iSup_le fun _ ↦ (comap_mono (Bornology.le_cofinite _)).trans (comap_cofinite_le _)

/-- Inverse image of a bornology. -/
abbrev Bornology.induced {α β : Type*} [Bornology β] (f : α → β) : Bornology α where
  cobounded' := comap f (cobounded β)
  le_cofinite' := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)

instance {p : α → Prop} : Bornology (Subtype p) :=
  Bornology.induced (Subtype.val : Subtype p → α)

namespace Bornology

/-!
### Bounded sets in `α × β`
-/


@[target] theorem cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) := by sorry


@[target] theorem isBounded_image_fst_and_snd {s : Set (α × β)} :
    IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded s := by sorry


lemma IsBounded.image_fst {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.fst '' s) :=
  (isBounded_image_fst_and_snd.2 hs).1

lemma IsBounded.image_snd {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.snd '' s) :=
  (isBounded_image_fst_and_snd.2 hs).2

variable {s : Set α} {t : Set β} {S : ∀ i, Set (π i)}

@[target] theorem IsBounded.fst_of_prod (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty) : IsBounded s := by sorry


@[target] theorem IsBounded.snd_of_prod (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty) : IsBounded t := by sorry


@[target] theorem IsBounded.prod (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ˢ t) := by sorry


theorem isBounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) :
    IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t :=
  ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩

theorem isBounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or]

@[target] theorem isBounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s := by sorry



@[target] theorem cobounded_pi : cobounded (∀ i, π i) = Filter.coprodᵢ fun i => cobounded (π i) := by sorry


theorem forall_isBounded_image_eval_iff {s : Set (∀ i, π i)} :
    (∀ i, IsBounded (eval i '' s)) ↔ IsBounded s :=
  compl_mem_coprodᵢ.symm

@[target] lemma IsBounded.image_eval {s : Set (∀ i, π i)} (hs : IsBounded s) (i : ι) :
    IsBounded (eval i '' s) := by sorry


theorem IsBounded.pi (h : ∀ i, IsBounded (S i)) : IsBounded (pi univ S) :=
  forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset

@[target] theorem isBounded_pi_of_nonempty (hne : (pi univ S).Nonempty) :
    IsBounded (pi univ S) ↔ ∀ i, IsBounded (S i) := by sorry


@[target] theorem isBounded_pi : IsBounded (pi univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, IsBounded (S i) := by sorry



@[target] theorem isBounded_induced {α β : Type*} [Bornology β] {f : α → β} {s : Set α} :
    @IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s) := by sorry


@[target] theorem isBounded_image_subtype_val {p : α → Prop} {s : Set { x // p x }} :
    IsBounded (Subtype.val '' s) ↔ IsBounded s := by sorry


end Bornology

/-!
### Bounded spaces
-/


open Bornology

instance [BoundedSpace α] [BoundedSpace β] : BoundedSpace (α × β) := by
  simp [← cobounded_eq_bot_iff, cobounded_prod]

instance [∀ i, BoundedSpace (π i)] : BoundedSpace (∀ i, π i) := by
  simp [← cobounded_eq_bot_iff, cobounded_pi]

@[target] theorem boundedSpace_induced_iff {α β : Type*} [Bornology β] {f : α → β} :
    @BoundedSpace α (Bornology.induced f) ↔ IsBounded (range f) := by sorry


@[target] theorem boundedSpace_subtype_iff {p : α → Prop} :
    BoundedSpace (Subtype p) ↔ IsBounded { x | p x } := by sorry


theorem boundedSpace_val_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s :=
  boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_subtype⟩ := boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_val⟩ := boundedSpace_val_set_iff

instance [BoundedSpace α] {p : α → Prop} : BoundedSpace (Subtype p) :=
  (IsBounded.all { x | p x }).boundedSpace_subtype

/-!
### `Additive`, `Multiplicative`

The bornology on those type synonyms is inherited without change.
-/


instance : Bornology (Additive α) :=
  ‹Bornology α›

instance : Bornology (Multiplicative α) :=
  ‹Bornology α›

instance [BoundedSpace α] : BoundedSpace (Additive α) :=
  ‹BoundedSpace α›

instance [BoundedSpace α] : BoundedSpace (Multiplicative α) :=
  ‹BoundedSpace α›

/-!
### Order dual

The bornology on this type synonym is inherited without change.
-/


instance : Bornology αᵒᵈ :=
  ‹Bornology α›

instance [BoundedSpace α] : BoundedSpace αᵒᵈ :=
  ‹BoundedSpace α›
