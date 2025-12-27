import VerifiedAgora.tagger
/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Topology.MetricSpace.Basic

/-!
# Infimum separation

This file defines the extended infimum separation of a set. This is approximately dual to the
diameter of a set, but where the extended diameter of a set is the supremum of the extended distance
between elements of the set, the extended infimum separation is the infimum of the (extended)
distance between *distinct* elements in the set.

We also define the infimum separation as the cast of the extended infimum separation to the reals.
This is the infimum of the distance between distinct elements of the set when in a pseudometric
space.

All lemmas and definitions are in the `Set` namespace to give access to dot notation.

## Main definitions
* `Set.einfsep`: Extended infimum separation of a set.
* `Set.infsep`: Infimum separation of a set (when in a pseudometric space).

-/


variable {α β : Type*}

namespace Set

section Einfsep

open ENNReal

open Function

/-- The "extended infimum separation" of a set with an edist function. -/
noncomputable def einfsep [EDist α] (s : Set α) : ℝ≥0∞ :=
  ⨅ (x ∈ s) (y ∈ s) (_ : x ≠ y), edist x y

section EDist

variable [EDist α] {x y : α} {s t : Set α}

@[target] theorem le_einfsep_iff {d} :
    d ≤ s.einfsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y := by sorry


@[target] theorem einfsep_zero : s.einfsep = 0 ↔ ∀ C > 0, ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < C := by sorry


@[target] theorem einfsep_pos : 0 < s.einfsep ↔ ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by sorry


@[target] theorem einfsep_top :
    s.einfsep = ∞ ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → edist x y = ∞ := by sorry


@[target] theorem einfsep_lt_top :
    s.einfsep < ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < ∞ := by sorry


@[target] theorem einfsep_ne_top :
    s.einfsep ≠ ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y ≠ ∞ := by sorry


@[target] theorem einfsep_lt_iff {d} :
    s.einfsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < d := by sorry


theorem nontrivial_of_einfsep_lt_top (hs : s.einfsep < ∞) : s.Nontrivial := by
  rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩

@[target] theorem nontrivial_of_einfsep_ne_top (hs : s.einfsep ≠ ∞) : s.Nontrivial := by sorry


@[target] theorem Subsingleton.einfsep (hs : s.Subsingleton) : s.einfsep = ∞ := by sorry


theorem le_einfsep_image_iff {d} {f : β → α} {s : Set β} : d ≤ einfsep (f '' s)
    ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) := by
  simp_rw [le_einfsep_iff, forall_mem_image]

@[target] theorem le_edist_of_le_einfsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.einfsep) : d ≤ edist x y := by sorry


@[target] theorem einfsep_le_edist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
    s.einfsep ≤ edist x y := by sorry


@[target] theorem einfsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : edist x y ≤ d) : s.einfsep ≤ d := by sorry


@[target] theorem le_einfsep {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y) : d ≤ s.einfsep := by sorry


@[target] theorem einfsep_empty : (∅ : Set α).einfsep = ∞ := by sorry


@[simp]
theorem einfsep_singleton : ({x} : Set α).einfsep = ∞ :=
  subsingleton_singleton.einfsep

@[target] theorem einfsep_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι → Set α) :
    (⋃ i ∈ o, s i).einfsep = ⨅ i ∈ o, (s i).einfsep := by sorry


@[target] theorem einfsep_anti (hst : s ⊆ t) : t.einfsep ≤ s.einfsep := by sorry


@[target] theorem einfsep_insert_le : (insert x s).einfsep ≤ ⨅ (y ∈ s) (_ : x ≠ y), edist x y := by sorry


@[target] theorem le_einfsep_pair : edist x y ⊓ edist y x ≤ ({x, y} : Set α).einfsep := by sorry


@[target] theorem einfsep_pair_le_left (hxy : x ≠ y) : ({x, y} : Set α).einfsep ≤ edist x y := by sorry


@[target] theorem einfsep_pair_le_right (hxy : x ≠ y) : ({x, y} : Set α).einfsep ≤ edist y x := by sorry


@[target] theorem einfsep_pair_eq_inf (hxy : x ≠ y) : ({x, y} : Set α).einfsep = edist x y ⊓ edist y x := by sorry


@[target] theorem einfsep_eq_iInf : s.einfsep = ⨅ d : s.offDiag, (uncurry edist) (d : α × α) := by sorry


theorem einfsep_of_fintype [DecidableEq α] [Fintype s] :
    s.einfsep = s.offDiag.toFinset.inf (uncurry edist) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

@[target] theorem Finite.einfsep (hs : s.Finite) : s.einfsep = hs.offDiag.toFinset.inf (uncurry edist) := by sorry


@[target] theorem Finset.coe_einfsep [DecidableEq α] {s : Finset α} :
    (s : Set α).einfsep = s.offDiag.inf (uncurry edist) := by sorry


@[target] theorem Nontrivial.einfsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep = edist x y := by sorry

  classical
    cases nonempty_fintype s
    simp_rw [einfsep_of_fintype]
    rcases Finset.exists_mem_eq_inf s.offDiag.toFinset (by simpa) (uncurry edist) with ⟨w, hxy, hed⟩
    simp_rw [mem_toFinset] at hxy
    exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

@[target] theorem Finite.einfsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep = edist x y := by sorry


end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y z : α} {s : Set α}

theorem einfsep_pair (hxy : x ≠ y) : ({x, y} : Set α).einfsep = edist x y := by
  nth_rw 1 [← min_self (edist x y)]
  convert einfsep_pair_eq_inf hxy using 2
  rw [edist_comm]

@[target] theorem einfsep_insert : einfsep (insert x s) =
    (⨅ (y ∈ s) (_ : x ≠ y), edist x y) ⊓ s.einfsep := by sorry


@[target] theorem einfsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    einfsep ({x, y, z} : Set α) = edist x y ⊓ edist x z ⊓ edist y z := by sorry


@[target] theorem le_einfsep_pi_of_le {π : β → Type*} [Fintype β] [∀ b, PseudoEMetricSpace (π b)]
    {s : ∀ b : β, Set (π b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ einfsep (s b)) :
    c ≤ einfsep (Set.pi univ s) := by sorry


end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {s : Set α}

theorem subsingleton_of_einfsep_eq_top (hs : s.einfsep = ∞) : s.Subsingleton := by
  rw [einfsep_top] at hs
  exact fun _ hx _ hy => of_not_not fun hxy => edist_ne_top _ _ (hs _ hx _ hy hxy)

@[target] theorem einfsep_eq_top_iff : s.einfsep = ∞ ↔ s.Subsingleton := by sorry


@[target] theorem Nontrivial.einfsep_ne_top (hs : s.Nontrivial) : s.einfsep ≠ ∞ := by sorry


@[target] theorem Nontrivial.einfsep_lt_top (hs : s.Nontrivial) : s.einfsep < ∞ := by sorry


@[target] theorem einfsep_lt_top_iff : s.einfsep < ∞ ↔ s.Nontrivial := by sorry


@[target] theorem einfsep_ne_top_iff : s.einfsep ≠ ∞ ↔ s.Nontrivial := by sorry


@[target] theorem le_einfsep_of_forall_dist_le {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y) :
    ENNReal.ofReal d ≤ s.einfsep := by sorry


end PseudoMetricSpace

section EMetricSpace

variable [EMetricSpace α] {s : Set α}

@[target] theorem einfsep_pos_of_finite [Finite s] : 0 < s.einfsep := by sorry


@[target] theorem relatively_discrete_of_finite [Finite s] :
    ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by sorry


@[target] theorem Finite.einfsep_pos (hs : s.Finite) : 0 < s.einfsep := by sorry


@[target] theorem Finite.relatively_discrete (hs : s.Finite) :
    ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by sorry


end EMetricSpace

end Einfsep

section Infsep

open ENNReal

open Set Function

/-- The "infimum separation" of a set with an edist function. -/
noncomputable def infsep [EDist α] (s : Set α) : ℝ :=
  ENNReal.toReal s.einfsep

section EDist

variable [EDist α] {x y : α} {s : Set α}

@[target] theorem infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞ := by sorry


@[target] theorem infsep_nonneg : 0 ≤ s.infsep := by sorry


@[target] theorem infsep_pos : 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞ := by sorry


@[target] theorem Subsingleton.infsep_zero (hs : s.Subsingleton) : s.infsep = 0 := by sorry


@[target] theorem nontrivial_of_infsep_pos (hs : 0 < s.infsep) : s.Nontrivial := by sorry


@[target] theorem infsep_empty : (∅ : Set α).infsep = 0 := by sorry


@[target] theorem infsep_singleton : ({x} : Set α).infsep = 0 := by sorry


@[target] theorem infsep_pair_le_toReal_inf (hxy : x ≠ y) :
    ({x, y} : Set α).infsep ≤ (edist x y ⊓ edist y x).toReal := by sorry


end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y : α}

theorem infsep_pair_eq_toReal : ({x, y} : Set α).infsep = (edist x y).toReal := by
  by_cases hxy : x = y
  · rw [hxy]
    simp only [infsep_singleton, pair_eq_singleton, edist_self, ENNReal.zero_toReal]
  · rw [infsep, einfsep_pair hxy]

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {x y z : α} {s t : Set α}

@[target] theorem Nontrivial.le_infsep_iff {d} (hs : s.Nontrivial) :
    d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y := by sorry


@[target] theorem Nontrivial.infsep_lt_iff {d} (hs : s.Nontrivial) :
    s.infsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ dist x y < d := by sorry


@[target] theorem Nontrivial.le_infsep {d} (hs : s.Nontrivial)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y) : d ≤ s.infsep := by sorry


@[target] theorem le_edist_of_le_infsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.infsep) : d ≤ dist x y := by sorry


@[target] theorem infsep_le_dist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.infsep ≤ dist x y := by sorry


theorem infsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : dist x y ≤ d) : s.infsep ≤ d :=
  le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'

theorem infsep_pair : ({x, y} : Set α).infsep = dist x y := by
  rw [infsep_pair_eq_toReal, edist_dist]
  exact ENNReal.toReal_ofReal dist_nonneg

@[target] theorem infsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ({x, y, z} : Set α).infsep = dist x y ⊓ dist x z ⊓ dist y z := by sorry


@[target] theorem Nontrivial.infsep_anti (hs : s.Nontrivial) (hst : s ⊆ t) : t.infsep ≤ s.infsep := by sorry


@[target] theorem infsep_eq_iInf [Decidable s.Nontrivial] :
    s.infsep = if s.Nontrivial then ⨅ d : s.offDiag, (uncurry dist) (d : α × α) else 0 := by sorry


@[target] theorem Nontrivial.infsep_eq_iInf (hs : s.Nontrivial) :
    s.infsep = ⨅ d : s.offDiag, (uncurry dist) (d : α × α) := by sorry

  classical rw [Set.infsep_eq_iInf, if_pos hs]

@[target] theorem infsep_of_fintype [Decidable s.Nontrivial] [DecidableEq α] [Fintype s] : s.infsep =
    if hs : s.Nontrivial then s.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 := by sorry


@[target] theorem Nontrivial.infsep_of_fintype [DecidableEq α] [Fintype s] (hs : s.Nontrivial) :
    s.infsep = s.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by sorry

  classical rw [Set.infsep_of_fintype, dif_pos hs]

@[target] theorem Finite.infsep [Decidable s.Nontrivial] (hsf : s.Finite) :
    s.infsep =
      if hs : s.Nontrivial then hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 := by sorry


@[target] theorem Finite.infsep_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    s.infsep = hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by sorry

  classical simp_rw [hsf.infsep, dif_pos hs]

@[target] theorem _root_.Finset.coe_infsep [DecidableEq α] (s : Finset α) : (s : Set α).infsep =
    if hs : s.offDiag.Nonempty then s.offDiag.inf' hs (uncurry dist) else 0 := by sorry


@[target] theorem _root_.Finset.coe_infsep_of_offDiag_nonempty [DecidableEq α] {s : Finset α}
    (hs : s.offDiag.Nonempty) : (s : Set α).infsep = s.offDiag.inf' hs (uncurry dist) := by sorry


@[target] theorem _root_.Finset.coe_infsep_of_offDiag_empty
    [DecidableEq α] {s : Finset α} (hs : s.offDiag = ∅) : (s : Set α).infsep = 0 := by sorry


@[target] theorem Nontrivial.infsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.infsep = dist x y := by sorry

  classical
    cases nonempty_fintype s
    simp_rw [hs.infsep_of_fintype]
    rcases Finset.exists_mem_eq_inf' (s := s.offDiag.toFinset) (by simpa) (uncurry dist) with
      ⟨w, hxy, hed⟩
    simp_rw [mem_toFinset] at hxy
    exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

theorem Finite.infsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.infsep = dist x y :=
  letI := hsf.fintype
  hs.infsep_exists_of_finite

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace α] {s : Set α}

theorem infsep_zero_iff_subsingleton_of_finite [Finite s] : s.infsep = 0 ↔ s.Subsingleton := by
  rw [infsep_zero, einfsep_eq_top_iff, or_iff_right_iff_imp]
  exact fun H => (einfsep_pos_of_finite.ne' H).elim

@[target] theorem infsep_pos_iff_nontrivial_of_finite [Finite s] : 0 < s.infsep ↔ s.Nontrivial := by sorry


@[target] theorem Finite.infsep_zero_iff_subsingleton (hs : s.Finite) : s.infsep = 0 ↔ s.Subsingleton := by sorry


@[target] theorem Finite.infsep_pos_iff_nontrivial (hs : s.Finite) : 0 < s.infsep ↔ s.Nontrivial := by sorry


@[target] theorem _root_.Finset.infsep_zero_iff_subsingleton (s : Finset α) :
    (s : Set α).infsep = 0 ↔ (s : Set α).Subsingleton := by sorry


@[target] theorem _root_.Finset.infsep_pos_iff_nontrivial (s : Finset α) :
    0 < (s : Set α).infsep ↔ (s : Set α).Nontrivial := by sorry


end MetricSpace

end Infsep

end Set
