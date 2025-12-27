import VerifiedAgora.tagger
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This files introduces:
* `EMetric.infEdist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `EMetric.hausdorffEdist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `Metric.infDist`
  and `Metric.hausdorffDist`

## Main results
* `infEdist_closure`: the edistance to a set and its closure coincide
* `EMetric.mem_closure_iff_infEdist_zero`: a point `x` belongs to the closure of `s` iff
  `infEdist x s = 0`
* `IsCompact.exists_infEdist_eq_edist`: if `s` is compact and non-empty, there exists a point `y`
  which attains this edistance
* `IsOpen.exists_iUnion_isClosed`: every open set `U` can be written as the increasing union
  of countably many closed subsets of `U`

* `hausdorffEdist_closure`: replacing a set by its closure does not change the Hausdorff edistance
* `hausdorffEdist_zero_iff_closure_eq_closure`: two sets have Hausdorff edistance zero
  iff their closures coincide
* the Hausdorff edistance is symmetric and satisfies the triangle inequality
* in particular, closed sets in an emetric space are an emetric space
  (this is shown in `EMetricSpace.closeds.emetricspace`)

* versions of these notions on metric spaces
* `hausdorffEdist_ne_top_of_nonempty_of_bounded`: if two sets in a metric space
  are nonempty and bounded in a metric space, they are at finite Hausdorff edistance.

## Tags
metric space, Hausdorff distance
-/


noncomputable section

open NNReal ENNReal Topology Set Filter Pointwise Bornology

universe u v w

variable {ι : Sort*} {α : Type u} {β : Type v}

namespace EMetric

section InfEdist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t : Set α} {Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ≥0∞`. -/

/-- The minimal edistance of a point to a set -/
def infEdist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅ y ∈ s, edist x y

@[target] theorem infEdist_empty : infEdist x ∅ = ∞ := by sorry


theorem le_infEdist {d} : d ≤ infEdist x s ↔ ∀ y ∈ s, d ≤ edist x y := by
  simp only [infEdist, le_iInf_iff]

/-- The edist to a union is the minimum of the edists -/
@[simp]
theorem infEdist_union : infEdist x (s ∪ t) = infEdist x s ⊓ infEdist x t :=
  iInf_union

@[target] theorem infEdist_iUnion (f : ι → Set α) (x : α) : infEdist x (⋃ i, f i) = ⨅ i, infEdist x (f i) := by sorry


@[target] lemma infEdist_biUnion {ι : Type*} (f : ι → Set α) (I : Set ι) (x : α) :
    infEdist x (⋃ i ∈ I, f i) = ⨅ i ∈ I, infEdist x (f i) := by sorry


/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp]
theorem infEdist_singleton : infEdist x {y} = edist x y :=
  iInf_singleton

/-- The edist to a set is bounded above by the edist to any of its points -/
@[target] theorem infEdist_le_edist_of_mem (h : y ∈ s) : infEdist x s ≤ edist x y := by sorry


/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
@[target] theorem infEdist_zero_of_mem (h : x ∈ s) : infEdist x s = 0 := by sorry


/-- The edist is antitone with respect to inclusion. -/
@[target] theorem infEdist_anti (h : s ⊆ t) : infEdist x t ≤ infEdist x s := by sorry


/-- The edist to a set is `< r` iff there exists a point in the set at edistance `< r` -/
@[target] theorem infEdist_lt_iff {r : ℝ≥0∞} : infEdist x s < r ↔ ∃ y ∈ s, edist x y < r := by sorry


/-- The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y` -/
theorem infEdist_le_infEdist_add_edist : infEdist x s ≤ infEdist y s + edist x y :=
  calc
    ⨅ z ∈ s, edist x z ≤ ⨅ z ∈ s, edist y z + edist x y :=
      iInf₂_mono fun _ _ => (edist_triangle _ _ _).trans_eq (add_comm _ _)
    _ = (⨅ z ∈ s, edist y z) + edist x y := by simp only [ENNReal.iInf_add]

@[target] theorem infEdist_le_edist_add_infEdist : infEdist x s ≤ edist x y + infEdist y s := by sorry


@[target] theorem edist_le_infEdist_add_ediam (hy : y ∈ s) : edist x y ≤ infEdist x s + diam s := by sorry


/-- The edist to a set depends continuously on the point -/
@[target] theorem continuous_infEdist : Continuous fun x => infEdist x s := by sorry


/-- The edist to a set and to its closure coincide -/
@[target] theorem infEdist_closure : infEdist x (closure s) = infEdist x s := by sorry


/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
theorem mem_closure_iff_infEdist_zero : x ∈ closure s ↔ infEdist x s = 0 :=
  ⟨fun h => by
    rw [← infEdist_closure]
    exact infEdist_zero_of_mem h,
   fun h =>
    EMetric.mem_closure_iff.2 fun ε εpos => infEdist_lt_iff.mp <| by rwa [h]⟩

/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
@[target] theorem mem_iff_infEdist_zero_of_closed (h : IsClosed s) : x ∈ s ↔ infEdist x s = 0 := by sorry


/-- The infimum edistance of a point to a set is positive if and only if the point is not in the
closure of the set. -/
theorem infEdist_pos_iff_not_mem_closure {x : α} {E : Set α} :
    0 < infEdist x E ↔ x ∉ closure E := by
  rw [mem_closure_iff_infEdist_zero, pos_iff_ne_zero]

@[target] theorem infEdist_closure_pos_iff_not_mem_closure {x : α} {E : Set α} :
    0 < infEdist x (closure E) ↔ x ∉ closure E := by sorry


theorem exists_real_pos_lt_infEdist_of_not_mem_closure {x : α} {E : Set α} (h : x ∉ closure E) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < infEdist x E := by
  rw [← infEdist_pos_iff_not_mem_closure, ENNReal.lt_iff_exists_real_btwn] at h
  rcases h with ⟨ε, ⟨_, ⟨ε_pos, ε_lt⟩⟩⟩
  exact ⟨ε, ⟨ENNReal.ofReal_pos.mp ε_pos, ε_lt⟩⟩

@[target] theorem disjoint_closedBall_of_lt_infEdist {r : ℝ≥0∞} (h : r < infEdist x s) :
    Disjoint (closedBall x r) s := by sorry


/-- The infimum edistance is invariant under isometries -/
@[target] theorem infEdist_image (hΦ : Isometry Φ) : infEdist (Φ x) (Φ '' t) = infEdist x t := by sorry


@[to_additive (attr := by sorry


@[target] theorem _root_.IsOpen.exists_iUnion_isClosed {U : Set α} (hU : IsOpen U) :
    ∃ F : ℕ → Set α, (∀ n, IsClosed (F n)) ∧ (∀ n, F n ⊆ U) ∧ ⋃ n, F n = U ∧ Monotone F := by sorry


theorem _root_.IsCompact.exists_infEdist_eq_edist (hs : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infEdist x s = edist x y := by
  have A : Continuous fun y => edist x y := continuous_const.edist continuous_id
  obtain ⟨y, ys, hy⟩ := hs.exists_isMinOn hne A.continuousOn
  exact ⟨y, ys, le_antisymm (infEdist_le_edist_of_mem ys) (by rwa [le_infEdist])⟩

@[target] theorem exists_pos_forall_lt_edist (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ x ∈ s, ∀ y ∈ t, (r : ℝ≥0∞) < edist x y := by sorry


end InfEdist

/-! ### The Hausdorff distance as a function into `ℝ≥0∞`. -/

/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
irreducible_def hausdorffEdist {α : Type u} [PseudoEMetricSpace α] (s t : Set α) : ℝ≥0∞ :=
  (⨆ x ∈ s, infEdist x t) ⊔ ⨆ y ∈ t, infEdist y s

section HausdorffEdist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x : α} {s t u : Set α} {Φ : α → β}

/-- The Hausdorff edistance of a set to itself vanishes. -/
@[simp]
theorem hausdorffEdist_self : hausdorffEdist s s = 0 := by
  simp only [hausdorffEdist_def, sup_idem, ENNReal.iSup_eq_zero]
  exact fun x hx => infEdist_zero_of_mem hx

/-- The Haudorff edistances of `s` to `t` and of `t` to `s` coincide. -/
@[target] theorem hausdorffEdist_comm : hausdorffEdist s t = hausdorffEdist t s := by sorry


/-- Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set -/
theorem hausdorffEdist_le_of_infEdist {r : ℝ≥0∞} (H1 : ∀ x ∈ s, infEdist x t ≤ r)
    (H2 : ∀ x ∈ t, infEdist x s ≤ r) : hausdorffEdist s t ≤ r := by
  simp only [hausdorffEdist_def, sup_le_iff, iSup_le_iff]
  exact ⟨H1, H2⟩

/-- Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem hausdorffEdist_le_of_mem_edist {r : ℝ≥0∞} (H1 : ∀ x ∈ s, ∃ y ∈ t, edist x y ≤ r)
    (H2 : ∀ x ∈ t, ∃ y ∈ s, edist x y ≤ r) : hausdorffEdist s t ≤ r := by
  refine hausdorffEdist_le_of_infEdist (fun x xs ↦ ?_) (fun x xt ↦ ?_)
  · rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infEdist_le_edist_of_mem yt) hy
  · rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infEdist_le_edist_of_mem ys) hy

/-- The distance to a set is controlled by the Hausdorff distance. -/
@[target] theorem infEdist_le_hausdorffEdist_of_mem (h : x ∈ s) : infEdist x t ≤ hausdorffEdist s t := by sorry


/-- If the Hausdorff distance is `< r`, then any point in one of the sets has
a corresponding point at distance `< r` in the other set. -/
theorem exists_edist_lt_of_hausdorffEdist_lt {r : ℝ≥0∞} (h : x ∈ s) (H : hausdorffEdist s t < r) :
    ∃ y ∈ t, edist x y < r :=
  infEdist_lt_iff.mp <|
    calc
      infEdist x t ≤ hausdorffEdist s t := infEdist_le_hausdorffEdist_of_mem h
      _ < r := H

/-- The distance from `x` to `s` or `t` is controlled in terms of the Hausdorff distance
between `s` and `t`. -/
theorem infEdist_le_infEdist_add_hausdorffEdist :
    infEdist x t ≤ infEdist x s + hausdorffEdist s t :=
  ENNReal.le_of_forall_pos_le_add fun ε εpos h => by
    have ε0 : (ε / 2 : ℝ≥0∞) ≠ 0 := by simpa [pos_iff_ne_zero] using εpos
    have : infEdist x s < infEdist x s + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).1.ne ε0
    obtain ⟨y : α, ys : y ∈ s, dxy : edist x y < infEdist x s + ↑ε / 2⟩ := infEdist_lt_iff.mp this
    have : hausdorffEdist s t < hausdorffEdist s t + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).2.ne ε0
    obtain ⟨z : α, zt : z ∈ t, dyz : edist y z < hausdorffEdist s t + ↑ε / 2⟩ :=
      exists_edist_lt_of_hausdorffEdist_lt ys this
    calc
      infEdist x t ≤ edist x z := infEdist_le_edist_of_mem zt
      _ ≤ edist x y + edist y z := edist_triangle _ _ _
      _ ≤ infEdist x s + ε / 2 + (hausdorffEdist s t + ε / 2) := add_le_add dxy.le dyz.le
      _ = infEdist x s + hausdorffEdist s t + ε := by
        simp [ENNReal.add_halves, add_comm, add_left_comm]

/-- The Hausdorff edistance is invariant under isometries. -/
@[target] theorem hausdorffEdist_image (h : Isometry Φ) :
    hausdorffEdist (Φ '' s) (Φ '' t) = hausdorffEdist s t := by sorry


/-- The Hausdorff distance is controlled by the diameter of the union. -/
theorem hausdorffEdist_le_ediam (hs : s.Nonempty) (ht : t.Nonempty) :
    hausdorffEdist s t ≤ diam (s ∪ t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffEdist_le_of_mem_edist ?_ ?_
  · intro z hz
    exact ⟨y, yt, edist_le_diam_of_mem (subset_union_left hz) (subset_union_right yt)⟩
  · intro z hz
    exact ⟨x, xs, edist_le_diam_of_mem (subset_union_right hz) (subset_union_left xs)⟩

/-- The Hausdorff distance satisfies the triangle inequality. -/
@[target] theorem hausdorffEdist_triangle : hausdorffEdist s u ≤ hausdorffEdist s t + hausdorffEdist t u := by sorry


/-- Two sets are at zero Hausdorff edistance if and only if they have the same closure. -/
@[target] theorem hausdorffEdist_zero_iff_closure_eq_closure :
    hausdorffEdist s t = 0 ↔ closure s = closure t := by sorry


/-- The Hausdorff edistance between a set and its closure vanishes. -/
@[target] theorem hausdorffEdist_self_closure : hausdorffEdist s (closure s) = 0 := by sorry


/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem hausdorffEdist_closure₁ : hausdorffEdist (closure s) t = hausdorffEdist s t := by
  refine le_antisymm ?_ ?_
  · calc
      _ ≤ hausdorffEdist (closure s) s + hausdorffEdist s t := hausdorffEdist_triangle
      _ = hausdorffEdist s t := by simp [hausdorffEdist_comm]
  · calc
      _ ≤ hausdorffEdist s (closure s) + hausdorffEdist (closure s) t := hausdorffEdist_triangle
      _ = hausdorffEdist (closure s) t := by simp

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem hausdorffEdist_closure₂ : hausdorffEdist s (closure t) = hausdorffEdist s t := by
  simp [@hausdorffEdist_comm _ _ s _]

/-- The Hausdorff edistance between sets or their closures is the same. -/
@[target] theorem hausdorffEdist_closure : hausdorffEdist (closure s) (closure t) = hausdorffEdist s t := by sorry


/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide. -/
@[target] theorem hausdorffEdist_zero_iff_eq_of_closed (hs : IsClosed s) (ht : IsClosed t) :
    hausdorffEdist s t = 0 ↔ s = t := by sorry


/-- The Haudorff edistance to the empty set is infinite. -/
@[target] theorem hausdorffEdist_empty (ne : s.Nonempty) : hausdorffEdist s ∅ = ∞ := by sorry


/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty. -/
@[target] theorem nonempty_of_hausdorffEdist_ne_top (hs : s.Nonempty) (fin : hausdorffEdist s t ≠ ⊤) :
    t.Nonempty := by sorry


@[target] theorem empty_or_nonempty_of_hausdorffEdist_ne_top (fin : hausdorffEdist s t ≠ ⊤) :
    (s = ∅ ∧ t = ∅) ∨ (s.Nonempty ∧ t.Nonempty) := by sorry


end HausdorffEdist

-- section
end EMetric

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`sInf` and `sSup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/

--namespace
namespace Metric

section

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t u : Set α} {x y : α} {Φ : α → β}

open EMetric

/-! ### Distance of a point to a set as a function into `ℝ`. -/

/-- The minimal distance of a point to a set -/
def infDist (x : α) (s : Set α) : ℝ := by sorry


theorem infDist_eq_iInf : infDist x s = ⨅ y : s, dist x y := by
  rw [infDist, infEdist, iInf_subtype', ENNReal.toReal_iInf]
  · simp only [dist_edist]
  · exact fun _ ↦ edist_ne_top _ _

/-- The minimal distance is always nonnegative -/
@[target] theorem infDist_nonneg : 0 ≤ infDist x s := by sorry


/-- The minimal distance to the empty set is 0 (if you want to have the more reasonable
value `∞` instead, use `EMetric.infEdist`, which takes values in `ℝ≥0∞`) -/
@[target] theorem infDist_empty : infDist x ∅ = 0 := by sorry


/-- In a metric space, the minimal edistance to a nonempty set is finite. -/
theorem infEdist_ne_top (h : s.Nonempty) : infEdist x s ≠ ⊤ := by
  rcases h with ⟨y, hy⟩
  exact ne_top_of_le_ne_top (edist_ne_top _ _) (infEdist_le_edist_of_mem hy)

@[simp]
theorem infEdist_eq_top_iff : infEdist x s = ∞ ↔ s = ∅ := by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [*, Nonempty.ne_empty, infEdist_ne_top]

/-- The minimal distance of a point to a set containing it vanishes. -/
theorem infDist_zero_of_mem (h : x ∈ s) : infDist x s = 0 := by
  simp [infEdist_zero_of_mem h, infDist]

/-- The minimal distance to a singleton is the distance to the unique point in this singleton. -/
@[target] theorem infDist_singleton : infDist x {y} = dist x y := by sorry


/-- The minimal distance to a set is bounded by the distance to any point in this set. -/
@[target] theorem infDist_le_dist_of_mem (h : y ∈ s) : infDist x s ≤ dist x y := by sorry


/-- The minimal distance is monotone with respect to inclusion. -/
@[target] theorem infDist_le_infDist_of_subset (h : s ⊆ t) (hs : s.Nonempty) : infDist x t ≤ infDist x s := by sorry


/-- The minimal distance to a set `s` is `< r` iff there exists a point in `s` at distance `< r`. -/
@[target] theorem infDist_lt_iff {r : ℝ} (hs : s.Nonempty) : infDist x s < r ↔ ∃ y ∈ s, dist x y < r := by sorry


/-- The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`, modulo
the distance between `x` and `y`. -/
@[target] theorem infDist_le_infDist_add_dist : infDist x s ≤ infDist y s + dist x y := by sorry


theorem not_mem_of_dist_lt_infDist (h : dist x y < infDist x s) : y ∉ s := fun hy =>
  h.not_le <| infDist_le_dist_of_mem hy

theorem disjoint_ball_infDist : Disjoint (ball x (infDist x s)) s :=
  disjoint_left.2 fun _y hy => not_mem_of_dist_lt_infDist <| mem_ball'.1 hy

theorem ball_infDist_subset_compl : ball x (infDist x s) ⊆ sᶜ :=
  (disjoint_ball_infDist (s := s)).subset_compl_right

theorem ball_infDist_compl_subset : ball x (infDist x sᶜ) ⊆ s :=
  ball_infDist_subset_compl.trans_eq (compl_compl s)

@[target] theorem disjoint_closedBall_of_lt_infDist {r : ℝ} (h : r < infDist x s) :
    Disjoint (closedBall x r) s := by sorry


@[target] theorem dist_le_infDist_add_diam (hs : IsBounded s) (hy : y ∈ s) :
    dist x y ≤ infDist x s + diam s := by sorry


variable (s)

/-- The minimal distance to a set is Lipschitz in point with constant 1 -/
@[target] theorem lipschitz_infDist_pt : LipschitzWith 1 (infDist · s) := by sorry


/-- The minimal distance to a set is uniformly continuous in point -/
theorem uniformContinuous_infDist_pt : UniformContinuous (infDist · s) :=
  (lipschitz_infDist_pt s).uniformContinuous

/-- The minimal distance to a set is continuous in point -/
@[target] theorem continuous_infDist_pt : Continuous (infDist · s) := by sorry


variable {s}

/-- The minimal distances to a set and its closure coincide. -/
theorem infDist_closure : infDist x (closure s) = infDist x s := by
  simp [infDist, infEdist_closure]

/-- If a point belongs to the closure of `s`, then its infimum distance to `s` equals zero.
The converse is true provided that `s` is nonempty, see `Metric.mem_closure_iff_infDist_zero`. -/
@[target] theorem infDist_zero_of_mem_closure (hx : x ∈ closure s) : infDist x s = 0 := by sorry


/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes. -/
theorem mem_closure_iff_infDist_zero (h : s.Nonempty) : x ∈ closure s ↔ infDist x s = 0 := by
  simp [mem_closure_iff_infEdist_zero, infDist, ENNReal.toReal_eq_zero_iff, infEdist_ne_top h]

@[target] theorem infDist_pos_iff_not_mem_closure (hs : s.Nonempty) :
    x ∉ closure s ↔ 0 < infDist x s := by sorry


/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
@[target] theorem _root_.IsClosed.mem_iff_infDist_zero (h : IsClosed s) (hs : s.Nonempty) :
    x ∈ s ↔ infDist x s = 0 := by sorry


/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes. -/
@[target] theorem _root_.IsClosed.not_mem_iff_infDist_pos (h : IsClosed s) (hs : s.Nonempty) :
    x ∉ s ↔ 0 < infDist x s := by sorry


@[target] theorem continuousAt_inv_infDist_pt (h : x ∉ closure s) :
    ContinuousAt (fun x ↦ (infDist x s)⁻¹) x := by sorry


/-- The infimum distance is invariant under isometries. -/
theorem infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ '' t) = infDist x t := by
  simp [infDist, infEdist_image hΦ]

@[target] theorem infDist_inter_closedBall_of_mem (h : y ∈ s) :
    infDist x (s ∩ closedBall x (dist y x)) = infDist x s := by sorry


@[target] theorem _root_.IsCompact.exists_infDist_eq_dist (h : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infDist x s = dist x y := by sorry


@[target] theorem _root_.IsClosed.exists_infDist_eq_dist [ProperSpace α] (h : IsClosed s) (hne : s.Nonempty)
    (x : α) : ∃ y ∈ s, infDist x s = dist x y := by sorry


@[target] theorem exists_mem_closure_infDist_eq_dist [ProperSpace α] (hne : s.Nonempty) (x : α) :
    ∃ y ∈ closure s, infDist x s = dist x y := by sorry


/-- The minimal distance of a point to a set as a `ℝ≥0` -/
def infNndist (x : α) (s : Set α) : ℝ≥0 := by sorry


@[simp]
theorem coe_infNndist : (infNndist x s : ℝ) = infDist x s :=
  rfl

/-- The minimal distance to a set (as `ℝ≥0`) is Lipschitz in point with constant 1 -/
theorem lipschitz_infNndist_pt (s : Set α) : LipschitzWith 1 fun x => infNndist x s :=
  LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

/-- The minimal distance to a set (as `ℝ≥0`) is uniformly continuous in point -/
theorem uniformContinuous_infNndist_pt (s : Set α) : UniformContinuous fun x => infNndist x s :=
  (lipschitz_infNndist_pt s).uniformContinuous

/-- The minimal distance to a set (as `ℝ≥0`) is continuous in point -/
@[target] theorem continuous_infNndist_pt (s : Set α) : Continuous fun x => infNndist x s := by sorry


/-- The Hausdorff distance between two sets is the smallest nonnegative `r` such that each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is defined to
be `0`, arbitrarily. -/
def hausdorffDist (s t : Set α) : ℝ :=
  ENNReal.toReal (hausdorffEdist s t)

/-- The Hausdorff distance is nonnegative. -/
@[target] theorem hausdorffDist_nonneg : 0 ≤ hausdorffDist s t := by sorry


/-- If two sets are nonempty and bounded in a metric space, they are at finite Hausdorff
edistance. -/
@[target] theorem hausdorffEdist_ne_top_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Nonempty)
    (bs : IsBounded s) (bt : IsBounded t) : hausdorffEdist s t ≠ ⊤ := by sorry


/-- The Hausdorff distance between a set and itself is zero. -/
@[simp]
theorem hausdorffDist_self_zero : hausdorffDist s s = 0 := by simp [hausdorffDist]

/-- The Hausdorff distances from `s` to `t` and from `t` to `s` coincide. -/
theorem hausdorffDist_comm : hausdorffDist s t = hausdorffDist t s := by
  simp [hausdorffDist, hausdorffEdist_comm]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value `∞` instead, use `EMetric.hausdorffEdist`, which takes values in `ℝ≥0∞`). -/
@[simp]
theorem hausdorffDist_empty : hausdorffDist s ∅ = 0 := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [hausdorffDist, hausdorffEdist_empty h]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value `∞` instead, use `EMetric.hausdorffEdist`, which takes values in `ℝ≥0∞`). -/
@[simp]
theorem hausdorffDist_empty' : hausdorffDist ∅ s = 0 := by simp [hausdorffDist_comm]

/-- Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set -/
theorem hausdorffDist_le_of_infDist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x ∈ s, infDist x t ≤ r)
    (H2 : ∀ x ∈ t, infDist x s ≤ r) : hausdorffDist s t ≤ r := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rwa [hs, hausdorffDist_empty']
  rcases t.eq_empty_or_nonempty with ht | ht
  · rwa [ht, hausdorffDist_empty]
  have : hausdorffEdist s t ≤ ENNReal.ofReal r := by
    apply hausdorffEdist_le_of_infEdist _ _
    · simpa only [infDist, ← ENNReal.le_ofReal_iff_toReal_le (infEdist_ne_top ht) hr] using H1
    · simpa only [infDist, ← ENNReal.le_ofReal_iff_toReal_le (infEdist_ne_top hs) hr] using H2
  exact ENNReal.toReal_le_of_le_ofReal hr this

/-- Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
@[target] theorem hausdorffDist_le_of_mem_dist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x ∈ s, ∃ y ∈ t, dist x y ≤ r)
    (H2 : ∀ x ∈ t, ∃ y ∈ s, dist x y ≤ r) : hausdorffDist s t ≤ r := by sorry


/-- The Hausdorff distance is controlled by the diameter of the union. -/
@[target] theorem hausdorffDist_le_diam (hs : s.Nonempty) (bs : IsBounded s) (ht : t.Nonempty)
    (bt : IsBounded t) : hausdorffDist s t ≤ diam (s ∪ t) := by sorry


/-- The distance to a set is controlled by the Hausdorff distance. -/
@[target] theorem infDist_le_hausdorffDist_of_mem (hx : x ∈ s) (fin : hausdorffEdist s t ≠ ⊤) :
    infDist x t ≤ hausdorffDist s t := by sorry


/-- If the Hausdorff distance is `< r`, any point in one of the sets is at distance
`< r` of a point in the other set. -/
@[target] theorem exists_dist_lt_of_hausdorffDist_lt {r : ℝ} (h : x ∈ s) (H : hausdorffDist s t < r)
    (fin : hausdorffEdist s t ≠ ⊤) : ∃ y ∈ t, dist x y < r := by sorry


/-- If the Hausdorff distance is `< r`, any point in one of the sets is at distance
`< r` of a point in the other set. -/
theorem exists_dist_lt_of_hausdorffDist_lt' {r : ℝ} (h : y ∈ t) (H : hausdorffDist s t < r)
    (fin : hausdorffEdist s t ≠ ⊤) : ∃ x ∈ s, dist x y < r := by
  rw [hausdorffDist_comm] at H
  rw [hausdorffEdist_comm] at fin
  simpa [dist_comm] using exists_dist_lt_of_hausdorffDist_lt h H fin

/-- The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t` -/
@[target] theorem infDist_le_infDist_add_hausdorffDist (fin : hausdorffEdist s t ≠ ⊤) :
    infDist x t ≤ infDist x s + hausdorffDist s t := by sorry


/-- The Hausdorff distance is invariant under isometries. -/
@[target] theorem hausdorffDist_image (h : Isometry Φ) :
    hausdorffDist (Φ '' s) (Φ '' t) = hausdorffDist s t := by sorry


/-- The Hausdorff distance satisfies the triangle inequality. -/
@[target] theorem hausdorffDist_triangle (fin : hausdorffEdist s t ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u := by sorry


/-- The Hausdorff distance satisfies the triangle inequality. -/
theorem hausdorffDist_triangle' (fin : hausdorffEdist t u ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u := by
  rw [hausdorffEdist_comm] at fin
  have I : hausdorffDist u s ≤ hausdorffDist u t + hausdorffDist t s :=
    hausdorffDist_triangle fin
  simpa [add_comm, hausdorffDist_comm] using I

/-- The Hausdorff distance between a set and its closure vanishes. -/
@[simp]
theorem hausdorffDist_self_closure : hausdorffDist s (closure s) = 0 := by simp [hausdorffDist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem hausdorffDist_closure₁ : hausdorffDist (closure s) t = hausdorffDist s t := by
  simp [hausdorffDist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem hausdorffDist_closure₂ : hausdorffDist s (closure t) = hausdorffDist s t := by
  simp [hausdorffDist]

/-- The Hausdorff distances between two sets and their closures coincide. -/
@[target] theorem hausdorffDist_closure : hausdorffDist (closure s) (closure t) = hausdorffDist s t := by sorry


/-- Two sets are at zero Hausdorff distance if and only if they have the same closures. -/
theorem hausdorffDist_zero_iff_closure_eq_closure (fin : hausdorffEdist s t ≠ ⊤) :
    hausdorffDist s t = 0 ↔ closure s = closure t := by
  simp [← hausdorffEdist_zero_iff_closure_eq_closure, hausdorffDist,
    ENNReal.toReal_eq_zero_iff, fin]

/-- Two closed sets are at zero Hausdorff distance if and only if they coincide. -/
theorem _root_.IsClosed.hausdorffDist_zero_iff_eq (hs : IsClosed s) (ht : IsClosed t)
    (fin : hausdorffEdist s t ≠ ⊤) : hausdorffDist s t = 0 ↔ s = t := by
  simp [← hausdorffEdist_zero_iff_eq_of_closed hs ht, hausdorffDist, ENNReal.toReal_eq_zero_iff,
    fin]

end

end Metric
