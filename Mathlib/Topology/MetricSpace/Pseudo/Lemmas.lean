import VerifiedAgora.tagger
/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Compact

/-!
# Extra lemmas about pseudo-metric spaces
-/

open Bornology Filter Metric Set
open scoped NNReal Topology

variable {ι α : Type*} [PseudoMetricSpace α]

instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

@[target] lemma Real.singleton_eq_inter_Icc (b : ℝ) : {b} = ⋂ (r > 0), Icc (b - r) (b + r) := by sorry


/-- Special case of the sandwich lemma; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
@[target] lemma squeeze_zero' {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ᶠ t in t₀, 0 ≤ f t)
    (hft : ∀ᶠ t in t₀, f t ≤ g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) := by sorry


/-- Special case of the sandwich lemma; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
lemma squeeze_zero {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall hf) (Eventually.of_forall hft) g0

/-- If `u` is a neighborhood of `x`, then for small enough `r`, the closed ball
`Metric.closedBall x r` is contained in `u`. -/
@[target] lemma eventually_closedBall_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : ℝ), closedBall x r ⊆ u := by sorry


@[target] lemma tendsto_closedBall_smallSets (x : α) : Tendsto (closedBall x) (𝓝 0) (𝓝 x).smallSets := by sorry


namespace Metric
variable {x y z : α} {ε ε₁ ε₂ : ℝ} {s : Set α}

@[target] lemma isClosed_closedBall : IsClosed (closedBall x ε) := by sorry


@[deprecated (since := "2025-02-11")] alias isClosed_ball := isClosed_closedBall

@[target] lemma isClosed_sphere : IsClosed (sphere x ε) := by sorry


@[target] lemma closure_closedBall : closure (closedBall x ε) = closedBall x ε := by sorry


@[simp]
lemma closure_sphere : closure (sphere x ε) = sphere x ε :=
  isClosed_sphere.closure_eq

lemma closure_ball_subset_closedBall : closure (ball x ε) ⊆ closedBall x ε :=
  closure_minimal ball_subset_closedBall isClosed_closedBall

@[target] lemma frontier_ball_subset_sphere : frontier (ball x ε) ⊆ sphere x ε := by sorry


lemma frontier_closedBall_subset_sphere : frontier (closedBall x ε) ⊆ sphere x ε :=
  frontier_le_subset_eq (continuous_id.dist continuous_const) continuous_const

@[target] lemma closedBall_zero' (x : α) : closedBall x 0 = closure {x} := by sorry


lemma eventually_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompact (closedBall x r) := by
  rcases exists_compact_mem_nhds x with ⟨s, s_compact, hs⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_closedBall hr

@[target] lemma exists_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∃ r, 0 < r ∧ IsCompact (closedBall x r) := by sorry


theorem biInter_gt_closedBall (x : α) (r : ℝ) : ⋂ r' > r, closedBall x r' = closedBall x r := by
  ext
  simp [forall_gt_imp_ge_iff_le_of_dense]

theorem biInter_gt_ball (x : α) (r : ℝ) : ⋂ r' > r, ball x r' = closedBall x r := by
  ext
  simp [forall_lt_iff_le']

@[target] theorem biUnion_lt_ball (x : α) (r : ℝ) : ⋃ r' < r, ball x r' = ball x r := by sorry


theorem biUnion_lt_closedBall (x : α) (r : ℝ) : ⋃ r' < r, closedBall x r' = ball x r := by
  ext
  rw [← not_iff_not]
  simp [forall_lt_iff_le]

end Metric

@[target] theorem lebesgue_number_lemma_of_metric {s : Set α} {ι : Sort*} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i := by sorry


@[target] theorem lebesgue_number_lemma_of_metric_sUnion {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀ c) : ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, ball x δ ⊆ t := by sorry
