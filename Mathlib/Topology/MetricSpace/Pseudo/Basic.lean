import VerifiedAgora.tagger
/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Bound.Attribute
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
## Pseudo-metric spaces

Further results about pseudo-metric spaces.

-/

open Set Filter TopologicalSpace Bornology
open scoped ENNReal NNReal Uniformity Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*}

variable [PseudoMetricSpace α]

/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
@[target] theorem dist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, dist (f i) (f (i + 1)) := by sorry


/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
@[target] theorem dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) := by sorry


/-- A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
@[target] theorem dist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ}
    (hd : ∀ {k}, m ≤ k → k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, d i := by sorry


/-- A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
@[target] theorem dist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ}
    (hd : ∀ {k}, k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, d i := by sorry


namespace Metric

-- instantiate pseudometric space as a topology

nonrec theorem isUniformInducing_iff [PseudoMetricSpace β] {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  isUniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_dist.comap _).le_basis_iff uniformity_basis_dist).trans <| by
      simp only [subset_def, Prod.forall, gt_iff_lt, preimage_setOf_eq, Prod.map_apply, mem_setOf]

@[deprecated (since := "2024-10-05")]
alias uniformInducing_iff := isUniformInducing_iff

nonrec theorem isUniformEmbedding_iff [PseudoMetricSpace β] {f : α → β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [isUniformEmbedding_iff, and_comm, isUniformInducing_iff]

@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_iff := isUniformEmbedding_iff

/-- If a map between pseudometric spaces is a uniform embedding then the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_isUniformEmbedding [PseudoMetricSpace β] {f : α → β}
    (h : IsUniformEmbedding f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformEmbedding_iff.1 h).2.2⟩

@[deprecated (since := "2024-10-01")]
alias controlled_of_uniformEmbedding := controlled_of_isUniformEmbedding

@[target] theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε := by sorry


/-- A pseudometric space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
@[target] theorem totallyBounded_of_finite_discretization {s : Set α}
    (H : ∀ ε > (0 : ℝ),
        ∃ (β : Type u) (_ : Fintype β) (F : s → β), ∀ x y, F x = F y → dist (x : α) y < ε) :
    TotallyBounded s := by sorry


@[target] theorem finite_approx_of_totallyBounded {s : Set α} (hs : TotallyBounded s) :
    ∀ ε > 0, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y ε := by sorry


/-- Expressing uniform convergence using `dist` -/
theorem tendstoUniformlyOnFilter_iff {F : ι → β → α} {f : β → α} {p : Filter ι} {p' : Filter β} :
    TendstoUniformlyOnFilter F f p p' ↔
      ∀ ε > 0, ∀ᶠ n : ι × β in p ×ˢ p', dist (f n.snd) (F n.fst n.snd) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hn => hε hn

/-- Expressing locally uniform convergence on a set using `dist`. -/
@[target] theorem tendstoLocallyUniformlyOn_iff [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε := by sorry


/-- Expressing uniform convergence on a set using `dist`. -/
@[target] theorem tendstoUniformlyOn_iff {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, dist (f x) (F n x) < ε := by sorry


/-- Expressing locally uniform convergence using `dist`. -/
theorem tendstoLocallyUniformly_iff [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, nhdsWithin_univ,
    mem_univ, forall_const, exists_prop]

/-- Expressing uniform convergence using `dist`. -/
theorem tendstoUniformly_iff {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, dist (f x) (F n x) < ε := by
  rw [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff]
  simp

protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff

variable {s : Set α}

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is an open ball
centered at `x` and intersecting `s` only at `x`. -/
@[target] theorem exists_ball_inter_eq_singleton_of_mem_discrete [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.ball x ε ∩ s = {x} := by sorry


/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is a closed ball
of positive radius centered at `x` and intersecting `s` only at `x`. -/
@[target] theorem exists_closedBall_inter_eq_singleton_of_discrete [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.closedBall x ε ∩ s = {x} := by sorry


end Metric

open Metric

@[target] theorem Metric.inseparable_iff_nndist {x y : α} : Inseparable x y ↔ nndist x y = 0 := by sorry


@[target] theorem Metric.inseparable_iff {x y : α} : Inseparable x y ↔ dist x y = 0 := by sorry


/-- A weaker version of `tendsto_nhds_unique` for `PseudoMetricSpace`. -/
@[target] theorem tendsto_nhds_unique_dist {f : β → α} {l : Filter β} {x y : α} [NeBot l]
    (ha : Tendsto f l (𝓝 x)) (hb : Tendsto f l (𝓝 y)) : dist x y = 0 := by sorry


section Real

@[target] theorem cauchySeq_iff_tendsto_dist_atTop_0 [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (fun n : β × β => dist (u n.1) (u n.2)) atTop (𝓝 0) := by sorry


end Real

namespace Topology

-- Porting note: `TopologicalSpace.IsSeparable.separableSpace` moved to `EMetricSpace`

/-- The preimage of a separable set by an inducing map is separable. -/
protected lemma IsInducing.isSeparable_preimage {f : β → α} [TopologicalSpace β]
    (hf : IsInducing f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) := by
  have : SeparableSpace s := hs.separableSpace
  have : SecondCountableTopology s := UniformSpace.secondCountable_of_separable _
  have : IsInducing ((mapsTo_preimage f s).restrict _ _ _) :=
    (hf.comp IsInducing.subtypeVal).codRestrict _
  have := this.secondCountableTopology
  exact .of_subtype _

@[deprecated (since := "2024-10-28")]
alias _root_.Inducing.isSeparable_preimage := IsInducing.isSeparable_preimage

protected theorem IsEmbedding.isSeparable_preimage {f : β → α} [TopologicalSpace β]
    (hf : IsEmbedding f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) :=
  hf.isInducing.isSeparable_preimage hs

@[deprecated (since := "2024-10-26")]
alias _root_.Embedding.isSeparable_preimage := IsEmbedding.isSeparable_preimage

end Topology

/-- A compact set is separable. -/
theorem IsCompact.isSeparable {s : Set α} (hs : IsCompact s) : IsSeparable s :=
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  .of_subtype s

namespace Metric

section SecondCountable

open TopologicalSpace

/-- A pseudometric space is second countable if, for every `ε > 0`, there is a countable set which
is `ε`-dense. -/
@[target] theorem secondCountable_of_almost_dense_set
    (H : ∀ ε > (0 : ℝ), ∃ s : Set α, s.Countable ∧ ∀ x, ∃ y ∈ s, dist x y ≤ ε) :
    SecondCountableTopology α := by sorry


end SecondCountable

end Metric

section Compact

/-- Any compact set in a pseudometric space can be covered by finitely many balls of a given
positive radius -/
@[target] theorem finite_cover_balls_of_compact {α : Type u} [PseudoMetricSpace α] {s : Set α}
    (hs : IsCompact s) {e : ℝ} (he : 0 < e) :
    ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ x ∈ t, ball x e := by sorry


end Compact

/-- If a map is continuous on a separable set `s`, then the image of `s` is also separable. -/
theorem ContinuousOn.isSeparable_image [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) (hs : IsSeparable s) : IsSeparable (f '' s) := by
  rw [image_eq_range, ← image_univ]
  exact (isSeparable_univ_iff.2 hs.separableSpace).image hf.restrict
