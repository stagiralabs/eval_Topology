import VerifiedAgora.tagger
/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Sets.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℕ, ℝ)`.
Any partially defined Lipschitz map into `ℓ^∞` can be extended to the whole space.

-/

noncomputable section


open Set Metric TopologicalSpace NNReal ENNReal lp Function

universe u

variable {α : Type u}

namespace KuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℕ, ℝ) -/


variable {n : ℕ} [MetricSpace α] (x : ℕ → α) (a : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `kuratowskiEmbedding`,
without density assumptions. -/
def embeddingOfSubset : ℓ^∞(ℕ) := by sorry


theorem embeddingOfSubset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl

/-- The embedding map is always a semi-contraction. -/
@[target] theorem embeddingOfSubset_dist_le (a b : α) :
    dist (embeddingOfSubset x a) (embeddingOfSubset x b) ≤ dist a b := by sorry


/-- When the reference set is dense, the embedding map is an isometry on its image. -/
@[target] theorem embeddingOfSubset_isometry (H : DenseRange x) : Isometry (embeddingOfSubset x) := by sorry


/-- Every separable metric space embeds isometrically in `ℓ^∞(ℕ)`. -/
theorem exists_isometric_embedding (α : Type u) [MetricSpace α] [SeparableSpace α] :
    ∃ f : α → ℓ^∞(ℕ), Isometry f := by
  rcases (univ : Set α).eq_empty_or_nonempty with h | h
  · use fun _ => 0; intro x; exact absurd h (Nonempty.ne_empty ⟨x, mem_univ x⟩)
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    haveI : Inhabited α := ⟨basepoint⟩
    have : ∃ s : Set α, s.Countable ∧ Dense s := exists_countable_dense α
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩
    rcases Set.countable_iff_exists_subset_range.1 S_countable with ⟨x, x_range⟩
    -- Use embeddingOfSubset to construct the desired isometry
    exact ⟨embeddingOfSubset x, embeddingOfSubset_isometry x (S_dense.mono x_range)⟩

end KuratowskiEmbedding

open TopologicalSpace KuratowskiEmbedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℕ, ℝ)`.
-/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [SeparableSpace α] : α → ℓ^∞(ℕ) := by sorry


/--
The Kuratowski embedding is an isometry.
Theorem 2.1 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]. -/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.choose_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
nonrec def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α]
    [Nonempty α] : NonemptyCompacts ℓ^∞(ℕ) where
  carrier := range (kuratowskiEmbedding α)
  isCompact' := isCompact_range (kuratowskiEmbedding.isometry α).continuous
  nonempty' := range_nonempty _

/--
A function `f : α → ℓ^∞(ι, ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.

Theorem 2.2 of [Assaf Naor, *Metric Embeddings and Lipschitz Extensions*][Naor-2015]

The same result for the case of a finite type `ι` is implemented in
`LipschitzOnWith.extend_pi`.
-/
@[target] theorem LipschitzOnWith.extend_lp_infty [PseudoMetricSpace α] {s : Set α} {ι : Type*}
    {f : α → ℓ^∞(ι)} {K : ℝ≥0} (hfl : LipschitzOnWith K f s) :
    ∃ g : α → ℓ^∞(ι), LipschitzWith K g ∧ EqOn f g s := by sorry
