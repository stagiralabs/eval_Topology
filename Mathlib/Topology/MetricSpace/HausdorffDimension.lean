import VerifiedAgora.tagger
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Hausdorff dimension

The Hausdorff dimension of a set `X` in an (extended) metric space is the unique number
`dimH s : ℝ≥0∞` such that for any `d : ℝ≥0` we have

- `μH[d] s = 0` if `dimH s < d`, and
- `μH[d] s = ∞` if `d < dimH s`.

In this file we define `dimH s` to be the Hausdorff dimension of `s`, then prove some basic
properties of Hausdorff dimension.

## Main definitions

* `MeasureTheory.dimH`: the Hausdorff dimension of a set. For the Hausdorff dimension of the whole
  space we use `MeasureTheory.dimH (Set.univ : Set X)`.

## Main results

### Basic properties of Hausdorff dimension

* `hausdorffMeasure_of_lt_dimH`, `dimH_le_of_hausdorffMeasure_ne_top`,
  `le_dimH_of_hausdorffMeasure_eq_top`, `hausdorffMeasure_of_dimH_lt`, `measure_zero_of_dimH_lt`,
  `le_dimH_of_hausdorffMeasure_ne_zero`, `dimH_of_hausdorffMeasure_ne_zero_ne_top`: various forms
  of the characteristic property of the Hausdorff dimension;
* `dimH_union`: the Hausdorff dimension of the union of two sets is the maximum of their Hausdorff
  dimensions.
* `dimH_iUnion`, `dimH_bUnion`, `dimH_sUnion`: the Hausdorff dimension of a countable union of sets
  is the supremum of their Hausdorff dimensions;
* `dimH_empty`, `dimH_singleton`, `Set.Subsingleton.dimH_zero`, `Set.Countable.dimH_zero` : `dimH s
  = 0` whenever `s` is countable;

### (Pre)images under (anti)lipschitz and Hölder continuous maps

* `HolderWith.dimH_image_le` etc: if `f : X → Y` is Hölder continuous with exponent `r > 0`, then
  for any `s`, `dimH (f '' s) ≤ dimH s / r`. We prove versions of this statement for `HolderWith`,
  `HolderOnWith`, and locally Hölder maps, as well as for `Set.image` and `Set.range`.
* `LipschitzWith.dimH_image_le` etc: Lipschitz continuous maps do not increase the Hausdorff
  dimension of sets.
* for a map that is known to be both Lipschitz and antilipschitz (e.g., for an `Isometry` or
  a `ContinuousLinearEquiv`) we also prove `dimH (f '' s) = dimH s`.

### Hausdorff measure in `ℝⁿ`

* `Real.dimH_of_nonempty_interior`: if `s` is a set in a finite dimensional real vector space `E`
  with nonempty interior, then the Hausdorff dimension of `s` is equal to the dimension of `E`.
* `dense_compl_of_dimH_lt_finrank`: if `s` is a set in a finite dimensional real vector space `E`
  with Hausdorff dimension strictly less than the dimension of `E`, the `s` has a dense complement.
* `ContDiff.dense_compl_range_of_finrank_lt_finrank`: the complement to the range of a `C¹`
  smooth map is dense provided that the dimension of the domain is strictly less than the dimension
  of the codomain.

## Notations

We use the following notation localized in `MeasureTheory`. It is defined in
`MeasureTheory.Measure.Hausdorff`.

- `μH[d]` : `MeasureTheory.Measure.hausdorffMeasure d`

## Implementation notes

* The definition of `dimH` explicitly uses `borel X` as a measurable space structure. This way we
  can formulate lemmas about Hausdorff dimension without assuming that the environment has a
  `[MeasurableSpace X]` instance that is equal but possibly not defeq to `borel X`.

  Lemma `dimH_def` unfolds this definition using whatever `[MeasurableSpace X]` instance we have in
  the environment (as long as it is equal to `borel X`).

* The definition `dimH` is irreducible; use API lemmas or `dimH_def` instead.

## Tags

Hausdorff measure, Hausdorff dimension, dimension
-/


open scoped MeasureTheory ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace Module Filter

variable {ι X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

/-- Hausdorff dimension of a set in an (e)metric space. -/
@[irreducible] noncomputable def dimH (s : Set X) : ℝ≥0∞ := by
  borelize X; exact ⨆ (d : ℝ≥0) (_ : @hausdorffMeasure X _ _ ⟨rfl⟩ d s = ∞), d

/-!
### Basic properties
-/


section Measurable

variable [MeasurableSpace X] [BorelSpace X]

/-- Unfold the definition of `dimH` using `[MeasurableSpace X] [BorelSpace X]` from the
environment. -/
@[target] theorem dimH_def (s : Set X) : dimH s = ⨆ (d : ℝ≥0) (_ : μH[d] s = ∞), (d : ℝ≥0∞) := by sorry


@[target] theorem hausdorffMeasure_of_lt_dimH {s : Set X} {d : ℝ≥0} (h : ↑d < dimH s) : μH[d] s = ∞ := by sorry


theorem dimH_le {s : Set X} {d : ℝ≥0∞} (H : ∀ d' : ℝ≥0, μH[d'] s = ∞ → ↑d' ≤ d) : dimH s ≤ d :=
  (dimH_def s).trans_le <| iSup₂_le H

theorem dimH_le_of_hausdorffMeasure_ne_top {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ ∞) : dimH s ≤ d :=
  le_of_not_lt <| mt hausdorffMeasure_of_lt_dimH h

theorem le_dimH_of_hausdorffMeasure_eq_top {s : Set X} {d : ℝ≥0} (h : μH[d] s = ∞) :
    ↑d ≤ dimH s := by
  rw [dimH_def]; exact le_iSup₂ (α := ℝ≥0∞) d h

@[target] theorem hausdorffMeasure_of_dimH_lt {s : Set X} {d : ℝ≥0} (h : dimH s < d) : μH[d] s = 0 := by sorry


theorem measure_zero_of_dimH_lt {μ : Measure X} {d : ℝ≥0} (h : μ ≪ μH[d]) {s : Set X}
    (hd : dimH s < d) : μ s = 0 :=
  h <| hausdorffMeasure_of_dimH_lt hd

theorem le_dimH_of_hausdorffMeasure_ne_zero {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ 0) : ↑d ≤ dimH s :=
  le_of_not_lt <| mt hausdorffMeasure_of_dimH_lt h

@[target] theorem dimH_of_hausdorffMeasure_ne_zero_ne_top {d : ℝ≥0} {s : Set X} (h : μH[d] s ≠ 0)
    (h' : μH[d] s ≠ ∞) : dimH s = d := by sorry


end Measurable

@[target] theorem dimH_mono {s t : Set X} (h : s ⊆ t) : dimH s ≤ dimH t := by sorry


@[target] theorem dimH_subsingleton {s : Set X} (h : s.Subsingleton) : dimH s = 0 := by sorry


@[simp]
theorem dimH_empty : dimH (∅ : Set X) = 0 :=
  subsingleton_empty.dimH_zero

@[target] theorem dimH_singleton (x : X) : dimH ({x} : Set X) = 0 := by sorry


@[simp]
theorem dimH_iUnion {ι : Sort*} [Countable ι] (s : ι → Set X) :
    dimH (⋃ i, s i) = ⨆ i, dimH (s i) := by
  borelize X
  refine le_antisymm (dimH_le fun d hd => ?_) (iSup_le fun i => dimH_mono <| subset_iUnion _ _)
  contrapose! hd
  have : ∀ i, μH[d] (s i) = 0 := fun i =>
    hausdorffMeasure_of_dimH_lt ((le_iSup (fun i => dimH (s i)) i).trans_lt hd)
  rw [measure_iUnion_null this]
  exact ENNReal.zero_ne_top

@[target] theorem dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι → Set X) :
    dimH (⋃ i ∈ s, t i) = ⨆ i ∈ s, dimH (t i) := by sorry


@[target] theorem dimH_sUnion {S : Set (Set X)} (hS : S.Countable) : dimH (⋃₀ S) = ⨆ s ∈ S, dimH s := by sorry


@[simp]
theorem dimH_union (s t : Set X) : dimH (s ∪ t) = max (dimH s) (dimH t) := by
  rw [union_eq_iUnion, dimH_iUnion, iSup_bool_eq, cond, cond]

@[target] theorem dimH_countable {s : Set X} (hs : s.Countable) : dimH s = 0 := by sorry


@[target] theorem dimH_finite {s : Set X} (hs : s.Finite) : dimH s = 0 := by sorry


@[target] theorem dimH_coe_finset (s : Finset X) : dimH (s : Set X) = 0 := by sorry



section

variable [SecondCountableTopology X]

/-- If `r` is less than the Hausdorff dimension of a set `s` in an (extended) metric space with
second countable topology, then there exists a point `x ∈ s` such that every neighborhood
`t` of `x` within `s` has Hausdorff dimension greater than `r`. -/
@[target] theorem exists_mem_nhdsWithin_lt_dimH_of_lt_dimH {s : Set X} {r : ℝ≥0∞} (h : r < dimH s) :
    ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, r < dimH t := by sorry


/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over `x ∈ s` of the limit superiors of `dimH t` along
`(𝓝[s] x).smallSets`. -/
@[target] theorem bsupr_limsup_dimH (s : Set X) : ⨆ x ∈ s, limsup dimH (𝓝[s] x).smallSets = dimH s := by sorry


/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over all `x` of the limit superiors of `dimH t` along
`(𝓝[s] x).smallSets`. -/
theorem iSup_limsup_dimH (s : Set X) : ⨆ x, limsup dimH (𝓝[s] x).smallSets = dimH s := by
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · rw [← bsupr_limsup_dimH]; exact iSup₂_le_iSup _ _

end

/-!
### Hausdorff dimension and Hölder continuity
-/


variable {C K r : ℝ≥0} {f : X → Y} {s : Set X}

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then `dimH (f '' s) ≤ dimH s / r`. -/
theorem HolderOnWith.dimH_image_le (h : HolderOnWith C r f s) (hr : 0 < r) :
    dimH (f '' s) ≤ dimH s / r := by
  borelize X Y
  refine dimH_le fun d hd => ?_
  have := h.hausdorffMeasure_image_le hr d.coe_nonneg
  rw [hd, ← ENNReal.coe_rpow_of_nonneg _ d.coe_nonneg, top_le_iff] at this
  have Hrd : μH[(r * d : ℝ≥0)] s = ⊤ := by
    contrapose this
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top this
  rw [ENNReal.le_div_iff_mul_le, mul_comm, ← ENNReal.coe_mul]
  exacts [le_dimH_of_hausdorffMeasure_eq_top Hrd, Or.inl (mt ENNReal.coe_eq_zero.1 hr.ne'),
    Or.inl ENNReal.coe_ne_top]

namespace HolderWith

/-- If `f : X → Y` is Hölder continuous with a positive exponent `r`, then the Hausdorff dimension
of the image of a set `s` is at most `dimH s / r`. -/
@[target] theorem dimH_image_le (h : HolderWith C r f) (hr : 0 < r) (s : Set X) :
    dimH (f '' s) ≤ dimH s / r := by sorry


/-- If `f` is a Hölder continuous map with exponent `r > 0`, then the Hausdorff dimension of its
range is at most the Hausdorff dimension of its domain divided by `r`. -/
theorem dimH_range_le (h : HolderWith C r f) (hr : 0 < r) :
    dimH (range f) ≤ dimH (univ : Set X) / r :=
  @image_univ _ _ f ▸ h.dimH_image_le hr univ

end HolderWith

/-- If `s` is a set in a space `X` with second countable topology and `f : X → Y` is Hölder
continuous in a neighborhood within `s` of every point `x ∈ s` with the same positive exponent `r`
but possibly different coefficients, then the Hausdorff dimension of the image `f '' s` is at most
the Hausdorff dimension of `s` divided by `r`. -/
theorem dimH_image_le_of_locally_holder_on [SecondCountableTopology X] {r : ℝ≥0} {f : X → Y}
    (hr : 0 < r) {s : Set X} (hf : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C r f t) :
    dimH (f '' s) ≤ dimH s / r := by
  choose! C t htn hC using hf
  rcases countable_cover_nhdsWithin htn with ⟨u, hus, huc, huU⟩
  replace huU := inter_eq_self_of_subset_left huU; rw [inter_iUnion₂] at huU
  rw [← huU, image_iUnion₂, dimH_bUnion huc, dimH_bUnion huc]; simp only [ENNReal.iSup_div]
  exact iSup₂_mono fun x hx => ((hC x (hus hx)).mono inter_subset_right).dimH_image_le hr

/-- If `f : X → Y` is Hölder continuous in a neighborhood of every point `x : X` with the same
positive exponent `r` but possibly different coefficients, then the Hausdorff dimension of the range
of `f` is at most the Hausdorff dimension of `X` divided by `r`. -/
theorem dimH_range_le_of_locally_holder_on [SecondCountableTopology X] {r : ℝ≥0} {f : X → Y}
    (hr : 0 < r) (hf : ∀ x : X, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, HolderOnWith C r f s) :
    dimH (range f) ≤ dimH (univ : Set X) / r := by
  rw [← image_univ]
  refine dimH_image_le_of_locally_holder_on hr fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

/-!
### Hausdorff dimension and Lipschitz continuity
-/


/-- If `f : X → Y` is Lipschitz continuous on `s`, then `dimH (f '' s) ≤ dimH s`. -/
@[target] theorem LipschitzOnWith.dimH_image_le (h : LipschitzOnWith K f s) : dimH (f '' s) ≤ dimH s := by sorry


namespace LipschitzWith

/-- If `f` is a Lipschitz continuous map, then `dimH (f '' s) ≤ dimH s`. -/
theorem dimH_image_le (h : LipschitzWith K f) (s : Set X) : dimH (f '' s) ≤ dimH s :=
  h.lipschitzOnWith.dimH_image_le

/-- If `f` is a Lipschitz continuous map, then the Hausdorff dimension of its range is at most the
Hausdorff dimension of its domain. -/
theorem dimH_range_le (h : LipschitzWith K f) : dimH (range f) ≤ dimH (univ : Set X) :=
  @image_univ _ _ f ▸ h.dimH_image_le univ

end LipschitzWith

/-- If `s` is a set in an extended metric space `X` with second countable topology and `f : X → Y`
is Lipschitz in a neighborhood within `s` of every point `x ∈ s`, then the Hausdorff dimension of
the image `f '' s` is at most the Hausdorff dimension of `s`. -/
@[target] theorem dimH_image_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X → Y} {s : Set X}
    (hf : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith C f t) : dimH (f '' s) ≤ dimH s := by sorry


/-- If `f : X → Y` is Lipschitz in a neighborhood of each point `x : X`, then the Hausdorff
dimension of `range f` is at most the Hausdorff dimension of `X`. -/
@[target] theorem dimH_range_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X → Y}
    (hf : ∀ x : X, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith C f s) :
    dimH (range f) ≤ dimH (univ : Set X) := by sorry


namespace AntilipschitzWith

theorem dimH_preimage_le (hf : AntilipschitzWith K f) (s : Set Y) : dimH (f ⁻¹' s) ≤ dimH s := by
  borelize X Y
  refine dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top ?_
  have := hf.hausdorffMeasure_preimage_le d.coe_nonneg s
  rw [hd, top_le_iff] at this
  contrapose! this
  exact ENNReal.mul_ne_top (by simp) this

@[target] theorem le_dimH_image (hf : AntilipschitzWith K f) (s : Set X) : dimH s ≤ dimH (f '' s) := by sorry


end AntilipschitzWith

/-!
### Isometries preserve Hausdorff dimension
-/


@[target] theorem Isometry.dimH_image (hf : Isometry f) (s : Set X) : dimH (f '' s) = dimH s := by sorry


namespace IsometryEquiv

@[target] theorem dimH_image (e : X ≃ᵢ Y) (s : Set X) : dimH (e '' s) = dimH s := by sorry


@[target] theorem dimH_preimage (e : X ≃ᵢ Y) (s : Set Y) : dimH (e ⁻¹' s) = dimH s := by sorry


@[target] theorem dimH_univ (e : X ≃ᵢ Y) : dimH (univ : Set X) = dimH (univ : Set Y) := by sorry


end IsometryEquiv

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
theorem dimH_image (e : E ≃L[𝕜] F) (s : Set E) : dimH (e '' s) = dimH s :=
  le_antisymm (e.lipschitz.dimH_image_le s) <| by
    simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp]
theorem dimH_preimage (e : E ≃L[𝕜] F) (s : Set F) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm_eq_preimage, e.symm.dimH_image]

theorem dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : Set E) = dimH (univ : Set F) := by
  rw [← e.dimH_preimage, preimage_univ]

end ContinuousLinearEquiv

/-!
### Hausdorff dimension in a real vector space
-/


namespace Real

variable {E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

@[target] theorem dimH_ball_pi (x : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    dimH (Metric.ball x r) = Fintype.card ι := by sorry


theorem dimH_ball_pi_fin {n : ℕ} (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    dimH (Metric.ball x r) = n := by rw [dimH_ball_pi x hr, Fintype.card_fin]

theorem dimH_univ_pi (ι : Type*) [Fintype ι] : dimH (univ : Set (ι → ℝ)) = Fintype.card ι := by
  simp only [← Metric.iUnion_ball_nat_succ (0 : ι → ℝ), dimH_iUnion,
    dimH_ball_pi _ (Nat.cast_add_one_pos _), iSup_const]

theorem dimH_univ_pi_fin (n : ℕ) : dimH (univ : Set (Fin n → ℝ)) = n := by
  rw [dimH_univ_pi, Fintype.card_fin]

@[target] theorem dimH_of_mem_nhds {x : E} {s : Set E} (h : s ∈ 𝓝 x) : dimH s = finrank ℝ E := by sorry


theorem dimH_of_nonempty_interior {s : Set E} (h : (interior s).Nonempty) : dimH s = finrank ℝ E :=
  let ⟨_, hx⟩ := h
  dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)

variable (E)

@[target] theorem dimH_univ_eq_finrank : dimH (univ : Set E) = finrank ℝ E := by sorry


theorem dimH_univ : dimH (univ : Set ℝ) = 1 := by
  rw [dimH_univ_eq_finrank ℝ, Module.finrank_self, Nat.cast_one]

variable {E}

lemma hausdorffMeasure_of_finrank_lt [MeasurableSpace E] [BorelSpace E] {d : ℝ}
    (hd : finrank ℝ E < d) : (μH[d] : Measure E) = 0 := by
  lift d to ℝ≥0 using (Nat.cast_nonneg _).trans hd.le
  rw [← measure_univ_eq_zero]
  apply hausdorffMeasure_of_dimH_lt
  rw [dimH_univ_eq_finrank]
  exact mod_cast hd

end Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[target] theorem dense_compl_of_dimH_lt_finrank {s : Set E} (hs : dimH s < finrank ℝ E) : Dense sᶜ := by sorry



/-- Let `f` be a function defined on a finite dimensional real normed space. If `f` is `C¹`-smooth
on a convex set `s`, then the Hausdorff dimension of `f '' s` is less than or equal to the Hausdorff
dimension of `s`.

TODO: do we actually need `Convex ℝ s`? -/
@[target] theorem ContDiffOn.dimH_image_le {f : E → F} {s t : Set E} (hf : ContDiffOn ℝ 1 f s)
    (hc : Convex ℝ s) (ht : t ⊆ s) : dimH (f '' t) ≤ dimH t := by sorry


/-- The Hausdorff dimension of the range of a `C¹`-smooth function defined on a finite dimensional
real normed space is at most the dimension of its domain as a vector space over `ℝ`. -/
@[target] theorem ContDiff.dimH_range_le {f : E → F} (h : ContDiff ℝ 1 f) : dimH (range f) ≤ finrank ℝ E := by sorry


/-- A particular case of Sard's Theorem. Let `f : E → F` be a map between finite dimensional real
vector spaces. Suppose that `f` is `C¹` smooth on a convex set `s` of Hausdorff dimension strictly
less than the dimension of `F`. Then the complement of the image `f '' s` is dense in `F`. -/
theorem ContDiffOn.dense_compl_image_of_dimH_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
    {s t : Set E} (h : ContDiffOn ℝ 1 f s) (hc : Convex ℝ s) (ht : t ⊆ s)
    (htF : dimH t < finrank ℝ F) : Dense (f '' t)ᶜ :=
  dense_compl_of_dimH_lt_finrank <| (h.dimH_image_le hc ht).trans_lt htF

/-- A particular case of Sard's Theorem. If `f` is a `C¹` smooth map from a real vector space to a
real vector space `F` of strictly larger dimension, then the complement of the range of `f` is dense
in `F`. -/
@[target] theorem ContDiff.dense_compl_range_of_finrank_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
    (h : ContDiff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) : Dense (range f)ᶜ := by sorry
