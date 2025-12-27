import VerifiedAgora.tagger
/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Order.Filter.AtTopBot.Floor
import Mathlib.Topology.Algebra.Order.Group

/-!
# Topological facts about `Int.floor`, `Int.ceil` and `Int.fract`

This file proves statements about limits and continuity of functions involving `floor`, `ceil` and
`fract`.

## Main declarations

* `tendsto_floor_atTop`, `tendsto_floor_atBot`, `tendsto_ceil_atTop`, `tendsto_ceil_atBot`:
  `Int.floor` and `Int.ceil` tend to +-∞ in +-∞.
* `continuousOn_floor`: `Int.floor` is continuous on `Ico n (n + 1)`, because constant.
* `continuousOn_ceil`: `Int.ceil` is continuous on `Ioc n (n + 1)`, because constant.
* `continuousOn_fract`: `Int.fract` is continuous on `Ico n (n + 1)`.
* `ContinuousOn.comp_fract`: Precomposing a continuous function satisfying `f 0 = f 1` with
  `Int.fract` yields another continuous function.
-/


open Filter Function Int Set Topology

namespace FloorSemiring

open scoped Nat

variable {K : Type*} [LinearOrderedField K] [FloorSemiring K] [TopologicalSpace K] [OrderTopology K]

@[target] theorem tendsto_mul_pow_div_factorial_sub_atTop (a c : K) (d : ℕ) :
    Tendsto (fun n ↦ a * c ^ n / (n - d)!) atTop (𝓝 0) := by sorry


@[target] theorem tendsto_pow_div_factorial_atTop (c : K) :
    Tendsto (fun n ↦ c ^ n / n !) atTop (𝓝 0) := by sorry


end FloorSemiring

variable {α β γ : Type*} [LinearOrderedRing α] [FloorRing α]

-- TODO: move to `Mathlib.Order.Filter.AtTopBot.Floor`

@[target] theorem tendsto_floor_atTop : Tendsto (floor : α → ℤ) atTop atTop := by sorry


@[target] theorem tendsto_floor_atBot : Tendsto (floor : α → ℤ) atBot atBot := by sorry


@[target] theorem tendsto_ceil_atTop : Tendsto (ceil : α → ℤ) atTop atTop := by sorry


theorem tendsto_ceil_atBot : Tendsto (ceil : α → ℤ) atBot atBot :=
  ceil_mono.tendsto_atBot_atBot fun b =>
    ⟨(b - 1 : ℤ), by rw [ceil_intCast]; exact (sub_one_lt _).le⟩

variable [TopologicalSpace α]

theorem continuousOn_floor (n : ℤ) :
    ContinuousOn (fun x => floor x : α → α) (Ico n (n + 1) : Set α) :=
  (continuousOn_congr <| floor_eq_on_Ico' n).mpr continuousOn_const

@[target] theorem continuousOn_ceil (n : ℤ) :
    ContinuousOn (fun x => ceil x : α → α) (Ioc (n - 1) n : Set α) := by sorry


section OrderClosedTopology

variable [OrderClosedTopology α]

@[target] theorem tendsto_floor_right_pure_floor (x : α) : Tendsto (floor : α → ℤ) (𝓝[≥] x) (pure ⌊x⌋) := by sorry


@[target] theorem tendsto_floor_right_pure (n : ℤ) : Tendsto (floor : α → ℤ) (𝓝[≥] n) (pure n) := by sorry


@[target] theorem tendsto_ceil_left_pure_ceil (x : α) : Tendsto (ceil : α → ℤ) (𝓝[≤] x) (pure ⌈x⌉) := by sorry


theorem tendsto_ceil_left_pure (n : ℤ) : Tendsto (ceil : α → ℤ) (𝓝[≤] n) (pure n) := by
  simpa only [ceil_intCast] using tendsto_ceil_left_pure_ceil (n : α)

theorem tendsto_floor_left_pure_ceil_sub_one (x : α) :
    Tendsto (floor : α → ℤ) (𝓝[<] x) (pure (⌈x⌉ - 1)) :=
  have h₁ : ↑(⌈x⌉ - 1) < x := by rw [cast_sub, cast_one, sub_lt_iff_lt_add]; exact ceil_lt_add_one _
  have h₂ : x ≤ ↑(⌈x⌉ - 1) + 1 := by rw [cast_sub, cast_one, sub_add_cancel]; exact le_ceil _
  tendsto_pure.2 <| mem_of_superset (Ico_mem_nhdsLT h₁) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_le h₂⟩

@[target] theorem tendsto_floor_left_pure_sub_one (n : ℤ) :
    Tendsto (floor : α → ℤ) (𝓝[<] n) (pure (n - 1)) := by sorry


@[target] theorem tendsto_ceil_right_pure_floor_add_one (x : α) :
    Tendsto (ceil : α → ℤ) (𝓝[>] x) (pure (⌊x⌋ + 1)) := by sorry


theorem tendsto_ceil_right_pure_add_one (n : ℤ) :
    Tendsto (ceil : α → ℤ) (𝓝[>] n) (pure (n + 1)) := by
  simpa only [floor_intCast] using tendsto_ceil_right_pure_floor_add_one (n : α)

@[target] theorem tendsto_floor_right (n : ℤ) : Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝[≥] n) := by sorry


theorem tendsto_floor_right' (n : ℤ) : Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝 n) :=
  (tendsto_floor_right n).mono_right inf_le_left

@[target] theorem tendsto_ceil_left (n : ℤ) : Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝[≤] n) := by sorry


theorem tendsto_ceil_left' (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝 n) :=
  (tendsto_ceil_left n).mono_right inf_le_left

@[target] theorem tendsto_floor_left (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝[≤] (n - 1)) := by sorry


@[target] theorem tendsto_ceil_right (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝[≥] (n + 1)) := by sorry


theorem tendsto_floor_left' (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝 (n - 1)) :=
  (tendsto_floor_left n).mono_right inf_le_left

theorem tendsto_ceil_right' (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝 (n + 1)) :=
  (tendsto_ceil_right n).mono_right inf_le_left

end OrderClosedTopology

@[target] theorem continuousOn_fract [IsTopologicalAddGroup α] (n : ℤ) :
    ContinuousOn (fract : α → α) (Ico n (n + 1) : Set α) := by sorry


@[target] theorem continuousAt_fract [OrderClosedTopology α] [IsTopologicalAddGroup α]
    {x : α} (h : x ≠ ⌊x⌋) : ContinuousAt fract x := by sorry


@[target] theorem tendsto_fract_left' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝 1) := by sorry


theorem tendsto_fract_left [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝[<] 1) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (Eventually.of_forall fract_lt_one)

@[target] theorem tendsto_fract_right' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝 0) := by sorry


theorem tendsto_fract_right [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (Eventually.of_forall fract_nonneg)

local notation "I" => (Icc 0 1 : Set α)

variable [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

/-- Do not use this, use `ContinuousOn.comp_fract` instead. -/
@[target] theorem ContinuousOn.comp_fract' {f : β → α → γ} (h : ContinuousOn (uncurry f) <| univ ×ˢ I)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun st : β × α => f st.1 (fract st.2) := by sorry


theorem ContinuousOn.comp_fract {s : β → α} {f : β → α → γ}
    (h : ContinuousOn (uncurry f) <| univ ×ˢ Icc 0 1) (hs : Continuous s)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun x : β => f x <| Int.fract (s x) :=
  (h.comp_fract' hf).comp (continuous_id.prod_mk hs)

/-- A special case of `ContinuousOn.comp_fract`. -/
theorem ContinuousOn.comp_fract'' {f : α → β} (h : ContinuousOn f I) (hf : f 0 = f 1) :
    Continuous (f ∘ fract) :=
  ContinuousOn.comp_fract (h.comp continuousOn_snd fun _x hx => (mem_prod.mp hx).2) continuous_id
    fun _ => hf
