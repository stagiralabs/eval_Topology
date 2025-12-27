import VerifiedAgora.tagger
/-
Copyright (c) 2022 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Devon Tuma, Eric Rodriguez, Oliver Nash
-/
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Order.Group

/-!
# Topologies on linear ordered fields

In this file we prove that a linear ordered field with order topology has continuous multiplication
and division (apart from zero in the denominator). We also prove theorems like
`Filter.Tendsto.mul_atTop`: if `f` tends to a positive number and `g` tends to positive infinity,
then `f * g` tends to positive infinity.
-/


open Set Filter TopologicalSpace Function
open scoped Pointwise Topology
open OrderDual (toDual ofDual)

/-- If a (possibly non-unital and/or non-associative) ring `R` admits a submultiplicative
nonnegative norm `norm : R → 𝕜`, where `𝕜` is a linear ordered field, and the open balls
`{ x | norm x < ε }`, `ε > 0`, form a basis of neighborhoods of zero, then `R` is a topological
ring. -/
@[target] theorem IsTopologicalRing.of_norm {R 𝕜 : Type*} [NonUnitalNonAssocRing R] [LinearOrderedField 𝕜]
    [TopologicalSpace R] [IsTopologicalAddGroup R] (norm : R → 𝕜)
    (norm_nonneg : ∀ x, 0 ≤ norm x) (norm_mul_le : ∀ x y, norm (x * y) ≤ norm x * norm y)
    (nhds_basis : (𝓝 (0 : R)).HasBasis ((0 : 𝕜) < ·) (fun ε ↦ { x | norm x < ε })) :
    IsTopologicalRing R := by sorry


variable {𝕜 α : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedField.topologicalRing : IsTopologicalRing 𝕜 :=
  .of_norm abs abs_nonneg (fun _ _ ↦ (abs_mul _ _).le) <| by
    simpa using nhds_basis_abs_sub_lt (0 : 𝕜)

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.atTop_mul {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0]
    with x hg hf using mul_le_mul_of_nonneg_left hg.le hf

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `Filter.atTop` then `f * g` tends to `Filter.atTop`. -/
@[target] theorem Filter.Tendsto.mul_atTop {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop := by sorry


/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atBot`. -/
@[target] theorem Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by sorry


/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atTop` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.neg_mul_atTop {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atTop_mul_neg hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atBot`. -/
@[target] theorem Filter.Tendsto.atBot_mul {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by sorry


/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atTop`. -/
@[target] theorem Filter.Tendsto.atBot_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by sorry


/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atBot`. -/
@[target] theorem Filter.Tendsto.mul_atBot {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot := by sorry


/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atTop`. -/
@[target] theorem Filter.Tendsto.neg_mul_atBot {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atTop := by sorry


@[simp]
lemma inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0 :=
  (((atTop_basis_Ioi' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis <|
    (nhdsGT_basis _).congr (by simp) fun a ha ↦ by simp [inv_Ioi₀ (inv_pos.2 ha)]

@[simp]
lemma inv_atBot₀ : (atBot : Filter 𝕜)⁻¹ = 𝓝[<] 0 :=
  (((atBot_basis_Iio' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis <|
    (nhdsLT_basis _).congr (by simp) fun a ha ↦ by simp [inv_Iio₀ (inv_neg''.2 ha)]

@[simp]
lemma inv_nhdsGT_zero : (𝓝[>] (0 : 𝕜))⁻¹ = atTop := by rw [← inv_atTop₀, inv_inv]

@[deprecated (since := "2024-12-22")] alias inv_nhdsWithin_Ioi_zero := inv_nhdsGT_zero

@[simp]
lemma inv_nhdsLT_zero : (𝓝[<] (0 : 𝕜))⁻¹ = atBot := by
  rw [← inv_atBot₀, inv_inv]

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
@[target] theorem tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[>] (0 : 𝕜)) atTop := by sorry


@[deprecated (since := "2024-12-22")]
alias tendsto_inv_zero_atTop := tendsto_inv_nhdsGT_zero

/-- The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`. -/
@[target] theorem tendsto_inv_atTop_nhdsGT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 : 𝕜)) := by sorry


@[deprecated (since := "2024-12-22")]
alias tendsto_inv_atTop_zero' := tendsto_inv_atTop_nhdsGT_zero

@[target] theorem tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝 0) := by sorry


/-- The function `x ↦ x⁻¹` tends to `-∞` on the left of `0`. -/
@[target] theorem tendsto_inv_zero_atBot : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[<] (0 : 𝕜)) atBot := by sorry


/-- The function `r ↦ r⁻¹` tends to `0` on the left as `r → -∞`. -/
@[target] theorem tendsto_inv_atBot_zero' : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝[<] (0 : 𝕜)) := by sorry


theorem tendsto_inv_atBot_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝 0) :=
  tendsto_inv_atBot_zero'.mono_right inf_le_left

@[target] theorem Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by sorry


@[target] theorem Filter.Tendsto.div_atBot {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by sorry


lemma Filter.Tendsto.const_div_atTop (hg : Tendsto g l atTop) (r : 𝕜)  :
    Tendsto (fun n ↦ r / g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atTop hg

@[target] lemma Filter.Tendsto.const_div_atBot (hg : Tendsto g l atBot) (r : 𝕜)  :
    Tendsto (fun n ↦ r / g n) l (𝓝 0) := by sorry


@[target] theorem Filter.Tendsto.inv_tendsto_atTop (h : Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0) := by sorry


@[target] theorem Filter.Tendsto.inv_tendsto_atBot (h : Tendsto f l atBot) : Tendsto f⁻¹ l (𝓝 0) := by sorry


@[target] theorem Filter.Tendsto.inv_tendsto_nhdsGT_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop := by sorry


@[deprecated (since := "2024-12-22")]
alias Filter.Tendsto.inv_tendsto_zero := Filter.Tendsto.inv_tendsto_nhdsGT_zero

@[target] theorem Filter.Tendsto.inv_tendsto_nhdsLT_zero (h : Tendsto f l (𝓝[<] 0)) : Tendsto f⁻¹ l atBot := by sorry


/-- If `g` tends to zero and there exists a constant `C : 𝕜` such that eventually `|f x| ≤ C`,
  then the product `f * g` tends to zero. -/
theorem bdd_le_mul_tendsto_zero' {f g : α → 𝕜} (C : 𝕜) (hf : ∀ᶠ x in l, |f x| ≤ C)
    (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x ↦ f x * g x) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hC : Tendsto (fun x ↦ |C * g x|) l (𝓝 0) := by
    convert (hg.const_mul C).abs
    simp_rw [mul_zero, abs_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
  · filter_upwards [hf] with x _ using abs_nonneg _
  · filter_upwards [hf] with x hx
    simp only [comp_apply, abs_mul]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (abs_nonneg _)

/-- If `g` tends to zero and there exist constants `b B : 𝕜` such that eventually `b ≤ f x| ≤ B`,
  then the product `f * g` tends to zero. -/
theorem bdd_le_mul_tendsto_zero {f g : α → 𝕜} {b B : 𝕜} (hb : ∀ᶠ x in l, b ≤ f x)
    (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x ↦ f x * g x) l (𝓝 0) := by
  set C := max |b| |B|
  have hbC : -C ≤ b := neg_le.mpr (le_max_of_le_left (neg_le_abs b))
  have hBC : B ≤ C := le_max_of_le_right (le_abs_self B)
  apply bdd_le_mul_tendsto_zero' C _ hg
  filter_upwards [hb, hB]
  exact fun x hbx hBx ↦ abs_le.mpr ⟨hbC.trans hbx, hBx.trans hBC⟩

/-- If `g` tends to `atTop` and there exist constants `b B : 𝕜` such that eventually
  `b ≤ f x| ≤ B`, then the quotient `f / g` tends to zero. -/
@[target] theorem tendsto_bdd_div_atTop_nhds_zero {f g : α → 𝕜} {b B : 𝕜}
    (hb : ∀ᶠ x in l, b ≤ f x) (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by sorry


/-- The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_atTop`. -/
@[target] theorem tendsto_pow_neg_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : 𝕜 => x ^ (-(n : ℤ))) atTop (𝓝 0) := by sorry


@[target] theorem tendsto_zpow_atTop_zero {n : ℤ} (hn : n < 0) :
    Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0) := by sorry


@[target] theorem tendsto_const_mul_zpow_atTop_zero {n : ℤ} {c : 𝕜} (hn : n < 0) :
    Tendsto (fun x => c * x ^ n) atTop (𝓝 0) := by sorry


@[target] theorem tendsto_const_mul_pow_nhds_iff' {n : ℕ} {c d : 𝕜} :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ (c = 0 ∨ n = 0) ∧ c = d := by sorry


theorem tendsto_const_mul_pow_nhds_iff {n : ℕ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d := by
  simp [tendsto_const_mul_pow_nhds_iff', hc]

@[target] theorem tendsto_const_mul_zpow_atTop_nhds_iff {n : ℤ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d ∨ n < 0 ∧ d = 0 := by sorry

instance (priority := 100) LinearOrderedSemifield.toHasContinuousInv₀ {𝕜}
    [LinearOrderedSemifield 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ContinuousMul 𝕜] :
    HasContinuousInv₀ 𝕜 := .of_nhds_one <| tendsto_order.2 <| by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨x', h₀, hxx', h₁⟩ : ∃ x', 0 < x' ∧ x ≤ x' ∧ x' < 1 :=
      ⟨max x (1 / 2), one_half_pos.trans_le (le_max_right _ _), le_max_left _ _,
        max_lt hx one_half_lt_one⟩
    filter_upwards [Ioo_mem_nhds one_pos ((one_lt_inv₀ h₀).2 h₁)] with y hy
    exact hxx'.trans_lt <| lt_inv_of_lt_inv₀ hy.1 hy.2
  · filter_upwards [Ioi_mem_nhds (inv_lt_one_of_one_lt₀ hx)] with y hy
    exact inv_lt_of_inv_lt₀ (by positivity) hy

instance (priority := 100) LinearOrderedField.toTopologicalDivisionRing :
    TopologicalDivisionRing 𝕜 := ⟨⟩

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: generalize to a `GroupWithZero`
@[target] theorem comap_mulLeft_nhdsGT_zero {x : 𝕜} (hx : 0 < x) : comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0 := by sorry


@[deprecated (since := "2024-12-22")]
alias nhdsWithin_pos_comap_mul_left := comap_mulLeft_nhdsGT_zero

@[target] theorem eventually_nhdsGT_zero_mul_left {x : 𝕜} (hx : 0 < x) {p : 𝕜 → Prop}
    (h : ∀ᶠ ε in 𝓝[>] 0, p ε) : ∀ᶠ ε in 𝓝[>] 0, p (x * ε) := by sorry


@[deprecated (since := "2024-12-22")]
alias eventually_nhdsWithin_pos_mul_left := eventually_nhdsGT_zero_mul_left
