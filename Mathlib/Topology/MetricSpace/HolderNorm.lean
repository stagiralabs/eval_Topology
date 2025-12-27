import VerifiedAgora.tagger
/-
Copyright (c) 2024 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder norm

This file defines the Hölder (semi-)norm for Hölder functions alongside some basic properties.
The `r`-Hölder norm of a function `f : X → Y` between two metric spaces is the least non-negative
real number `C` for which `f` is `r`-Hölder continuous with constant `C`, i.e. it is the least `C`
for which `WithHolder C r f` is true.

## Main definitions

* `eHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f`.
* `nnHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0` of a function `f`.
* `MemHolder r f`: Predicate for a function `f` being `r`-Hölder continuous.

## Main results

* `eHolderNorm_eq_zero`: the Hölder norm of a function is zero if and only if it is constant.
* `MemHolder.holderWith`: The Hölder norm of a Hölder function `f` is a Hölder constant of `f`.

## Tags

Hölder norm, Hoelder norm, Holder norm

-/

variable {X Y : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {r : ℝ≥0} {f : X → Y}

/-- The `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f` is the least non-negative real
number `C` for which `f` is `r`-Hölder continuous with constant `C`. This is `∞` if no such
non-negative real exists. -/
noncomputable
def eHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0∞ := by sorry


/-- The `r`-Hölder (semi)norm in `ℝ≥0`. -/
noncomputable
def nnHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0 := by sorry


/-- A function `f` is `MemHolder r f` if it is Hölder continuous. Namely, `f` has a finite
`r`-Hölder constant. This is equivalent to `f` having finite Hölder norm.
c.f. `memHolder_iff`. -/
def MemHolder (r : ℝ≥0) (f : X → Y) : Prop := by sorry


@[target] lemma HolderWith.memHolder {C : ℝ≥0} (hf : HolderWith C r f) : MemHolder r f := by sorry


@[target] lemma eHolderNorm_lt_top : eHolderNorm r f < ∞ ↔ MemHolder r f := by sorry


@[target] lemma eHolderNorm_ne_top : eHolderNorm r f ≠ ∞ ↔ MemHolder r f := by sorry


@[target] lemma eHolderNorm_eq_top : eHolderNorm r f = ∞ ↔ ¬ MemHolder r f := by sorry


protected alias ⟨_, MemHolder.eHolderNorm_lt_top⟩ := eHolderNorm_lt_top
protected alias ⟨_, MemHolder.eHolderNorm_ne_top⟩ := eHolderNorm_ne_top

lemma coe_nnHolderNorm_le_eHolderNorm {r : ℝ≥0} {f : X → Y} :
    (nnHolderNorm r f : ℝ≥0∞) ≤ eHolderNorm r f :=
  coe_toNNReal_le_self

variable (X) in
@[target] lemma eHolderNorm_const (r : ℝ≥0) (c : Y) : eHolderNorm r (Function.const X c) = 0 := by sorry


variable (X) in
@[simp]
lemma eHolderNorm_zero [Zero Y] (r : ℝ≥0) : eHolderNorm r (0 : X → Y) = 0 :=
  eHolderNorm_const X r 0

variable (X) in
@[target] lemma nnHolderNorm_const (r : ℝ≥0) (c : Y) : nnHolderNorm r (Function.const X c) = 0 := by sorry


variable (X) in
@[simp]
lemma nnHolderNorm_zero [Zero Y] (r : ℝ≥0) : nnHolderNorm r (0 : X → Y) = 0 :=
  nnHolderNorm_const X r 0

attribute [simp] eHolderNorm_const eHolderNorm_zero

@[target] lemma eHolderNorm_of_isEmpty [hX : IsEmpty X] :
    eHolderNorm r f = 0 := by sorry


@[target] lemma HolderWith.eHolderNorm_le {C : ℝ≥0} (hf : HolderWith C r f) :
    eHolderNorm r f ≤ C := by sorry


/-- See also `memHolder_const` for the version with the spelling `fun _ ↦ c`. -/
@[target] lemma memHolder_const {c : Y} : MemHolder r (Function.const X c) := by sorry


/-- Version of `memHolder_const` with the spelling `fun _ ↦ c` for the constant function. -/
@[simp]
lemma memHolder_const' {c : Y} : MemHolder r (fun _ ↦ c : X → Y) :=
  memHolder_const

@[target] lemma memHolder_zero [Zero Y] : MemHolder r (0 : X → Y) := by sorry


end PseudoEMetricSpace

section MetricSpace

variable [MetricSpace X] [EMetricSpace Y]

@[target] lemma eHolderNorm_eq_zero {r : ℝ≥0} {f : X → Y} :
    eHolderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by sorry


@[target] lemma MemHolder.holderWith {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    HolderWith (nnHolderNorm r f) r f := by sorry


@[target] lemma memHolder_iff_holderWith {r : ℝ≥0} {f : X → Y} :
    MemHolder r f ↔ HolderWith (nnHolderNorm r f) r f := by sorry


lemma MemHolder.coe_nnHolderNorm_eq_eHolderNorm
    {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    (nnHolderNorm r f : ℝ≥0∞) = eHolderNorm r f := by
  rw [nnHolderNorm, coe_toNNReal]
  exact ne_of_lt <| lt_of_le_of_lt hf.holderWith.eHolderNorm_le <| coe_lt_top

lemma HolderWith.nnholderNorm_le {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    nnHolderNorm r f ≤ C := by
  rw [← ENNReal.coe_le_coe, hf.memHolder.coe_nnHolderNorm_eq_eHolderNorm]
  exact hf.eHolderNorm_le

lemma MemHolder.comp {r s : ℝ≥0} {Z : Type*} [MetricSpace Z] {f : Z → X} {g : X → Y}
    (hf : MemHolder r f) (hg : MemHolder s g) : MemHolder (s * r) (g ∘ f) :=
  (hg.holderWith.comp hf.holderWith).memHolder

@[target] lemma MemHolder.nnHolderNorm_eq_zero {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    nnHolderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by sorry


end MetricSpace

section SeminormedAddCommGroup

variable [MetricSpace X] [NormedAddCommGroup Y]
variable {r : ℝ≥0} {f g : X → Y}

@[target] lemma MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f + g) := by sorry


@[target] lemma MemHolder.smul {𝕜} [NormedDivisionRing 𝕜] [Module 𝕜 Y] [BoundedSMul 𝕜 Y]
    {c : 𝕜} (hf : MemHolder r f) : MemHolder r (c • f) := by sorry


@[target] lemma MemHolder.nsmul [Module ℝ Y] [BoundedSMul ℝ Y] (n : ℕ) (hf : MemHolder r f) :
    MemHolder r (n • f) := by sorry


lemma MemHolder.nnHolderNorm_add_le (hf : MemHolder r f) (hg : MemHolder r g) :
    nnHolderNorm r (f + g) ≤ nnHolderNorm r f + nnHolderNorm r g :=
  (hf.add hg).holderWith.nnholderNorm_le.trans <|
    coe_le_coe.2 (hf.holderWith.add hg.holderWith).nnholderNorm_le

lemma eHolderNorm_add_le :
    eHolderNorm r (f + g) ≤ eHolderNorm r f + eHolderNorm r g := by
  by_cases hfg : MemHolder r f  ∧ MemHolder r g
  · obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_nnHolderNorm_eq_eHolderNorm, ← hg.coe_nnHolderNorm_eq_eHolderNorm,
      ← (hf.add hg).coe_nnHolderNorm_eq_eHolderNorm, ← coe_add, ENNReal.coe_le_coe]
    exact hf.nnHolderNorm_add_le hg
  · rw [Classical.not_and_iff_or_not_not, ← eHolderNorm_eq_top, ← eHolderNorm_eq_top] at hfg
    obtain (h | h) := hfg
    all_goals simp [h]

lemma eHolderNorm_smul {α} [NormedDivisionRing α] [Module α Y] [BoundedSMul α Y] (c : α) :
    eHolderNorm r (c • f) = ‖c‖₊ * eHolderNorm r f := by
  by_cases hc : ‖c‖₊ = 0
  · rw [nnnorm_eq_zero] at hc
    simp [hc]
  by_cases hf : MemHolder r f
  · refine le_antisymm ((hf.holderWith.smul c).eHolderNorm_le.trans ?_) <| mul_le_of_le_div' ?_
    · rw [coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm, mul_comm]
    · rw [← (hf.holderWith.smul c).memHolder.coe_nnHolderNorm_eq_eHolderNorm, ← coe_div hc]
      refine HolderWith.eHolderNorm_le fun x₁ x₂ => ?_
      rw [coe_div hc, ← ENNReal.mul_div_right_comm,
        ENNReal.le_div_iff_mul_le (Or.inl <| coe_ne_zero.2 hc) <| Or.inl coe_ne_top,
        mul_comm, ← smul_eq_mul, ← ENNReal.smul_def, ← edist_smul₀, ← Pi.smul_apply,
        ← Pi.smul_apply]
      exact hf.smul.holderWith x₁ x₂
  · rw [← eHolderNorm_eq_top] at hf
    rw [hf, mul_top <| coe_ne_zero.2 hc, eHolderNorm_eq_top]
    rw [nnnorm_eq_zero] at hc
    intro h
    have := h.smul (c := c⁻¹)
    rw [inv_smul_smul₀ hc] at this
    exact this.eHolderNorm_lt_top.ne hf

@[target] lemma MemHolder.nnHolderNorm_smul {α} [NormedDivisionRing α] [Module α Y] [BoundedSMul α Y]
    (hf : MemHolder r f) (c : α) :
    nnHolderNorm r (c • f) = ‖c‖₊ * nnHolderNorm r f := by sorry


@[target] lemma eHolderNorm_nsmul [Module ℝ Y] [BoundedSMul ℝ Y] (n : ℕ) :
    eHolderNorm r (n • f) = n • eHolderNorm r f := by sorry


@[target] lemma MemHolder.nnHolderNorm_nsmul [Module ℝ Y] [BoundedSMul ℝ Y] (n : ℕ) (hf : MemHolder r f) :
    nnHolderNorm r (n • f) = n • nnHolderNorm r f := by sorry


end SeminormedAddCommGroup
