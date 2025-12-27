import VerifiedAgora.tagger
/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Correspondence between nontrivial nonarchimedean norms and rank one valuations

Nontrivial nonarchimedean norms correspond to rank one valuations.

## Main Definitions
* `NormedField.toValued` : the valued field structure on a nonarchimedean normed field `K`,
  determined by the norm.
* `Valued.toNormedField` : the normed field structure determined by a rank one valuation.

## Tags

norm, nonarchimedean, nontrivial, valuation, rank one
-/


noncomputable section

open Filter Set Valuation

open scoped NNReal

section

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

namespace NormedField

/-- The valuation on a nonarchimedean normed field `K` defined as `nnnorm`. -/
def valuation : Valuation K ℝ≥0 where
  toFun := by sorry


@[target] theorem valuation_apply (x : K) : valuation x = ‖x‖₊ := by sorry


/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
def toValued : Valued K ℝ≥0 := by sorry


instance {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] :
    Valuation.RankOne (valuation (K := K)) where
  hom := .id _
  strictMono' := strictMono_id
  nontrivial' := (exists_one_lt_norm K).imp fun x h ↦ by
    have h' : x ≠ 0 := norm_eq_zero.not.mp (h.gt.trans' (by simp)).ne'
    simp [valuation_apply, ← NNReal.coe_inj, h.ne', h']

end NormedField

end

namespace Valued

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : RankOne val.v]

/-- The norm function determined by a rank one valuation on a field `L`. -/
def norm : L → ℝ := fun x : L => hv.hom (Valued.v x)

@[target] theorem norm_nonneg (x : L) : 0 ≤ norm x := by sorry


@[target] theorem norm_add_le (x y : L) : norm (x + y) ≤ max (norm x) (norm y) := by sorry


@[target] theorem norm_eq_zero {x : L} (hx : norm x = 0) : x = 0 := by sorry


variable (L) (Γ₀)

/-- The normed field structure determined by a rank one valuation. -/
def toNormedField : NormedField L := by sorry


section NormedField

open scoped Valued

protected lemma isNonarchimedean_norm : IsNonarchimedean ((‖·‖): L → ℝ) := Valued.norm_add_le

instance : IsUltrametricDist L :=
  ⟨fun x y z ↦ by
    refine (Valued.norm_add_le (x - y) (y - z)).trans_eq' ?_
    simp only [sub_add_sub_cancel]
    rfl ⟩

lemma coe_valuation_eq_rankOne_hom_comp_valuation : ⇑NormedField.valuation = hv.hom ∘ val.v := rfl

end NormedField

variable {L} {Γ₀}

namespace toNormedField

variable {x x' : L}

@[target] theorem norm_le_iff : ‖x‖ ≤ ‖x'‖ ↔ val.v x ≤ val.v x' := by sorry


@[target] theorem norm_lt_iff : ‖x‖ < ‖x'‖ ↔ val.v x < val.v x' := by sorry


@[target] theorem norm_le_one_iff : ‖x‖ ≤ 1 ↔ val.v x ≤ 1 := by sorry


@[target] theorem norm_lt_one_iff : ‖x‖ < 1 ↔ val.v x < 1 := by sorry


@[target] theorem one_le_norm_iff : 1 ≤ ‖x‖ ↔ 1 ≤ val.v x := by sorry


@[target] theorem one_lt_norm_iff : 1 < ‖x‖ ↔ 1 < val.v x := by sorry


end toNormedField

/--
The nontrivially normed field structure determined by a rank one valuation.
-/
def toNontriviallyNormedField: NontriviallyNormedField L := by sorry


end Valued
