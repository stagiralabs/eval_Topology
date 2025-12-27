import VerifiedAgora.tagger
/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.MetricSpace.Dilation

/-!
# Dilation equivalence

In this file we define `DilationEquiv X Y`, a type of bundled equivalences between `X` and Y` such
that `edist (f x) (f y) = r * edist x y` for some `r : ℝ≥0`, `r ≠ 0`.

We also develop basic API about these equivalences.

## TODO

- Add missing lemmas (compare to other `*Equiv` structures).
- [after-port] Add `DilationEquivInstance` for `IsometryEquiv`.
-/

open scoped NNReal ENNReal
open Function Set Filter Bornology
open Dilation (ratio ratio_ne_zero ratio_pos edist_eq)

section Class

variable (F : Type*) (X Y : outParam Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- Typeclass saying that `F` is a type of bundled equivalences such that all `e : F` are
dilations. -/
class DilationEquivClass [EquivLike F X Y] : Prop where
  edist_eq' : ∀ f : F, ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : X, edist (f x) (f y) = r * edist x y

instance (priority := 100) [EquivLike F X Y] [DilationEquivClass F X Y] : DilationClass F X Y :=
  { inferInstanceAs (FunLike F X Y), ‹DilationEquivClass F X Y› with }

end Class

/-- Type of equivalences `X ≃ Y` such that `∀ x y, edist (f x) (f y) = r * edist x y` for some
`r : ℝ≥0`, `r ≠ 0`. -/
structure DilationEquiv (X Y : Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    extends X ≃ Y, Dilation X Y

@[inherit_doc] infixl:25 " ≃ᵈ " => DilationEquiv

namespace DilationEquiv

section PseudoEMetricSpace

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

instance : EquivLike (X ≃ᵈ Y) X Y where
  coe f := f.1
  inv f := f.1.symm
  left_inv f := f.left_inv'
  right_inv f := f.right_inv'
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h -; congr; exact DFunLike.ext' h

instance : DilationEquivClass (X ≃ᵈ Y) X Y where
  edist_eq' f := f.edist_eq'

@[target] theorem coe_toEquiv (e : X ≃ᵈ Y) : ⇑e.toEquiv = e := by sorry


@[ext]
protected theorem ext {e e' : X ≃ᵈ Y} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/-- Inverse `DilationEquiv`. -/
def symm (e : X ≃ᵈ Y) : Y ≃ᵈ X where
  toEquiv := by sorry


@[target] theorem symm_symm (e : X ≃ᵈ Y) : e.symm.symm = e := by sorry


theorem symm_bijective : Function.Bijective (DilationEquiv.symm : (X ≃ᵈ Y) → Y ≃ᵈ X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[target] theorem apply_symm_apply (e : X ≃ᵈ Y) (x : Y) : e (e.symm x) = x := by sorry

@[target] theorem symm_apply_apply (e : X ≃ᵈ Y) (x : X) : e.symm (e x) = x := by sorry


/-- See Note [custom simps projection]. -/
def Simps.symm_apply (e : X ≃ᵈ Y) : Y → X := e.symm

initialize_simps_projections DilationEquiv (toFun → apply, invFun → symm_apply)

@[target] lemma ratio_toDilation (e : X ≃ᵈ Y) : ratio e.toDilation = ratio e := by sorry


/-- Identity map as a `DilationEquiv`. -/
@[simps! (config := by sorry


@[target] theorem refl_symm : (refl X).symm = refl X := by sorry

@[simp] theorem ratio_refl : ratio (refl X) = 1 := Dilation.ratio_id

/-- Composition of `DilationEquiv`s. -/
@[simps! (config := by sorry


@[simp] theorem refl_trans (e : X ≃ᵈ Y) : (refl X).trans e = e := rfl
@[simp] theorem trans_refl (e : X ≃ᵈ Y) : e.trans (refl Y) = e := rfl

@[target] theorem symm_trans_self (e : X ≃ᵈ Y) : e.symm.trans e = refl Y := by sorry


@[target] theorem self_trans_symm (e : X ≃ᵈ Y) : e.trans e.symm = refl X := by sorry


protected theorem surjective (e : X ≃ᵈ Y) : Surjective e := e.1.surjective
protected theorem bijective (e : X ≃ᵈ Y) : Bijective e := e.1.bijective
protected theorem injective (e : X ≃ᵈ Y) : Injective e := e.1.injective

@[target] theorem ratio_trans (e : X ≃ᵈ Y) (e' : Y ≃ᵈ Z) : ratio (e.trans e') = ratio e * ratio e' := by sorry


@[target] theorem ratio_symm (e : X ≃ᵈ Y) : ratio e.symm = (ratio e)⁻¹ := by sorry


instance : Group (X ≃ᵈ X) where
  mul e e' := e'.trans e
  mul_assoc _ _ _ := rfl
  one := refl _
  one_mul _ := rfl
  mul_one _ := rfl
  inv := symm
  inv_mul_cancel := self_trans_symm

@[target] theorem mul_def (e e' : X ≃ᵈ X) : e * e' = e'.trans e := by sorry

@[target] theorem one_def : (1 : X ≃ᵈ X) = refl X := by sorry

@[target] theorem inv_def (e : X ≃ᵈ X) : e⁻¹ = e.symm := by sorry


@[target] theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : ⇑(f * g) = f * g := by sorry

@[target] theorem coe_one : ⇑(1 : X ≃ᵈ X) = id := by sorry

@[target] theorem coe_inv (e : X ≃ᵈ X) : ⇑(e⁻¹) = e.symm := by sorry


/-- `Dilation.ratio` as a monoid homomorphism. -/
noncomputable def ratioHom : (X ≃ᵈ X) →* ℝ≥0 where
  toFun := Dilation.ratio
  map_one' := ratio_refl
  map_mul' _ _ := (ratio_trans _ _).trans (mul_comm _ _)

@[simp]
theorem ratio_inv (e : X ≃ᵈ X) : ratio (e⁻¹) = (ratio e)⁻¹ := ratio_symm e

@[target] theorem ratio_pow (e : X ≃ᵈ X) (n : ℕ) : ratio (e ^ n) = ratio e ^ n := by sorry


@[target] theorem ratio_zpow (e : X ≃ᵈ X) (n : ℤ) : ratio (e ^ n) = ratio e ^ n := by sorry


/-- `DilationEquiv.toEquiv` as a monoid homomorphism. -/
@[simps]
def toPerm : (X ≃ᵈ X) →* Equiv.Perm X where
  toFun e := by sorry


@[target] theorem coe_pow (e : X ≃ᵈ X) (n : ℕ) : ⇑(e ^ n) = e^[n] := by sorry

/-- Every isometry equivalence is a dilation equivalence of ratio `1`. -/
def _root_.IsometryEquiv.toDilationEquiv (e : X ≃ᵢ Y) : X ≃ᵈ Y where
  edist_eq' := by sorry


@[target] lemma _root_.IsometryEquiv.toDilationEquiv_apply (e : X ≃ᵢ Y) (x : X) :
    e.toDilationEquiv x = e x := by sorry


@[target] lemma _root_.IsometryEquiv.toDilationEquiv_symm (e : X ≃ᵢ Y) :
    e.toDilationEquiv.symm = e.symm.toDilationEquiv := by sorry


@[simp]
lemma _root_.IsometryEquiv.toDilationEquiv_toDilation (e : X ≃ᵢ Y) :
    (e.toDilationEquiv.toDilation : X →ᵈ Y) = e.isometry.toDilation :=
  rfl

@[target] lemma _root_.IsometryEquiv.toDilationEquiv_ratio (e : X ≃ᵢ Y) : ratio e.toDilationEquiv = 1 := by sorry


/-- Reinterpret a `DilationEquiv` as a homeomorphism. -/
def toHomeomorph (e : X ≃ᵈ Y) : X ≃ₜ Y where
  continuous_toFun := by sorry


@[target] lemma coe_toHomeomorph (e : X ≃ᵈ Y) : ⇑e.toHomeomorph = e := by sorry


@[target] lemma toHomeomorph_symm (e : X ≃ᵈ Y) : e.toHomeomorph.symm = e.symm.toHomeomorph := by sorry


end PseudoEMetricSpace

section PseudoMetricSpace

variable {X Y F : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable [EquivLike F X Y] [DilationEquivClass F X Y]

@[target] lemma map_cobounded (e : F) : map e (cobounded X) = cobounded Y := by sorry


end PseudoMetricSpace

end DilationEquiv
