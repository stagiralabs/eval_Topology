import VerifiedAgora.tagger
/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.Algebra.Algebra

/-!
# Isomorphisms of topological algebras

This file contains an API for `ContinuousAlgEquiv R A B`, the type of
continuous `R`-algebra isomorphisms with continuous inverses. Here `R` is a
commutative (semi)ring, and `A` and `B` are `R`-algebras with topologies.

## Main definitions

Let `R` be a commutative semiring and let `A` and `B` be `R`-algebras which
are also topological spaces.

* `ContinuousAlgEquiv R A B`: the type of continuous `R`-algebra isomorphisms
  from `A` to `B` with continuous inverses.

## Notations

`A ≃A[R] B` : notation for `ContinuousAlgEquiv R A B`.

## Tags

* continuous, isomorphism, algebra
-/

open scoped Topology


/--
`ContinuousAlgEquiv R A B`, with notation `A ≃A[R] B`, is the type of bijections
between the topological `R`-algebras `A` and `B` which are both homeomorphisms
and `R`-algebra isomorphisms.
-/
structure ContinuousAlgEquiv (R A B : Type*) [CommSemiring R]
    [Semiring A] [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A]
    [Algebra R B] extends A ≃ₐ[R] B, A ≃ₜ B

@[inherit_doc]
notation:50 A " ≃A[" R "] " B => ContinuousAlgEquiv R A B

attribute [nolint docBlame] ContinuousAlgEquiv.toHomeomorph

/--
`ContinuousAlgEquivClass F R A B` states that `F` is a type of topological algebra
  structure-preserving equivalences. You should extend this class when you
  extend `ContinuousAlgEquiv`.
-/
class ContinuousAlgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
    [Semiring A] [TopologicalSpace A] [Semiring B] [TopologicalSpace B]
    [Algebra R A] [Algebra R B] [EquivLike F A B]
    extends AlgEquivClass F R A B, HomeomorphClass F A B : Prop

namespace ContinuousAlgEquiv

variable {R A B C : Type*}
  [CommSemiring R] [Semiring A] [TopologicalSpace A] [Semiring B]
  [TopologicalSpace B] [Semiring C] [TopologicalSpace C] [Algebra R A] [Algebra R B]
  [Algebra R C]

/-- The natural coercion from a continuous algebra isomorphism to a continuous
algebra morphism. -/
@[coe]
def toContinuousAlgHom (e : A ≃A[R] B) : A →A[R] B where
  __ := e.toAlgHom
  cont := e.continuous_toFun

instance coe : Coe (A ≃A[R] B) (A →A[R] B) := ⟨toContinuousAlgHom⟩

instance equivLike : EquivLike (A ≃A[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨_, _⟩, _⟩
    rcases g' with ⟨⟨_, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance continuousAlgEquivClass : ContinuousAlgEquivClass (A ≃A[R] B) R A B where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

theorem coe_apply (e : A ≃A[R] B) (a : A) : (e : A →A[R] B) a = e a := rfl

@[simp]
theorem coe_coe (e : A ≃A[R] B) : ⇑(e : A →A[R] B) = e := rfl

theorem toAlgEquiv_injective : Function.Injective (toAlgEquiv : (A ≃A[R] B) → A ≃ₐ[R] B) := by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[target] theorem ext {f g : C_c(α, β)} (h : ∀ x, f x = g x) : f = g := by sorry


theorem coe_injective : Function.Injective ((↑) : (A ≃A[R] B) → A →A[R] B) :=
  fun _ _ h => ext <| funext <| ContinuousAlgHom.ext_iff.1 h

@[simp]
theorem coe_inj {f g : A ≃A[R] B} : (f : A →A[R] B) = g ↔ f = g :=
  coe_injective.eq_iff

@[simp]
theorem coe_toAlgEquiv (e : A ≃A[R] B) : ⇑e.toAlgEquiv = e := rfl

theorem isOpenMap (e : A ≃A[R] B) : IsOpenMap e :=
  e.toHomeomorph.isOpenMap

theorem image_closure (e : A ≃A[R] B) (S : Set A) : e '' closure S = closure (e '' S) :=
  e.toHomeomorph.image_closure S

theorem preimage_closure (e : A ≃A[R] B) (S : Set B) : e ⁻¹' closure S = closure (e ⁻¹' S) :=
  e.toHomeomorph.preimage_closure S

@[simp]
theorem isClosed_image (e : A ≃A[R] B) {S : Set A} : IsClosed (e '' S) ↔ IsClosed S :=
  e.toHomeomorph.isClosed_image

theorem map_nhds_eq (e : A ≃A[R] B) (a : A) : Filter.map e (𝓝 a) = 𝓝 (e a) :=
  e.toHomeomorph.map_nhds_eq a

theorem map_eq_zero_iff (e : A ≃A[R] B) {a : A} : e a = 0 ↔ a = 0 :=
  e.toAlgEquiv.toLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousAlgEquiv.continuous_invFun ContinuousAlgEquiv.continuous_toFun

@[fun_prop]
theorem continuous (e : A ≃A[R] B) : Continuous e := e.continuous_toFun

theorem continuousOn (e : A ≃A[R] B) {S : Set A} : ContinuousOn e S :=
  e.continuous.continuousOn

theorem continuousAt (e : A ≃A[R] B) {a : A} : ContinuousAt e a :=
  e.continuous.continuousAt

theorem continuousWithinAt (e : A ≃A[R] B) {S : Set A} {a : A} :
    ContinuousWithinAt e S a :=
  e.continuous.continuousWithinAt

theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : A ≃A[R] B) {f : α → A} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff

theorem comp_continuous_iff' {β : Type*} [TopologicalSpace β] (e : A ≃A[R] B) {g : B → β} :
    Continuous (g ∘ e) ↔ Continuous g :=
  e.toHomeomorph.comp_continuous_iff'

variable (R A)

/-- The identity isomorphism as a continuous `R`-algebra equivalence. -/
@[refl]
def refl : A ≃A[R] A where
  __ := AlgEquiv.refl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem refl_apply (a : A) : refl R A a = a := rfl

@[simp]
theorem coe_refl : refl R A = ContinuousAlgHom.id R A := rfl

@[simp]
theorem coe_refl' : ⇑(refl R A) = id := rfl

variable {R A}

/-- The inverse of a continuous algebra equivalence. -/
@[symm]
def symm (e : A ≃A[R] B) : B ≃A[R] A where
  __ := e.toAlgEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

@[simp]
theorem apply_symm_apply (e : A ≃A[R] B) (b : B) : e (e.symm b) = b :=
  e.1.right_inv b

@[simp]
theorem symm_apply_apply (e : A ≃A[R] B) (a : A) : e.symm (e a) = a :=
  e.1.left_inv a

@[simp]
theorem symm_image_image (e : A ≃A[R] B) (S : Set A) : e.symm '' (e '' S) = S :=
  e.toEquiv.symm_image_image S

@[simp]
theorem image_symm_image (e : A ≃A[R] B) (S : Set B) : e '' (e.symm '' S) = S :=
  e.symm.symm_image_image S

@[simp]
theorem symm_toAlgEquiv (e : A ≃A[R] B) : e.symm.toAlgEquiv = e.toAlgEquiv.symm := rfl

@[simp]
theorem symm_toHomeomorph (e : A ≃A[R] B) : e.symm.toHomeomorph = e.toHomeomorph.symm := rfl

theorem symm_map_nhds_eq (e : A ≃A[R] B) (a : A) : Filter.map e.symm (𝓝 (e a)) = 𝓝 a :=
  e.toHomeomorph.symm_map_nhds_eq a

/-- The composition of two continuous algebra equivalences. -/
@[trans]
def trans (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) : A ≃A[R] C where
  __ := e₁.toAlgEquiv.trans e₂.toAlgEquiv
  continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
  continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun

@[simp]
theorem trans_toAlgEquiv (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) :
    (e₁.trans e₂).toAlgEquiv = e₁.toAlgEquiv.trans e₂.toAlgEquiv :=
  rfl

@[simp]
theorem trans_apply (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) (a : A) :
    (e₁.trans e₂) a = e₂ (e₁ a) :=
  rfl

@[simp]
theorem symm_trans_apply (e₁ : B ≃A[R] A) (e₂ : C ≃A[R] B) (a : A) :
    (e₂.trans e₁).symm a = e₂.symm (e₁.symm a) :=
  rfl

theorem comp_coe (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) :
    e₂.toAlgHom.comp e₁.toAlgHom = e₁.trans e₂ := by
  rfl

@[simp high]
theorem coe_comp_coe_symm (e : A ≃A[R] B) :
    e.toContinuousAlgHom.comp e.symm = ContinuousAlgHom.id R B :=
  ContinuousAlgHom.ext e.apply_symm_apply

@[simp high]
theorem coe_symm_comp_coe (e : A ≃A[R] B) :
    e.symm.toContinuousAlgHom.comp e = ContinuousAlgHom.id R A :=
  ContinuousAlgHom.ext e.symm_apply_apply

@[simp]
theorem symm_comp_self (e : A ≃A[R] B) : (e.symm : B → A) ∘ e = id := by
  exact funext <| e.symm_apply_apply

@[simp]
theorem self_comp_symm (e : A ≃A[R] B) : (e : A → B) ∘ e.symm = id :=
  funext <| e.apply_symm_apply

@[simp]
theorem symm_symm (e : A ≃A[R] B) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A ≃A[R] B) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem refl_symm : (refl R A).symm = refl R A := rfl

theorem symm_symm_apply (e : A ≃A[R] B) (a : A) : e.symm.symm a = e a := rfl

theorem symm_apply_eq (e : A ≃A[R] B) {a : A} {b : B} : e.symm b = a ↔ b = e a :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : A ≃A[R] B) {a : A} {b : B} : a = e.symm b ↔ e a = b :=
  e.toEquiv.eq_symm_apply

theorem image_eq_preimage (e : A ≃A[R] B) (S : Set A) : e '' S = e.symm ⁻¹' S :=
  e.toEquiv.image_eq_preimage S

theorem image_symm_eq_preimage (e : A ≃A[R] B) (S : Set B) : e.symm '' S = e ⁻¹' S := by
  rw [e.symm.image_eq_preimage, e.symm_symm]

@[simp]
theorem symm_preimage_preimage (e : A ≃A[R] B) (S : Set B) : e.symm ⁻¹' (e ⁻¹' S) = S :=
  e.toEquiv.symm_preimage_preimage S

@[simp]
theorem preimage_symm_preimage (e : A ≃A[R] B) (S : Set A) : e ⁻¹' (e.symm ⁻¹' S) = S :=
  e.symm.symm_preimage_preimage S

theorem isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂] [Ring E₁]
    [UniformAddGroup E₁] [Algebra R E₁] [Ring E₂] [UniformAddGroup E₂] [Algebra R E₂]
    (e : E₁ ≃A[R] E₂) : IsUniformEmbedding e :=
  e.toAlgEquiv.isUniformEmbedding e.toContinuousAlgHom.uniformContinuous
    e.symm.toContinuousAlgHom.uniformContinuous

theorem _root_.AlgEquiv.isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [Ring E₁] [UniformAddGroup E₁] [Algebra R E₁] [Ring E₂] [UniformAddGroup E₂] [Algebra R E₂]
    (e : E₁ ≃ₐ[R] E₂) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    IsUniformEmbedding e :=
  ContinuousAlgEquiv.isUniformEmbedding { e with continuous_toFun := h₁ }

end ContinuousAlgEquiv
