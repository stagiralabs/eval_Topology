import VerifiedAgora.tagger
/-
Copyright (c) 2024 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous bundled maps on intervals

In this file we prove a few results about `ContinuousMap` when the domain is an interval.
-/

open Set ContinuousMap Filter Topology

namespace ContinuousMap

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable {a b c : α} [Fact (a ≤ b)] [Fact (b ≤ c)]
variable {E : Type*} [TopologicalSpace E]

/-- The embedding into an interval from a sub-interval lying on the left, as a `ContinuousMap`. -/
def IccInclusionLeft : C(Icc a b, Icc a c) :=
  .inclusion <| Icc_subset_Icc le_rfl Fact.out

/-- The embedding into an interval from a sub-interval lying on the right, as a `ContinuousMap`. -/
def IccInclusionRight : C(Icc b c, Icc a c) :=
  .inclusion <| Icc_subset_Icc Fact.out le_rfl

/-- The map `projIcc` from `α` onto an interval in `α`, as a `ContinuousMap`. -/
def projIccCM : C(α, Icc a b) :=
  ⟨projIcc a b Fact.out, continuous_projIcc⟩

/-- The extension operation from continuous maps on an interval to continuous maps on the whole
  type, as a `ContinuousMap`. -/
def IccExtendCM : C(C(Icc a b, E), C(α, E)) where
  toFun f := f.comp projIccCM
  continuous_toFun := continuous_precomp projIccCM

@[target] theorem IccExtendCM_of_mem {f : C(Icc a b, E)} {x : α} (hx : x ∈ Icc a b) :
    IccExtendCM f x = f ⟨x, hx⟩ := by sorry


/-- The concatenation of two continuous maps defined on adjacent intervals. If the values of the
functions on the common bound do not agree, this is defined as an arbitrarily chosen constant
map. See `concatCM` for the corresponding map on the subtype of compatible function pairs. -/
noncomputable def concat (f : C(Icc a b, E)) (g : C(Icc b c, E)) :
    C(Icc a c, E) := by
  by_cases hb : f ⊤ = g ⊥
  · let h (t : α) : E := if t ≤ b then IccExtendCM f t else IccExtendCM g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl
    simpa [IccExtendCM, projIccCM]
  · exact .const _ (f ⊥) -- junk value

variable {f : C(Icc a b, E)} {g : C(Icc b c, E)}

@[target] theorem concat_comp_IccInclusionLeft (hb : f ⊤ = g ⊥) :
    (concat f g).comp IccInclusionLeft = f := by sorry


theorem concat_comp_IccInclusionRight (hb : f ⊤ = g ⊥) :
    (concat f g).comp IccInclusionRight = g := by
  ext ⟨x, hx⟩
  obtain rfl | hxb := eq_or_ne x b
  · simpa [concat, IccInclusionRight, IccExtendCM, projIccCM, inclusion, hb]
  · have h : ¬ x ≤ b := lt_of_le_of_ne hx.1 (Ne.symm hxb) |>.not_le
    simp [concat, hb, IccInclusionRight, h, IccExtendCM, projIccCM, projIcc, inclusion, hx.2, hx.1]

@[target] theorem concat_left (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : t ≤ b) :
    concat f g t = f ⟨t, t.2.1, ht⟩ := by sorry


@[target] theorem concat_right (hb : f ⊤ = g ⊥) {t : Icc a c} (ht : b ≤ t) :
    concat f g t = g ⟨t, ht, t.2.2⟩ := by sorry


@[target] theorem tendsto_concat {ι : Type*} {p : Filter ι} {F : ι → C(Icc a b, E)} {G : ι → C(Icc b c, E)}
    (hfg : ∀ᶠ i in p, (F i) ⊤ = (G i) ⊥) (hfg' : f ⊤ = g ⊥)
    (hf : Tendsto F p (𝓝 f)) (hg : Tendsto G p (𝓝 g)) :
    Tendsto (fun i => concat (F i) (G i)) p (𝓝 (concat f g)) := by sorry


/-- The concatenation of compatible pairs of continuous maps on adjacent intervals, defined as a
`ContinuousMap` on a subtype of the product. -/
noncomputable def concatCM :
    C({fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}, C(Icc a c, E))
    where
  toFun fg := concat fg.val.1 fg.val.2
  continuous_toFun := by
    let S : Set (C(Icc a b, E) × C(Icc b c, E)) := {fg | fg.1 ⊤ = fg.2 ⊥}
    change Continuous (S.restrict concat.uncurry)
    refine continuousOn_iff_continuous_restrict.mp (fun fg hfg => ?_)
    refine tendsto_concat ?_ hfg ?_ ?_
    · exact eventually_nhdsWithin_of_forall (fun _ => id)
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_fst
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_snd

@[target] theorem concatCM_left {x : Icc a c} (hx : x ≤ b)
    {fg : {fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}} :
    concatCM fg x = fg.1.1 ⟨x.1, x.2.1, hx⟩ := by sorry


@[target] theorem concatCM_right {x : Icc a c} (hx : b ≤ x)
    {fg : {fg : C(Icc a b, E) × C(Icc b c, E) // fg.1 ⊤ = fg.2 ⊥}} :
    concatCM fg x = fg.1.2 ⟨x.1, hx, x.2.2⟩ := by sorry


end ContinuousMap
