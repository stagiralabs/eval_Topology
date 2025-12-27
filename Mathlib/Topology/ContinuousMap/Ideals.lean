import VerifiedAgora.tagger
/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.CharacterSpace

/-!
# Ideals of continuous functions

For a topological semiring `R` and a topological space `X` there is a Galois connection between
`Ideal C(X, R)` and `Set X` given by sending each `I : Ideal C(X, R)` to
`{x : X | ∀ f ∈ I, f x = 0}ᶜ` and mapping `s : Set X` to the ideal with carrier
`{f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}`, and we call these maps `ContinuousMap.setOfIdeal` and
`ContinuousMap.idealOfSet`. As long as `R` is Hausdorff, `ContinuousMap.setOfIdeal I` is open,
and if, in addition, `X` is locally compact, then `ContinuousMap.setOfIdeal s` is closed.

When `R = 𝕜` with `RCLike 𝕜` and `X` is compact Hausdorff, then this Galois connection can be
improved to a true Galois correspondence (i.e., order isomorphism) between the type `opens X` and
the subtype of closed ideals of `C(X, 𝕜)`. Because we do not have a bundled type of closed ideals,
we simply register this as a Galois insertion between `Ideal C(X, 𝕜)` and `opens X`, which is
`ContinuousMap.idealOpensGI`. Consequently, the maximal ideals of `C(X, 𝕜)` are precisely those
ideals corresponding to (complements of) singletons in `X`.

In addition, when `X` is locally compact and `𝕜` is a nontrivial topological integral domain, then
there is a natural continuous map from `X` to `WeakDual.characterSpace 𝕜 C(X, 𝕜)` given by point
evaluation, which is herein called `WeakDual.CharacterSpace.continuousMapEval`. Again, when `X` is
compact Hausdorff and `RCLike 𝕜`, more can be obtained. In particular, in that context this map is
bijective, and since the domain is compact and the codomain is Hausdorff, it is a homeomorphism,
herein called `WeakDual.CharacterSpace.homeoEval`.

## Main definitions

* `ContinuousMap.idealOfSet`: ideal of functions which vanish on the complement of a set.
* `ContinuousMap.setOfIdeal`: complement of the set on which all functions in the ideal vanish.
* `ContinuousMap.opensOfIdeal`: `ContinuousMap.setOfIdeal` as a term of `opens X`.
* `ContinuousMap.idealOpensGI`: The Galois insertion `ContinuousMap.opensOfIdeal` and
  `fun s ↦ ContinuousMap.idealOfSet ↑s`.
* `WeakDual.CharacterSpace.continuousMapEval`: the natural continuous map from a locally compact
  topological space `X` to the `WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point
  evaluation at `x`, with modest hypothesis on `𝕜`.
* `WeakDual.CharacterSpace.homeoEval`: this is `WeakDual.CharacterSpace.continuousMapEval`
  upgraded to a homeomorphism when `X` is compact Hausdorff and `RCLike 𝕜`.

## Main statements

* `ContinuousMap.idealOfSet_ofIdeal_eq_closure`: when `X` is compact Hausdorff and
  `RCLike 𝕜`, `idealOfSet 𝕜 (setOfIdeal I) = I.closure` for any ideal `I : Ideal C(X, 𝕜)`.
* `ContinuousMap.setOfIdeal_ofSet_eq_interior`: when `X` is compact Hausdorff and `RCLike 𝕜`,
  `setOfIdeal (idealOfSet 𝕜 s) = interior s` for any `s : Set X`.
* `ContinuousMap.ideal_isMaximal_iff`: when `X` is compact Hausdorff and `RCLike 𝕜`, a closed
  ideal of `C(X, 𝕜)` is maximal if and only if it is `idealOfSet 𝕜 {x}ᶜ` for some `x : X`.

## Implementation details

Because there does not currently exist a bundled type of closed ideals, we don't provide the actual
order isomorphism described above, and instead we only consider the Galois insertion
`ContinuousMap.idealOpensGI`.

## Tags

ideal, continuous function, compact, Hausdorff
-/


open scoped NNReal

namespace ContinuousMap

open TopologicalSpace

section IsTopologicalRing

variable {X R : Type*} [TopologicalSpace X] [Semiring R]
variable [TopologicalSpace R] [IsTopologicalSemiring R]
variable (R)

/-- Given a topological ring `R` and `s : Set X`, construct the ideal in `C(X, R)` of functions
which vanish on the complement of `s`. -/
def idealOfSet (s : Set X) : Ideal C(X, R) where
  carrier := by sorry


@[target] theorem idealOfSet_closed [T2Space R] (s : Set X) :
    IsClosed (idealOfSet R s : Set C(X, R)) := by sorry


variable {R}

theorem mem_idealOfSet {s : Set X} {f : C(X, R)} :
    f ∈ idealOfSet R s ↔ ∀ ⦃x : X⦄, x ∈ sᶜ → f x = 0 := by
  convert Iff.rfl

@[target] theorem not_mem_idealOfSet {s : Set X} {f : C(X, R)} : f ∉ idealOfSet R s ↔ ∃ x ∈ sᶜ, f x ≠ 0 := by sorry


/-- Given an ideal `I` of `C(X, R)`, construct the set of points for which every function in the
ideal vanishes on the complement. -/
def setOfIdeal (I : Ideal C(X, R)) : Set X := by sorry


@[target] theorem not_mem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x ∉ setOfIdeal I ↔ ∀ ⦃f : C(X, R)⦄, f ∈ I → f x = 0 := by sorry


@[target] theorem mem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x ∈ setOfIdeal I ↔ ∃ f ∈ I, (f : C(X, R)) x ≠ 0 := by sorry


@[target] theorem setOfIdeal_open [T2Space R] (I : Ideal C(X, R)) : IsOpen (setOfIdeal I) := by sorry


/-- The open set `ContinuousMap.setOfIdeal I` realized as a term of `opens X`. -/
@[simps]
def opensOfIdeal [T2Space R] (I : Ideal C(X, R)) : Opens X :=
  ⟨setOfIdeal I, setOfIdeal_open I⟩

@[target] theorem setOfTop_eq_univ [Nontrivial R] : setOfIdeal (⊤ : Ideal C(X, R)) = Set.univ := by sorry


@[target] theorem idealOfEmpty_eq_bot : idealOfSet R (∅ : Set X) = ⊥ := by sorry


@[target] theorem mem_idealOfSet_compl_singleton (x : X) (f : C(X, R)) :
    f ∈ idealOfSet R ({x}ᶜ : Set X) ↔ f x = 0 := by sorry


variable (X R)

@[target] theorem ideal_gc : GaloisConnection (setOfIdeal : Ideal C(X, R) → Set X) (idealOfSet R) := by sorry


end IsTopologicalRing

section RCLike

open RCLike

variable {X 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]

/-- An auxiliary lemma used in the proof of `ContinuousMap.idealOfSet_ofIdeal_eq_closure` which may
be useful on its own. -/
@[target] theorem exists_mul_le_one_eqOn_ge (f : C(X, ℝ≥0)) {c : ℝ≥0} (hc : 0 < c) :
    ∃ g : C(X, ℝ≥0), (∀ x : X, (g * f) x ≤ 1) ∧ {x : X | c ≤ f x}.EqOn (g * f) 1 := by sorry


variable [CompactSpace X] [T2Space X]

@[target] theorem idealOfSet_ofIdeal_eq_closure (I : Ideal C(X, 𝕜)) :
    idealOfSet 𝕜 (setOfIdeal I) = I.closure := by sorry


@[target] theorem idealOfSet_ofIdeal_isClosed {I : Ideal C(X, 𝕜)} (hI : IsClosed (I : Set C(X, 𝕜))) :
    idealOfSet 𝕜 (setOfIdeal I) = I := by sorry


variable (𝕜)

@[target] theorem setOfIdeal_ofSet_eq_interior (s : Set X) : setOfIdeal (idealOfSet 𝕜 s) = interior s := by sorry


@[target] theorem setOfIdeal_ofSet_of_isOpen {s : Set X} (hs : IsOpen s) : setOfIdeal (idealOfSet 𝕜 s) = s := by sorry


variable (X) in
/-- The Galois insertion `ContinuousMap.opensOfIdeal : Ideal C(X, 𝕜) → Opens X` and
`fun s ↦ ContinuousMap.idealOfSet ↑s`. -/
@[simps]
def idealOpensGI :
    GaloisInsertion (opensOfIdeal : Ideal C(X, 𝕜) → Opens X) fun s => idealOfSet 𝕜 s where
  choice I _ := by sorry


@[target] theorem idealOfSet_isMaximal_iff (s : Opens X) :
    (idealOfSet 𝕜 (s : Set X)).IsMaximal ↔ IsCoatom s := by sorry


@[target] theorem idealOf_compl_singleton_isMaximal (x : X) : (idealOfSet 𝕜 ({x}ᶜ : Set X)).IsMaximal := by sorry


variable {𝕜}

@[target] theorem setOfIdeal_eq_compl_singleton (I : Ideal C(X, 𝕜)) [hI : I.IsMaximal] :
    ∃ x : X, setOfIdeal I = {x}ᶜ := by sorry


theorem ideal_isMaximal_iff (I : Ideal C(X, 𝕜)) [hI : IsClosed (I : Set C(X, 𝕜))] :
    I.IsMaximal ↔ ∃ x : X, idealOfSet 𝕜 {x}ᶜ = I := by
  refine
    ⟨?_, fun h =>
      let ⟨x, hx⟩ := h
      hx ▸ idealOf_compl_singleton_isMaximal 𝕜 x⟩
  intro hI'
  obtain ⟨x, hx⟩ := setOfIdeal_eq_compl_singleton I
  exact
    ⟨x, by
      simpa only [idealOfSet_ofIdeal_eq_closure, I.closure_eq_of_isClosed hI] using
        congr_arg (idealOfSet 𝕜) hx.symm⟩

end RCLike

end ContinuousMap

namespace WeakDual

namespace CharacterSpace

open Function ContinuousMap

variable (X 𝕜 : Type*) [TopologicalSpace X]

section ContinuousMapEval

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
variable [Nontrivial 𝕜] [NoZeroDivisors 𝕜]

/-- The natural continuous map from a locally compact topological space `X` to the
`WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point evaluation at `x`. -/
def continuousMapEval : C(X, characterSpace 𝕜 C(X, 𝕜)) where
  toFun x := by sorry


@[target] theorem continuousMapEval_apply_apply (x : X) (f : C(X, 𝕜)) : continuousMapEval X 𝕜 x f = f x := by sorry


end ContinuousMapEval

variable [CompactSpace X] [T2Space X] [RCLike 𝕜]

theorem continuousMapEval_bijective : Bijective (continuousMapEval X 𝕜) := by
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · contrapose! hxy
    rcases exists_continuous_zero_one_of_isClosed (isClosed_singleton : _root_.IsClosed {x})
        (isClosed_singleton : _root_.IsClosed {y}) (Set.disjoint_singleton.mpr hxy) with
      ⟨f, fx, fy, -⟩
    rw [DFunLike.ne_iff]
    use (⟨fun (x : ℝ) => (x : 𝕜), RCLike.continuous_ofReal⟩ : C(ℝ, 𝕜)).comp f
    simpa only [continuousMapEval_apply_apply, ContinuousMap.comp_apply, coe_mk, Ne,
      RCLike.ofReal_inj] using
      ((fx (Set.mem_singleton x)).symm ▸ (fy (Set.mem_singleton y)).symm ▸ zero_ne_one : f x ≠ f y)
  · obtain ⟨x, hx⟩ := (ideal_isMaximal_iff (RingHom.ker φ)).mp inferInstance
    refine ⟨x, CharacterSpace.ext_ker <| Ideal.ext fun f => ?_⟩
    simpa only [RingHom.mem_ker, continuousMapEval_apply_apply, mem_idealOfSet_compl_singleton,
      RingHom.mem_ker] using SetLike.ext_iff.mp hx f

/-- This is the natural homeomorphism between a compact Hausdorff space `X` and the
`WeakDual.characterSpace 𝕜 C(X, 𝕜)`. -/
noncomputable def homeoEval : X ≃ₜ characterSpace 𝕜 C(X, 𝕜) :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    { Equiv.ofBijective _ (continuousMapEval_bijective X 𝕜) with toFun := continuousMapEval X 𝕜 }
    (map_continuous (continuousMapEval X 𝕜))

end CharacterSpace

end WeakDual
