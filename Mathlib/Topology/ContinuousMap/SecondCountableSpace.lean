import VerifiedAgora.tagger
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.CompactOpen

/-!
# Second countable topology on `C(X, Y)`

In this file we prove that `C(X, Y)` with compact-open topology has second countable topology, if

- both `X` and `Y` have second countable topology;
- `X` is a locally compact space;
-/

open scoped Topology
open Set Function Filter TopologicalSpace

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[target] theorem compactOpen_eq_generateFrom {S : Set (Set X)} {T : Set (Set Y)}
    (hS₁ : ∀ K ∈ S, IsCompact K) (hT : IsTopologicalBasis T)
    (hS₂ : ∀ f : C(X, Y), ∀ x, ∀ V ∈ T, f x ∈ V → ∃ K ∈ S, K ∈ 𝓝 x ∧ MapsTo f K V) :
    compactOpen = .generateFrom (.image2 (fun K t ↦
      {f : C(X, Y) | MapsTo f K (⋃₀ t)}) S {t : Set (Set Y) | t.Finite ∧ t ⊆ T}) := by sorry


/-- A version of `instSecondCountableTopology` with a technical assumption
instead of `[SecondCountableTopology X] [LocallyCompactSpace X]`.
It is here as a reminder of what could be an intermediate goal,
if someone tries to weaken the assumptions in the instance
(e.g., from `[LocallyCompactSpace X]` to `[LocallyCompactPair X Y]` - not sure if it's true). -/
theorem secondCountableTopology [SecondCountableTopology Y]
    (hX : ∃ S : Set (Set X), S.Countable ∧ (∀ K ∈ S, IsCompact K) ∧
      ∀ f : C(X, Y), ∀ V, IsOpen V → ∀ x ∈ f ⁻¹' V, ∃ K ∈ S, K ∈ 𝓝 x ∧ MapsTo f K V) :
    SecondCountableTopology C(X, Y) where
  is_open_generated_countable := by
    rcases hX with ⟨S, hScount, hScomp, hS⟩
    refine ⟨_, ?_, compactOpen_eq_generateFrom (S := S) hScomp (isBasis_countableBasis _) ?_⟩
    · exact .image2 hScount (countable_setOf_finite_subset (countable_countableBasis Y)) _
    · intro f x V hV hx
      apply hS
      exacts [isOpen_of_mem_countableBasis hV, hx]

instance instSecondCountableTopology [SecondCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopology Y] : SecondCountableTopology C(X, Y) := by
  apply secondCountableTopology
  have (U : countableBasis X) : LocallyCompactSpace U.1 :=
    (isOpen_of_mem_countableBasis U.2).locallyCompactSpace
  set K := fun U : countableBasis X ↦ CompactExhaustion.choice U.1
  use ⋃ U : countableBasis X, Set.range fun n ↦ K U n
  refine ⟨countable_iUnion fun _ ↦ countable_range _, ?_, ?_⟩
  · simp only [mem_iUnion, mem_range]
    rintro K ⟨U, n, rfl⟩
    exact ((K U).isCompact _).image continuous_subtype_val
  · intro f V hVo x hxV
    obtain ⟨U, hU, hxU, hUV⟩ : ∃ U ∈ countableBasis X, x ∈ U ∧ U ⊆ f ⁻¹' V := by
      rw [← (isBasis_countableBasis _).mem_nhds_iff]
      exact (hVo.preimage (map_continuous f)).mem_nhds hxV
    lift x to U using hxU
    lift U to countableBasis X using hU
    rcases (K U).exists_mem_nhds x with ⟨n, hn⟩
    refine ⟨K U n, mem_iUnion.2 ⟨U, mem_range_self _⟩, ?_, ?_⟩
    · rw [← map_nhds_subtype_coe_eq_nhds x.2]
      exacts [image_mem_map hn, (isOpen_of_mem_countableBasis U.2).mem_nhds x.2]
    · rw [mapsTo_image_iff]
      exact fun y _ ↦ hUV y.2

instance instSeparableSpace [SecondCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopology Y] : SeparableSpace C(X, Y) :=
  inferInstance

end ContinuousMap
