import VerifiedAgora.tagger
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Algebraic operations on `SeparationQuotient`

In this file we construct a section of the quotient map `E → SeparationQuotient E` as a continuous
linear map `SeparationQuotient E →L[K] E`.
-/

open Topology

namespace SeparationQuotient
section VectorSpace

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul K E]

/-- There exists a continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`.

Note that continuity of this map comes for free, because `mk` is a topology inducing map.
-/
@[target] theorem exists_out_continuousLinearMap :
    ∃ f : SeparationQuotient E →L[K] E, mkCLM K E ∘L f = .id K (SeparationQuotient E) := by sorry


/-- A continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`. -/
noncomputable def outCLM : SeparationQuotient E →L[K] E :=
  (exists_out_continuousLinearMap K E).choose

@[target] theorem mkCLM_comp_outCLM : mkCLM K E ∘L outCLM K E = .id K (SeparationQuotient E) := by sorry


variable {E} in
@[target] theorem mk_outCLM (x : SeparationQuotient E) : mk (outCLM K E x) = x := by sorry


@[target] theorem mk_comp_outCLM : mk ∘ outCLM K E = id := by sorry


variable {K} in
theorem postcomp_mkCLM_surjective {L : Type*} [Semiring L] (σ : L →+* K)
    (F : Type*) [AddCommMonoid F] [Module L F] [TopologicalSpace F] :
    Function.Surjective ((mkCLM K E).comp : (F →SL[σ] E) → (F →SL[σ] SeparationQuotient E)) := by
  intro f
  use (outCLM K E).comp f
  rw [← ContinuousLinearMap.comp_assoc, mkCLM_comp_outCLM, ContinuousLinearMap.id_comp]

/-- The `SeparationQuotient.outCLM K E` map is a topological embedding. -/
theorem isEmbedding_outCLM : IsEmbedding (outCLM K E) :=
  Function.LeftInverse.isEmbedding (mk_outCLM K) continuous_mk (map_continuous _)

@[deprecated (since := "2024-10-26")]
alias outCLM_embedding := isEmbedding_outCLM

@[target] theorem outCLM_injective : Function.Injective (outCLM K E) := by sorry


end VectorSpace

section VectorSpaceUniform

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
    [UniformSpace E] [UniformAddGroup E] [ContinuousConstSMul K E]

@[target] theorem outCLM_isUniformInducing : IsUniformInducing (outCLM K E) := by sorry


@[deprecated (since := "2024-10-05")]
alias outCLM_uniformInducing := outCLM_isUniformInducing

theorem outCLM_isUniformEmbedding : IsUniformEmbedding (outCLM K E) where
  injective := outCLM_injective K E
  toIsUniformInducing := outCLM_isUniformInducing K E

@[deprecated (since := "2024-10-01")]
alias outCLM_uniformEmbedding := outCLM_isUniformEmbedding

@[target] theorem outCLM_uniformContinuous : UniformContinuous (outCLM K E) := by sorry


end VectorSpaceUniform
end SeparationQuotient
