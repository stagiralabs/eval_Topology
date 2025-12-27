import VerifiedAgora.tagger
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/


open Filter

open Topology Filter

variable {α β : Type*}

/-- In a separated space, a complete set is closed. -/
@[target] theorem IsComplete.isClosed [UniformSpace α] [T0Space α] {s : Set α} (h : IsComplete s) :
    IsClosed s := by sorry


@[target] theorem IsUniformEmbedding.isClosedEmbedding [UniformSpace α] [UniformSpace β] [CompleteSpace α]
    [T0Space β] {f : α → β} (hf : IsUniformEmbedding f) :
    IsClosedEmbedding f := by sorry


@[deprecated (since := "2024-10-30")]
alias IsUniformEmbedding.toIsClosedEmbedding := IsUniformEmbedding.isClosedEmbedding

@[deprecated (since := "2024-10-20")]
alias IsUniformEmbedding.toClosedEmbedding := IsUniformEmbedding.isClosedEmbedding

@[deprecated (since := "2024-10-01")]
alias UniformEmbedding.toIsClosedEmbedding := IsUniformEmbedding.isClosedEmbedding

@[deprecated (since := "2024-10-20")]
alias UniformEmbedding.toClosedEmbedding := IsUniformEmbedding.isClosedEmbedding

namespace IsDenseInducing

open Filter

variable [TopologicalSpace α] {β : Type*} [TopologicalSpace β]
variable {γ : Type*} [UniformSpace γ] [CompleteSpace γ] [T0Space γ]

theorem continuous_extend_of_cauchy {e : α → β} {f : α → γ} (de : IsDenseInducing e)
    (h : ∀ b : β, Cauchy (map f (comap e <| 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend fun b => CompleteSpace.complete (h b)

end IsDenseInducing
