import VerifiedAgora.tagger
/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
## Ultrametric spaces

This file defines ultrametric spaces, implemented as a mixin on the `Dist`,
so that it can apply on pseudometric spaces as well.

## Main definitions

* `IsUltrametricDist X`: Annotates `dist : X → X → ℝ` as respecting the ultrametric inequality
  of `dist(x, z) ≤ max {dist(x,y), dist(y,z)}`

## Implementation details

The mixin could have been defined as a hypothesis to be carried around, instead of relying on
typeclass synthesis. However, since we declare a (pseudo)metric space on a type using
typeclass arguments, one can declare the ultrametricity at the same time.
For example, one could say `[Norm K] [Fact (IsNonarchimedean (norm : K → ℝ))]`,

The file imports a later file in the hierarchy of pseudometric spaces, since
`Metric.isClosed_closedBall` and `Metric.isClosed_sphere` is proven in a later file
using more conceptual results.

TODO: Generalize to ultrametric uniformities

## Tags

ultrametric, nonarchimedean
-/

variable {X : Type*}

/-- The `dist : X → X → ℝ` respects the ultrametric inequality
of `dist(x, z) ≤ max (dist(x,y)) (dist(y,z))`. -/
class IsUltrametricDist (X : Type*) [Dist X] : Prop where
  dist_triangle_max : ∀ x y z : X, dist x z ≤ max (dist x y) (dist y z)

open Metric

variable [PseudoMetricSpace X] [IsUltrametricDist X] (x y z : X) (r s : ℝ)

@[target] lemma dist_triangle_max : dist x z ≤ max (dist x y) (dist y z) := by sorry


namespace IsUltrametricDist

/-- All triangles are isosceles in an ultrametric space. -/
@[target] lemma dist_eq_max_of_dist_ne_dist (h : dist x y ≠ dist y z) :
    dist x z = max (dist x y) (dist y z) := by sorry


instance subtype (p : X → Prop) : IsUltrametricDist (Subtype p) :=
  ⟨fun _ _ _ ↦ by simpa [Subtype.dist_eq] using dist_triangle_max _ _ _⟩

lemma ball_eq_of_mem {x y : X} {r : ℝ} (h : y ∈ ball x r) : ball x r = ball y r := by
  ext a
  simp_rw [mem_ball] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans_lt (max_lt h' (dist_comm x _ ▸ h))

lemma mem_ball_iff {x y : X} {r : ℝ} : y ∈ ball x r ↔ x ∈ ball y r := by
  cases lt_or_le 0 r with
  | inl hr =>
    constructor <;> intro h <;>
    rw [← ball_eq_of_mem h] <;>
    simp [hr]
  | inr hr => simp [ball_eq_empty.mpr hr]

@[target] lemma ball_subset_trichotomy :
    ball x r ⊆ ball y s ∨ ball y s ⊆ ball x r ∨ Disjoint (ball x r) (ball y s) := by sorry


@[target] lemma ball_eq_or_disjoint :
    ball x r = ball y r ∨ Disjoint (ball x r) (ball y r) := by sorry


lemma closedBall_eq_of_mem {x y: X} {r : ℝ} (h : y ∈ closedBall x r) :
    closedBall x r = closedBall y r := by
  ext
  simp_rw [mem_closedBall] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans (max_le h' (dist_comm x _ ▸ h))

@[target] lemma mem_closedBall_iff {x y: X} {r : ℝ} :
    y ∈ closedBall x r ↔ x ∈ closedBall y r := by sorry


lemma closedBall_subset_trichotomy :
    closedBall x r ⊆ closedBall y s ∨ closedBall y s ⊆ closedBall x r ∨
    Disjoint (closedBall x r) (closedBall y s) := by
  wlog hrs : r ≤ s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := _ ⊆ _), or_assoc]
    exact this y x s r (lt_of_not_le hrs).le
  · refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y s) |>.symm.imp
      (fun h ↦ ?_) (Or.inr ·)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff _ _ _).mp h.some_mem
    have hx := closedBall_subset_closedBall hrs (x := x)
    rwa [closedBall_eq_of_mem hyz |>.trans (closedBall_eq_of_mem <| hx hxz).symm]

@[target] lemma isClosed_ball (x : X) (r : ℝ) : IsClosed (ball x r) := by sorry


@[target] lemma isClopen_ball : IsClopen (ball x r) := by sorry


@[target] lemma frontier_ball_eq_empty : frontier (ball x r) = ∅ := by sorry


@[target] lemma closedBall_eq_or_disjoint :
    closedBall x r = closedBall y r ∨ Disjoint (closedBall x r) (closedBall y r) := by sorry


@[target] lemma isOpen_closedBall {r : ℝ} (hr : r ≠ 0) : IsOpen (closedBall x r) := by sorry


@[target] lemma isClopen_closedBall {r : ℝ} (hr : r ≠ 0) : IsClopen (closedBall x r) := by sorry


lemma frontier_closedBall_eq_empty {r : ℝ} (hr : r ≠ 0) : frontier (closedBall x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_closedBall x hr)

@[target] lemma isOpen_sphere {r : ℝ} (hr : r ≠ 0) : IsOpen (sphere x r) := by sorry


@[target] lemma isClopen_sphere {r : ℝ} (hr : r ≠ 0) : IsClopen (sphere x r) := by sorry


end IsUltrametricDist
