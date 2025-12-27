import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
import Mathlib.Topology.Sheaves.PresheafOfFunctions
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheaf conditions for presheaves of (continuous) functions.

We show that
* `Top.Presheaf.toType_isSheaf`: not-necessarily-continuous functions into a type form a sheaf
* `Top.Presheaf.toTypes_isSheaf`: in fact, these may be dependent functions into a type family

For
* `Top.sheafToTop`: continuous functions into a topological space form a sheaf
please see `Topology/Sheaves/LocalPredicate.lean`, where we set up a general framework
for constructing sub(pre)sheaves of the sheaf of dependent functions.

## Future work
Obviously there's more to do:
* sections of a fiber bundle
* various classes of smooth and structure preserving functions
* functions into spaces with algebraic structure, which the sections inherit
-/


open CategoryTheory Limits TopologicalSpace Opens

universe u

noncomputable section

variable (X : TopCat.{u})

open TopCat

namespace TopCat.Presheaf

/-- We show that the presheaf of functions to a type `T`
(no continuity assumptions, just plain functions)
form a sheaf.

In fact, the proof is identical when we do this for dependent functions to a type family `T`,
so we do the more general case.
-/
@[target] theorem toTypes_isSheaf (T : X → Type u) : (presheafToTypes X T).IsSheaf := by sorry

/-- The presheaf of not-necessarily-continuous functions to
a target type `T` satisfies the sheaf condition.
-/
@[target] theorem toType_isSheaf (T : Type u) : (presheafToType X T).IsSheaf := by sorry


end TopCat.Presheaf

namespace TopCat

/-- The sheaf of not-necessarily-continuous functions on `X` with values in type family
`T : X → Type u`.
-/
def sheafToTypes (T : X → Type u) : Sheaf (Type u) X :=
  ⟨presheafToTypes X T, Presheaf.toTypes_isSheaf _ _⟩

/-- The sheaf of not-necessarily-continuous functions on `X` with values in a type `T`.
-/
def sheafToType (T : Type u) : Sheaf (Type u) X :=
  ⟨presheafToType X T, Presheaf.toType_isSheaf _ _⟩

end TopCat
