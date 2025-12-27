import VerifiedAgora.tagger
/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Presheaves on `PUnit`

Presheaves on `PUnit` satisfy sheaf condition iff its value at empty set is a terminal object.
-/


namespace TopCat.Presheaf

universe u v w

open CategoryTheory CategoryTheory.Limits TopCat Opposite

variable {C : Type u} [Category.{v} C]

@[target] theorem isSheaf_of_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (F : Presheaf C X)
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf := by sorry


@[target] theorem isSheaf_iff_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤)
    (F : Presheaf C X) : F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥) := by sorry


@[target] theorem isSheaf_on_punit_of_isTerminal (F : Presheaf C (TopCat.of PUnit))
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf := by sorry


theorem isSheaf_on_punit_iff_isTerminal (F : Presheaf C (TopCat.of PUnit)) :
    F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ => isSheaf_on_punit_of_isTerminal F it⟩

end TopCat.Presheaf
