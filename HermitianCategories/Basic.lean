/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Hermitian Categories

This file defines the core `HermitianCategory` typeclass, formalizing categories equipped
with a contravariant duality functor. It also defines sesquilinear forms and establishes
their abelian group structure in preadditive categories.
-/

open CategoryTheory
open Opposite

universe v u

class HermitianCategory (C : Type u) [Category.{v} C] where
  /-- The contravariant duality functor (often denoted by * or D) -/
  duality : Cᵒᵖ ⥤ C

  /-- The natural isomorphism between the identity functor and the double dual -/
  doubleDualIso : 𝟭 C ≅ duality.rightOp ⋙ duality

  /-- The symmetric coherence condition: D(η_X) ∘ η_{D(X)} = id_{D(X)} -/
  coherence : ∀ (X : C),
    (doubleDualIso.hom.app (duality.obj (op X))) ≫
    (duality.map (doubleDualIso.hom.app X).op) = 𝟙 (duality.obj (op X))


variable {C : Type u} [Category.{v} C] [HermitianCategory C]

/--
A sesquilinear form on an object M is a morphism from M to D(M).
We use the `duality` functor from our `HermitianCategory` class.
--/
abbrev SesquilinearForm (M : C) : Type v :=
  M ⟶ HermitianCategory.duality.obj (op M)

/--
S(M) is introduced as an abbreviation for the type of sesquilinear forms on M.
--/
abbrev S (M : C) := SesquilinearForm M

-- To guarantee that S(M) is an abelian group, we require the category C
-- to be preadditive.
variable [Preadditive C]

/--
Because C is a preadditive category, every Hom-set in C is automatically
an abelian group. S(M) trivially inherits this structure.
--/
instance (M : C) : AddCommGroup (S M) :=
  inferInstance
