/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Hermitian Categories

The constructions proceed from a category with duality to sesquilinear forms,
λ-Hermitian forms, and the category of nonsingular λ-Hermitian objects with isometries.
The parameters λ come from `Z1Mul R` in `TateCohomology`.

Composition is written in diagrammatic order: `f ≫ g` means first f, then g.
For `D : Cᵒᵖ ⥤ C`, the dual of an object M is `D.obj (op M)`, whereas the dual
of a morphism f is `D.map f.op`. Taking opposites reverses the arrows; D itself
is an ordinary covariant functor whose domain is the opposite category.

The assumptions are introduced in layers: duality defines forms and their adjoints;
preadditivity supplies addition; additivity of D makes adjoints additive; and
`StarLinearDuality` controls how adjoints interact with scalar multiplication.
-/

set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false

open CategoryTheory
open Opposite

-- Objects live in universe u and morphisms in universe v; these need not coincide.
universe v u

/-- A category with a duality functor, a double-dual identification, and coherence. -/
class HermitianCategory (C : Type u) [Category.{v} C] where
  /-- The contravariant duality functor (often denoted by * or D). -/
  duality : Cᵒᵖ ⥤ C

  /-- The double-dual identification. `rightOp` turns D into a functor C ⥤ Cᵒᵖ,
  so `duality.rightOp ⋙ duality` has both source and target C. -/
  doubleDualIso : 𝟭 C ≅ duality.rightOp ⋙ duality

  /-- The symmetric coherence condition: D(η_X) ∘ η_{D(X)} = id_{D(X)} -/
  coherence : ∀ (X : C),
    (doubleDualIso.hom.app (duality.obj (op X))) ≫
    (duality.map (doubleDualIso.hom.app X).op) = 𝟙 (duality.obj (op X))


/-! ## Sesquilinear forms -/
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
abbrev Sesq (M : C) := SesquilinearForm M

/-- A form is nonsingular when its associated morphism M ⟶ D(M) is an isomorphism.
This is a property of the form, distinct from invertibility of an isometry between forms. -/
abbrev isNonSingular {M : C} (f : Sesq M) : Prop :=
  IsIso f

-- To guarantee that S(M) is an abelian group, we require the category C
-- to be preadditive.
variable [Preadditive C]

/--
Because C is a preadditive category, every Hom-set in C is automatically
an abelian group. S(M) trivially inherits this structure.
--/

instance (M : C) : AddCommGroup (Sesq M) :=
  inferInstance

/-! ## Duality preserving functors -/

variable {C : Type u} [Category.{v} C] [HermitianCategory C]
variable {D : Type u} [Category.{v} D] [HermitianCategory D]

structure DualityPreservingFunctor (functor : C ⥤ D) where
  nat_iso : functor.op ⋙ (HermitianCategory.duality (C := D)) ≅ (HermitianCategory.duality (C := C) ⋙ functor)
  coherence : ∀ X : C,
    functor.map ((HermitianCategory.doubleDualIso (C := C)).hom.app X) =
    (HermitianCategory.doubleDualIso (C := D)).hom.app (functor.obj X) ≫
    (HermitianCategory.duality (C := D)).map (nat_iso.inv.app (op X)).op ≫
    nat_iso.hom.app (op ((HermitianCategory.duality (C := C)).obj (op X)))

def mapSesqForms {M : C} (F : C ⥤ D)
 (hf : DualityPreservingFunctor F) (h : Sesq M) : Sesq (F.obj M) :=
  (F.map h) ≫ (hf.nat_iso.inv.app (op M))
