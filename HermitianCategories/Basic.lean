/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Linear.Basic
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

/-! ## Rings with Involution and Z¹(R) -/

-- Let R be a commutative ring equipped with an involution (star operation)
variable (R : Type u) [CommRing R] [StarRing R]

/--
The subgroup Z¹(R) of the units of R, containing all x ∈ Rˣ such that x * x* = 1.
--/
def Z1 : Subgroup Rˣ where
  carrier := { x | (x : R) * star (x : R) = 1 }
  one_mem' := by simp
  mul_mem' := by
    -- For x, y ∈ Z¹(R), we have (xy)(xy)* = x y y* x* = x 1 x* = x x* = 1.
    -- Proof sketched via sorry for the setup stage.
    sorry
  inv_mem' := sorry

/-! ### λ-Hermitian Forms -/

-- We now assume our Hermitian category C is enriched over R-modules.
-- `Linear R C` provides the `Module R (X ⟶ Y)` typeclass instance automatically.
variable {C : Type u} [Category.{v} C] [HermitianCategory C] [Linear R C]

/--
The dual form f^† : M ⟶ D(M).
In diagrammatic order (f ≫ g), this applies η_M followed by D(f).
--/
def formDual {M : C} (f : S M) : S M :=
  (HermitianCategory.doubleDualIso.hom.app M) ≫ (HermitianCategory.duality.map f.op)

/--
A sesquilinear form f is λ-Hermitian if f = λ • f^†.
We use double coercion `((λ : Rˣ) : R)` to extract the element from the subgroup
and cast the unit into the underlying ring so it can act via scalar multiplication.
--/
def IsLambdaHermitian {M : C} (λ : Z1 R) (f : S M) : Prop :=
  f = ((λ : Rˣ) : R) • formDual f

/--
The collection of λ-Hermitian forms on M.

*Mathematical Note:* This is defined as an `AddSubgroup` (an abelian group) rather
than an `R`-submodule. In a Hermitian category with a non-trivial involution, scalar
multiplication generally does not preserve λ-Hermiticity: if f is λ-Hermitian,
r • f is only λ-Hermitian if r = r*.
--/
def LambdaHermitianForms (M : C) (λ : Z1 R) : AddSubgroup (S M) where
  carrier := { f | IsLambdaHermitian R λ f }
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry
