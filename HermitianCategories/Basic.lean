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

import HermitianCategories.TateCohomology

set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false

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

/-! ## λ-Hermitian Forms -/

-- We re-introduce our base ring R to use for our Linear enrichment and Lambda definitions.
variable (R : Type u) [CommRing R] [StarRing R]

-- We now assume our Hermitian category C is enriched over R-modules.
-- `Linear R C` provides the `Module R (X ⟶ Y)` typeclass instance automatically.
variable [Linear R C]
variable [Functor.Additive (HermitianCategory.duality (C := C))]

/--
The dual form f^† : M ⟶ D(M).
In diagrammatic order (f ≫ g), this applies η_M followed by D(f).
--/
def formDual {M : C} (f : S M) : S M :=
  (HermitianCategory.doubleDualIso.hom.app M) ≫ (HermitianCategory.duality.map f.op)

/--
A sesquilinear form f is λ-Hermitian if f = λ • f^†.
We use double coercion `((lam : Rˣ) : R)` to extract the element from the subgroup
and cast the unit into the underlying ring so it can act via scalar multiplication.
--/
def IsLambdaHermitian {M : C} (lam : Z1Mul R) (f : S M) : Prop :=
  f = ((lam : Rˣ) : R) • formDual f

/--
The collection of λ-Hermitian forms on M.
--/
def LambdaHermitianForms (M : C) (lam : Z1Mul R) : AddSubgroup (S M) where
  carrier := { f | IsLambdaHermitian R lam f }
  zero_mem' := by
    simp only [IsLambdaHermitian, Set.mem_ofPred_eq]
    -- We want to prove 0 = λ • formDual 0.
    -- Lean's `simp` automatically knows that additive functors map 0 to 0,
    -- composition with 0 is 0, and scalar multiplying 0 is 0!
    simp [formDual]
  add_mem' := by
    intro f g hf hg
    simp only [IsLambdaHermitian, Set.mem_ofPred_eq] at *
    -- Build the equality chain step-by-step
    calc f + g
      -- 1. Replace f and g ONLY on the left side of this step
      _ = ((lam : Rˣ) : R) • formDual f + ((lam : Rˣ) : R) • formDual g := by
        conv_lhs => rw [hf, hg]
      -- 2. Factor out the scalar lambda
      _ = ((lam : Rˣ) : R) • (formDual f + formDual g) := by rw [← smul_add]
      -- 3. Show that formDual distributes over addition
      _ = ((lam : Rˣ) : R) • formDual (f + g) := by
        -- `congr 1` strips away `lam •`, leaving `formDual f + formDual g = formDual (f + g)`
        congr 1
        -- Lean's simplifier automatically knows functors and composition are additive!
        simp [formDual]
  neg_mem' := by
    intro f hf
    simp only [IsLambdaHermitian, Set.mem_ofPred_eq] at *
    calc -f
      -- 1. Replace f ONLY on the left side
      _ = - (((lam : Rˣ) : R) • formDual f) := by
        conv_lhs => rw [hf]
      -- 2. Factor the negative sign inside the scalar multiplication
      _ = ((lam : Rˣ) : R) • -(formDual f) := by rw [← smul_neg]
      -- 3. Show that formDual preserves negatives
      _ = ((lam : Rˣ) : R) • formDual (-f) := by
        congr 1
        simp [formDual]
