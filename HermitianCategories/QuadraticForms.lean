/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Linear.LinearFunctor

import HermitianCategories.Basic
import HermitianCategories.TateCohomology
import HermitianCategories.HermitianForms

/-! # The category of Λ-quadratic forms -/

open CategoryTheory
open Opposite

-- Objects live in universe u and morphisms in universe v; these need not coincide.
universe v u

-- Imports bring in declarations, but do not carry over another file's `variable` context.
-- In particular, Preadditive C must be available before we can assume Linear R C.
variable {C : Type u} [Category.{v} C] [HermitianCategory C] [Preadditive C]

-- We re-introduce our base ring R to use for our Linear enrichment and Lambda definitions.
variable (R : Type u) [CommRing R] [StarRing R]

-- We now assume our Hermitian category C is enriched over R-modules.
-- `Linear R C` provides the `Module R (X ⟶ Y)` typeclass instance automatically.
variable [Linear R C]
-- Additivity of D is a separate assumption: an arbitrary functor between
-- preadditive categories need not preserve sums of morphisms.
variable [Functor.Additive (HermitianCategory.duality (C := C))]

/-! ## Form parameters -/

set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false

def LambdaMin (M : C) (lam : Z1Mul R) : AddSubgroup (Sesq M) where
  carrier := { h | ∃ q : Sesq M, h = q - lam • (formDual q) }

  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    use 0
    have : formDual (0 : Sesq M) = 0 := by
      sorry
    sorry

  add_mem' := sorry

  neg_mem' := sorry

def LambdaMax (M : C) (lam : Z1Mul R) : AddSubgroup (Sesq M) where
  carrier := { h | h + lam • (formDual h) = 0 }

  zero_mem' := sorry

  add_mem' := sorry

  neg_mem' := sorry

lemma LambdaMinSubsLambdaMax [StarLinearDuality R C] (M : C) (lam : Z1Mul R) : LambdaMin R M lam ≤ LambdaMax R M lam := sorry
