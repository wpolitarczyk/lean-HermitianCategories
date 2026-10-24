/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.Algebra.Module.Hom
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

/-! ### The twisted adjoint and its form parameters

The endomorphism is explicit because different values of λ give different
involutions on the same additive group of sesquilinear forms. Defining its kernel
and range requires only additivity; containment uses conjugate-linearity.
-/

/-- The additive twisted adjoint q ↦ λ • q†. -/
def twistedFormDualHom (M : C) (lam : Z1Mul R) : Sesq M →+ Sesq M :=
  ((lam : Rˣ) : R) • formDualHom M

@[simp]
lemma twistedFormDualHom_apply (M : C) (lam : Z1Mul R) (q : Sesq M) :
    twistedFormDualHom R M lam q = ((lam : Rˣ) : R) • formDual q := rfl

/-- The norm-one condition on λ makes the conjugate-linear twisted adjoint involutive. -/
lemma twistedFormDualHom_involutive [StarLinearDuality R C]
    (M : C) (lam : Z1Mul R) : Function.Involutive (twistedFormDualHom R M lam) := by
  intro q
  have hunit : (lam : Rˣ) * star (lam : Rˣ) = 1 :=
    (mem_Z1Mul R (lam : Rˣ)).mp lam.property
  have hscalar : ((lam : Rˣ) : R) * star ((lam : Rˣ) : R) = 1 := by
    exact congrArg (fun x : Rˣ => (x : R)) hunit
  simp only [twistedFormDualHom_apply, formDual_smul, formDoubleDual, smul_smul,
    hscalar, one_smul]

/-- Minimal form parameters: the range of q ↦ q - λ • q†. -/
def LambdaMin (M : C) (lam : Z1Mul R) : AddSubgroup (Sesq M) :=
  AdditiveTate.B1 (twistedFormDualHom R M lam)

@[simp]
lemma mem_LambdaMin (M : C) (lam : Z1Mul R) (h : Sesq M) :
    h ∈ LambdaMin R M lam ↔ ∃ q : Sesq M, h = q - ((lam : Rˣ) : R) • formDual q :=
  AdditiveTate.mem_B1 (twistedFormDualHom R M lam) h

/-- Maximal form parameters: the kernel of h ↦ h + λ • h†. -/
def LambdaMax (M : C) (lam : Z1Mul R) : AddSubgroup (Sesq M) :=
  AdditiveTate.Z1 (twistedFormDualHom R M lam)

@[simp]
lemma mem_LambdaMax (M : C) (lam : Z1Mul R) (h : Sesq M) :
    h ∈ LambdaMax R M lam ↔ h + ((lam : Rˣ) : R) • formDual h = 0 :=
  AdditiveTate.mem_Z1 (twistedFormDualHom R M lam) h

/-- Every minimal form parameter is maximal, by the additive boundary-cycle inclusion. -/
lemma LambdaMinSubsLambdaMax [StarLinearDuality R C]
    (M : C) (lam : Z1Mul R) : LambdaMin R M lam ≤ LambdaMax R M lam :=
  AdditiveTate.B1_le_Z1 (twistedFormDualHom R M lam)
    (twistedFormDualHom_involutive R M lam)

/-- Multiplication by a self-adjoint scalar preserves minimal form parameters.
Scale the difference witness by the same scalar. -/
lemma LambdaMin.smul [StarLinearDuality R C] {M : C} {lam : Z1Mul R}
    {h : Sesq M} (hh : h ∈ LambdaMin R M lam) {r : R} (hr : IsSelfAdjoint r) :
    r • h ∈ LambdaMin R M lam := by
  rw [mem_LambdaMin] at hh ⊢
  obtain ⟨q, rfl⟩ := hh
  refine ⟨r • q, ?_⟩
  rw [smul_sub, formDual_smul, hr, smul_comm r ((lam : Rˣ) : R)]

/-- Multiplication by a self-adjoint scalar preserves maximal form parameters.
The trace of the scaled form is the scalar multiple of its original trace. -/
lemma LambdaMax.smul [StarLinearDuality R C] {M : C} {lam : Z1Mul R}
    {h : Sesq M} (hh : h ∈ LambdaMax R M lam) {r : R} (hr : IsSelfAdjoint r) :
    r • h ∈ LambdaMax R M lam := by
  rw [mem_LambdaMax] at hh ⊢
  rw [formDual_smul, hr, smul_comm ((lam : Rˣ) : R) r, ← smul_add, hh, smul_zero]

/-- Pullback along any morphism preserves minimal form parameters.
The pullback of a difference is the difference of the pulled-back witness. -/
lemma LambdaMin.pullback {M N : C} {lam : Z1Mul R} {h : Sesq M}
    (hh : h ∈ LambdaMin R M lam) (f : N ⟶ M) :
    f ≫ h ≫ HermitianCategory.duality.map f.op ∈ LambdaMin R N lam := by
  rw [mem_LambdaMin] at hh ⊢
  obtain ⟨q, rfl⟩ := hh
  refine ⟨f ≫ q ≫ HermitianCategory.duality.map f.op, ?_⟩
  simp only [formDual_pullback, Preadditive.comp_sub, Preadditive.sub_comp,
    Linear.comp_smul, Linear.smul_comp]

/-- Pullback along any morphism preserves maximal form parameters.
The trace of the pullback is the pullback of the original trace. -/
lemma LambdaMax.pullback {M N : C} {lam : Z1Mul R} {h : Sesq M}
    (hh : h ∈ LambdaMax R M lam) (f : N ⟶ M) :
    f ≫ h ≫ HermitianCategory.duality.map f.op ∈ LambdaMax R N lam := by
  rw [mem_LambdaMax] at hh ⊢
  calc
    (f ≫ h ≫ HermitianCategory.duality.map f.op) +
        ((lam : Rˣ) : R) • formDual (f ≫ h ≫ HermitianCategory.duality.map f.op) =
        f ≫ (h + ((lam : Rˣ) : R) • formDual h) ≫
          HermitianCategory.duality.map f.op := by
      simp only [formDual_pullback, Preadditive.comp_add, Preadditive.add_comp,
        Linear.comp_smul, Linear.smul_comp]
    _ = 0 := by rw [hh]; simp

/-- A generalized half-unit makes the minimal and maximal form parameters equal.
For a maximal form h, multiplying h by a half-unit gives a difference witness. -/
lemma LambdaMin_eq_LambdaMax_of_halfUnit [StarLinearDuality R C]
    (M : C) (lam : Z1Mul R) (hhalf : ∃ r : R, isGeneralizedHalfUnit R r) :
    LambdaMin R M lam = LambdaMax R M lam := by
  apply le_antisymm (LambdaMinSubsLambdaMax R M lam)
  intro h hh
  rw [mem_LambdaMax] at hh
  rw [mem_LambdaMin]
  obtain ⟨r, hr⟩ := hhalf
  have hdual : ((lam : Rˣ) : R) • formDual h = -h :=
    eq_neg_of_add_eq_zero_right hh
  refine ⟨r • h, ?_⟩
  symm
  rw [formDual_smul, smul_comm ((lam : Rˣ) : R) (star r), hdual,
    smul_neg, sub_neg_eq_add, ← add_smul, hr, one_smul]

/-- Vanishing of additive degree-zero Tate cohomology of R makes the two form
parameters equal for every object and every norm-one parameter. -/
lemma LambdaMin_eq_LambdaMax_of_tateCohomologyZeroAddVanishes [StarLinearDuality R C]
    (M : C) (lam : Z1Mul R) (hzero : Subsingleton (TateCohomologyZeroAdd R)) :
    LambdaMin R M lam = LambdaMax R M lam :=
  LambdaMin_eq_LambdaMax_of_halfUnit R M lam
    (existsGeneralizedHalfUnit_of_tateCohomologyZeroAddVanishes R hzero)
