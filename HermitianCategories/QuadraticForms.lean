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

/-! ### The twisted adjoint and maximal and minimal form parameters

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

/-! ### Form parameters

A form parameter `Λ` for `λ`-quadratic forms selects, for each object `M : C`, an
additive subgroup `Λ M ≤ Sesq M` lying between `LambdaMin R M lam` and
`LambdaMax R M lam` and closed under pullbacks along morphisms and multiplication
by self-adjoint scalars. These form parameters form a bounded lattice under
pointwise inclusion, and collapse to a single element whenever `R` admits a
generalized half-unit (or equivalently, when `TateCohomologyZeroAdd R` vanishes). -/

variable (lam : Z1Mul R)

/-- A form parameter for `λ`-quadratic forms assigns to each object `M : C` an
additive subgroup `func M ≤ Sesq M` sandwiched between `LambdaMin` and `LambdaMax`,
and closed under pullback and multiplication by self-adjoint scalars. -/
@[ext]
structure FormParameter where
  /-- The underlying additive subgroup of sesquilinear forms on each object `M : C`. -/
  func : (M : C) → AddSubgroup (Sesq M)
  /-- Every minimal form parameter element belongs to `func M`. -/
  subLambdaMin : ∀ (M : C), LambdaMin R M lam ≤ func M
  /-- Every element of `func M` is a maximal form parameter element. -/
  supLambdaMax : ∀ (M : C), func M ≤ LambdaMax R M lam
  /-- Pullback stability: pulling back a form in `func M` along `f : N ⟶ M` stays in `func N`. -/
  pullback : ∀ {M N : C} {h : Sesq M},
    h ∈ func M → ∀ (f : N ⟶ M),
      f ≫ h ≫ HermitianCategory.duality.map f.op ∈ func N
  /-- Self-adjoint scalar stability: scaling a form in `func M` by `r` with `star r = r` stays in `func M`. -/
  smul : ∀ {M : C} {h : Sesq M},
    h ∈ func M → ∀ {r : R}, IsSelfAdjoint r → r • h ∈ func M

namespace FormParameter

/-- Coerce a `FormParameter` to its underlying family of additive subgroups `M ↦ Λ.func M`. -/
instance : CoeFun (FormParameter (C := C) R lam) (fun _ => (M : C) → AddSubgroup (Sesq M)) where
  coe Λ := Λ.func

/-- Pointwise inclusion `Λ₁ ≤ Λ₂` defined by `∀ M, Λ₁.func M ≤ Λ₂.func M`.
Antisymmetry reduces to pointwise subgroup equality via `FormParameter.ext`. -/
instance : PartialOrder (FormParameter (C := C) R lam) where
  le Λ₁ Λ₂ := ∀ M : C, Λ₁.func M ≤ Λ₂.func M
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁₂ h₂₃ M := (h₁₂ M).trans (h₂₃ M)
  le_antisymm _ _ h₁₂ h₂₁ := by
    -- Extensionality reduces equality of form parameters to equality of each subgroup `func M`.
    ext M x
    exact ⟨fun hx => h₁₂ M hx, fun hx => h₂₁ M hx⟩

/-- Characterize `Λ₁ ≤ Λ₂` as pointwise inclusion of the underlying subgroups. -/
lemma le_def {Λ₁ Λ₂ : FormParameter (C := C) R lam} :
    Λ₁ ≤ Λ₂ ↔ ∀ M : C, Λ₁.func M ≤ Λ₂.func M := Iff.rfl

/-- The minimal form parameter `Λ_min`, given pointwise by `LambdaMin R M lam`. -/
def minParam [StarLinearDuality R C] : FormParameter (C := C) R lam where
  func M := LambdaMin R M lam
  subLambdaMin _ := le_rfl
  supLambdaMax M := LambdaMinSubsLambdaMax R M lam
  pullback hh f := LambdaMin.pullback R hh f
  smul := fun hh _ hr => LambdaMin.smul R hh hr

/-- The maximal form parameter `Λ_max`, given pointwise by `LambdaMax R M lam`. -/
def maxParam [StarLinearDuality R C] : FormParameter (C := C) R lam where
  func M := LambdaMax R M lam
  subLambdaMin M := LambdaMinSubsLambdaMax R M lam
  supLambdaMax _ := le_rfl
  pullback hh f := LambdaMax.pullback R hh f
  smul := fun hh _ hr => LambdaMax.smul R hh hr

/-- `minParam` is the least element (`⊥`) among all form parameters. -/
instance [StarLinearDuality R C] : OrderBot (FormParameter (C := C) R lam) where
  bot := minParam R lam
  bot_le Λ M := Λ.subLambdaMin M

/-- `maxParam` is the greatest element (`⊤`) among all form parameters. -/
instance [StarLinearDuality R C] : OrderTop (FormParameter (C := C) R lam) where
  top := maxParam R lam
  le_top Λ M := Λ.supLambdaMax M

/-- Pointwise intersection `Λ₁ ⊓ Λ₂` of two form parameters.
All four axioms hold componentwise because membership in `A ⊓ B` is conjunction. -/
instance : Min (FormParameter (C := C) R lam) where
  min Λ₁ Λ₂ :=
    { func := fun M => Λ₁.func M ⊓ Λ₂.func M
      subLambdaMin := by
        -- `LambdaMin` lies in both `Λ₁.func M` and `Λ₂.func M`, hence in their intersection.
        intro M h hh
        exact ⟨Λ₁.subLambdaMin M hh, Λ₂.subLambdaMin M hh⟩
      supLambdaMax := by
        -- Membership in the intersection implies membership in `Λ₁.func M ≤ LambdaMax`.
        intro M h hh
        exact Λ₁.supLambdaMax M hh.1
      pullback := by
        -- Pullback preserves both components of the intersection.
        intro M N h hh f
        exact ⟨Λ₁.pullback hh.1 f, Λ₂.pullback hh.2 f⟩
      smul := by
        -- Self-adjoint scalar multiplication preserves both components of the intersection.
        intro M h hh r hr
        exact ⟨Λ₁.smul hh.1 hr, Λ₂.smul hh.2 hr⟩ }

/-- Pointwise sum (join) `Λ₁ ⊔ Λ₂` of two form parameters.
Closure under `LambdaMax`, pullbacks, and self-adjoint scalars follows by decomposing
an element of `Λ₁.func M ⊔ Λ₂.func M` as a sum `h₁ + h₂` and using additivity. -/
instance : Max (FormParameter (C := C) R lam) where
  max Λ₁ Λ₂ :=
    { func := fun M => Λ₁.func M ⊔ Λ₂.func M
      subLambdaMin := by
        -- Embed `h ∈ LambdaMin` as `h + 0 ∈ Λ₁.func M ⊔ Λ₂.func M`.
        intro M h hh
        exact AddSubgroup.mem_sup.mpr
          ⟨h, Λ₁.subLambdaMin M hh, 0, (Λ₂.func M).zero_mem, add_zero h⟩
      supLambdaMax := by
        -- Decompose `h = h₁ + h₂` and use that `LambdaMax` is closed under addition.
        intro M h hh
        rcases AddSubgroup.mem_sup.mp hh with ⟨h₁, hh₁, h₂, hh₂, rfl⟩
        exact (LambdaMax R M lam).add_mem
          (Λ₁.supLambdaMax M hh₁) (Λ₂.supLambdaMax M hh₂)
      pullback := by
        -- Decompose `h = h₁ + h₂` and distribute composition over addition.
        intro M N h hh f
        rcases AddSubgroup.mem_sup.mp hh with ⟨h₁, hh₁, h₂, hh₂, rfl⟩
        rw [Preadditive.add_comp, Preadditive.comp_add]
        exact AddSubgroup.mem_sup.mpr
          ⟨_, Λ₁.pullback hh₁ f, _, Λ₂.pullback hh₂ f, rfl⟩
      smul := by
        -- Decompose `h = h₁ + h₂` and distribute scalar multiplication over addition.
        intro M h hh r hr
        rcases AddSubgroup.mem_sup.mp hh with ⟨h₁, hh₁, h₂, hh₂, rfl⟩
        rw [smul_add]
        exact AddSubgroup.mem_sup.mpr
          ⟨_, Λ₁.smul hh₁ hr, _, Λ₂.smul hh₂ hr, rfl⟩ }

/-- Form parameters form a lattice under pointwise subgroup intersection and sum. -/
instance : Lattice (FormParameter (C := C) R lam) where
  inf := (· ⊓ ·)
  sup := (· ⊔ ·)
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ h₁ h₂ M := le_inf (h₁ M) (h₂ M)
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h₁ h₂ M := sup_le (h₁ M) (h₂ M)

/-- With `StarLinearDuality R C`, form parameters form a bounded lattice with `minParam` and `maxParam`. -/
instance [StarLinearDuality R C] : BoundedOrder (FormParameter (C := C) R lam) where
  __ := (inferInstance : OrderBot (FormParameter (C := C) R lam))
  __ := (inferInstance : OrderTop (FormParameter (C := C) R lam))

/-- When `R` has a generalized half-unit, every form parameter equals `Λ_min`.
Since `LambdaMin = LambdaMax` in this case, the sandwich `LambdaMin ≤ Λ M ≤ LambdaMax` forces equality. -/
lemma eq_min_of_halfUnit [StarLinearDuality R C]
    (hhalf : ∃ r : R, isGeneralizedHalfUnit R r) (Λ : FormParameter (C := C) R lam) :
    Λ = minParam R lam := by
  ext M h
  change (h ∈ Λ.func M) ↔ h ∈ LambdaMin R M lam
  constructor
  · -- Upper bound: `Λ.func M ≤ LambdaMax = LambdaMin`.
    intro hh
    rw [LambdaMin_eq_LambdaMax_of_halfUnit R M lam hhalf]
    exact Λ.supLambdaMax M hh
  · -- Lower bound: `LambdaMin ≤ Λ.func M` by definition of a form parameter.
    intro hh
    exact Λ.subLambdaMin M hh

/-- When `R` has a generalized half-unit, `FormParameter (C := C) R lam` is a subsingleton.
Any two form parameters both equal `minParam R lam`. -/
lemma subsingleton_of_halfUnit [StarLinearDuality R C]
    (hhalf : ∃ r : R, isGeneralizedHalfUnit R r) :
    Subsingleton (FormParameter (C := C) R lam) := by
  constructor
  intro Λ₁ Λ₂
  -- Rewrite both `Λ₁` and `Λ₂` to `minParam R lam`.
  exact (eq_min_of_halfUnit R lam hhalf Λ₁).trans
    (eq_min_of_halfUnit R lam hhalf Λ₂).symm

/-- Vanishing of `TateCohomologyZeroAdd R` makes the form parameter unique,
by extracting a generalized half-unit and applying `subsingleton_of_halfUnit`. -/
lemma subsingleton_of_tateCohomologyZeroAddVanishes [StarLinearDuality R C]
    (hzero : Subsingleton (TateCohomologyZeroAdd R)) :
    Subsingleton (FormParameter (C := C) R lam) :=
  subsingleton_of_halfUnit R lam (existsGeneralizedHalfUnit_of_tateCohomologyZeroAddVanishes R hzero)

end FormParameter
