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
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.GroupTheory.QuotientGroup.Basic


/-! # Rings with Involution and their Tate cohomology groups -/

-- Let R be a commutative ring equipped with an involution (star operation)
variable (R : Type u) [CommRing R] [StarRing R]

/-! ## Additive Tate cohomology groups -/

/--
The additive subgroup Z⁰(R) of R, containing all x ∈ R such that x = x*
-/
def isZeroCycleAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  x = star x

def Z0Add : AddSubgroup R where
  carrier := { x | isZeroCycleAdd x }
  zero_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry

/--
The additive subgroup of boundaries B⁰(R) consisting of traces, i.e., elements y + y*.
-/
def isZeroNormAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  ∃ y : R, x = y + star y

def B0Add : AddSubgroup R where
  carrier := { x | isZeroNormAdd x }
  zero_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry

/--
B⁰(R) is an additive subgroup of Z⁰(R).
-/
lemma B0Add_le_Z0Add : B0Add R ≤ Z0Add R := by sorry

/--
Mathematically restrict B⁰(R) to be an AddSubgroup of Z⁰(R).
Note: For additive subgroups, the restriction method is `addSubgroupOf`.
-/
def B0Add_in_Z0Add (R : Type u) [CommRing R] [StarRing R] : AddSubgroup (Z0Add R) :=
  (B0Add R).addSubgroupOf (Z0Add R)

/--
The additive Tate cohomology group H⁰(C₂;R).
-/
abbrev TateCohomologyZeroAdd (R : Type u) [CommRing R] [StarRing R] : Type u :=
  ↥(Z0Add R) ⧸ B0Add_in_Z0Add R

instance : AddCommGroup (TateCohomologyZeroAdd R) := inferInstance


/--
The additive subgroup Z¹(R) of R, containing all x ∈ R such that x + x* = 0.
-/
def isOneCycleAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  x + star x = 0

def Z1Add : AddSubgroup R where
  carrier := { x | isOneCycleAdd x }
  zero_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry

/--
The additive subgroup of boundaries B¹(R) consisting of elements of the form y - y*.
-/
def isOneNormAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  ∃ y : R, x = y - star y

def B1Add : AddSubgroup R where
  carrier := { x | isOneNormAdd x }
  zero_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry

/--
B¹(R) is an additive subgroup of Z¹(R).
-/
lemma B1Add_le_Z1Add : B1Add R ≤ Z1Add R := by sorry

/--
Mathematically restrict B¹(R) to be an AddSubgroup of Z¹(R).
-/
def B1Add_in_Z1Add (R : Type u) [CommRing R] [StarRing R] : AddSubgroup (Z1Add R) :=
  (B1Add R).addSubgroupOf (Z1Add R)

/--
The additive Tate cohomology group H¹(C₂;R).
-/
abbrev TateCohomologyOneAdd (R : Type u) [CommRing R] [StarRing R] : Type u :=
  ↥(Z1Add R) ⧸ B1Add_in_Z1Add R

instance : AddCommGroup (TateCohomologyOneAdd R) := inferInstance

/-! ## Multiplicative Tate cohomology groups -/

/--
The subgroup Z⁰(R) of the units of R, containing all x ∈ Rˣ such that x = x*
and the corresponding subgroup of coboundaries B⁰(R) consisting of all products x * (star x), for x in R.
-/
def isZeroCycleMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  x = star x

def Z0Mul : Subgroup Rˣ where
  carrier := { x | isZeroCycleMul x }
  one_mem' := by simp [isZeroCycleMul]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, isZeroCycleMul] at *
    rw [star_mul, ← ha, ← hb, mul_comm]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, isZeroCycleMul] at *
    rw [star_inv, ← hx]

def isZeroNormMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  ∃ y : Rˣ, x = y * star y

def B0Mul : Subgroup Rˣ where
  carrier := { x | isZeroNormMul x }
  one_mem' := by
    rw [Set.mem_ofPred_eq]
    use 1
    rw [star_one, mul_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rcases ha with ⟨ya, hya⟩
    rcases hb with ⟨yb, hyb⟩
    use ya * yb
    rw [hya, hyb, star_mul]
    ac_rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at *
    rcases hx with ⟨z, hz⟩
    use z⁻¹
    rw [hz, mul_inv, star_inv]

lemma B0Mul_le_Z0Mul : B0Mul R ≤ Z0Mul R := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  change y * star y = star (y * star y)
  rw [star_mul, star_star]

/--
Here we establish that B⁰(R) is a subgroup of Z⁰(R).
-/

def B0Mul_in_Z0Mul (R : Type u) [CommRing R] [StarRing R] : Subgroup (Z0Mul R) :=
  (B0Mul R).subgroupOf (Z0Mul R)

/--
The Tate cohomology group H⁰(C₂;Rˣ) of the multiplicative group.
-/

abbrev TateCohomologyZeroMul (R : Type u) [CommRing R] [StarRing R] : Type u :=
  Z0Mul R ⧸ B0Mul_in_Z0Mul R

instance : CommGroup (TateCohomologyZeroMul R) := inferInstance

/--
The subgroup Z¹(R) of the units of R, containing all x ∈ Rˣ such that x * x* = 1.
--/
def isOneCycleMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  x * star x = 1

def Z1Mul : Subgroup Rˣ where
  carrier := { x | isOneCycleMul x }
  one_mem' := by simp [isOneCycleMul]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, isOneCycleMul] at *
    rw [star_mul]
    calc a * b * (star b * star a)
    _ = (a * star a) * (b * star b) := by ac_rfl
    _ = 1 * 1 := by rw [ha, hb]
    _ = 1 := by rw [mul_one]

  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, isOneCycleMul] at *
    rw [star_inv, ← mul_inv, hx, inv_one]

/--
The subgroup of boundaries B¹(R) consisting of 1-norms, i.e. elements of the form x / x*.
-/

def isOneNormMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  ∃ y : Rˣ, x = y * (star y)⁻¹

def B1Mul : Subgroup Rˣ where
  carrier := { x | isOneNormMul x}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, isOneNormMul]
    use 1
    rw [star_one, inv_one, mul_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, isOneNormMul] at *
    rcases ha with ⟨ya, rfl⟩
    rcases hb with ⟨yb, rfl⟩
    use ya * yb
    rw [star_mul, mul_inv]
    ac_rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, isOneNormMul] at *
    rcases hx with ⟨y, rfl⟩
    use y⁻¹
    rw [mul_inv, inv_inv, star_inv, inv_inv]

/--
Here we establish that B¹(R) is a subgroup of Z¹(R).
-/

lemma B1Mul_le_Z1Mul : B1Mul R ≤ Z1Mul R := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  change y * (star y)⁻¹ * star (y * (star y)⁻¹) = 1
  rw [star_mul, star_inv, star_star]
  calc y * (star y)⁻¹ * (y⁻¹ * star y)
  _ = (y * y⁻¹) * (star y * (star y)⁻¹) := by ac_rfl
  _ = 1 := by simp

/--
B¹(R) is a subgroup of Z¹(R).
-/

def B1Mul_in_Z1Mul (R : Type u) [CommRing R] [StarRing R] : Subgroup (Z1Mul R) :=
  (B1Mul R).subgroupOf (Z1Mul R)

/--
Define the Tate cohomology group H¹(C₂;Rˣ) of the unit group Rˣ.
-/

abbrev TateCohomologyOneMul (R : Type u) [CommRing R] [StarRing R] : Type u :=
  Z1Mul R ⧸ B1Mul_in_Z1Mul R

instance : CommGroup (TateCohomologyOneMul R) := inferInstance

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

-- We now assume our Hermitian category C is enriched over R-modules.
-- `Linear R C` provides the `Module R (X ⟶ Y)` typeclass instance automatically.
variable {C : Type u} [Category.{v} C] [HermitianCategory C]
variable [Preadditive C] [Linear R C]
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
    -- Requires Functor.Additive to know D(0) = 0
    simp [IsLambdaHermitian, formDual]
  add_mem' := by
    intro f g hf hg
    -- Requires Functor.Additive to know D(f + g) = D(f) + D(g)
    simp only [IsLambdaHermitian, formDual] at *
    sorry -- Follows from linearity of composition and additivity of D
  neg_mem' := sorry
