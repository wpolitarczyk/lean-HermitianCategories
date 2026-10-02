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
  zero_mem' := by simp [isZeroCycleAdd]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, isZeroCycleAdd] at *
    rw [star_add, ← ha, ← hb]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, isZeroCycleAdd] at *
    rw [star_neg, ← hx]

/--
The additive subgroup of boundaries B⁰(R) consisting of traces, i.e., elements y + y*.
-/
def isZeroNormAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  ∃ y : R, x = y + star y

def B0Add : AddSubgroup R where
  carrier := { x | isZeroNormAdd x }
  zero_mem' := by
    simp only [isZeroNormAdd]
    use 0
    rw [star_zero, add_zero]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, isZeroNormAdd] at *
    rcases ha with ⟨ya, rfl⟩
    rcases hb with ⟨yb, rfl⟩
    use (ya + yb)
    rw [star_add]
    ac_rfl
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, isZeroNormAdd] at *
    rcases hx with ⟨y, rfl⟩
    use -y
    rw [star_neg, neg_add]

/--
B⁰(R) is an additive subgroup of Z⁰(R).
-/
lemma B0Add_le_Z0Add : B0Add R ≤ Z0Add R := by
  intro x hx
  rcases hx with ⟨y, rfl⟩

  -- Unfold the subgroup membership into the `isZeroCycleAdd` equation
  change y + star y = star (y + star y)

  rw [star_add, star_star, add_comm]

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
  zero_mem' := by
    simp [isOneCycleAdd]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, isOneCycleAdd] at *
    rw [star_add]
    -- Group the terms to expose (a + star a) and (b + star b)
    calc a + b + (star a + star b)
      _ = (a + star a) + (b + star b) := by ac_rfl
      _ = 0 + 0 := by rw [ha, hb]
      _ = 0 := by rw [add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, isOneCycleAdd] at *
    rw [star_neg, ← neg_add, ha, neg_zero]

/--
The additive subgroup of boundaries B¹(R) consisting of elements of the form y - y*.
-/
def isOneNormAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  ∃ y : R, x = y - star y

def B1Add : AddSubgroup R where
  carrier := { x | isOneNormAdd x }
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, isOneNormAdd]
    -- 0 = 0 - 0*
    use 0
    rw [star_zero, sub_zero]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, isOneNormAdd] at *
    rcases ha with ⟨ya, rfl⟩
    rcases hb with ⟨yb, rfl⟩
    use ya + yb

    -- `sub_add_sub_comm` is the exact Mathlib lemma for (a - b) + (c - d) = (a + c) - (b + d)
    calc ya - star ya + (yb - star yb)
      _ = (ya + yb) - (star ya + star yb) := by rw [sub_add_sub_comm]
      _ = (ya + yb) - star (ya + yb) := by rw [← star_add]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, isOneNormAdd] at *
    rcases hx with ⟨y, rfl⟩
    use -y

    -- We can carefully step through the negative distribution
    calc -(y - star y)
      _ = star y - y := by rw [neg_sub]
      _ = star y + -y := by rw [sub_eq_add_neg]
      _ = -y + star y := by rw [add_comm]
      _ = -y - -star y := by rw [← sub_neg_eq_add]
      _ = -y - star (-y) := by rw [← star_neg]

/--
B¹(R) is an additive subgroup of Z¹(R).
-/
lemma B1Add_le_Z1Add : B1Add R ≤ Z1Add R := by
  intro x hx
  rcases hx with ⟨y, rfl⟩

  -- Unfold the membership of Z¹(R)
  change (y - star y) + star (y - star y) = 0

  -- Step-by-step collapse to zero
  calc (y - star y) + star (y - star y)
    _ = (y - star y) + (star y - star (star y)) := by rw [star_sub]
    _ = (y - star y) + (star y - y) := by rw [star_star]
    _ = (y - star y) + -(y - star y) := by rw [← neg_sub]
    _ = 0 := by rw [add_neg_cancel]

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

def isGeneralizedHalfUnit (R : Type u) [CommRing R] [StarRing R] (x : R) : Prop :=
  x + star x = 1

lemma TateCohomologyZeroAddVanishes
  (h : ∃ r : R, isGeneralizedHalfUnit R r) : Subsingleton (TateCohomologyZeroAdd R) := by
  -- Extract the generalized half unit
  rcases h with ⟨r, hr⟩

  -- Prove that every element is the zero element, i.e. every cycle is a norm.
  have h_zero : ∀ x : TateCohomologyZeroAdd R, x = 0 := by
    intro x

    -- Because x is in a quotient, we can lift it to a representative element 'a' in Z⁰(R)
    induction x using Quotient.inductionOn
    rename_i a

    -- To show that the class of 'a' is 0, we must show that 'a' is a coboundary.
    -- The Mathlib lemma for ⟦a⟧ = 0 is QuotientAddGroup.eq_zero_iff
    rw [QuotientAddGroup.eq_zero_iff]

    -- This brings us to the core mathematical goal, i.e. to show that a is a norm.
    -- Tell Lean to treat `a` as a raw ring element and unfold the B0Add definition.
    change ∃ y : R, (a : R) = y + star y

    -- Now provide the witness!
    use (a : R) * r

    -- Extract the proof that `a = a*` from the package `a`
    have ha : (a : R) = star (a : R) := a.property

    calc (a : R)
    _ = (a : R) * (1 : R) := by rw [mul_one]
    _ = (a : R) * (r + star r) := by rw [hr]
    _ = ((a : R) * r) + ((a : R) * star r) := by rw [mul_add]
    _ = ((a : R) * r) + (star (a : R) * star r) := by rw [← ha]
    _ = ((a : R) * r) + star (r * (a : R)) := by rw [← star_mul]
    _ = ((a : R) * r) + star ((a : R) * r) := by rw [mul_comm]

  -- Now that we know every element is 0, Subsingleton is trivial
  constructor
  intro a b
  rw [h_zero a, h_zero b]

lemma TateCohomologyOneAddVanishes
  (h : ∃ r : R, isGeneralizedHalfUnit R r) : Subsingleton (TateCohomologyOneAdd R) := by
  -- Extract the generalized half unit
  rcases h with ⟨r, hr⟩

  -- Prove that every element is the zero element, i.e. every cycle is a norm.
  have h_zero : ∀ x : TateCohomologyOneAdd R, x = 0 := by
    intro x

    -- Because x is in a quotient, we can lift it to a representative element 'a' in Z⁰(R)
    induction x using Quotient.inductionOn
    rename_i a

    -- To show that the class of 'a' is 0, we must show that 'a' is a coboundary.
    -- The Mathlib lemma for ⟦a⟧ = 0 is QuotientAddGroup.eq_zero_iff
    rw [QuotientAddGroup.eq_zero_iff]

    -- This brings us to the core mathematical goal, i.e. to show that a is a norm.
    -- Tell Lean to treat `a` as a raw ring element and unfold the B0Add definition.
    change ∃ y : R, (a : R) = y - star y

    -- Now provide the witness!
    use (a : R) * r

    -- Extract the proof that `star a = -a` using a robust calc block
    have ha : star (a : R) = - (a : R) := by
      calc star (a : R)
        _ = star (a : R) + 0 := by rw [add_zero]
        _ = star (a : R) + ((a : R) + - (a : R)) := by rw [← add_neg_cancel (a : R)]
        _ = (star (a : R) + (a : R)) + - (a : R) := by rw [← add_assoc]
        _ = ((a : R) + star (a : R)) + - (a : R) := by rw [add_comm (star (a : R))]
        _ = 0 + - (a : R) := by rw [a.property]
        _ = - (a : R) := by rw [zero_add]

    -- Our goal right now is: (a : R) = (a : R) * r - star ((a : R) * r)
    -- It is much easier to start with the messy witness and simplify it down to `a`.
    -- `symm` flips the goal so the messy side is on the left!
    symm

    -- Now we just simplify the witness down to `a` step-by-step
    calc (a : R) * r - star ((a : R) * r)
      _ = (a : R) * r - star r * star (a : R) := by rw [star_mul]
      _ = (a : R) * r - star (a : R) * star r := by rw [mul_comm (star r)]
      _ = (a : R) * r - (-(a : R)) * star r := by rw [ha]
      _ = (a : R) * r - -( (a : R) * star r ) := by rw [neg_mul]
      _ = (a : R) * r + (a : R) * star r := by rw [sub_neg_eq_add]
      _ = (a : R) * (r + star r) := by rw [← mul_add]
      _ = (a : R) * 1 := by rw [hr]
      _ = (a : R) := by rw [mul_one]

  -- Now that we know every element is 0, Subsingleton is trivial
  constructor
  intro a b
  rw [h_zero a, h_zero b]

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
