/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

import Mathlib.Tactic.Ring

/-!
# Rings with involution and their Tate cohomology groups

This file defines explicit cycle/boundary presentations in degrees zero and one
for the order-two action given by `star`. For the additive group of R:

* Z⁰ consists of fixed elements; B⁰ consists of traces y + star y.
* Z¹ consists of elements with x + star x = 0; B¹ consists of differences y - star y.

The multiplicative constructions use the abelian unit group Rˣ instead of R:
sums become products, differences become y * (star y)⁻¹, and zero becomes one.
Cycles are kernels and boundaries are ranges of the trace/norm and difference
homomorphisms. Membership lemmas recover the explicit predicates. Each construction
proves B ≤ Z, then forms the quotient Z/B. These are direct presentations; no comparison with
Mathlib's general Tate-cohomology functor is constructed here.

The two additive vanishing results use a generalized half-unit r with r + star r = 1.
The norm-one unit subgroup `Z1Mul` also supplies the parameters λ used in `HermitianForms`.
-/

set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false

-- Let R be a commutative ring equipped with an involution (star operation)
variable (R : Type u) [CommRing R] [StarRing R]

/-! ## Additive Tate cohomology groups -/

/-- The additive trace map associated with the involution. -/
def tateTraceHom : R →+ R where
  toFun x := x + star x
  map_zero' := by simp
  map_add' x y := by simp only [star_add]; ac_rfl

/-- The additive difference map associated with the involution. -/
def tateDifferenceHom : R →+ R where
  toFun x := x - star x
  map_zero' := by simp
  map_add' x y := by rw [star_add, sub_add_sub_comm]

@[simp] lemma tateTraceHom_apply (x : R) : tateTraceHom R x = x + star x := rfl
@[simp] lemma tateDifferenceHom_apply (x : R) : tateDifferenceHom R x = x - star x := rfl

/--
The degree-zero cycle condition: x is fixed by the involution.
-/
def isZeroCycleAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  x = star x

/-- Fixed elements are the kernel of the difference map. -/
def Z0Add : AddSubgroup R := (tateDifferenceHom R).ker

@[simp] lemma mem_Z0Add (x : R) : x ∈ Z0Add R ↔ isZeroCycleAdd x := by
  simp [Z0Add, isZeroCycleAdd, sub_eq_zero]

/--
The degree-zero boundary condition: x is the trace y + star y of some ring element y.
-/
def isZeroNormAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  ∃ y : R, x = y + star y

/-- Additive degree-zero boundaries are the range of the trace map. -/
def B0Add : AddSubgroup R := (tateTraceHom R).range

@[simp] lemma mem_B0Add (x : R) : x ∈ B0Add R ↔ isZeroNormAdd x := by
  simp [B0Add, AddMonoidHom.mem_range, isZeroNormAdd, eq_comm]

/--
B⁰(R) is an additive subgroup of Z⁰(R).
-/
lemma B0Add_le_Z0Add : B0Add R ≤ Z0Add R := by
  intro x hx
  rw [mem_B0Add] at hx
  rw [mem_Z0Add]
  rcases hx with ⟨y, rfl⟩

  -- Unfold the subgroup membership into the `isZeroCycleAdd` equation
  change y + star y = star (y + star y)

  rw [star_add, star_star, add_comm]

/--
Mathematically restrict B⁰(R) to be an AddSubgroup of Z⁰(R).
`addSubgroupOf` takes the preimage under the inclusion Z⁰(R) → R. The preceding
inclusion theorem ensures this represents all of B⁰(R), not just an intersection.
-/
def B0Add_in_Z0Add (R : Type u) [CommRing R] [StarRing R] : AddSubgroup (Z0Add R) :=
  (B0Add R).addSubgroupOf (Z0Add R)

/--
The additive Tate cohomology group in degree zero: fixed elements modulo traces.
The numerator `↥(Z0Add R)` is a subtype: a ring element paired with its cycle proof.
-/
abbrev TateCohomologyZeroAdd (R : Type u) [CommRing R] [StarRing R] : Type u :=
  ↥(Z0Add R) ⧸ B0Add_in_Z0Add R

-- The quotient inherits its additive group structure from Mathlib's quotient construction.
instance : AddCommGroup (TateCohomologyZeroAdd R) := inferInstance

/--
The degree-one cycle condition: x + star x = 0, equivalently star x = -x.
-/
def isOneCycleAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  x + star x = 0

/-- Additive degree-one cycles are the kernel of the trace map. -/
def Z1Add : AddSubgroup R := (tateTraceHom R).ker

@[simp] lemma mem_Z1Add (x : R) : x ∈ Z1Add R ↔ isOneCycleAdd x := by
  rfl

/--
The degree-one boundary condition: x is a difference y - star y.
-/
def isOneNormAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  ∃ y : R, x = y - star y

/-- Additive degree-one boundaries are the range of the difference map. -/
def B1Add : AddSubgroup R := (tateDifferenceHom R).range

@[simp] lemma mem_B1Add (x : R) : x ∈ B1Add R ↔ isOneNormAdd x := by
  simp [B1Add, AddMonoidHom.mem_range, isOneNormAdd, eq_comm]

/--
B¹(R) is an additive subgroup of Z¹(R).
-/
lemma B1Add_le_Z1Add : B1Add R ≤ Z1Add R := by
  intro x hx
  rw [mem_B1Add] at hx
  rw [mem_Z1Add]
  rcases hx with ⟨y, rfl⟩
  change (y - star y) + star (y - star y) = 0

  -- Push the star inside, canceling the double star on the second 'y'
  rw [star_sub, star_star]

  -- The goal is now `y - star y + (star y - y) = 0`, which is pure algebra!
  ring
  -- Alternative manual cancellation proof, kept for comparison with `ring`:
  -- intro x hx
  -- rcases hx with ⟨y, rfl⟩

  -- -- Unfold the membership of Z¹(R)
  -- change (y - star y) + star (y - star y) = 0

  -- -- Step-by-step collapse to zero
  -- calc (y - star y) + star (y - star y)
  --   _ = (y - star y) + (star y - star (star y)) := by rw [star_sub]
  --   _ = (y - star y) + (star y - y) := by rw [star_star]
  --   _ = (y - star y) + -(y - star y) := by rw [← neg_sub]
  --   _ = 0 := by rw [add_neg_cancel]

/--
Mathematically restrict B¹(R) to be an AddSubgroup of Z¹(R).
-/
def B1Add_in_Z1Add (R : Type u) [CommRing R] [StarRing R] : AddSubgroup (Z1Add R) :=
  (B1Add R).addSubgroupOf (Z1Add R)

/--
The additive Tate cohomology group in degree one: cycles modulo differences y - star y.
-/
abbrev TateCohomologyOneAdd (R : Type u) [CommRing R] [StarRing R] : Type u :=
  ↥(Z1Add R) ⧸ B1Add_in_Z1Add R

instance : AddCommGroup (TateCohomologyOneAdd R) := inferInstance

/-- A generalized half-unit has trace one; no division operation is required. -/
def isGeneralizedHalfUnit (R : Type u) [CommRing R] [StarRing R] (x : R) : Prop :=
  x + star x = 1

/-- A generalized half-unit makes every degree-zero cycle a trace.
`Subsingleton` expresses triviality here because this quotient group contains zero. -/
lemma TateCohomologyZeroAddVanishes
  (h : ∃ r : R, isGeneralizedHalfUnit R r) : Subsingleton (TateCohomologyZeroAdd R) := by
  -- Extract the generalized half unit
  rcases h with ⟨r, hr⟩

  -- Prove that every element is the zero element, i.e. every cycle is a norm.
  have h_zero : ∀ x : TateCohomologyZeroAdd R, x = 0 := by
    intro x

    -- Quotient induction reduces the proposition to a representative a in Z⁰(R).
    -- This does not choose a preferred representative or define a map out of the quotient.
    induction x using Quotient.inductionOn
    rename_i a

    -- To show that the class of 'a' is 0, we must show that 'a' is a coboundary.
    -- The Mathlib lemma for ⟦a⟧ = 0 is QuotientAddGroup.eq_zero_iff
    rw [QuotientAddGroup.eq_zero_iff]

    -- This brings us to the core mathematical goal, i.e. to show that a is a norm.
    -- Use the boundary membership lemma to expose a trace witness.
    change (a : R) ∈ B0Add R
    rw [mem_B0Add]
    change ∃ y : R, (a : R) = y + star y

    -- For a fixed element a, the trace of a*r is a*(r + star r) = a.
    use (a : R) * r

    -- Extract the proof that `a = a*` from the package `a`
    have ha : (a : R) = star (a : R) := (mem_Z0Add R a).mp a.property

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

/-- A generalized half-unit also makes every degree-one cycle a boundary.
The same witness a*r works, now using star a = -a and the difference map. -/
lemma TateCohomologyOneAddVanishes
  (h : ∃ r : R, isGeneralizedHalfUnit R r) : Subsingleton (TateCohomologyOneAdd R) := by
  -- Extract the generalized half unit
  rcases h with ⟨r, hr⟩

  -- Prove that every quotient class is zero by exhibiting a boundary witness for each cycle.
  have h_zero : ∀ x : TateCohomologyOneAdd R, x = 0 := by
    intro x

    -- Quotient induction reduces the goal to a representative a in Z¹(R).
    induction x using Quotient.inductionOn
    rename_i a

    -- To show that the class of 'a' is 0, we must show that 'a' is a coboundary.
    -- The Mathlib lemma for ⟦a⟧ = 0 is QuotientAddGroup.eq_zero_iff
    rw [QuotientAddGroup.eq_zero_iff]

    -- Use the boundary membership lemma to expose a difference witness.
    change (a : R) ∈ B1Add R
    rw [mem_B1Add]
    change ∃ y : R, (a : R) = y - star y

    -- For star a = -a, the difference a*r - star (a*r) equals a*(r + star r) = a.
    use (a : R) * r

    -- Recover the cycle equation through the membership API.
    have hcycle : (a : R) + star (a : R) = 0 := (mem_Z1Add R a).mp a.property
    have ha : star (a : R) = - (a : R) := by
      calc star (a : R)
        _ = star (a : R) + 0 := by rw [add_zero]
        _ = star (a : R) + ((a : R) + - (a : R)) := by rw [← add_neg_cancel (a : R)]
        _ = (star (a : R) + (a : R)) + - (a : R) := by rw [← add_assoc]
        _ = ((a : R) + star (a : R)) + - (a : R) := by rw [add_comm (star (a : R))]
        _ = 0 + - (a : R) := by rw [hcycle]
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

/-!
## Multiplicative Tate cohomology groups

All witnesses below belong to Rˣ, so their inverses are available even when R is not a field.
Commutativity of R makes Rˣ abelian; in particular the boundary subgroups are normal,
as required by the quotient group construction.
-/

/-- The multiplicative norm homomorphism on units. -/
def tateNormHom : Rˣ →* Rˣ where
  toFun x := x * star x
  map_one' := by simp
  map_mul' x y := by simp only [star_mul]; ac_rfl

/-- The multiplicative difference homomorphism on units. -/
def tateDifferenceMulHom : Rˣ →* Rˣ where
  toFun x := x * (star x)⁻¹
  map_one' := by simp
  map_mul' x y := by simp only [star_mul, mul_inv]; ac_rfl

@[simp] lemma tateNormHom_apply (x : Rˣ) : tateNormHom R x = x * star x := rfl
@[simp] lemma tateDifferenceMulHom_apply (x : Rˣ) :
    tateDifferenceMulHom R x = x * (star x)⁻¹ := rfl

/--
The degree-zero multiplicative cycle condition: a unit is fixed by star.
-/
def isZeroCycleMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  x = star x

/-- Fixed units are the kernel of the multiplicative difference map. -/
def Z0Mul : Subgroup Rˣ := (tateDifferenceMulHom R).ker

@[simp] lemma mem_Z0Mul (x : Rˣ) : x ∈ Z0Mul R ↔ isZeroCycleMul x := by
  simp [Z0Mul, isZeroCycleMul, mul_inv_eq_one]

/-- A multiplicative norm is a product y * star y with y a unit, not an arbitrary ring element. -/
def isZeroNormMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  ∃ y : Rˣ, x = y * star y

/-- Multiplicative degree-zero boundaries are the range of the norm map on units. -/
def B0Mul : Subgroup Rˣ := (tateNormHom R).range

@[simp] lemma mem_B0Mul (x : Rˣ) : x ∈ B0Mul R ↔ isZeroNormMul x := by
  simp [B0Mul, MonoidHom.mem_range, isZeroNormMul, eq_comm]

/-- Multiplicative norms are fixed by star, so they represent degree-zero boundaries. -/
lemma B0Mul_le_Z0Mul : B0Mul R ≤ Z0Mul R := by
  intro x hx
  rw [mem_B0Mul] at hx
  rw [mem_Z0Mul]
  rcases hx with ⟨y, rfl⟩
  change y * star y = star (y * star y)
  rw [star_mul, star_star]

/--
View the boundary subgroup as a subgroup of the cycle group, using `subgroupOf`.
The actual containment in the ambient unit group was proved in `B0Mul_le_Z0Mul`.
-/

def B0Mul_in_Z0Mul (R : Type u) [CommRing R] [StarRing R] : Subgroup (Z0Mul R) :=
  (B0Mul R).subgroupOf (Z0Mul R)

/--
The multiplicative Tate group in degree zero: fixed units modulo multiplicative norms.
-/

abbrev TateCohomologyZeroMul (R : Type u) [CommRing R] [StarRing R] : Type u :=
  Z0Mul R ⧸ B0Mul_in_Z0Mul R

instance : CommGroup (TateCohomologyZeroMul R) := inferInstance

/--
The degree-one multiplicative cycle condition: a unit has norm one.
--/
def isOneCycleMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  x * star x = 1

/-- Norm-one units form the kernel of the norm map and supply Hermitian parameters. -/
def Z1Mul : Subgroup Rˣ := (tateNormHom R).ker

@[simp] lemma mem_Z1Mul (x : Rˣ) : x ∈ Z1Mul R ↔ isOneCycleMul x := by
  rfl

/--
The degree-one multiplicative boundary condition: a unit has the form y * (star y)⁻¹.
-/

def isOneNormMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  ∃ y : Rˣ, x = y * (star y)⁻¹

/-- Multiplicative degree-one boundaries are the range of the difference map on units. -/
def B1Mul : Subgroup Rˣ := (tateDifferenceMulHom R).range

@[simp] lemma mem_B1Mul (x : Rˣ) : x ∈ B1Mul R ↔ isOneNormMul x := by
  simp [B1Mul, MonoidHom.mem_range, isOneNormMul, eq_comm]

/--
Here we establish that B¹(R) is a subgroup of Z¹(R).
-/

lemma B1Mul_le_Z1Mul : B1Mul R ≤ Z1Mul R := by
  intro x hx
  rw [mem_B1Mul] at hx
  rw [mem_Z1Mul]
  rcases hx with ⟨y, rfl⟩
  change y * (star y)⁻¹ * star (y * (star y)⁻¹) = 1
  rw [star_mul, star_inv, star_star]
  -- Commutativity lets us regroup into two unit/inverse pairs, each of which cancels.
  calc y * (star y)⁻¹ * (y⁻¹ * star y)
  _ = (y * y⁻¹) * (star y * (star y)⁻¹) := by ac_rfl
  _ = 1 := by simp

/--
Restrict B¹(R) to the cycle group, whose elements carry proofs of the norm-one condition.
-/

def B1Mul_in_Z1Mul (R : Type u) [CommRing R] [StarRing R] : Subgroup (Z1Mul R) :=
  (B1Mul R).subgroupOf (Z1Mul R)

/--
The multiplicative Tate group in degree one: norm-one units modulo y * (star y)⁻¹.
An element of this quotient is a class of cocycles, unlike an element of `Z1Mul R` itself.
-/

abbrev TateCohomologyOneMul (R : Type u) [CommRing R] [StarRing R] : Type u :=
  Z1Mul R ⧸ B1Mul_in_Z1Mul R

instance : CommGroup (TateCohomologyOneMul R) := inferInstance
