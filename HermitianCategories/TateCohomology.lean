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
Each construction first packages cycles and boundaries as subgroups, proves B ≤ Z,
then forms the quotient Z/B. These are direct presentations; no comparison with
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

/--
The degree-zero cycle condition: x is fixed by the involution.
-/
def isZeroCycleAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  x = star x

/-- Fixed elements form an additive subgroup; the fields below prove closure. -/
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
The degree-zero boundary condition: x is the trace y + star y of some ring element y.
-/
def isZeroNormAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  ∃ y : R, x = y + star y

/-- The trace subgroup. Closure is proved by adding or negating the trace witnesses. -/
def B0Add : AddSubgroup R where
  carrier := { x | isZeroNormAdd x }
  zero_mem' := by
    simp only [isZeroNormAdd]
    use 0
    rw [star_zero, add_zero]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, isZeroNormAdd] at *
    -- Extract the trace witnesses and substitute their expressions for a and b.
    rcases ha with ⟨ya, rfl⟩
    rcases hb with ⟨yb, rfl⟩
    use (ya + yb)
    rw [star_add]
    -- `ac_rfl` rearranges terms using associativity and commutativity.
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

/-- The kernel of the additive trace map: elements with x + star x = 0. -/
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
The degree-one boundary condition: x is a difference y - star y.
-/
def isOneNormAdd {R : Type u} [CommRing R] [StarRing R] (x : R) : Prop :=
  ∃ y : R, x = y - star y

/-- The image of the difference map y ↦ y - star y, as an additive subgroup. -/
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
    -- Tell Lean to treat `a` as a raw ring element and unfold the B0Add definition.
    change ∃ y : R, (a : R) = y + star y

    -- For a fixed element a, the trace of a*r is a*(r + star r) = a.
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

    -- Unfold the B1Add membership condition, viewing the cycle a as a ring element.
    change ∃ y : R, (a : R) = y - star y

    -- For star a = -a, the difference a*r - star (a*r) equals a*(r + star r) = a.
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

/-!
## Multiplicative Tate cohomology groups

All witnesses below belong to Rˣ, so their inverses are available even when R is not a field.
Commutativity of R makes Rˣ abelian; in particular the boundary subgroups are normal,
as required by the quotient group construction.
-/

/--
The degree-zero multiplicative cycle condition: a unit is fixed by star.
-/
def isZeroCycleMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  x = star x

/-- The subgroup of units fixed by the involution. -/
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

/-- A multiplicative norm is a product y * star y with y a unit, not an arbitrary ring element. -/
def isZeroNormMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  ∃ y : Rˣ, x = y * star y

/-- The image of the norm map on units y ↦ y * star y. -/
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

/-- Multiplicative norms are fixed by star, so they represent degree-zero boundaries. -/
lemma B0Mul_le_Z0Mul : B0Mul R ≤ Z0Mul R := by
  intro x hx
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

/-- Norm-one units. `HermitianForms` uses elements of this subgroup as λ-Hermitian parameters. -/
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
The degree-one multiplicative boundary condition: a unit has the form y * (star y)⁻¹.
-/

def isOneNormMul {R : Type u} [CommRing R] [StarRing R] (x : Rˣ) : Prop :=
  ∃ y : Rˣ, x = y * (star y)⁻¹

/-- Multiplicative degree-one boundaries, with witnesses in the unit group. -/
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
