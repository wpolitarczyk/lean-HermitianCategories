/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite

import HermitianCategories.Basic
import HermitianCategories.TateCohomology

/-!
# The category of λ-Hermitian forms

Starting from the sesquilinear forms in `Basic`, this file defines the adjoint
operation, λ-Hermitian forms, and nonsingular objects with isometries as morphisms.
The parameter λ is a norm-one unit, represented by `Z1Mul R` from `TateCohomology`.

Preadditivity supplies addition of forms; `Linear R C` supplies scalar multiplication.
Additivity of the duality makes adjoints additive, while `StarLinearDuality` makes
them conjugate-linear. The involutivity proof uses naturality and coherence of
the double-dual isomorphism.

Every isometry has an inverse isometry, so the category of nonsingular
λ-Hermitian objects is equipped with a groupoid instance.

`HermitianFunctors` builds on this file to define compatible functors, transport,
induced equivalences, and scaling.
-/

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

/-! ## Adjoints and their additive structure -/

set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false

/--
A mixin typeclass asserting that the duality functor of a Hermitian category
is conjugate-linear (star-linear) with respect to the `StarRing R` action.
-/
class StarLinearDuality (R : Type*) [CommRing R] [StarRing R] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear R C] [HermitianCategory C] : Prop where
  /-- Dualizing a scalar multiple conjugates its scalar by the ring involution. -/
  map_smul : ∀ (r : R) {X Y : C} (f : X ⟶ Y),
    HermitianCategory.duality.map (r • f).op = star r • HermitianCategory.duality.map f.op

/--
The dual form f^† : M ⟶ D(M).
In diagrammatic order (f ≫ g), this applies η_M followed by D(f).
Here f.op : op (D(M)) ⟶ op M, so D(f.op) : D²(M) ⟶ D(M);
the double-dual map η_M supplies the missing arrow from M to D²(M).
-/
def formDual {M : C} (f : Sesq M) : Sesq M :=
  (HermitianCategory.doubleDualIso.hom.app M) ≫ (HermitianCategory.duality.map f.op)

/-- The adjoint of the zero form is zero. -/
@[simp]
lemma formDual_zero {M : C} : formDual (0 : Sesq M) = 0 := by
  -- Opposites and the additive duality preserve zero; composition with zero is zero.
  simp [formDual]

/-- Taking adjoints preserves addition of forms. -/
@[simp]
lemma formDual_add {M : C} (g h : Sesq M) : formDual (g+h) = formDual g + formDual h := by
  -- The duality maps sums to sums, and precomposition with η_M distributes over them.
  simp [formDual]

/-- Taking adjoints commutes with additive inverses. -/
@[simp]
lemma formDual_neg {M : C} (g : Sesq M) : formDual (-g) = -formDual g := by
  simp [formDual]

/-- Taking adjoints preserves differences of forms. -/
@[simp]
lemma formDual_sub {M : C} (g h : Sesq M) : formDual (g - h) = formDual g - formDual h := by
  simp [formDual]

/-- The adjoint operation bundled as an endomorphism of the abelian group `Sesq M`.
The notation `→+` bundles a function with preservation of zero and addition;
preservation of negation and subtraction is then available from `AddMonoidHom`.
This construction uses additivity of the duality, without scalar compatibility.
In general the adjoint is conjugate-linear, so this is not bundled as an R-linear map. -/
def formDualHom (M : C) : Sesq M →+ Sesq M where
  toFun := formDual

  map_zero' := formDual_zero

  map_add' := formDual_add

-- Scalar compatibility is a separate hypothesis from the additive facts above.
variable [StarLinearDuality R C]

omit [Functor.Additive (HermitianCategory.duality (C := C))] in
/-- The dual form map is conjugate-linear: (r • f)† = r* • f†. -/
@[simp]
lemma formDual_smul (r : R) {M : C} (f : Sesq M) :
    formDual (r • f) = star r • formDual f := by
  dsimp [formDual]
  rw [StarLinearDuality.map_smul]
  -- Re-associate scalar multiplication out of the categorical composition:
  -- η_M ≫ (star r • D(f.op)) = star r • (η_M ≫ D(f.op))
  apply CategoryTheory.Linear.comp_smul

-- Involutivity follows from the categorical duality alone; no additive laws enter.
omit [Functor.Additive (HermitianCategory.duality (C := C))] [Preadditive C] in
/-- Taking the dual form twice recovers the original form, by naturality and coherence. -/
@[simp]
lemma formDoubleDual {M : C} (f : Sesq M) :
  formDual (formDual f) = f := by
  -- Expand both occurrences of the dual form: f† = η_M ≫ D.map f.op.
  simp only [formDual]
  -- Name the duality functor and the components of η : Id_C ⟶ D².
  -- Specifying C makes the choice of HermitianCategory instance unambiguous.
  let D := HermitianCategory.duality (C := C)
  let η := HermitianCategory.doubleDualIso (C := C).hom
  let η_M := HermitianCategory.doubleDualIso.hom.app M
  let η_D_M := HermitianCategory.doubleDualIso.hom.app (D.obj (op M))
  -- Restate the goal using these abbreviations; this is a definitional equality.
  change η_M ≫ D.map (η_M ≫ D.map (f.op)).op = f
  -- Opposites reverse composition, and D preserves the resulting composition.
  -- Reassociate to isolate η_M ≫ D²(f), the part to which naturality applies.
  rw [op_comp, Functor.map_comp, ← Category.assoc]
  -- Naturality for f : M ⟶ D(M), oriented to move f before the component of η.
  have nat : η_M ≫ D.map (D.map f.op).op = f ≫ η_D_M := by
    -- Fold the explicit double-dual map into (D.rightOp ⋙ D).map f,
    -- matching the form in which the naturality theorem is stated.
    rw [← Functor.rightOp_map, ← Functor.comp_map]
    rw [← HermitianCategory.doubleDualIso.hom.naturality f]
    -- The identity functor acts as the identity on morphisms.
    rw [Functor.id_map]
  rw [nat]
  -- Regroup to expose η_{D(M)} ≫ D(η_M), where D(η_M) means D.map η_M.op.
  rw [Category.assoc]
  -- Coherence identifies this pair with the identity morphism of D(M).
  rw [HermitianCategory.coherence]
  -- Postcomposing f with the identity recovers f.
  rw [Category.comp_id]

omit [Preadditive C] [Functor.Additive (HermitianCategory.duality (C := C))] in
/-- Taking the adjoint commutes with pulling a form back along a morphism. -/
lemma formDual_pullback {M N : C} (f : M ⟶ N) (h : Sesq N) :
    formDual (f ≫ h ≫ HermitianCategory.duality.map f.op) =
      f ≫ formDual h ≫ HermitianCategory.duality.map f.op := by
  simp only [formDual, op_comp, Functor.map_comp, Category.assoc]
  -- Naturality moves the double dual of f across the double-dual identification.
  have hn := HermitianCategory.doubleDualIso.hom.naturality f
  dsimp at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]

/-! ## λ-Hermitian forms and isometries -/

/--
A sesquilinear form f is λ-Hermitian if f^† = λ • f.
The type `Z1Mul R` ensures λ is a unit satisfying λ * star λ = 1.
Here λ is an actual cocycle, not a class in the multiplicative Tate quotient.
We use double coercion `((lam : Rˣ) : R)` to extract the element from the subgroup
and cast the unit into the underlying ring so it can act via scalar multiplication.
-/
def IsLambdaHermitian {M : C} (lam : Z1Mul R) (f : Sesq M) : Prop :=
  formDual f = ((lam : Rˣ) : R) • f

/-- Combine the symmetry condition with invertibility of the form morphism. -/
abbrev isLambdaHermitian_and_Nonsingular {M : C} (lam : Z1Mul R) (f : Sesq M) : Prop :=
  IsLambdaHermitian R lam f ∧ isNonSingular f
/--
The additive subgroup of all λ-Hermitian forms on M, including singular forms.
Nonsingularity is imposed later on objects: it is not generally preserved by addition.
An arbitrary scalar need not preserve the parameter λ; self-adjoint scalars do,
as shown by `IsLambdaHermitian.smul` below.
-/
def LambdaHermitianForms (M : C) (lam : Z1Mul R) : AddSubgroup (Sesq M) where
  carrier := { f | IsLambdaHermitian R lam f }

  zero_mem' := by
    simp only [IsLambdaHermitian, Set.mem_ofPred_eq, formDual]
    -- Isolate the functor's zero mapping:
    have H_zero : HermitianCategory.duality.map (0 : Sesq M).op = 0 := by
      exact Functor.map_zero HermitianCategory.duality _ _

    rw [H_zero]
    rw [CategoryTheory.Limits.comp_zero]
    rw [smul_zero]

  add_mem' := by
    intro f g hf hg
    simp only [IsLambdaHermitian, Set.mem_ofPred_eq] at *
    calc formDual (f + g)
      _ = formDual f + formDual g := by
        simp only [formDual]
        rw [← CategoryTheory.Preadditive.comp_add]

        -- Explicitly provide the functor and the morphisms to map_add.
        -- Lean natively knows that f.op + g.op is the exact same thing as (f + g).op
        have H_add : HermitianCategory.duality.map f.op + HermitianCategory.duality.map g.op = HermitianCategory.duality.map (f + g).op := by
          exact (Functor.map_add HermitianCategory.duality).symm

        rw [H_add]
      -- Substitute the Hermitian equations for the two adjoints.
      _ = ((lam : Rˣ) : R) • f + ((lam : Rˣ) : R) • g := by rw [hf, hg]
      _ = ((lam : Rˣ) : R) • (f + g) := by rw [smul_add]

  neg_mem' := by
    intro f hf
    simp only [IsLambdaHermitian, Set.mem_ofPred_eq] at *
    calc formDual (-f)
      _ = -formDual f := by
        simp only [formDual]
        rw [← CategoryTheory.Preadditive.comp_neg]

        -- Explicitly provide the functor and the morphism to map_neg
        have H_neg : -(HermitianCategory.duality.map f.op) = HermitianCategory.duality.map (-f).op := by
          exact (Functor.map_neg HermitianCategory.duality).symm

        rw [H_neg]
      _ = -(((lam : Rˣ) : R) • f) := by rw [hf]
      _ = ((lam : Rˣ) : R) • (-f) := by rw [smul_neg]

/--
A λ-Hermitian form on M is an element of the subgroup of λ-Hermitian forms.
The `↥` coerces the subgroup into a Type. For an element h, `h.val` is the
underlying morphism and `h.property` is its λ-Hermitian condition.
-/
abbrev LambdaHermitianForm (M : C) (lam : Z1Mul R) : Type v :=
  ↥(LambdaHermitianForms R M lam)

omit [Functor.Additive (HermitianCategory.duality (C := C))] in
/-- If `r` is invariant under the involution (self-adjoint), scalar multiplication
preserves λ-Hermitian forms. -/
lemma IsLambdaHermitian.smul {M : C} {lam : Z1Mul R} {f : Sesq M}
    (hf : IsLambdaHermitian R lam f) {r : R} (hr : IsSelfAdjoint r) :
    IsLambdaHermitian R lam (r • f) := by
  dsimp [IsLambdaHermitian] at *
  calc formDual (r • f)
    _ = star r • formDual f := by rw [formDual_smul]
    -- Self-adjoint scalars are fixed by star, so the parameter λ is unchanged.
    _ = r • (((lam : Rˣ) : R) • f) := by rw [hr, hf]
    _ = ((lam : Rˣ) : R) • (r • f) := by rw [smul_comm]

/--
An isometry is an invertible morphism that pulls back the target form to the source form.
The conjunction separates invertibility of f from the form-preservation equation.
-/
def isIsometryLambdaHermitianForms {M N : C} (lam : Z1Mul R)
  (hM : LambdaHermitianForm R M lam)
  (hN : LambdaHermitianForm R N lam)
  (f : M ⟶ N) : Prop :=
  IsIso f ∧
  f ≫ hN.val ≫ (HermitianCategory.duality.map f.op) = hM.val

omit [StarLinearDuality R C] in
lemma invIsIsometry {M N : C} (lam : Z1Mul R)
    (hM : LambdaHermitianForm R M lam)
    (hN : LambdaHermitianForm R N lam)
    (f : M ⟶ N)
    (hf : isIsometryLambdaHermitianForms R lam hM hN f) :
    letI : IsIso f := hf.1
    isIsometryLambdaHermitianForms R lam hN hM (inv f) := by
  constructor
  · infer_instance
  · let : IsIso f := hf.1
    let h_eq := hf.2
    have h_left := whisker_eq (inv f) h_eq
    rw [← Category.assoc (inv f) f, IsIso.inv_hom_id, Category.id_comp] at h_left
    have h_right := eq_whisker h_left ((HermitianCategory.duality (C := C)).map (inv f).op)
    rw [Category.assoc, op_inv, Functor.map_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      ← Functor.map_inv, ← op_inv] at h_right
    exact h_right.symm

/--
The type of all isometries between two specific λ-Hermitian forms.
For an element f of this subtype, `f.val` is the underlying morphism in C.
The proofs `f.property.1` and `f.property.2` assert invertibility and form preservation.
-/
def Isometry {M N : C} (lam : Z1Mul R)
  (hM : LambdaHermitianForm R M lam)
  (hN : LambdaHermitianForm R N lam) : Type v :=
  { f : M ⟶ N // isIsometryLambdaHermitianForms R lam hM hN f }

omit [StarLinearDuality R C] in
/-- The identity morphism is an isometry of any λ-Hermitian form, including a singular one. -/
lemma idIsIsometry {M : C} (lam : Z1Mul R)
  (hM : LambdaHermitianForm R M lam) : isIsometryLambdaHermitianForms R lam hM hM (𝟙 M) := by
    constructor
    · infer_instance
    · simp

noncomputable def inverseIsIsometry {M N : C} (lam : Z1Mul R)
    (hM : LambdaHermitianForm R M lam)
    (hN : LambdaHermitianForm R N lam)
    (f : Isometry R lam hM hN) :
    Isometry R lam hN hM := by
  letI : IsIso f.val := f.property.1
  exact ⟨inv f.val,
    invIsIsometry R lam hM hN f.val f.property⟩

/--
A nonsingular λ-Hermitian object consists of a base object M, a λ-Hermitian form,
and a proof that its associated morphism is invertible.
-/
structure HermitianObject (lam : Z1Mul R) where
  /-- The underlying object of the original category. -/
  M : C
  /-- A form together with its λ-Hermitian symmetry proof. -/
  form : LambdaHermitianForm R M lam
  /-- Invertibility of the underlying form morphism, imposed in addition to symmetry. -/
  nonsingular : isNonSingular form.val

/--
Define the Category instance.
We tell Lean that the morphisms are our `Isometries`, and we provide the proofs
that the identity morphism is an isometry, and that composing two isometries
results in another isometry.

The remaining category laws use Mathlib's default proof tactics: equality of these
subtype morphisms reduces to equality of their underlying morphisms in C.
-/
instance (lam : Z1Mul R) : Category (HermitianObject (C := C) R lam) where
  -- The hom-set between X and Y is the subtype of isometries
  Hom X Y := Isometry R lam X.form Y.form

  -- Pair the underlying identity with the two proofs required of an isometry.
  id X := ⟨𝟙 X.M, by
    unfold isIsometryLambdaHermitianForms
    let D := HermitianCategory.duality (C := C)
    change IsIso (𝟙 X.M) ∧ 𝟙 X.M ≫ X.form ≫ D.map (𝟙 X.M).op = X.form
    -- The identity is its own inverse. This explicit construction separates
    -- the existential witness from the IsIso structure that contains it.
    have h1 : IsIso ( 𝟙 X.M ) := by
      have : ∃ g, 𝟙 X.M ≫ g = 𝟙 X.M ∧ g ≫ 𝟙 X.M = 𝟙 X.M := by
        use 𝟙 X.M
        -- `constructor` splits the conjunction; `<;>` applies the rewrite to both goals.
        constructor <;> rw [Category.id_comp]
      -- The anonymous `have` is named `this`; IsIso.mk packages it as the field `out`.
      exact IsIso.mk this
    -- Opposites and functors preserve identity arrows, so pulling back along
    -- the identity leaves the form unchanged.
    have h2 : 𝟙 X.M ≫ X.form ≫ D.map (𝟙 X.M).op = X.form := by
      rw [Category.id_comp, op_id, D.map_id, Category.comp_id]
    exact ⟨ h1, h2 ⟩
    ⟩

  -- Compose the underlying morphisms, then prove invertibility and form preservation.
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by
    unfold isIsometryLambdaHermitianForms
    let D := HermitianCategory.duality (C := C)
    change IsIso (f.val ≫ g.val) ∧ (f.val ≫ g.val) ≫ Z.form ≫ D.map (f.val ≫ g.val).op = X.form
    -- Subtype proofs are not automatically registered as typeclass instances.
    -- These local instances make `inv` and its cancellation lemmas available.
    let _ : IsIso f.val := f.property.1
    let _ : IsIso g.val := g.property.1
    have h1 : ∃ h, (f.val ≫ g.val) ≫ h = 𝟙 X.M ∧ h ≫ (f.val ≫ g.val) = 𝟙 Z.M := by
      -- The inverse runs in the opposite order: Z.M ⟶ Y.M ⟶ X.M.
      use (inv g.val) ≫ (inv f.val)
      -- Associativity and inverse-cancellation simp lemmas prove both equations.
      constructor <;> simp
    have h2 : (f.val ≫ g.val) ≫ Z.form ≫ D.map (f.val ≫ g.val).op = X.form := by
      have f_preserves_form : f.val ≫ Y.form ≫ D.map (f.val).op = X.form := f.property.2
      have g_preserves_form : g.val ≫ Z.form ≫ D.map (g.val).op = Y.form := g.property.2
      -- Dualizing a composite reverses its factors. This exposes a pullback
      -- along g followed by a pullback along f.
      rw [op_comp, D.map_comp]
      calc
        (f.val ≫ g.val) ≫ Z.form ≫ D.map (g.val).op ≫ D.map (f.val).op
        -- Only the parentheses change here; the order of morphisms is preserved.
        _ = f.val ≫ (g.val ≫ Z.form ≫ D.map (g.val).op) ≫ D.map (f.val).op := by simp only [Category.assoc]
        _ = f.val ≫ Y.form ≫ D.map f.val.op := by rw [g_preserves_form]
        _ = X.form := by rw [f_preserves_form]
    -- h1 is an existential proof, so package it as IsIso before pairing it with h2.
    exact ⟨IsIso.mk h1, h2⟩
  ⟩

/-- A name for the category of nonsingular λ-Hermitian objects and their isometries.
As an abbreviation, this reuses the category instance on `HermitianObject` directly. -/
abbrev HermitianFormCat (lam : Z1Mul R) : Type _ :=
  HermitianObject (C := C) R lam

instance (lam : Z1Mul R)
    {X Y : (HermitianObject (C := C)) R lam} (f : X ⟶ Y) :
    IsIso f := by
  let : IsIso f.val := f.property.1
  let g := inverseIsIsometry R lam X.form Y.form f
  use g
  constructor
  · apply Subtype.ext
    change f.val ≫ inv f.val = 𝟙 X.M
    exact IsIso.hom_inv_id f.val
  · apply Subtype.ext
    change inv f.val ≫ f.val = 𝟙 Y.M
    exact IsIso.inv_hom_id f.val

noncomputable instance (lam : Z1Mul R) : Groupoid ((HermitianFormCat (C := C)) R lam) := by
  apply Groupoid.ofIsIso
  intro X Y f
  infer_instance
