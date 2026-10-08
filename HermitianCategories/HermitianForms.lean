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

/-!
# The category of λ-Hermitian forms

Starting from the sesquilinear forms in `Basic`, this file defines the adjoint
operation, λ-Hermitian forms, and nonsingular objects with isometries as morphisms.
The parameter λ is a norm-one unit, represented by `Z1Mul R` from `TateCohomology`.

Preadditivity supplies addition of forms; `Linear R C` supplies scalar multiplication.
Additivity of the duality makes adjoints additive, while `StarLinearDuality` makes
them conjugate-linear. The involutivity proof uses naturality and coherence of
the double-dual isomorphism.
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

/-! ## λ-Hermitian Forms -/

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
--/
def formDual {M : C} (f : Sesq M) : Sesq M :=
  (HermitianCategory.doubleDualIso.hom.app M) ≫ (HermitianCategory.duality.map f.op)

variable [StarLinearDuality R C]

/-- The dual form map is conjugate-linear: (r • f)† = r* • f†. -/
@[simp]
lemma formDual_smul (r : R) {M : C} (f : Sesq M) :
    formDual (r • f) = star r • formDual f := by
  dsimp [formDual]
  rw [StarLinearDuality.map_smul]
  -- Re-associate scalar multiplication out of the categorical composition:
  -- η_M ≫ (star r • D(f.op)) = star r • (η_M ≫ D(f.op))
  apply CategoryTheory.Linear.comp_smul

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

/--
A sesquilinear form f is λ-Hermitian if f = λ • f^†.
The type `Z1Mul R` ensures λ is a unit satisfying λ * star λ = 1.
Here λ is an actual cocycle, not a class in the multiplicative Tate quotient.
We use double coercion `((lam : Rˣ) : R)` to extract the element from the subgroup
and cast the unit into the underlying ring so it can act via scalar multiplication.
--/
def IsLambdaHermitian {M : C} (lam : Z1Mul R) (f : Sesq M) : Prop :=
  f = ((lam : Rˣ) : R) • formDual f

/-- Combine the symmetry condition with invertibility of the form morphism. -/
abbrev isLambdaHermitian_and_Nonsingular {M : C} (lam : Z1Mul R) (f : Sesq M) : Prop :=
  IsLambdaHermitian R lam f ∧ isNonSingular f
/--
The additive subgroup of all λ-Hermitian forms on M, including singular forms.
Nonsingularity is imposed later on objects: it is not generally preserved by addition.
--/
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
    calc f + g
      _ = ((lam : Rˣ) : R) • formDual f + ((lam : Rˣ) : R) • formDual g := by
        -- Restrict rewriting to the left side, so f and g inside the target
        -- adjoints are not themselves replaced by their Hermitian expressions.
        conv_lhs => rw [hf, hg]
      _ = ((lam : Rˣ) : R) • (formDual f + formDual g) := by rw [← smul_add]
      _ = ((lam : Rˣ) : R) • formDual (f + g) := by
        congr 1
        simp only [formDual]
        rw [← CategoryTheory.Preadditive.comp_add]

        -- Explicitly provide the functor and the morphisms to map_add.
        -- Lean natively knows that f.op + g.op is the exact same thing as (f + g).op
        have H_add : HermitianCategory.duality.map f.op + HermitianCategory.duality.map g.op = HermitianCategory.duality.map (f + g).op := by
          exact (Functor.map_add HermitianCategory.duality).symm

        rw [H_add]

  neg_mem' := by
    intro f hf
    simp only [IsLambdaHermitian, Set.mem_ofPred_eq] at *
    calc -f
      _ = - (((lam : Rˣ) : R) • formDual f) := by
        conv_lhs => rw [hf]
      _ = ((lam : Rˣ) : R) • -(formDual f) := by rw [← smul_neg]
      _ = ((lam : Rˣ) : R) • formDual (-f) := by
        congr 1
        simp only [formDual]
        rw [← CategoryTheory.Preadditive.comp_neg]

        -- Explicitly provide the functor and the morphism to map_neg
        have H_neg : -(HermitianCategory.duality.map f.op) = HermitianCategory.duality.map (-f).op := by
          exact (Functor.map_neg HermitianCategory.duality).symm

        rw [H_neg]

/--
A λ-Hermitian form on M is an element of the subgroup of λ-Hermitian forms.
The `↥` coerces the subgroup into a Type. For an element h, `h.val` is the
underlying morphism and `h.property` is its λ-Hermitian condition.
-/
abbrev LambdaHermitianForm (M : C) (lam : Z1Mul R) : Type v :=
  ↥(LambdaHermitianForms R M lam)

/-- If `r` is invariant under the involution (self-adjoint), scalar multiplication
preserves λ-Hermitian forms. -/
lemma IsLambdaHermitian.smul {M : C} {lam : Z1Mul R} {f : Sesq M}
    (hf : IsLambdaHermitian R lam f) {r : R} (hr : IsSelfAdjoint r) :
    IsLambdaHermitian R lam (r • f) := by
  dsimp [IsLambdaHermitian] at *
  calc r • f
    -- Apply scalar multiplication to the equality hf without rewriting f
    -- inside the expression on its right-hand side.
    _ = r • (((lam : Rˣ) : R) • formDual f) := congrArg (fun g : Sesq M => r • g) hf
    _ = ((lam : Rˣ) : R) • (r • formDual f) := by rw [smul_comm]
    _ = ((lam : Rˣ) : R) • (star r • formDual f) := by rw [hr]
    _ = ((lam : Rˣ) : R) • formDual (r • f) := by rw [formDual_smul]

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

/--
The type of all isometries between two specific λ-Hermitian forms.
For an element f of this subtype, `f.val` is the underlying morphism in C.
The proofs `f.property.1` and `f.property.2` assert invertibility and form preservation.
-/
def Isometries {M N : C} (lam : Z1Mul R)
  (hM : LambdaHermitianForm R M lam)
  (hN : LambdaHermitianForm R N lam) : Type v :=
  { f : M ⟶ N // isIsometryLambdaHermitianForms R lam hM hN f }

/--
A nonsingular λ-Hermitian object consists of a base object M, a λ-Hermitian form,
and a proof that its associated morphism is invertible.
-/
structure HermitianObject (lam : Z1Mul R) where
  M : C
  form : LambdaHermitianForm R M lam
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
  Hom X Y := Isometries R lam X.form Y.form

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

/-! ## Hermitian functors -/

variable {D : Type u} [Category D] [Preadditive D] [Linear R D] [HermitianCategory D]
variable (functor : C ⥤ D)

def HermitianFunctor (hf : DualityPreservingFunctor functor)
    (eta : Z1Mul R) : Prop :=
  ∀ M : C,
    hf.nat_iso.hom.app
        (op ((HermitianCategory.duality (C := C)).obj (op M))) =
      ((eta : Rˣ) : R) •
        ((HermitianCategory.duality (C := D)).map
            (hf.nat_iso.hom.app (op M)).op ≫
          (HermitianCategory.doubleDualIso (C := D)).inv.app (functor.obj M) ≫
          functor.map ((HermitianCategory.doubleDualIso (C := C)).hom.app M))

/- Maybe prove some basic properties like the fact that a composition of Hermitian functors is a Hermitian functor. -/

variable [Functor.Additive (HermitianCategory.duality (C := D))]
variable [Functor.Additive functor] [Functor.Linear R functor]

/-- Transport λ-Hermitian forms to (eta * λ)-Hermitian forms.
For the convention h† = λ • h, compatibility gives T(h)† = eta • T(h†). -/
def mapHermitianForms {M : C}
    (hf : DualityPreservingFunctor functor)
    (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    (h : LambdaHermitianForm R M lam) :
    LambdaHermitianForm R (functor.obj M) (eta * lam) := by
  refine ⟨mapSesqForms functor hf h.val, ?_⟩
  change IsLambdaHermitian R (eta * lam)
    (mapSesqForms functor hf h.val)
  simp only [IsLambdaHermitian, mapSesqForms, formDual]
  let F := functor
  let θ := hf.nat_iso.inv.app
  let DD := HermitianCategory.duality (C := D)
  let η := HermitianCategory.doubleDualIso (C := D)
  change η.hom.app (F.obj M) ≫ DD.map (F.map h ≫ θ (op M)).op =
    ((eta * lam : Rˣ) : R) • (F.map h ≫ θ (op M))

  let DC := HermitianCategory.duality (C := C)
  let j := HermitianCategory.doubleDualIso (C := C)
  let N := DC.obj (op M)

  -- Naturality of the inverse comparison.
  have nat : F.map (DC.map h.val.op) ≫ θ (op M) =
      θ (op N) ≫ DD.map (F.map h.val).op := by
    simpa [F, DC, DD, θ, N] using
      hf.nat_iso.inv.naturality h.val.op

  -- The duals of the comparison and its inverse cancel.
  have cancel_dual : DD.map (θ (op M)).op ≫
      DD.map (hf.nat_iso.hom.app (op M)).op = 𝟙 _ := by
    rw [← DD.map_comp, ← op_comp]
    simp [θ]

  -- Express the Hermitian condition using the inverse comparison.
  have compat : η.hom.app (F.obj M) ≫ DD.map (θ (op M)).op =
      ((eta : Rˣ) : R) • (F.map (j.hom.app M) ≫ θ (op N)) := by
    have hc := congrArg
      (fun k =>
        η.hom.app (F.obj M) ≫
          DD.map (θ (op M)).op ≫ k ≫ θ (op N))
      (hermf M)

    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc] at hc
    rw [← Category.assoc (DD.map (θ (op M)).op)
      (DD.map (hf.nat_iso.hom.app (op M)).op),
      cancel_dual, Category.id_comp] at hc
    simp only [θ, N, DC, DD, η, F, Iso.hom_inv_id_app,
      Iso.hom_inv_id_app_assoc] at hc

    -- Reduce the object expressions before cancelling the remaining identity.
    dsimp at hc
    simp only [Category.comp_id] at hc

    exact hc

  -- Move the adjoint through transport, then use h† = λ • h.
  rw [op_comp, DD.map_comp, ← Category.assoc, compat, Linear.smul_comp,
    Category.assoc, ← nat, ← Category.assoc, ← F.map_comp]
  change ((eta : Rˣ) : R) • (F.map (formDual h.val) ≫ θ (op M)) = _
  rw [h.property, Functor.Linear.map_smul, Linear.smul_comp, smul_smul]
  simp only [Units.val_mul]


def mapHermitianFormsHom {M : C}
  (hf : DualityPreservingFunctor functor)
  (lam eta : Z1Mul R)
  (hermf : HermitianFunctor R functor hf eta) :
  LambdaHermitianForm R M lam →+ LambdaHermitianForm R (functor.obj M) (eta * lam) where
  toFun := sorry

  map_zero' := sorry

  map_add' := sorry

/- Hermitian functors induce functors of the respective categories of Hermitian objects. -/

/- The scaling functor as a special case of a Hermitian functor. -/
