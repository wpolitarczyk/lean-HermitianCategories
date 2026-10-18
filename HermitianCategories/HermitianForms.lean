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

Hermitian comparisons are closed under composition, with their compatibility
parameters multiplied; the canonical identity comparison has parameter 1.
Identity and composition laws also hold for transport of forms and objects,
for the underlying isometry morphisms, and for the induced functors after
identifying the resulting parameters.

A linear equivalence with a Hermitian comparison induces an equivalence of
Hermitian-form categories. Full faithfulness lifts and reflects isometries;
essential surjectivity is proved by pulling back and lifting a target form.
`equivalenceHermitianCategories` bundles the resulting equivalence.

The transport constructions send a λ-Hermitian form to an (eta * λ)-Hermitian
form using a duality comparison with scalar compatibility `eta`. In particular,
`scalingHermitianCategories R s lam` multiplies forms by `s⁻¹` and changes their
parameter by `scalingParameter R s`. The final theorem proves that this scaling
functor is an equivalence, with inverse scaling by `s⁻¹` and a parameter cast.
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

/-! ## Hermitian functors -/

variable {D : Type u} [Category D] [Preadditive D] [Linear R D] [HermitianCategory D]
variable (functor : C ⥤ D)

/-- Scalar-dependent compatibility of a comparison with the double-dual maps.
This condition allows transport to change the Hermitian parameter by `eta`.
The argument `hf` is comparison data for the already specified functor; this
predicate supplies the extra compatibility needed to transport Hermitian forms. -/
def HermitianFunctor (hf : DualityComparison functor)
    (eta : Z1Mul R) : Prop :=
  ∀ M : C,
    hf.nat_iso.hom.app
        (op ((HermitianCategory.duality (C := C)).obj (op M))) =
      ((eta : Rˣ) : R) •
        ((HermitianCategory.duality (C := D)).map
            (hf.nat_iso.hom.app (op M)).op ≫
          (HermitianCategory.doubleDualIso (C := D)).inv.app (functor.obj M) ≫
          functor.map ((HermitianCategory.doubleDualIso (C := C)).hom.app M))

omit [Preadditive C] [Linear R C]
  [Functor.Additive (HermitianCategory.duality (C := C))] [StarLinearDuality R C] in
/-- Hermitian comparisons compose, multiplying their compatibility parameters.
The comparison data is the composite constructed in `Basic`.
Linearity of G allows the parameter for F to pass through G's action on morphisms;
linearity of F is not needed for this compatibility statement. -/
lemma compHermitianFunctors {E : Type u} [Category E] [Preadditive E] [Linear R E] [HermitianCategory E]
  (F : C ⥤ D) (G : D ⥤ E)
  [Functor.Additive G] [Functor.Linear R G]
  (hfDC : DualityComparison F)
  (hgDC : DualityComparison G)
  (eta1 : Z1Mul R) (eta2 : Z1Mul R)
  (hf : HermitianFunctor R F hfDC eta1)
  (hg : HermitianFunctor R G hgDC eta2) :
  HermitianFunctor R (F ⋙ G)
    (compDualityComparison F G hfDC hgDC)
    (eta1 * eta2) := by
    intro M
    -- Expand the composite comparison into its two whiskered components.
    dsimp [compDualityComparison, Trans.trans]
    simp only [Category.id_comp, Category.comp_id]
    -- Apply compatibility for F and pull its parameter through G.
    rw [hf M, Functor.map_smul]
    simp only [Functor.map_comp, Linear.comp_smul, Category.assoc]
    -- Naturality moves the dual of F's comparison past G's comparison.
    -- The postcomposition in `naturality_assoc` retains the double-dual inverse
    -- and the image of the source double-dual map already present in the goal.
    have hn := hgDC.nat_iso.hom.naturality_assoc
      (hfDC.nat_iso.hom.app (op M)).op
      (G.map ((HermitianCategory.doubleDualIso (C := D)).inv.app (F.obj M)) ≫
        G.map (F.map ((HermitianCategory.doubleDualIso (C := C)).hom.app M)))
    dsimp at hn
    rw [← hn, hg (F.obj M)]
    -- Combine the scalars and cancel the double-dual maps inside G.
    simp only [Linear.comp_smul, Linear.smul_comp, smul_smul, Category.assoc,
      ← G.map_comp, Iso.hom_inv_id_app_assoc]

omit [Functor.Additive (HermitianCategory.duality (C := C))] [StarLinearDuality R C] in
/-- The canonical comparison for the identity functor is Hermitian with parameter 1.
Its comparison components are identities, and the double-dual inverse and forward
maps cancel. Neither additivity nor conjugate-linearity of the duality is needed. -/
lemma IdIsHermitianFunctor : HermitianFunctor R (Functor.id C) IdIsDualityComparison (1 : Z1Mul R) := by
  intro M
  -- Expand the comparison, including the isomorphism compositions in its `calc` block.
  dsimp [IdIsDualityComparison, Trans.trans]
  -- Remove the unit scalar, cancel the double-dual maps, and evaluate the
  -- components of identity natural transformations as identity morphisms.
  simp only [Category.comp_id, Category.id_comp, Functor.opId, Iso.refl, one_smul,
    Iso.inv_hom_id_app, NatTrans.id_app]
  -- Reduce object expressions involving the opposite identity functor before
  -- simplifying the duality's images of identity morphisms.
  dsimp
  simp

/-- Regard a Hermitian object with parameter `lam1` as one with the equal parameter `lam2`.
The underlying object, form morphism, and isometry morphisms are unchanged;
only the proofs involving the parameter are transported along `h`.
This makes an equality of parameters usable when composing functors whose
source and target categories are not definitionally equal. -/
def castHermitianHermitianCategories {lam1 lam2 : Z1Mul R} (h : lam1 = lam2) :
  HermitianFormCat (C := C) R lam1 ⥤ HermitianFormCat (C := C) R lam2 where
  obj X := {
    M := X.M
    form := ⟨X.form.val, by rw [← h]; exact X.form.property ⟩
    nonsingular := X.nonsingular
  }

  map f := ⟨f.val, by cases h; exact f.property ⟩

  map_id := by
    intro CC
    -- Equality elimination reduces the cast to the case where both parameters coincide.
    cases h
    rfl

  map_comp f g := by
    cases h
    rfl

/-! ## Transport of forms, nonsingular objects, and isometries -/

-- Additivity and linearity of the transporting functor are used below to
-- preserve sums of forms and move the Hermitian parameter through its map.
variable [Functor.Additive (HermitianCategory.duality (C := D))]
variable [Functor.Additive functor] [Functor.Linear R functor]

omit [Preadditive C] [Linear R C] [StarLinearDuality R C]
  [Functor.Additive (HermitianCategory.duality (C := C))]
  [Functor.Additive (HermitianCategory.duality (C := D))]
  [Functor.Additive functor] [Functor.Linear R functor] in
/-- Adjoint and transport commute up to the compatibility parameter, for any
sesquilinear form, without assuming a Hermitian symmetry condition. -/
lemma mapSesqForms_formDual (hf : DualityComparison functor) (eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta) {M : C} (h : Sesq M) :
    formDual (mapSesqForms functor hf h) =
      ((eta : Rˣ) : R) • mapSesqForms functor hf (formDual h) := by
  let F := functor
  let θ := hf.nat_iso.inv.app
  let DD := HermitianCategory.duality (C := D)
  -- Greek η here is the target double-dual isomorphism; `eta` is the scalar parameter.
  let η := HermitianCategory.doubleDualIso (C := D)
  change η.hom.app (F.obj M) ≫ DD.map (F.map h ≫ θ (op M)).op =
    ((eta : Rˣ) : R) • (F.map (formDual h) ≫ θ (op M))

  let DC := HermitianCategory.duality (C := C)
  let j := HermitianCategory.doubleDualIso (C := C)
  let N := DC.obj (op M)

  -- Naturality of the inverse comparison.
  have nat : F.map (DC.map h.op) ≫ θ (op M) =
      θ (op N) ≫ DD.map (F.map h).op := by
    simpa [F, DC, DD, θ, N] using
      hf.nat_iso.inv.naturality h.op

  -- The duals of the comparison and its inverse cancel.
  have cancel_dual : DD.map (θ (op M)).op ≫
      DD.map (hf.nat_iso.hom.app (op M)).op = 𝟙 _ := by
    rw [← DD.map_comp, ← op_comp]
    simp [θ]

  -- Express the Hermitian condition using the inverse comparison.
  have compat : η.hom.app (F.obj M) ≫ DD.map (θ (op M)).op =
      ((eta : Rˣ) : R) • (F.map (j.hom.app M) ≫ θ (op N)) := by
    -- Compose the compatibility equation on both sides with inverse comparison maps.
    -- This lets us replace its forward comparison components by the inverses used in T.
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

  -- Move the adjoint through transport using compatibility and naturality.
  rw [op_comp, DD.map_comp, ← Category.assoc, compat, Linear.smul_comp,
    Category.assoc, ← nat, ← Category.assoc, ← F.map_comp]
  rfl


/-- Transport λ-Hermitian forms to (eta * λ)-Hermitian forms.
For the convention h† = λ • h, compatibility gives T(h)† = eta • T(h†).
The underlying transported form is F(h) followed by the inverse comparison
F(D(M)) ⟶ D(F(M)); this explains the use of `hf.nat_iso.inv` in the proof. -/
def mapHermitianForms {M : C}
    (hf : DualityComparison functor)
    (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    (h : LambdaHermitianForm R M lam) :
    LambdaHermitianForm R (functor.obj M) (eta * lam) := by
  refine ⟨mapSesqForms functor hf h.val, ?_⟩
  change IsLambdaHermitian R (eta * lam)
    (mapSesqForms functor hf h.val)
  simp only [IsLambdaHermitian]
  rw [mapSesqForms_formDual R functor hf eta hermf, h.property]
  simp [mapSesqForms, Functor.map_smul, Linear.smul_comp, smul_smul]

omit [StarLinearDuality R C] in
/-- Transport along the composite comparison agrees with successive transport
on the underlying form morphisms. The bundled forms have parameters
`(etaF * etaG) * lam` and `etaG * (etaF * lam)` respectively; comparing `.val`
avoids a cast between these propositionally equal parameters. -/
lemma mapHermitianFormsComp {E : Type u} {M : C} [Category.{v} E] [Preadditive E] [Linear R E] [HermitianCategory E]
  [Functor.Additive (HermitianCategory.duality (C := E))]
  (F : C ⥤ D) (G : D ⥤ E)
  [Functor.Additive F] [Functor.Additive G] [Functor.Linear R F] [Functor.Linear R G]
  (hf : DualityComparison F) (hg : DualityComparison G)
  (lam etaF etaG : Z1Mul R)
  (hermf : HermitianFunctor R F hf etaF)
  (hermg : HermitianFunctor R G hg etaG)
  (h : LambdaHermitianForm R M lam) :
  (mapHermitianForms R (F ⋙ G) (compDualityComparison F G hf hg) lam (etaF * etaG) (compHermitianFunctors R F G hf hg etaF etaG hermf hermg) h).val =
  (mapHermitianForms R G hg (etaF * lam) etaG hermg (mapHermitianForms R F hf lam (etaF) hermf h)).val := by
    -- Only the underlying sesquilinear transport remains after taking `.val`.
    -- The inverse composite comparison applies G to F's inverse comparison,
    -- then follows it by G's inverse comparison.
    dsimp [mapHermitianForms, mapSesqForms, compDualityComparison, Trans.trans]
    -- Expand G's map of the first transport and reassociate the resulting arrows.
    simp [Functor.map_comp, Category.assoc]

omit [StarLinearDuality R C] in
/-- Transport along the canonical identity comparison leaves the underlying
form unchanged. Comparing `.val` avoids casting the parameter `1 * lam` to `lam`. -/
lemma mapHermitianFormsId {M : C}
  (lam : Z1Mul R)
  (hf : LambdaHermitianForm R M lam) :
  (mapHermitianForms R (Functor.id C) IdIsDualityComparison lam 1 (IdIsHermitianFunctor R) hf).val =
    hf.val := by
    -- Identity transport maps the form by Id and postcomposes with the inverse
    -- identity comparison; unfolding exposes only identity maps and unitors.
    dsimp [mapHermitianForms, mapSesqForms, IdIsDualityComparison, Trans.trans]
    simp

/-- Transport of Hermitian forms bundled as an additive homomorphism.
After `Subtype.ext` removes the symmetry proof fields, the additive laws are
exactly those of `mapSesqFormsHom` on the underlying sesquilinear forms. -/
def mapHermitianFormsHom {M : C}
  (hf : DualityComparison functor)
  (lam eta : Z1Mul R)
  (hermf : HermitianFunctor R functor hf eta) :
  LambdaHermitianForm R M lam →+ LambdaHermitianForm R (functor.obj M) (eta * lam) where
  toFun := mapHermitianForms R functor hf lam eta hermf

  map_zero' := by
    apply Subtype.ext
    apply (mapSesqFormsHom functor M hf).map_zero

  map_add' := by
    intro h k
    apply Subtype.ext
    apply (mapSesqFormsHom functor M hf).map_add h.val k.val

/- Hermitian functors induce functors of the respective categories of Hermitian objects. -/

/-- Transport a nonsingular Hermitian object and change its parameter to `eta * lam`.
The transported form is a composite of two isomorphisms, so remains nonsingular. -/
def mapHermitianObjects
  (hf : DualityComparison functor)
  (lam eta : Z1Mul R)
  (hermf : HermitianFunctor R functor hf eta)
  (X : HermitianObject (C := C) R lam) : HermitianObject (C := D) R (eta * lam) where
    M := functor.obj X.M

    form := mapHermitianForms R functor hf lam eta hermf X.form

    nonsingular := by
      -- Expose the stored nonsingularity proof to typeclass search. Functors preserve
      -- isomorphisms, and the inverse comparison component is also an isomorphism.
      let : IsIso X.form.val := X.nonsingular
      change IsIso
        (functor.map X.form.val ≫ hf.nat_iso.inv.app (op X.M))
      infer_instance

omit [StarLinearDuality R C] in
/-- Composite transport of a nonsingular Hermitian object agrees with successive
transport after casting the parameter. The form equality comes from
`mapHermitianFormsComp`; nonsingularity fields agree by proof irrelevance. -/
lemma mapHermitianObjectsComp {E : Type u} [Category.{v} E] [Preadditive E] [Linear R E] [HermitianCategory E]
  [Functor.Additive (HermitianCategory.duality (C := E))]
  (F : C ⥤ D) (G : D ⥤ E)
  [Functor.Additive F] [Functor.Additive G] [Functor.Linear R F] [Functor.Linear R G]
  (hf : DualityComparison F)
  (hg : DualityComparison G)
  (lam etaF etaG : Z1Mul R)
  (hermf : HermitianFunctor R F hf etaF)
  (hermg : HermitianFunctor R G hg etaG)
  (X : HermitianObject (C := C) R lam) :
  (castHermitianHermitianCategories (C := E) R (show (etaF * etaG) * lam = etaG * (etaF * lam) by ac_rfl)).obj
  (mapHermitianObjects R (F ⋙ G) (compDualityComparison F G hf hg) lam (etaF * etaG) (compHermitianFunctors R F G hf hg etaF etaG hermf hermg) X) =
  (mapHermitianObjects R G hg (etaF * lam) etaG hermg (mapHermitianObjects R F hf lam etaF hermf X)) := by
    -- The base objects are definitionally equal. Reduce equality of the remaining
    -- structure fields to equality of the underlying form morphisms.
    dsimp [castHermitianHermitianCategories, mapHermitianObjects]
    congr 1
    apply Subtype.ext
    exact mapHermitianFormsComp R F G hf hg lam etaF etaG hermf hermg X.form

omit [StarLinearDuality R C] in
/-- Identity transport recovers the original Hermitian object after identifying
its parameter `1 * lam` with `lam`. -/
lemma mapHermitianObjectsId (lam : Z1Mul R) (X : HermitianObject R lam) :
  (castHermitianHermitianCategories (C := C) R (show 1 * lam = lam by ac_rfl)).obj
  (mapHermitianObjects R (Functor.id C) IdIsDualityComparison lam (1 : Z1Mul R) (IdIsHermitianFunctor R)  X) = X := by
  -- Expose the fields of X so structure equality reduces to the form identity law.
  cases X with
  | mk M form nonsingular =>
    dsimp [castHermitianHermitianCategories, mapHermitianObjects]
    congr 1
    apply Subtype.ext
    exact mapHermitianFormsId R lam form

/-- Apply the underlying functor to an isometry between Hermitian objects.
Naturality of the comparison ensures that the image preserves the transported forms. -/
def mapIsometry
  (hf : DualityComparison functor)
  (lam eta : Z1Mul R)
  (hermf : HermitianFunctor R functor hf eta)
  (X Y : HermitianObject (C := C) R lam)
  (hisom : Isometry R lam X.form Y.form) :
   Isometry R (eta * lam) (mapHermitianObjects R functor hf lam eta hermf X).form (mapHermitianObjects R functor hf lam eta hermf Y).form where
   val := functor.map hisom.val

   property := by
    -- Treat invertibility and preservation of the form as separate obligations.
    simp only [isIsometryLambdaHermitianForms]
    constructor
    · let : IsIso hisom.val := hisom.property.1
      apply Functor.map_isIso functor hisom.val

    · let DC := HermitianCategory.duality (C := C)
      let DD := HermitianCategory.duality (C := D)
      let θ := hf.nat_iso.inv.app

      -- Naturality relates the two ways of dualizing the mapped isometry.
      have nat : functor.map (DC.map hisom.val.op) ≫ θ (op X.M) =
          θ (op Y.M) ≫ DD.map (functor.map hisom.val).op := by
        simpa [DC, DD, θ] using
          hf.nat_iso.inv.naturality hisom.val.op

      change functor.map hisom.val ≫
          (functor.map Y.form.val ≫ θ (op Y.M)) ≫
          DD.map (functor.map hisom.val).op =
        functor.map X.form.val ≫ θ (op X.M)

      simp only [Category.assoc]
      rw [← nat]

      -- Apply the functor to the original form-preservation equation,
      -- then postcompose with the inverse comparison.
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun k => functor.map k ≫ θ (op X.M))
          hisom.property.2

omit [StarLinearDuality R C] in
/-- Composite and successive transport of an isometry have the same underlying
morphism. Taking `.val` avoids transporting between the different form types. -/
lemma mapIsometryComp {E : Type u} [Category.{v} E] [Preadditive E] [Linear R E] [HermitianCategory E]
  [Functor.Additive (HermitianCategory.duality (C := E))]
  (F : C ⥤ D) (G : D ⥤ E)
  [Functor.Additive F] [Functor.Additive G] [Functor.Linear R F] [Functor.Linear R G]
  (hf : DualityComparison F)
  (hg : DualityComparison G)
  (lam etaF etaG : Z1Mul R)
  (hermf : HermitianFunctor R F hf etaF)
  (hermg : HermitianFunctor R G hg etaG)
  (X Y : HermitianObject R lam)
  (hisom : Isometry R lam X.form Y.form) :
  (mapIsometry R (F ⋙ G) (compDualityComparison F G hf hg) lam (etaF * etaG) (compHermitianFunctors R F G hf hg etaF etaG hermf hermg) X Y hisom).val =
  (mapIsometry R G hg (etaF * lam) etaG hermg (mapHermitianObjects R F hf lam etaF hermf X) (mapHermitianObjects R F hf lam etaF hermf Y) (mapIsometry R F hf lam etaF hermf X Y hisom)).val := by
  -- The underlying maps are definitionally those of the composite or identity functor.
  rfl

omit [StarLinearDuality R C] in
/-- Identity transport leaves the underlying morphism of an isometry unchanged. -/
lemma mapIsometryId (lam : Z1Mul R) (X Y : HermitianObject R lam) (hisom : Isometry R lam X.form Y.form) :
  (mapIsometry R (Functor.id C) IdIsDualityComparison lam (1 : Z1Mul R) (IdIsHermitianFunctor R) X Y hisom).val = hisom.val := by
  -- The underlying maps are definitionally those of the composite or identity functor.
  rfl

/-- The induced functor on categories of nonsingular Hermitian forms.
Its identity and composition laws reduce to those of the original functor by
comparing the underlying morphisms of the bundled isometries. -/
def functorHermitianCategories
  (hf : DualityComparison functor)
  (lam eta : Z1Mul R)
  (hermf : HermitianFunctor R functor hf eta) : HermitianFormCat (C := C) R lam ⥤ HermitianFormCat (C := D) R (eta * lam) where
    obj := mapHermitianObjects R functor hf lam eta hermf

    map := mapIsometry R functor hf lam eta hermf _ _

    map_id := by
      intro X
      apply Subtype.ext
      exact functor.map_id X.M

    map_comp := by
      intro f g Z f1 g1
      apply Subtype.ext
      apply functor.map_comp f1.val g1.val

omit [StarLinearDuality R C] in
/-- The induced functor of a composite comparison equals the composite of the
induced functors after the parameter cast. This is equality of functors, not
merely a natural isomorphism. -/
lemma functorHermitianCategoriesComp {E : Type u} [Category.{v} E] [Preadditive E] [Linear R E] [HermitianCategory E]
  [Functor.Additive (HermitianCategory.duality (C := E))]
  (F : C ⥤ D) (G : D ⥤ E)
  [Functor.Additive F] [Functor.Additive G] [Functor.Linear R F] [Functor.Linear R G]
  (hf : DualityComparison F)
  (hg : DualityComparison G)
  (lam etaF etaG : Z1Mul R)
  (hermf : HermitianFunctor R F hf etaF)
  (hermg : HermitianFunctor R G hg etaG) :
  (functorHermitianCategories R (F ⋙ G) (compDualityComparison F G hf hg) lam (etaF * etaG) (compHermitianFunctors R F G hf hg etaF etaG hermf hermg))
  ⋙ (castHermitianHermitianCategories R (show etaF * etaG * lam = etaG * (etaF * lam) by ac_rfl)) =
  (functorHermitianCategories R F hf lam etaF hermf) ⋙ (functorHermitianCategories R G hg (etaF * lam) etaG hermg) := by
  -- Heterogeneous equality compares maps whose source and target objects are
  -- propositionally equal; the object equalities are supplied separately.
  apply Functor.hext
  · intro X
    exact mapHermitianObjectsComp R F G hf hg lam etaF etaG hermf hermg X
  · intro X Y f
    -- Identify the isometry predicates, then compare only the underlying arrows.
    apply (Subtype.heq_iff_coe_eq (by
      intro k
      dsimp [functorHermitianCategories, castHermitianHermitianCategories,
        mapHermitianObjects, isIsometryLambdaHermitianForms]
      simp [mapHermitianForms, mapSesqForms, compDualityComparison,
        Trans.trans, Functor.map_comp, Category.assoc])).mpr
    rfl

omit [StarLinearDuality R C] in
/-- The functor induced by the canonical identity comparison, followed by the
parameter cast, equals the identity functor on Hermitian objects. -/
lemma functorHermitianCategoriesId (lam : Z1Mul R) :
  (functorHermitianCategories R (Functor.id C) (IdIsDualityComparison) lam 1 (IdIsHermitianFunctor R))
  ⋙ (castHermitianHermitianCategories R (show 1*lam = lam by ac_rfl))
   = Functor.id (HermitianFormCat (C := C) R lam) := by
  -- Heterogeneous equality compares maps whose source and target objects are
  -- propositionally equal; the object equalities are supplied separately.
  apply Functor.hext
  · intro X
    exact mapHermitianObjectsId R lam X
  · intro X Y f
    -- Identify the isometry predicates, then compare only the underlying arrows.
    apply (Subtype.heq_iff_coe_eq (by
      intro k
      dsimp [functorHermitianCategories, castHermitianHermitianCategories,
        mapHermitianObjects, isIsometryLambdaHermitianForms]
      simp [mapHermitianForms, mapSesqForms,
        IdIsDualityComparison, Trans.trans, Category.assoc])).mpr
    rfl

/-! ## Equivalences induced by Hermitian functors -/

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

omit [Preadditive C] [Preadditive D]
  [Functor.Additive (HermitianCategory.duality (C := C))]
  [Functor.Additive (HermitianCategory.duality (C := D))]
  [Functor.Additive functor] in
/-- A faithful functor with a duality comparison transports forms injectively. -/
lemma mapSesqForms_injective (hf : DualityComparison functor) [functor.Faithful]
    {M : C} : Function.Injective (mapSesqForms functor hf (M := M)) := by
  intro h k heq
  -- Cancel the inverse comparison, then reflect equality through the faithful functor.
  apply functor.map_injective
  exact (cancel_mono (hf.nat_iso.inv.app (op M))).mp heq

omit [Preadditive C] [Preadditive D]
  [Functor.Additive (HermitianCategory.duality (C := C))]
  [Functor.Additive (HermitianCategory.duality (C := D))]
  [Functor.Additive functor] in
/-- Transport commutes with pullback of sesquilinear forms. -/
lemma mapSesqForms_pullback (hf : DualityComparison functor)
    {M N : C} (f : M ⟶ N) (h : Sesq N) :
    mapSesqForms functor hf (f ≫ h ≫ HermitianCategory.duality.map f.op) =
      functor.map f ≫ mapSesqForms functor hf h ≫
        HermitianCategory.duality.map (functor.map f).op := by
  have hn := hf.nat_iso.inv.naturality f.op
  dsimp at hn
  simp only [mapSesqForms, Functor.map_comp, Category.assoc]
  rw [hn]

omit [StarLinearDuality R C] [Functor.Additive functor] in
/-- Faithfulness of the underlying functor implies faithfulness on isometries. -/
lemma functorHermitianCategories_faithful (hf : DualityComparison functor)
    (lam eta : Z1Mul R) (hermf : HermitianFunctor R functor hf eta)
    [functor.Faithful] :
    (functorHermitianCategories R functor hf lam eta hermf).Faithful where
  map_injective := by
    intro X Y f g h
    apply Subtype.ext
    apply functor.map_injective
    exact congrArg Subtype.val h

omit [StarLinearDuality R C] [Functor.Additive functor] in
/-- A fully faithful functor with a Hermitian comparison is full on isometries.
Lift the underlying arrow, reflect its invertibility, and use injectivity of
transport to reflect the form-preservation equation. -/
lemma functorHermitianCategories_full (hf : DualityComparison functor)
    (lam eta : Z1Mul R) (hermf : HermitianFunctor R functor hf eta)
    [functor.Full] [functor.Faithful] :
    (functorHermitianCategories R functor hf lam eta hermf).Full where
  map_surjective := by
    intro X Y f
    -- Lift the underlying arrow; full faithfulness reflects its invertibility.
    let g := functor.preimage f.val
    have hg : functor.map g = f.val := functor.map_preimage _
    let : IsIso (functor.map g) := by rw [hg]; exact f.property.1
    let : IsIso g := isIso_of_reflects_iso g functor
    -- The transported pullback equation is the given isometry equation for f.
    have hp : g ≫ Y.form.val ≫ HermitianCategory.duality.map g.op = X.form.val := by
      apply mapSesqForms_injective functor hf
      rw [mapSesqForms_pullback, hg]
      exact f.property.2
    refine ⟨⟨g, inferInstance, hp⟩, ?_⟩
    exact Subtype.ext hg

omit [StarLinearDuality R C]
  [Functor.Additive (HermitianCategory.duality (C := C))]
  [Functor.Additive (HermitianCategory.duality (C := D))]
  [Functor.Additive functor] in
/-- Faithful Hermitian transport reflects the Hermitian symmetry condition.
The compatibility parameter is a unit, so it can be cancelled from the
transported adjoint equation. -/
lemma isLambdaHermitian_of_mapSesqForms (hf : DualityComparison functor)
    (lam eta : Z1Mul R) (hermf : HermitianFunctor R functor hf eta)
    [functor.Faithful] {M : C} (h : Sesq M)
    (hh : IsLambdaHermitian R (eta * lam) (mapSesqForms functor hf h)) :
    IsLambdaHermitian R lam h := by
  apply mapSesqForms_injective functor hf
  have heq := hh
  rw [IsLambdaHermitian, mapSesqForms_formDual R functor hf eta hermf] at heq
  -- Multiply by the inverse unit to cancel eta without any nonzero-ring assumption.
  have hc := congrArg (fun k => (((eta : Rˣ)⁻¹ : Rˣ) : R) • k) heq
  simpa [mapSesqForms, Functor.map_smul, Linear.smul_comp, smul_smul,
    ← mul_assoc] using hc

omit [StarLinearDuality R C] [Functor.Additive functor] in
/-- A compatible equivalence is essentially surjective on nonsingular Hermitian
objects. Pull a target form back to an object in the image, then lift it using
fullness. Faithfulness reflects symmetry, and full faithfulness reflects
nonsingularity. -/
lemma functorHermitianCategories_essSurj (hf : DualityComparison functor)
    (lam eta : Z1Mul R) (hermf : HermitianFunctor R functor hf eta)
    [functor.IsEquivalence] :
    (functorHermitianCategories R functor hf lam eta hermf).EssSurj where
  mem_essImage Y := by
    -- Choose an object in the source whose image is isomorphic to Y.M.
    let M := functor.objPreimage Y.M
    let e : functor.obj M ≅ Y.M := functor.objObjPreimageIso Y.M
    let DD := HermitianCategory.duality (C := D)
    -- Pull back Y's form along e, then undo the comparison before lifting it.
    let k : Sesq (functor.obj M) := e.hom ≫ Y.form.val ≫ DD.map e.hom.op
    let h : Sesq M := functor.preimage (k ≫ hf.nat_iso.hom.app (op M))
    -- Transport of the lift recovers the pulled-back form exactly.
    have ht : mapSesqForms functor hf h = k := by
      simp [mapSesqForms, h, Category.assoc]
    have hk : IsLambdaHermitian R (eta * lam) k := by
      dsimp [IsLambdaHermitian, k]
      rw [formDual_pullback, Y.form.property]
      simp only [Linear.comp_smul, Linear.smul_comp]
      rfl
    have hh : IsLambdaHermitian R lam h :=
      isLambdaHermitian_of_mapSesqForms R functor hf lam eta hermf h (by rw [ht]; exact hk)
    let : IsIso Y.form.val := Y.nonsingular
    -- The image of h is a composite of isomorphisms, so h itself is invertible.
    have hn : IsIso h := by
      let : IsIso (functor.map h) := by
        dsimp [h]
        rw [Functor.map_preimage]
        dsimp [k]
        infer_instance
      exact isIso_of_reflects_iso h functor
    let X : HermitianObject (C := C) R lam := ⟨M, ⟨h, hh⟩, hn⟩
    -- Lift e to an isomorphism of Hermitian objects, with inverse e.inv.
    refine ⟨X, ⟨?_⟩⟩
    refine {
      hom := ⟨e.hom, by change IsIso e.hom; infer_instance, ?_⟩
      inv := ⟨e.inv, by change IsIso e.inv; infer_instance, ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_
    }
    · exact ht.symm
    · change e.inv ≫ mapSesqForms functor hf h ≫ DD.map e.inv.op = Y.form.val
      rw [ht]
      dsimp [k]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← DD.map_comp, ← op_comp]
      rw [e.inv_hom_id, op_id, DD.map_id]
      exact Category.comp_id Y.form.val
    · apply Subtype.ext
      exact e.hom_inv_id
    · apply Subtype.ext
      exact e.inv_hom_id

omit [StarLinearDuality R C] [Functor.Additive functor] in
/-- A linear equivalence equipped with a Hermitian comparison induces an
equivalence between the categories of nonsingular λ-Hermitian and
(eta * λ)-Hermitian forms. The proof establishes full faithfulness and
essential surjectivity of the induced functor. -/
lemma functorHermitianCategoriesIsEquivalence (hf : DualityComparison functor)
    (lam eta : Z1Mul R) (hermf : HermitianFunctor R functor hf eta)
    [functor.IsEquivalence] :
    (functorHermitianCategories R functor hf lam eta hermf).IsEquivalence where
  faithful := functorHermitianCategories_faithful R functor hf lam eta hermf
  full := functorHermitianCategories_full R functor hf lam eta hermf
  essSurj := functorHermitianCategories_essSurj R functor hf lam eta hermf

omit [StarLinearDuality R C] [Functor.Additive functor] in
/-- Bundle the induced equivalence, with an inverse chosen from the lifting
construction and the unit and counit supplied by `Functor.asEquivalence`. -/
noncomputable def equivalenceHermitianCategories (hf : DualityComparison functor)
    (lam eta : Z1Mul R) (hermf : HermitianFunctor R functor hf eta)
    [functor.IsEquivalence] :
    HermitianFormCat (C := C) R lam ≌ HermitianFormCat (C := D) R (eta * lam) := by
  let := functorHermitianCategoriesIsEquivalence R functor hf lam eta hermf
  exact (functorHermitianCategories R functor hf lam eta hermf).asEquivalence

/-! ## Scaling functors -/

/-- The norm-one unit σ(s) = s * star (s⁻¹) governing the change in Hermitian parameter.
Indeed, (s⁻¹ • h)† = star (s⁻¹) • h† = (σ(s) * λ) • (s⁻¹ • h)
when h† = λ • h. Scalars in this identity are understood as elements of R. -/
def scalingParameter (s : Rˣ) : Z1Mul R :=
  ⟨s * star (s⁻¹), by
    change (s * star (s⁻¹)) * star (s * star (s⁻¹)) = 1
    simp [mul_comm, mul_left_comm, mul_assoc]⟩

/-- The parameter changes associated with two units multiply. -/
@[simp]
lemma scalingParameter_mul (s t : Rˣ) :
  scalingParameter R (s * t) = (scalingParameter R s) * (scalingParameter R t) := by
  simp [scalingParameter]
  ac_rfl

/-- Scaling by the unit 1 leaves the Hermitian parameter unchanged. -/
@[simp]
lemma scalingParameter_one : scalingParameter R 1 = 1 := by
  simp [scalingParameter]

/-- A duality comparison for the identity functor, with components `s • 𝟙`.
This is comparison data, not a functor between categories of Hermitian forms.
Transport uses the inverse comparison, so it scales forms by `s⁻¹`. -/
def scalingFunctorCat (s : Rˣ) : DualityComparison (Functor.id C) where
  nat_iso := NatIso.ofComponents
    (fun X =>
      { hom := (s : R) • 𝟙 (HermitianCategory.duality.obj X)
        inv := ((s⁻¹ : Rˣ) : R) • 𝟙 (HermitianCategory.duality.obj X)
        -- Inverse units give mutually inverse scalar multiples of the identity.
        hom_inv_id := by
          simp [Linear.comp_smul, smul_smul]
        inv_hom_id := by
          simp [Linear.comp_smul, smul_smul] })
    (by
      intro X Y f
      -- Bilinearity lets the scalar pass through either side of the naturality square.
      simp [Linear.smul_comp, Linear.comp_smul])

omit [Functor.Additive (HermitianCategory.duality (C := C))] in
/-- The scaling comparison satisfies the scalar-dependent coherence condition. -/
lemma scalingFunctorCat_hermitian (s : Rˣ) :
    HermitianFunctor R (Functor.id C)
      (scalingFunctorCat R s) (scalingParameter R s) := by
  intro M
  change (s : R) • 𝟙 _ =
    ((s * star (s⁻¹) : Rˣ) : R) •
      (HermitianCategory.duality.map
          ((s : R) • 𝟙 (HermitianCategory.duality.obj (op M))).op ≫
        HermitianCategory.doubleDualIso.inv.app M ≫
        HermitianCategory.doubleDualIso.hom.app M)
  rw [StarLinearDuality.map_smul]
  simp [smul_smul, mul_assoc, ← star_mul]

omit [StarRing R] [Functor.Additive (HermitianCategory.duality (C := C))]
    [StarLinearDuality R C] in
/-- Transport along the scaling comparison multiplies a form by the inverse unit. -/
@[simp] lemma scalingFunctorCat_mapSesq {M : C} (s : Rˣ) (h : Sesq M) :
    mapSesqForms (Functor.id C) (scalingFunctorCat R s) h =
      ((s⁻¹ : Rˣ) : R) • h := by
  simp [mapSesqForms, scalingFunctorCat, Linear.comp_smul]

/-- Scale forms by `s⁻¹`, changing their parameter by `s * star (s⁻¹)`.
The underlying objects and morphisms are unchanged. -/
def scalingHermitianCategories (s : Rˣ) (lam : Z1Mul R) :
    HermitianFormCat (C := C) R lam ⥤
      HermitianFormCat (C := C) R (scalingParameter R s * lam) :=
  functorHermitianCategories R (Functor.id C)
    (scalingFunctorCat R s) lam (scalingParameter R s)
    (scalingFunctorCat_hermitian R s)

/-- Scaling first by s and then by t is naturally isomorphic to scaling by t * s.
The cast identifies σ(t * s) * λ with σ(t) * (σ(s) * λ), so the functors have
the same target category. Both sides give the same underlying forms after
simplifying scalar multiplication; the components are identity isometries.
The result is a natural isomorphism (`≅`), rather than an equality of functors. -/
def scalingFunctorCompIso (s t : Rˣ) (lam : Z1Mul R) :
  (scalingHermitianCategories (C := C) R s lam) ⋙ (scalingHermitianCategories (C := C) R t ((scalingParameter R s) * lam)) ≅
  (scalingHermitianCategories (C:= C) R (t * s) lam) ⋙ castHermitianHermitianCategories R (by rw [scalingParameter_mul, mul_assoc]) :=
  NatIso.ofComponents
  (fun X =>
    {
      hom := ⟨𝟙 X.M, by
        constructor
        · exact IsIso.id (C := C) X.M
        · simp [scalingHermitianCategories, castHermitianHermitianCategories, functorHermitianCategories, mapHermitianObjects, mapHermitianForms]
          simp [smul_smul, mul_comm]
      ⟩
      inv := ⟨𝟙 X.M, by
        constructor
        · exact IsIso.id (C := C) X.M
        · simp [scalingHermitianCategories, castHermitianHermitianCategories, functorHermitianCategories, mapHermitianObjects, mapHermitianForms]
          simp [smul_smul, mul_comm]
      ⟩
      hom_inv_id := by
        apply Subtype.ext
        change 𝟙 X.M ≫ 𝟙 X.M = 𝟙 X.M
        simp
      inv_hom_id := by
        apply Subtype.ext
        change 𝟙 X.M ≫ 𝟙 X.M = 𝟙 X.M
        simp
    }
  )
  (by
    intro X Y f
    -- Both functors preserve the underlying morphism f.val, so naturality is an identity law.
    apply Subtype.ext
    change f.val ≫ 𝟙 Y.M = 𝟙 X.M ≫ f.val
    simp
  )

/-- Scaling by a unit gives an equivalence between the corresponding Hermitian categories.
The inverse uses the unit s⁻¹ and casts its resulting parameter back to λ.
The unit and counit are constructed directly from identity isometries. -/
lemma scalingFunctorIsEquivalence (s : Rˣ) (lam : Z1Mul R) :
  Functor.IsEquivalence (scalingHermitianCategories (C := C) R s lam) := by
  let sigma s := scalingParameter R s

  -- Multiplicativity of σ cancels the two parameter changes. The parentheses
  -- match the target parameter produced by the inverse scaling functor H below.
  have h_scalingParam : (sigma s⁻¹) * ((sigma s) * lam) = lam := by
    unfold sigma
    rw [← mul_assoc, ← scalingParameter_mul, inv_mul_cancel, scalingParameter_one, one_mul]

  let F := scalingHermitianCategories (C := C) R s lam
  -- H multiplies forms by s, undoing F's multiplication by s⁻¹.
  let H := scalingHermitianCategories (C := C) R s⁻¹ (sigma s * lam)
  -- K corrects the target parameter without changing the underlying forms or arrows.
  let K := castHermitianHermitianCategories (C:= C) R h_scalingParam
  let G := H ⋙ K

  -- The unit has source Id and target F ⋙ G, the orientation required by `mk'`.
  have h_eta : Functor.id (HermitianFormCat (C := C) R lam) ≅ F ⋙ G := by
    -- The two scalings cancel on forms, so each component is the identity on X.M.
    refine NatIso.ofComponents (fun X => {
      hom := ⟨𝟙 X.M, by
        constructor
        · exact IsIso.id (C := C) X.M
        · simp [F, G, H, K, scalingHermitianCategories, castHermitianHermitianCategories,
            functorHermitianCategories, mapHermitianObjects, mapHermitianForms, smul_smul]⟩
      inv := ⟨𝟙 X.M, by
        constructor
        · exact IsIso.id (C := C) X.M
        · simp [F, G, H, K, scalingHermitianCategories, castHermitianHermitianCategories,
            functorHermitianCategories, mapHermitianObjects, mapHermitianForms, smul_smul]⟩
      hom_inv_id := by
        -- Equality of bundled isometries reduces to equality of their underlying arrows.
        apply Subtype.ext
        change 𝟙 X.M ≫ 𝟙 X.M = 𝟙 X.M
        simp
      inv_hom_id := by
        apply Subtype.ext
        change 𝟙 X.M ≫ 𝟙 X.M = 𝟙 X.M
        simp
    }) ?_
    -- F and G act identically on underlying arrows, so identity components are natural.
    intro X Y f
    apply Subtype.ext
    change f.val ≫ 𝟙 Y.M = 𝟙 X.M ≫ f.val
    simp

  -- The counit lives in the target category, with parameter σ(s) * λ.
  have h_eps : G ⋙ F ≅ Functor.id (HermitianFormCat (C := C) R (sigma s * lam)) := by
    -- Cancellation in the other order gives the counit, again with identity components.
    refine NatIso.ofComponents (fun X => {
      hom := ⟨𝟙 X.M, by
        constructor
        · exact IsIso.id (C := C) X.M
        · simp [F, G, H, K, scalingHermitianCategories, castHermitianHermitianCategories,
            functorHermitianCategories, mapHermitianObjects, mapHermitianForms, smul_smul]⟩
      inv := ⟨𝟙 X.M, by
        constructor
        · exact IsIso.id (C := C) X.M
        · simp [F, G, H, K, scalingHermitianCategories, castHermitianHermitianCategories,
            functorHermitianCategories, mapHermitianObjects, mapHermitianForms, smul_smul]⟩
      hom_inv_id := by
        apply Subtype.ext
        change 𝟙 X.M ≫ 𝟙 X.M = 𝟙 X.M
        simp
      inv_hom_id := by
        apply Subtype.ext
        change 𝟙 X.M ≫ 𝟙 X.M = 𝟙 X.M
        simp
    }) ?_
    intro X Y f
    apply Subtype.ext
    change f.val ≫ 𝟙 Y.M = 𝟙 X.M ≫ f.val
    simp

  -- `mk'` derives full faithfulness and essential surjectivity from this inverse data;
  -- it does not require us to supply a separate triangle-identity proof.
  exact Functor.IsEquivalence.mk' G h_eta h_eps
