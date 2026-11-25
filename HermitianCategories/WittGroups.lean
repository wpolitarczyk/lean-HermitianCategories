/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import HermitianCategories.HermitianForms
import HermitianCategories.QuadraticForms

/-!
# Witt groups of Hermitian and (λ, Λ)-quadratic forms

This file constructs Witt groups for nonsingular λ-Hermitian forms and
`(λ, Λ)`-quadratic forms in a preadditive `R`-linear Hermitian category `C`
with binary biproducts and a zero object:

- **Generic stable quotient (`StableWittData`)**: packages orthogonal direct sums,
  zero, negation, and a class of metabolic objects, yielding the Witt equivalence
  setoid, `AddCommGroup` instance, and quotient API (`mk`, `mk_zero`, `mk_add`,
  `mk_neg`, `mk_eq_mk_iff`).
- **Metabolic objects**:
  - `IsSplitMetabolic`: existence of a split short exact sequence
    `0 ⟶ L ⟶ X.M ⟶ D(L) ⟶ 0` with `L` isotropic (works in any preadditive
    category with binary biproducts and a zero object).
  - `IsMetabolic` (requiring `[Abelian C]`): existence of an arbitrary short exact
    sequence `0 ⟶ L ⟶ X.M ⟶ D(L) ⟶ 0` with `L` isotropic.
  - `IsQuadraticMetabolic`: existence of a split short exact sequence
    `0 ⟶ L ⟶ X.M ⟶ D(L) ⟶ 0` with `L` quadratically isotropic
    (`pullbackQuadraticForm i X.form = 0`).
- **Witt groups and canonical comparison homomorphisms**:
  - `SplitHermitianWittGroup R lam`,
  - `HermitianWittGroup R lam` (for `[Abelian C]`),
  - `QuadraticWittGroup R Λ` (split quadratic Witt group),
  together with `splitWittToWitt` and `quadraticWittToSplitWitt` (an isomorphism
  when `R` admits a generalized half-unit or `TateCohomologyZeroAdd R` vanishes).
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject
open Opposite

universe v u

set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false

/-! ## Generic stable Witt quotient -/

section GenericWitt

/-- Abstract data for a Witt group: a category of objects equipped with a symmetric
monoidal-like orthogonal sum, zero, negation, and a metabolicity predicate. -/
structure StableWittData (α : Type*) [Category α] where
  add : α → α → α
  zero : α
  neg : α → α
  metabolic : α → Prop
  add_comm : ∀ x y, Nonempty (add x y ≅ add y x)
  add_assoc : ∀ x y z, Nonempty (add (add x y) z ≅ add x (add y z))
  zero_add : ∀ x, Nonempty (add zero x ≅ x)
  add_congr : ∀ {x₁ x₂ y₁ y₂}, (x₁ ≅ x₂) → (y₁ ≅ y₂) → (add x₁ y₁ ≅ add x₂ y₂)
  metabolic_zero : metabolic zero
  metabolic_self_add_neg : ∀ x, metabolic (add x (neg x))
  metabolic_add : ∀ {x y}, metabolic x → metabolic y → metabolic (add x y)
  metabolic_of_iso : ∀ {x y}, (x ≅ y) → metabolic x → metabolic y

/-- Stable isomorphism modulo metabolic objects:
`x ≈ y` iff `x ⊕ m₁ ≅ y ⊕ m₂` for some metabolic `m₁, m₂`. -/
def StableWittEquiv {α : Type*} [Category α] (W : StableWittData α) (x y : α) : Prop :=
  ∃ m₁ m₂ : α, W.metabolic m₁ ∧ W.metabolic m₂ ∧ Nonempty (W.add x m₁ ≅ W.add y m₂)

/-- The setoid associated to `StableWittEquiv`. -/
def stableWittSetoid {α : Type*} [Category α] (W : StableWittData α) : Setoid α where
  r := StableWittEquiv W
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨W.zero, W.zero, W.metabolic_zero, W.metabolic_zero, ⟨Iso.refl _⟩⟩
    · intro x y ⟨m₁, m₂, hm₁, hm₂, ⟨e⟩⟩
      exact ⟨m₂, m₁, hm₂, hm₁, ⟨e.symm⟩⟩
    · intro x y z ⟨m₁, m₂, hm₁, hm₂, ⟨e₁⟩⟩ ⟨n₁, n₂, hn₁, hn₂, ⟨e₂⟩⟩
      refine ⟨W.add m₁ n₁, W.add m₂ n₂,
        W.metabolic_add hm₁ hn₁, W.metabolic_add hm₂ hn₂, ⟨?_⟩⟩
      -- Rearrange `(x + m₁) + n₁ ≅ (y + m₂) + n₁ ≅ (y + n₁) + m₂ ≅ (z + n₂) + m₂ ≅ z + (n₂ + m₂) ≅ z + (m₂ + n₂)`.
      have a₁ := (W.add_assoc x m₁ n₁).some.symm
      have a₂ := W.add_congr e₁ (Iso.refl n₁)
      have a₃ := (W.add_assoc y m₂ n₁).some
      have a₄ := W.add_congr (Iso.refl y) (W.add_comm m₂ n₁).some
      have a₅ := (W.add_assoc y n₁ m₂).some.symm
      have a₆ := W.add_congr e₂ (Iso.refl m₂)
      have a₇ := (W.add_assoc z n₂ m₂).some
      have a₈ := W.add_congr (Iso.refl z) (W.add_comm n₂ m₂).some
      exact a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅ ≪≫ a₆ ≪≫ a₇ ≪≫ a₈

/-- The Witt group of `W` as the quotient of `α` by `stableWittSetoid W`. -/
abbrev GenericWittGroup {α : Type*} [Category α] (W : StableWittData α) : Type _ :=
  Quotient (stableWittSetoid W)

private lemma stableWittEquiv_of_iso {α : Type*} [Category α] {W : StableWittData α}
    {x y : α} (e : x ≅ y) : StableWittEquiv W x y :=
  ⟨W.zero, W.zero, W.metabolic_zero, W.metabolic_zero,
    ⟨W.add_congr e (Iso.refl W.zero)⟩⟩

noncomputable instance {α : Type*} [Category α] (W : StableWittData α) :
    Zero (GenericWittGroup W) :=
  ⟨Quotient.mk (stableWittSetoid W) W.zero⟩

noncomputable instance {α : Type*} [Category α] (W : StableWittData α) :
    Add (GenericWittGroup W) :=
  ⟨Quotient.map₂ W.add (fun _ _ ⟨m₁, m₂, hm₁, hm₂, ⟨e₁⟩⟩ _ _ ⟨n₁, n₂, hn₁, hn₂, ⟨e₂⟩⟩ => by
    refine ⟨W.add m₁ n₁, W.add m₂ n₂,
      W.metabolic_add hm₁ hn₁, W.metabolic_add hm₂ hn₂, ⟨?_⟩⟩
    have swap4 (a b c d : α) : Nonempty (W.add (W.add a b) (W.add c d) ≅ W.add (W.add a c) (W.add b d)) := by
      refine ⟨(W.add_assoc a b (W.add c d)).some ≪≫
        W.add_congr (Iso.refl a) ((W.add_assoc b c d).some.symm ≪≫
          W.add_congr (W.add_comm b c).some (Iso.refl d) ≪≫
          (W.add_assoc c b d).some) ≪≫
        (W.add_assoc a c (W.add b d)).some.symm⟩
    exact (swap4 _ _ _ _).some ≪≫ W.add_congr e₁ e₂ ≪≫ (swap4 _ _ _ _).some)⟩

noncomputable instance {α : Type*} [Category α] (W : StableWittData α) :
    Neg (GenericWittGroup W) :=
  ⟨Quotient.map W.neg (fun x y ⟨m₁, m₂, hm₁, hm₂, ⟨e⟩⟩ => by
    refine ⟨W.add m₂ (W.add y (W.neg y)), W.add m₁ (W.add x (W.neg x)),
      W.metabolic_add hm₂ (W.metabolic_self_add_neg y),
      W.metabolic_add hm₁ (W.metabolic_self_add_neg x), ⟨?_⟩⟩
    have s1 : W.add (W.neg x) (W.add m₂ (W.add y (W.neg y))) ≅
        W.add (W.add (W.neg x) (W.add y m₂)) (W.neg y) :=
      W.add_congr (Iso.refl _)
        ((W.add_assoc m₂ y (W.neg y)).some.symm ≪≫
          W.add_congr (W.add_comm m₂ y).some (Iso.refl _)) ≪≫
        (W.add_assoc (W.neg x) (W.add y m₂) (W.neg y)).some.symm
    have s2 : W.add (W.add (W.neg x) (W.add y m₂)) (W.neg y) ≅
        W.add (W.add (W.neg x) (W.add x m₁)) (W.neg y) :=
      W.add_congr (W.add_congr (Iso.refl _) e.symm) (Iso.refl _)
    have s3 : W.add (W.add (W.neg x) (W.add x m₁)) (W.neg y) ≅
        W.add (W.neg y) (W.add m₁ (W.add x (W.neg x))) :=
      W.add_congr ((W.add_assoc (W.neg x) x m₁).some.symm ≪≫
        W.add_congr (W.add_comm (W.neg x) x).some (Iso.refl m₁) ≪≫
        (W.add_comm (W.add x (W.neg x)) m₁).some) (Iso.refl (W.neg y)) ≪≫
        (W.add_comm (W.add m₁ (W.add x (W.neg x))) (W.neg y)).some
    exact s1 ≪≫ s2 ≪≫ s3)⟩

noncomputable instance {α : Type*} [Category α] (W : StableWittData α) :
    AddCommGroup (GenericWittGroup W) where
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro x y z
    exact Quotient.sound (stableWittEquiv_of_iso (W.add_assoc x y z).some)
  zero_add a := by
    refine Quotient.inductionOn a ?_
    intro x
    exact Quotient.sound (stableWittEquiv_of_iso (W.zero_add x).some)
  add_zero a := by
    refine Quotient.inductionOn a ?_
    intro x
    exact Quotient.sound (stableWittEquiv_of_iso ((W.add_comm x W.zero).some ≪≫ (W.zero_add x).some))
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by
    refine Quotient.inductionOn a ?_
    intro x
    apply Quotient.sound
    have hm : W.metabolic (W.add (W.neg x) x) :=
      W.metabolic_of_iso (W.add_comm x (W.neg x)).some (W.metabolic_self_add_neg x)
    exact ⟨W.zero, W.add (W.neg x) x, W.metabolic_zero, hm,
      ⟨(W.add_comm _ W.zero).some ≪≫ (W.zero_add _).some ≪≫ (W.zero_add _).some.symm⟩⟩
  add_comm a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    exact Quotient.sound (stableWittEquiv_of_iso (W.add_comm x y).some)

namespace GenericWittGroup

variable {α : Type*} [Category α] {W : StableWittData α}

/-- Quotient projection into `GenericWittGroup W`. -/
def mk (W : StableWittData α) (x : α) : GenericWittGroup W :=
  Quotient.mk (stableWittSetoid W) x

/-- The zero object represents `0` in `GenericWittGroup W`. -/
@[simp]
lemma mk_zero : mk W W.zero = 0 := rfl

/-- Orthogonal direct sum descends to addition in `GenericWittGroup W`. -/
@[simp]
lemma mk_add (x y : α) : mk W (W.add x y) = mk W x + mk W y := rfl

/-- Negation descends to additive inversion in `GenericWittGroup W`. -/
@[simp]
lemma mk_neg (x : α) : mk W (W.neg x) = -mk W x := rfl

/-- Two objects represent the same class in `GenericWittGroup W` iff they are stably equivalent. -/
lemma mk_eq_mk_iff {x y : α} :
    mk W x = mk W y ↔ StableWittEquiv W x y :=
  Quotient.eq (r := stableWittSetoid W)

/-- Every metabolic object represents `0` in `GenericWittGroup W`. -/
lemma mk_eq_zero_of_metabolic {x : α} (hx : W.metabolic x) : mk W x = 0 := by
  rw [← mk_zero, mk_eq_mk_iff]
  exact ⟨W.zero, x, W.metabolic_zero, hx,
    ⟨(W.add_comm x W.zero).some ≪≫ (W.zero_add x).some ≪≫ (W.zero_add x).some.symm⟩⟩

end GenericWittGroup

end GenericWitt

section NonAbelian

variable {C : Type u} [Category.{v} C] [HermitianCategory C] [Preadditive C]
variable (R : Type u) [CommRing R] [StarRing R] [Linear R C]
variable [Functor.Additive (HermitianCategory.duality (C := C))]
variable [StarLinearDuality R C]
variable [HasBinaryBiproducts C] [HasZeroObject C]

/-! ## Zero-object and biproduct helpers -/

section Helpers

omit [HermitianCategory C] [Preadditive C] [Linear R C]
  [Functor.Additive (HermitianCategory.duality (C := C))] [StarLinearDuality R C]
  [HasBinaryBiproducts C] [HasZeroObject C] in
/-- Any morphism whose source and target are zero objects is an isomorphism. -/
lemma isZero_iso_of_isZero {X Y : C} (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) :
    IsIso f :=
  ⟨⟨hY.to_ X, hX.eq_of_src _ _, hY.eq_of_tgt _ _⟩⟩

omit [Linear R C] [StarLinearDuality R C] [HasBinaryBiproducts C] in
/-- The duality functor sends a zero object to a zero object. -/
lemma isZero_duality_zero : IsZero ((HermitianCategory.duality (C := C)).obj (op (0 : C))) := by
  refine IsZero.mk (fun Y => ⟨{ default := 0, uniq := fun f => ?_ }⟩)
    (fun Y => ⟨{ default := 0, uniq := fun f => ?_ }⟩)
  · have hid : 𝟙 ((HermitianCategory.duality (C := C)).obj (op (0 : C))) = 0 := by
      rw [← CategoryTheory.Functor.map_id, (isZero_zero C).op.eq_of_src (𝟙 (op (0 : C))) 0,
        CategoryTheory.Functor.map_zero]
    rw [← Category.id_comp f, hid, Limits.zero_comp]
  · have hid : 𝟙 ((HermitianCategory.duality (C := C)).obj (op (0 : C))) = 0 := by
      rw [← CategoryTheory.Functor.map_id, (isZero_zero C).op.eq_of_src (𝟙 (op (0 : C))) 0,
        CategoryTheory.Functor.map_zero]
    rw [← Category.comp_id f, hid, Limits.comp_zero]

/-- Canonical duality comparison isomorphism `D(L₁ ⊞ L₂) ≅ D(L₁) ⊞ D(L₂)`
for an additive contravariant duality functor. -/
noncomputable def dualityBiprodIso (L₁ L₂ : C) :
    (HermitianCategory.duality (C := C)).obj (op (L₁ ⊞ L₂)) ≅
      (HermitianCategory.duality (C := C)).obj (op L₁) ⊞
        (HermitianCategory.duality (C := C)).obj (op L₂) where
  hom := biprod.lift
    ((HermitianCategory.duality (C := C)).map biprod.inl.op)
    ((HermitianCategory.duality (C := C)).map biprod.inr.op)
  inv := biprod.desc
    ((HermitianCategory.duality (C := C)).map biprod.fst.op)
    ((HermitianCategory.duality (C := C)).map biprod.snd.op)
  hom_inv_id := by
    rw [biprod.lift_desc, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← op_comp, ← op_comp, ← CategoryTheory.Functor.map_add, ← op_add, biprod.total,
      op_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    ext <;> simp [← CategoryTheory.Functor.map_comp, ← op_comp]

/-- Componentwise biproduct of two split short complexes. -/
noncomputable def splittingBiprod {S₁ S₂ : ShortComplex C}
    (s₁ : S₁.Splitting) (s₂ : S₂.Splitting) :
    (ShortComplex.mk (biprod.map S₁.f S₂.f) (biprod.map S₁.g S₂.g) (by
      ext <;> simp)).Splitting where
  r := biprod.map s₁.r s₂.r
  s := biprod.map s₁.s s₂.s
  f_r := by ext <;> simp
  s_g := by ext <;> simp
  id := by
    ext <;> simp [← Preadditive.comp_add, s₁.id, s₂.id]

end Helpers

/-! ## Orthogonal direct sums, zero, and negation -/

section Operations

/-- Orthogonal direct sum of two sesquilinear forms on `M ⊞ N`. -/
noncomputable def sesqBiprod {M N : C} (hM : Sesq M) (hN : Sesq N) : Sesq (M ⊞ N) :=
  biprod.fst ≫ hM ≫ HermitianCategory.duality.map biprod.fst.op +
    biprod.snd ≫ hN ≫ HermitianCategory.duality.map biprod.snd.op

omit [HasZeroObject C] in
/-- Orthogonal direct sum of nonsingular sesquilinear forms is nonsingular. -/
lemma sesqBiprod_isNonSingular {M N : C} {hM : Sesq M} {hN : Sesq N}
    (hM_iso : isNonSingular hM) (hN_iso : isNonSingular hN) :
    isNonSingular (sesqBiprod hM hN) := by
  have : IsIso hM := hM_iso
  have : IsIso hN := hN_iso
  have map_comp_assoc : ∀ {A B C₀ : Cᵒᵖ} (f : A ⟶ B) (g : B ⟶ C₀) {Z : C}
      (k : (HermitianCategory.duality (C := C)).obj C₀ ⟶ Z),
      (HermitianCategory.duality (C := C)).map f ≫
        (HermitianCategory.duality (C := C)).map g ≫ k =
        (HermitianCategory.duality (C := C)).map (f ≫ g) ≫ k := by
    intro A B C₀ f g Z k
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  refine ⟨⟨HermitianCategory.duality.map biprod.inl.op ≫ inv hM ≫ biprod.inl +
      HermitianCategory.duality.map biprod.inr.op ≫ inv hN ≫ biprod.inr, ?_, ?_⟩⟩
  · simp [sesqBiprod, Preadditive.comp_add, Preadditive.add_comp,
      map_comp_assoc, ← op_comp]
  · simp only [sesqBiprod, Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_fst_assoc, biprod.inr_snd_assoc,
      Limits.zero_comp]
    simp only [Limits.comp_zero, add_zero, zero_add]
    simp only [IsIso.inv_hom_id_assoc]
    rw [← CategoryTheory.Functor.map_comp, ← op_comp,
      ← CategoryTheory.Functor.map_comp, ← op_comp,
      ← CategoryTheory.Functor.map_add, ← op_add, biprod.total, op_id,
      CategoryTheory.Functor.map_id]

omit [StarLinearDuality R C] [HasZeroObject C] in
/-- Orthogonal direct sum of `λ`-Hermitian forms is `λ`-Hermitian. -/
lemma sesqBiprod_isLambdaHermitian {M N : C} {lam : Z1Mul R}
    {hM : Sesq M} {hN : Sesq N}
    (hhM : IsLambdaHermitian R lam hM) (hhN : IsLambdaHermitian R lam hN) :
    IsLambdaHermitian R lam (sesqBiprod hM hN) := by
  rw [IsLambdaHermitian, sesqBiprod, formDual_add, formDual_pullback, formDual_pullback,
    hhM, hhN, Linear.smul_comp, Linear.comp_smul, Linear.smul_comp, Linear.comp_smul, ← smul_add]

/-- Orthogonal direct sum of two nonsingular `λ`-Hermitian objects. -/
noncomputable def hermitianBiprod {lam : Z1Mul R}
    (X Y : HermitianObject (C := C) R lam) : HermitianObject (C := C) R lam where
  M := X.M ⊞ Y.M
  form := ⟨sesqBiprod X.form.val Y.form.val,
    sesqBiprod_isLambdaHermitian R X.form.property Y.form.property⟩
  nonsingular := sesqBiprod_isNonSingular X.nonsingular Y.nonsingular

/-- The zero `λ`-Hermitian object. -/
noncomputable def hermitianZero (lam : Z1Mul R) : HermitianObject (C := C) R lam where
  M := (0 : C)
  form := 0
  nonsingular := by
    have hZ : IsZero ((HermitianCategory.duality (C := C)).obj (op (0 : C))) := isZero_duality_zero
    exact isZero_iso_of_isZero (isZero_zero C) hZ (0 : Sesq (0 : C))

/-- Negation `-X` of a nonsingular `λ`-Hermitian object. -/
def hermitianNeg {lam : Z1Mul R}
    (X : HermitianObject (C := C) R lam) : HermitianObject (C := C) R lam where
  M := X.M
  form := -X.form
  nonsingular := by
    change IsIso (-X.form.val)
    have : IsIso X.form.val := X.nonsingular
    refine ⟨⟨-inv X.form.val, by simp, by simp⟩⟩

/-- Orthogonal direct sum of two nonsingular `(λ, Λ)`-quadratic objects. -/
noncomputable def quadraticBiprod {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X Y : QuadraticObject (C := C) R Λ) : QuadraticObject (C := C) R Λ where
  M := X.M ⊞ Y.M
  form := pullbackQuadraticForm R Λ biprod.fst X.form +
    pullbackQuadraticForm R Λ biprod.snd Y.form
  nonsingular := by
    change IsIso (associatedHermitian R Λ (X.M ⊞ Y.M)
      (pullbackQuadraticForm R Λ biprod.fst X.form +
        pullbackQuadraticForm R Λ biprod.snd Y.form)).val
    rw [map_add]
    change IsIso
      ((associatedHermitian R Λ (X.M ⊞ Y.M) (pullbackQuadraticForm R Λ biprod.fst X.form)).val +
        (associatedHermitian R Λ (X.M ⊞ Y.M) (pullbackQuadraticForm R Λ biprod.snd Y.form)).val)
    rw [associatedHermitian_pullback, associatedHermitian_pullback]
    exact sesqBiprod_isNonSingular X.nonsingular Y.nonsingular

/-- The zero `(λ, Λ)`-quadratic object. -/
noncomputable def quadraticZero {lam : Z1Mul R} (Λ : FormParameter (C := C) R lam) :
    QuadraticObject (C := C) R Λ where
  M := (0 : C)
  form := 0
  nonsingular := by
    change IsIso (associatedHermitian R Λ (0 : C) 0).val
    rw [map_zero]
    exact isZero_iso_of_isZero (isZero_zero C) (isZero_duality_zero) (0 : Sesq (0 : C))

/-- Negation `-X` of a nonsingular `(λ, Λ)`-quadratic object. -/
def quadraticNeg {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X : QuadraticObject (C := C) R Λ) : QuadraticObject (C := C) R Λ where
  M := X.M
  form := -X.form
  nonsingular := by
    change IsIso (associatedHermitian R Λ X.M (-X.form)).val
    rw [map_neg]
    have : IsIso (associatedHermitian R Λ X.M X.form).val := X.nonsingular
    refine ⟨⟨-inv (associatedHermitian R Λ X.M X.form).val, by simp, by simp⟩⟩

-- Standard isomorphisms for orthogonal direct sums.

/-- Symmetry isometry `X ⊞ Y ≅ Y ⊞ X` for `λ`-Hermitian objects. -/
noncomputable def hermitianBiprodComm {lam : Z1Mul R}
    (X Y : HermitianObject (C := C) R lam) :
    hermitianBiprod R X Y ≅ hermitianBiprod R Y X := by
  let e := biprod.braiding X.M Y.M
  let f : hermitianBiprod R X Y ⟶ hermitianBiprod R Y X :=
    ⟨e.hom, Iso.isIso_hom e, by
      simp [e, hermitianBiprod, sesqBiprod, ← Functor.map_comp, ← op_comp,
        Preadditive.comp_add, Preadditive.add_comp, add_comm]⟩
  exact asIso f

/-- Associativity isometry `(X ⊞ Y) ⊞ Z ≅ X ⊞ (Y ⊞ Z)` for `λ`-Hermitian objects. -/
noncomputable def hermitianBiprodAssoc {lam : Z1Mul R}
    (X Y Z : HermitianObject (C := C) R lam) :
    hermitianBiprod R (hermitianBiprod R X Y) Z ≅
      hermitianBiprod R X (hermitianBiprod R Y Z) := by
  let e := biprod.associator X.M Y.M Z.M
  let f : hermitianBiprod R (hermitianBiprod R X Y) Z ⟶
      hermitianBiprod R X (hermitianBiprod R Y Z) :=
    ⟨e.hom, Iso.isIso_hom e, by
      simp [e, hermitianBiprod, sesqBiprod, ← Functor.map_comp, ← op_comp,
        Preadditive.comp_add, Preadditive.add_comp, add_assoc]⟩
  exact asIso f

/-- Left unit isometry `0 ⊞ X ≅ X` for `λ`-Hermitian objects. -/
noncomputable def hermitianZeroBiprod {lam : Z1Mul R}
    (X : HermitianObject (C := C) R lam) :
    hermitianBiprod R (hermitianZero R lam) X ≅ X := by
  let e := isoZeroBiprod (X := (0 : C)) (Y := X.M) (isZero_zero C)
  let f : hermitianBiprod R (hermitianZero R lam) X ⟶ X :=
    ⟨e.inv, Iso.isIso_inv e, by
      simp [e, hermitianBiprod, hermitianZero, sesqBiprod]⟩
  exact asIso f

/-- Congruence isometry on orthogonal direct sums of `λ`-Hermitian objects. -/
noncomputable def hermitianBiprodCongr {lam : Z1Mul R}
    {X₁ X₂ Y₁ Y₂ : HermitianObject (C := C) R lam}
    (e₁ : X₁ ≅ X₂) (e₂ : Y₁ ≅ Y₂) :
    hermitianBiprod R X₁ Y₁ ≅ hermitianBiprod R X₂ Y₂ := by
  letI : IsIso e₁.hom.val := e₁.hom.property.1
  letI : IsIso e₂.hom.val := e₂.hom.property.1
  let e := biprod.mapIso (asIso e₁.hom.val) (asIso e₂.hom.val)
  let f : hermitianBiprod R X₁ Y₁ ⟶ hermitianBiprod R X₂ Y₂ :=
    ⟨e.hom, Iso.isIso_hom e, by
      dsimp only [hermitianBiprod, sesqBiprod]
      simp only [e, Preadditive.comp_add, Preadditive.add_comp,
        biprod.mapIso_hom, asIso_hom, Category.assoc,
        biprod.map_fst_assoc, biprod.map_snd_assoc]
      simp only [← Functor.map_comp, ← op_comp, biprod.map_fst, biprod.map_snd]
      simp only [op_comp, Functor.map_comp]
      have h₁ : (e₁.hom.val : X₁.M ⟶ X₂.M) ≫ X₂.form.val ≫
          HermitianCategory.duality.map (e₁.hom.val : X₁.M ⟶ X₂.M).op = X₁.form.val :=
        e₁.hom.property.2
      have h₂ : (e₂.hom.val : Y₁.M ⟶ Y₂.M) ≫ Y₂.form.val ≫
          HermitianCategory.duality.map (e₂.hom.val : Y₁.M ⟶ Y₂.M).op = Y₁.form.val :=
        e₂.hom.property.2
      have h₁' : (e₁.hom.val : X₁.M ⟶ X₂.M) ≫ X₂.form.val ≫
          HermitianCategory.duality.map (e₁.hom.val : X₁.M ⟶ X₂.M).op ≫
          HermitianCategory.duality.map (biprod.fst : X₁.M ⊞ Y₁.M ⟶ X₁.M).op =
          X₁.form.val ≫ HermitianCategory.duality.map (biprod.fst : X₁.M ⊞ Y₁.M ⟶ X₁.M).op := by
        rw [← Category.assoc X₂.form.val, ← Category.assoc e₁.hom.val, h₁]
      have h₂' : (e₂.hom.val : Y₁.M ⟶ Y₂.M) ≫ Y₂.form.val ≫
          HermitianCategory.duality.map (e₂.hom.val : Y₁.M ⟶ Y₂.M).op ≫
          HermitianCategory.duality.map (biprod.snd : X₁.M ⊞ Y₁.M ⟶ Y₁.M).op =
          Y₁.form.val ≫ HermitianCategory.duality.map (biprod.snd : X₁.M ⊞ Y₁.M ⟶ Y₁.M).op := by
        rw [← Category.assoc Y₂.form.val, ← Category.assoc e₂.hom.val, h₂]
      rw [h₁', h₂']⟩
  exact asIso f

/-- Symmetry isometry `X ⊞ Y ≅ Y ⊞ X` for `(λ, Λ)`-quadratic objects. -/
noncomputable def quadraticBiprodComm {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X Y : QuadraticObject (C := C) R Λ) :
    quadraticBiprod R X Y ≅ quadraticBiprod R Y X := by
  let e := biprod.braiding X.M Y.M
  let f : quadraticBiprod R X Y ⟶ quadraticBiprod R Y X :=
    ⟨e.hom, Iso.isIso_hom e, by
      change pullbackQuadraticForm R Λ e.hom
        (pullbackQuadraticForm R Λ biprod.fst Y.form +
          pullbackQuadraticForm R Λ biprod.snd X.form) =
        pullbackQuadraticForm R Λ biprod.fst X.form +
          pullbackQuadraticForm R Λ biprod.snd Y.form
      rw [map_add, ← pullbackQuadraticForm_comp, ← pullbackQuadraticForm_comp]
      simp [e, add_comm]⟩
  exact asIso f

/-- Associativity isometry `(X ⊞ Y) ⊞ Z ≅ X ⊞ (Y ⊞ Z)` for `(λ, Λ)`-quadratic objects. -/
noncomputable def quadraticBiprodAssoc {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X Y Z : QuadraticObject (C := C) R Λ) :
    quadraticBiprod R (quadraticBiprod R X Y) Z ≅
      quadraticBiprod R X (quadraticBiprod R Y Z) := by
  let e := biprod.associator X.M Y.M Z.M
  let f : quadraticBiprod R (quadraticBiprod R X Y) Z ⟶
      quadraticBiprod R X (quadraticBiprod R Y Z) :=
    ⟨e.hom, Iso.isIso_hom e, by
      change pullbackQuadraticForm R Λ e.hom
        (pullbackQuadraticForm R Λ (biprod.fst : X.M ⊞ Y.M ⊞ Z.M ⟶ X.M) X.form +
          pullbackQuadraticForm R Λ (biprod.snd : X.M ⊞ Y.M ⊞ Z.M ⟶ Y.M ⊞ Z.M)
            (pullbackQuadraticForm R Λ (biprod.fst : Y.M ⊞ Z.M ⟶ Y.M) Y.form +
              pullbackQuadraticForm R Λ (biprod.snd : Y.M ⊞ Z.M ⟶ Z.M) Z.form)) =
        pullbackQuadraticForm R Λ (biprod.fst : (X.M ⊞ Y.M) ⊞ Z.M ⟶ X.M ⊞ Y.M)
            (pullbackQuadraticForm R Λ (biprod.fst : X.M ⊞ Y.M ⟶ X.M) X.form +
              pullbackQuadraticForm R Λ (biprod.snd : X.M ⊞ Y.M ⟶ Y.M) Y.form) +
          pullbackQuadraticForm R Λ (biprod.snd : (X.M ⊞ Y.M) ⊞ Z.M ⟶ Z.M) Z.form
      simp only [map_add]
      rw [← pullbackQuadraticForm_comp, ← pullbackQuadraticForm_comp,
        ← pullbackQuadraticForm_comp, ← pullbackQuadraticForm_comp,
        ← pullbackQuadraticForm_comp, ← pullbackQuadraticForm_comp,
        ← pullbackQuadraticForm_comp]
      simp [e, add_assoc]⟩
  exact asIso f

/-- Left unit isometry `0 ⊞ X ≅ X` for `(λ, Λ)`-quadratic objects. -/
noncomputable def quadraticZeroBiprod {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X : QuadraticObject (C := C) R Λ) :
    quadraticBiprod R (quadraticZero R Λ) X ≅ X := by
  let e := isoZeroBiprod (X := (0 : C)) (Y := X.M) (isZero_zero C)
  let f : quadraticBiprod R (quadraticZero R Λ) X ⟶ X :=
    ⟨e.inv, Iso.isIso_inv e, by
      dsimp [quadraticBiprod, quadraticZero]
      rw [map_zero, zero_add]
      simp [e]
      rfl⟩
  exact asIso f

/-- Congruence isometry on orthogonal direct sums of `(λ, Λ)`-quadratic objects. -/
noncomputable def quadraticBiprodCongr {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    {X₁ X₂ Y₁ Y₂ : QuadraticObject (C := C) R Λ}
    (e₁ : X₁ ≅ X₂) (e₂ : Y₁ ≅ Y₂) :
    quadraticBiprod R X₁ Y₁ ≅ quadraticBiprod R X₂ Y₂ := by
  letI : IsIso e₁.hom.val := e₁.hom.property.1
  letI : IsIso e₂.hom.val := e₂.hom.property.1
  let e := biprod.mapIso (asIso e₁.hom.val) (asIso e₂.hom.val)
  let f : quadraticBiprod R X₁ Y₁ ⟶ quadraticBiprod R X₂ Y₂ :=
    ⟨e.hom, Iso.isIso_hom e, by
      change pullbackQuadraticForm R Λ e.hom
        (pullbackQuadraticForm R Λ biprod.fst X₂.form +
          pullbackQuadraticForm R Λ biprod.snd Y₂.form) =
        pullbackQuadraticForm R Λ biprod.fst X₁.form +
          pullbackQuadraticForm R Λ biprod.snd Y₁.form
      rw [map_add, ← pullbackQuadraticForm_comp,
        ← pullbackQuadraticForm_comp]
      simp only [e, biprod.mapIso_hom, biprod.map_fst, biprod.map_snd, asIso_hom]
      rw [pullbackQuadraticForm_comp, e₁.hom.property.2,
        pullbackQuadraticForm_comp, e₂.hom.property.2]⟩
  exact asIso f

-- Symmetrization compatibility with zero, negation, and orthogonal direct sums.

omit [HasBinaryBiproducts C] in
lemma symmetrizationFunctor_obj_zero {lam : Z1Mul R} (Λ : FormParameter (C := C) R lam) :
    (symmetrizationFunctor R Λ).obj (quadraticZero R Λ) = hermitianZero R lam := by
  change HermitianObject.mk (0 : C)
      ((associatedHermitian R Λ (0 : C)) 0) _ =
    HermitianObject.mk (0 : C) 0 _
  congr
  exact map_zero (associatedHermitian R Λ (0 : C))

omit [HasBinaryBiproducts C] [HasZeroObject C] in
lemma symmetrizationFunctor_obj_neg {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X : QuadraticObject (C := C) R Λ) :
    (symmetrizationFunctor R Λ).obj (quadraticNeg R X) =
      hermitianNeg R ((symmetrizationFunctor R Λ).obj X) := by
  change HermitianObject.mk X.M
      ((associatedHermitian R Λ X.M) (-X.form)) _ =
    HermitianObject.mk X.M
      (-((associatedHermitian R Λ X.M) X.form)) _
  congr
  exact map_neg (associatedHermitian R Λ X.M) X.form

omit [HasZeroObject C] in
lemma symmetrizationFunctor_obj_biprod {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X Y : QuadraticObject (C := C) R Λ) :
    (symmetrizationFunctor R Λ).obj (quadraticBiprod R X Y) =
      hermitianBiprod R ((symmetrizationFunctor R Λ).obj X)
        ((symmetrizationFunctor R Λ).obj Y) := by
  change HermitianObject.mk (X.M ⊞ Y.M)
      ((associatedHermitian R Λ (X.M ⊞ Y.M))
        (pullbackQuadraticForm R Λ biprod.fst X.form +
          pullbackQuadraticForm R Λ biprod.snd Y.form)) _ =
    HermitianObject.mk (X.M ⊞ Y.M)
      ⟨sesqBiprod
        ((associatedHermitian R Λ X.M) X.form).val
        ((associatedHermitian R Λ Y.M) Y.form).val, _⟩ _
  congr
  apply Subtype.ext
  rw [map_add, AddSubgroup.coe_add, associatedHermitian_pullback,
    associatedHermitian_pullback]
  rfl

end Operations
