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

/-! ## Metabolizers and metabolic objects -/

section Metabolic

/-- The short complex `L ⟶ X.M ⟶ D(L)` associated to an isotropic morphism `i : L ⟶ X.M`. -/
def hermitianMetabolizerComplex {lam : Z1Mul R}
    (X : HermitianObject (C := C) R lam) {L : C} (i : L ⟶ X.M)
    (hi : i ≫ X.form.val ≫ HermitianCategory.duality.map i.op = 0) :
    ShortComplex C :=
  ShortComplex.mk i (X.form.val ≫ HermitianCategory.duality.map i.op) hi

/-- A `λ`-Hermitian object is split-metabolic if it admits a split metabolizer,
i.e., a split short exact sequence `0 ⟶ L ⟶ X.M ⟶ D(L) ⟶ 0` with `L` isotropic. -/
def IsSplitMetabolic {lam : Z1Mul R} (X : HermitianObject (C := C) R lam) : Prop :=
  ∃ (L : C) (i : L ⟶ X.M) (hi : i ≫ X.form.val ≫ HermitianCategory.duality.map i.op = 0),
    Nonempty (hermitianMetabolizerComplex R X i hi).Splitting

/-- A `(λ, Λ)`-quadratic object is metabolic if it admits a split metabolizer `i : L ⟶ X.M`
that is quadratically isotropic (`pullbackQuadraticForm i X.form = 0`). -/
def IsQuadraticMetabolic {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X : QuadraticObject (C := C) R Λ) : Prop :=
  ∃ (L : C) (i : L ⟶ X.M) (hi : pullbackQuadraticForm R Λ i X.form = 0),
    Nonempty (hermitianMetabolizerComplex R ((symmetrizationFunctor R Λ).obj X) i (by
      have h := congrArg (fun q => (associatedHermitian R Λ L q).val) hi
      rw [associatedHermitian_pullback, map_zero] at h
      exact h)).Splitting

omit [HasBinaryBiproducts C] [HasZeroObject C] in
/-- A quadratic-metabolic object has split-metabolic associated Hermitian form. -/
lemma IsQuadraticMetabolic.toSplitMetabolic {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    {X : QuadraticObject (C := C) R Λ} (hX : IsQuadraticMetabolic R X) :
    IsSplitMetabolic R ((symmetrizationFunctor R Λ).obj X) := by
  rcases hX with ⟨L, i, hi, hs⟩
  exact ⟨L, i, _, hs⟩

omit [HasBinaryBiproducts C] [HasZeroObject C] in
/-- When `R` has a generalized half-unit, split-metabolicity of `symmetrizationFunctor.obj X`
is equivalent to quadratic metabolicity of `X`. -/
lemma isQuadraticMetabolic_iff_isSplitMetabolic_of_halfUnit {lam : Z1Mul R}
    {Λ : FormParameter (C := C) R lam} (hhalf : ∃ r : R, isGeneralizedHalfUnit R r)
    (X : QuadraticObject (C := C) R Λ) :
    IsQuadraticMetabolic R X ↔ IsSplitMetabolic R ((symmetrizationFunctor R Λ).obj X) := by
  constructor
  · exact IsQuadraticMetabolic.toSplitMetabolic R
  · rintro ⟨L, i, hi, hs⟩
    change L ⟶ X.M at i
    refine ⟨L, i, ?_, hs⟩
    apply (associatedHermitian_bijective_of_halfUnit R Λ hhalf L).1
    apply Subtype.ext
    rw [associatedHermitian_pullback, map_zero]
    exact hi

omit [StarLinearDuality R C] [HasBinaryBiproducts C] in
/-- The zero `λ`-Hermitian object is split-metabolic. -/
lemma isSplitMetabolic_zero (lam : Z1Mul R) :
    IsSplitMetabolic R (hermitianZero (C := C) R lam) := by
  refine ⟨0, 0, by simp only [Limits.zero_comp], ?_⟩
  exact ⟨ShortComplex.Splitting.ofIsZero _
    (isZero_zero C) (isZero_zero C) (isZero_duality_zero (C := C))⟩

omit [StarLinearDuality R C] [HasZeroObject C] in
/-- `X ⊞ (-X)` is split-metabolic via the diagonal metabolizer `Δ : X.M ⟶ X.M ⊞ X.M`. -/
lemma isSplitMetabolic_self_add_neg {lam : Z1Mul R}
    (X : HermitianObject (C := C) R lam) :
    IsSplitMetabolic R (hermitianBiprod R X (hermitianNeg R X)) := by
  let i : X.M ⟶ X.M ⊞ X.M := biprod.lift (𝟙 X.M) (𝟙 X.M)
  let g : X.M ⊞ X.M ⟶ (HermitianCategory.duality (C := C)).obj (op X.M) :=
    (hermitianBiprod R X (hermitianNeg R X)).form.val ≫
      HermitianCategory.duality.map i.op
  have hi : i ≫ g = 0 := by
    simp [g, i, hermitianBiprod, hermitianNeg, sesqBiprod,
      Preadditive.comp_add, Preadditive.add_comp, ← Functor.map_comp, ← op_comp]
  refine ⟨X.M, i, hi, ⟨?_⟩⟩
  have : IsIso X.form.val := X.nonsingular
  refine {
    r := biprod.fst
    s := -inv X.form.val ≫ biprod.inr
    f_r := by
      change i ≫ (biprod.fst : X.M ⊞ X.M ⟶ X.M) = 𝟙 X.M
      simp [i]
    s_g := by
      change (-inv X.form.val ≫ (biprod.inr : X.M ⟶ X.M ⊞ X.M)) ≫ g = 𝟙 _
      simp [g, i, hermitianBiprod, hermitianNeg, sesqBiprod,
        Preadditive.comp_add, Preadditive.add_comp, ← Functor.map_comp, ← op_comp]
    id := by
      change (biprod.fst : X.M ⊞ X.M ⟶ X.M) ≫ i +
        g ≫ (-inv X.form.val ≫ (biprod.inr : X.M ⟶ X.M ⊞ X.M)) =
          𝟙 (X.M ⊞ X.M)
      ext <;>
        simp [g, i, hermitianBiprod, hermitianNeg, sesqBiprod,
          Preadditive.comp_add, Preadditive.add_comp, ← Functor.map_comp, ← op_comp] }

omit [StarLinearDuality R C] [HasZeroObject C] in
/-- Split-metabolicity is closed under orthogonal direct sums. -/
lemma isSplitMetabolic_biprod {lam : Z1Mul R}
    {X Y : HermitianObject (C := C) R lam}
    (hX : IsSplitMetabolic R X) (hY : IsSplitMetabolic R Y) :
    IsSplitMetabolic R (hermitianBiprod R X Y) := by
  rcases hX with ⟨L₁, i₁, hi₁, ⟨s₁⟩⟩
  rcases hY with ⟨L₂, i₂, hi₂, ⟨s₂⟩⟩
  let i : L₁ ⊞ L₂ ⟶ X.M ⊞ Y.M := biprod.map i₁ i₂
  have hi : i ≫ (hermitianBiprod R X Y).form.val ≫
      HermitianCategory.duality.map i.op = 0 := by
    dsimp [i]
    ext <;>
      simp only [hermitianBiprod, sesqBiprod, Preadditive.comp_add,
        Preadditive.add_comp, Category.assoc, biprod.map_fst_assoc,
        biprod.map_snd_assoc, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
        biprod.inr_fst_assoc, biprod.inr_snd_assoc, Limits.zero_comp,
        Limits.comp_zero, add_zero, zero_add]
    · rw [← Functor.map_comp, ← op_comp, biprod.map_fst,
        op_comp, Functor.map_comp]
      simpa using (reassoc_of% hi₁)
        (HermitianCategory.duality.map (biprod.fst : L₁ ⊞ L₂ ⟶ L₁).op)
    · rw [← Functor.map_comp, ← op_comp, biprod.map_snd,
        op_comp, Functor.map_comp]
      simpa using (reassoc_of% hi₂)
        (HermitianCategory.duality.map (biprod.snd : L₁ ⊞ L₂ ⟶ L₂).op)
  refine ⟨L₁ ⊞ L₂, i, hi, ⟨?_⟩⟩
  let g₁ := X.form.val ≫ HermitianCategory.duality.map i₁.op
  let g₂ := Y.form.val ≫ HermitianCategory.duality.map i₂.op
  let S := ShortComplex.mk (biprod.map i₁ i₂) (biprod.map g₁ g₂) (by
    ext <;> simp [g₁, g₂, hi₁, hi₂])
  have s : S.Splitting := splittingBiprod s₁ s₂
  apply ShortComplex.Splitting.ofIso s
  refine ShortComplex.isoMk
    (S₁ := S) (S₂ := hermitianMetabolizerComplex R (hermitianBiprod R X Y) i hi)
    (Iso.refl _) (Iso.refl _) (dualityBiprodIso L₁ L₂).symm ?_ ?_
  · change (𝟙 _) ≫ biprod.map i₁ i₂ = biprod.map i₁ i₂ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · ext <;>
      simp [S, i, g₁, g₂, hermitianMetabolizerComplex, hermitianBiprod, sesqBiprod,
        dualityBiprodIso, Preadditive.comp_add, Preadditive.add_comp,
        ← Functor.map_comp, ← op_comp]

omit [StarLinearDuality R C] [HasBinaryBiproducts C] [HasZeroObject C] in
/-- Split-metabolicity is invariant under isometry. -/
lemma isSplitMetabolic_of_iso {lam : Z1Mul R}
    {X Y : HermitianObject (C := C) R lam} (e : X ≅ Y)
    (hX : IsSplitMetabolic R X) : IsSplitMetabolic R Y := by
  rcases hX with ⟨L, i, hi, ⟨s⟩⟩
  let eM : X.M ≅ Y.M :=
    { hom := e.hom.val
      inv := e.inv.val
      hom_inv_id := congrArg Subtype.val e.hom_inv_id
      inv_hom_id := congrArg Subtype.val e.inv_hom_id }
  let j : L ⟶ Y.M := i ≫ eM.hom
  have he : eM.hom ≫ Y.form.val ≫ HermitianCategory.duality.map eM.hom.op =
      X.form.val := e.hom.property.2
  have hj : j ≫ Y.form.val ≫ HermitianCategory.duality.map j.op = 0 := by
    calc
      j ≫ Y.form.val ≫ HermitianCategory.duality.map j.op =
          i ≫ (eM.hom ≫ Y.form.val ≫ HermitianCategory.duality.map eM.hom.op) ≫
            HermitianCategory.duality.map i.op := by
              simp only [j, op_comp, Functor.map_comp, Category.assoc]
      _ = i ≫ X.form.val ≫ HermitianCategory.duality.map i.op := by rw [he]
      _ = 0 := hi
  refine ⟨L, j, hj, ⟨?_⟩⟩
  apply ShortComplex.Splitting.ofIso s
  refine ShortComplex.isoMk
    (S₁ := hermitianMetabolizerComplex R X i hi)
    (S₂ := hermitianMetabolizerComplex R Y j hj)
    (Iso.refl _) eM (Iso.refl _) ?_ ?_
  · change (𝟙 L) ≫ j = i ≫ eM.hom
    simp [j]
  · change eM.hom ≫ (Y.form.val ≫ HermitianCategory.duality.map j.op) =
      (X.form.val ≫ HermitianCategory.duality.map i.op) ≫ 𝟙 _
    simp only [j, op_comp, Functor.map_comp, Category.comp_id]
    simpa using (reassoc_of% he) (HermitianCategory.duality.map i.op)

omit [HasBinaryBiproducts C] in
/-- The zero `(λ, Λ)`-quadratic object is quadratic-metabolic. -/
lemma isQuadraticMetabolic_zero {lam : Z1Mul R} (Λ : FormParameter (C := C) R lam) :
    IsQuadraticMetabolic R (quadraticZero (C := C) R Λ) := by
  refine ⟨0, 0, ?_, ?_⟩
  · exact map_zero (pullbackQuadraticForm R Λ (0 : (0 : C) ⟶ (0 : C)))
  · exact ⟨ShortComplex.Splitting.ofIsZero _
      (isZero_zero C) (isZero_zero C) (isZero_duality_zero (C := C))⟩

omit [HasZeroObject C] in
/-- `X ⊞ (-X)` is quadratic-metabolic via the diagonal metabolizer `Δ : X.M ⟶ X.M ⊞ X.M`. -/
lemma isQuadraticMetabolic_self_add_neg {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    (X : QuadraticObject (C := C) R Λ) :
    IsQuadraticMetabolic R (quadraticBiprod R X (quadraticNeg R X)) := by
  let i : X.M ⟶ X.M ⊞ X.M := biprod.lift (𝟙 X.M) (𝟙 X.M)
  have hq : pullbackQuadraticForm R Λ i (quadraticBiprod R X (quadraticNeg R X)).form = 0 := by
    dsimp only [quadraticBiprod, quadraticNeg]
    rw [map_add, ← pullbackQuadraticForm_comp, ← pullbackQuadraticForm_comp]
    simp only [i, biprod.lift_fst, biprod.lift_snd, pullbackQuadraticForm_id,
      map_neg, add_neg_cancel]
  refine ⟨X.M, i, hq, ?_⟩
  have hform :
      ((symmetrizationFunctor R Λ).obj (quadraticBiprod R X (quadraticNeg R X))).form.val =
        (hermitianBiprod R ((symmetrizationFunctor R Λ).obj X)
          (hermitianNeg R ((symmetrizationFunctor R Λ).obj X))).form.val := by
    dsimp only [quadraticBiprod, quadraticNeg]
    change (associatedHermitian R Λ (X.M ⊞ X.M)
        (pullbackQuadraticForm R Λ biprod.fst X.form +
          pullbackQuadraticForm R Λ biprod.snd (-X.form))).val =
      sesqBiprod ((associatedHermitian R Λ X.M X.form).val)
        (-((associatedHermitian R Λ X.M X.form).val))
    rw [map_add]
    change
      (associatedHermitian R Λ (X.M ⊞ X.M)
          (pullbackQuadraticForm R Λ biprod.fst X.form)).val +
        (associatedHermitian R Λ (X.M ⊞ X.M)
          (pullbackQuadraticForm R Λ biprod.snd (-X.form))).val =
        sesqBiprod ((associatedHermitian R Λ X.M X.form).val)
          (-((associatedHermitian R Λ X.M X.form).val))
    rw [associatedHermitian_pullback, associatedHermitian_pullback, map_neg]
    rfl
  have : IsIso (associatedHermitian R Λ X.M X.form).val :=
    ((symmetrizationFunctor R Λ).obj X).nonsingular
  refine ⟨{
    r := biprod.fst
    s := -inv (associatedHermitian R Λ X.M X.form).val ≫ biprod.inr
    f_r := by
      change i ≫ (biprod.fst : X.M ⊞ X.M ⟶ X.M) = 𝟙 X.M
      simp [i]
    s_g := by
      have hsg : (-inv (associatedHermitian R Λ X.M X.form).val ≫
            (biprod.inr : X.M ⟶ X.M ⊞ X.M)) ≫
          sesqBiprod (associatedHermitian R Λ X.M X.form).val
            (-((associatedHermitian R Λ X.M X.form).val)) ≫
          HermitianCategory.duality.map i.op = 𝟙 _ := by
        simp [i, sesqBiprod, Preadditive.comp_add, Preadditive.add_comp,
          Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp, ← op_comp]
      dsimp [hermitianMetabolizerComplex]
      erw [hform]
      exact hsg
    id := by
      have hid : (biprod.fst : X.M ⊞ X.M ⟶ X.M) ≫ i +
          (sesqBiprod (associatedHermitian R Λ X.M X.form).val
            (-((associatedHermitian R Λ X.M X.form).val)) ≫
            HermitianCategory.duality.map i.op) ≫
          (-inv (associatedHermitian R Λ X.M X.form).val ≫
            (biprod.inr : X.M ⟶ X.M ⊞ X.M)) = 𝟙 (X.M ⊞ X.M) := by
        ext <;>
          simp [i, sesqBiprod, Preadditive.comp_add, Preadditive.add_comp,
            Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp, ← op_comp]
      dsimp [hermitianMetabolizerComplex]
      erw [hform]
      exact hid }⟩

omit [HasZeroObject C] in
/-- Quadratic-metabolicity is closed under orthogonal direct sums. -/
lemma isQuadraticMetabolic_biprod {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    {X Y : QuadraticObject (C := C) R Λ}
    (hX : IsQuadraticMetabolic R X) (hY : IsQuadraticMetabolic R Y) :
    IsQuadraticMetabolic R (quadraticBiprod R X Y) := by
  rcases hX with ⟨L₁, i₁, hq₁, ⟨s₁⟩⟩
  rcases hY with ⟨L₂, i₂, hq₂, ⟨s₂⟩⟩
  let i : L₁ ⊞ L₂ ⟶ X.M ⊞ Y.M := biprod.map i₁ i₂
  have hq : pullbackQuadraticForm R Λ i (quadraticBiprod R X Y).form = 0 := by
    dsimp only [quadraticBiprod]
    rw [map_add, ← pullbackQuadraticForm_comp, ← pullbackQuadraticForm_comp]
    simp only [i, biprod.map_fst, biprod.map_snd,
      pullbackQuadraticForm_comp, hq₁, hq₂, map_zero, add_zero]
  refine ⟨L₁ ⊞ L₂, i, hq, ?_⟩
  have hh₁ : i₁ ≫ (associatedHermitian R Λ X.M X.form).val ≫
      HermitianCategory.duality.map i₁.op = 0 := by
    have h := congrArg (fun q => (associatedHermitian R Λ L₁ q).val) hq₁
    rw [associatedHermitian_pullback, map_zero] at h
    exact h
  have hh₂ : i₂ ≫ (associatedHermitian R Λ Y.M Y.form).val ≫
      HermitianCategory.duality.map i₂.op = 0 := by
    have h := congrArg (fun q => (associatedHermitian R Λ L₂ q).val) hq₂
    rw [associatedHermitian_pullback, map_zero] at h
    exact h
  let g₁ := (associatedHermitian R Λ X.M X.form).val ≫
    HermitianCategory.duality.map i₁.op
  let g₂ := (associatedHermitian R Λ Y.M Y.form).val ≫
    HermitianCategory.duality.map i₂.op
  let S := ShortComplex.mk (biprod.map i₁ i₂) (biprod.map g₁ g₂) (by
    ext <;> simp [g₁, g₂, hh₁, hh₂])
  have s : S.Splitting := splittingBiprod s₁ s₂
  have hform :
      ((symmetrizationFunctor R Λ).obj (quadraticBiprod R X Y)).form.val =
        (hermitianBiprod R ((symmetrizationFunctor R Λ).obj X)
          ((symmetrizationFunctor R Λ).obj Y)).form.val := by
    dsimp only [quadraticBiprod]
    change (associatedHermitian R Λ (X.M ⊞ Y.M)
        (pullbackQuadraticForm R Λ biprod.fst X.form +
          pullbackQuadraticForm R Λ biprod.snd Y.form)).val =
      sesqBiprod (associatedHermitian R Λ X.M X.form).val
        (associatedHermitian R Λ Y.M Y.form).val
    rw [map_add]
    change
      (associatedHermitian R Λ (X.M ⊞ Y.M)
          (pullbackQuadraticForm R Λ biprod.fst X.form)).val +
        (associatedHermitian R Λ (X.M ⊞ Y.M)
          (pullbackQuadraticForm R Λ biprod.snd Y.form)).val =
        sesqBiprod (associatedHermitian R Λ X.M X.form).val
          (associatedHermitian R Λ Y.M Y.form).val
    rw [associatedHermitian_pullback, associatedHermitian_pullback]
    rfl
  refine ⟨ShortComplex.Splitting.ofIso s ?_⟩
  refine ShortComplex.isoMk
    (S₁ := S) (S₂ := hermitianMetabolizerComplex R
      ((symmetrizationFunctor R Λ).obj (quadraticBiprod R X Y)) i _)
    (Iso.refl _) (Iso.refl _) (dualityBiprodIso L₁ L₂).symm ?_ ?_
  · change (𝟙 _) ≫ biprod.map i₁ i₂ = biprod.map i₁ i₂ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · change (𝟙 (X.M ⊞ Y.M)) ≫
      (((symmetrizationFunctor R Λ).obj (quadraticBiprod R X Y)).form.val ≫
        HermitianCategory.duality.map i.op) =
      (biprod.map g₁ g₂) ≫ (dualityBiprodIso L₁ L₂).inv
    rw [Category.id_comp, hform]
    have h₁ :
        (biprod.inl : X.M ⟶ X.M ⊞ Y.M) ≫
            sesqBiprod (associatedHermitian R Λ X.M X.form).val
              (associatedHermitian R Λ Y.M Y.form).val ≫
            HermitianCategory.duality.map (biprod.map i₁ i₂).op =
          (associatedHermitian R Λ X.M X.form).val ≫
            HermitianCategory.duality.map (biprod.fst ≫ i₁).op := by
      rw [sesqBiprod, ← Category.assoc, Preadditive.comp_add]
      simp only [biprod.inl_fst_assoc, biprod.inl_snd_assoc,
        Limits.zero_comp, add_zero]
      rw [Category.assoc, ← Functor.map_comp, ← op_comp, biprod.map_fst]
    have h₂ :
        (biprod.inr : Y.M ⟶ X.M ⊞ Y.M) ≫
            sesqBiprod (associatedHermitian R Λ X.M X.form).val
              (associatedHermitian R Λ Y.M Y.form).val ≫
            HermitianCategory.duality.map (biprod.map i₁ i₂).op =
          (associatedHermitian R Λ Y.M Y.form).val ≫
            HermitianCategory.duality.map (biprod.snd ≫ i₂).op := by
      rw [sesqBiprod, ← Category.assoc, Preadditive.comp_add]
      simp only [biprod.inr_fst_assoc, biprod.inr_snd_assoc,
        Limits.zero_comp, zero_add]
      rw [Category.assoc, ← Functor.map_comp, ← op_comp, biprod.map_snd]
    ext
    · change (biprod.inl : X.M ⟶ X.M ⊞ Y.M) ≫
          sesqBiprod (associatedHermitian R Λ X.M X.form).val
            (associatedHermitian R Λ Y.M Y.form).val ≫
          HermitianCategory.duality.map (biprod.map i₁ i₂).op =
        (biprod.inl : X.M ⟶ X.M ⊞ Y.M) ≫ biprod.map g₁ g₂ ≫ (dualityBiprodIso L₁ L₂).inv
      rw [h₁]
      simp [g₁, dualityBiprodIso, ← Functor.map_comp, ← op_comp]
    · change (biprod.inr : Y.M ⟶ X.M ⊞ Y.M) ≫
          sesqBiprod (associatedHermitian R Λ X.M X.form).val
            (associatedHermitian R Λ Y.M Y.form).val ≫
          HermitianCategory.duality.map (biprod.map i₁ i₂).op =
        (biprod.inr : Y.M ⟶ X.M ⊞ Y.M) ≫ biprod.map g₁ g₂ ≫ (dualityBiprodIso L₁ L₂).inv
      rw [h₂]
      simp [g₂, dualityBiprodIso, ← Functor.map_comp, ← op_comp]

omit [HasBinaryBiproducts C] [HasZeroObject C] in
/-- Quadratic-metabolicity is invariant under isometry. -/
lemma isQuadraticMetabolic_of_iso {lam : Z1Mul R} {Λ : FormParameter (C := C) R lam}
    {X Y : QuadraticObject (C := C) R Λ} (e : X ≅ Y)
    (hX : IsQuadraticMetabolic R X) : IsQuadraticMetabolic R Y := by
  rcases hX with ⟨L, i, hi, ⟨s⟩⟩
  let eM : X.M ≅ Y.M :=
    { hom := e.hom.val
      inv := e.inv.val
      hom_inv_id := congrArg Subtype.val e.hom_inv_id
      inv_hom_id := congrArg Subtype.val e.inv_hom_id }
  let j : L ⟶ Y.M := i ≫ eM.hom
  have hj : pullbackQuadraticForm R Λ j Y.form = 0 := by
    dsimp [j]
    rw [pullbackQuadraticForm_comp, e.hom.property.2, hi]
  have he : eM.hom ≫ ((symmetrizationFunctor R Λ).obj Y).form.val ≫
      HermitianCategory.duality.map eM.hom.op =
        ((symmetrizationFunctor R Λ).obj X).form.val := by
    change eM.hom ≫ (associatedHermitian R Λ Y.M Y.form).val ≫
      HermitianCategory.duality.map eM.hom.op =
        (associatedHermitian R Λ X.M X.form).val
    rw [← associatedHermitian_pullback]
    exact congrArg Subtype.val
      (congrArg (associatedHermitian R Λ X.M) e.hom.property.2)
  refine ⟨L, j, hj, ⟨?_⟩⟩
  apply ShortComplex.Splitting.ofIso s
  refine ShortComplex.isoMk
    (S₁ := _) (S₂ := hermitianMetabolizerComplex R
      ((symmetrizationFunctor R Λ).obj Y) j _)
    (Iso.refl _) eM (Iso.refl _) ?_ ?_
  · change (𝟙 L) ≫ j = i ≫ eM.hom
    simp [j]
  · change eM.hom ≫
      (((symmetrizationFunctor R Λ).obj Y).form.val ≫
        HermitianCategory.duality.map j.op) =
      (((symmetrizationFunctor R Λ).obj X).form.val ≫
        HermitianCategory.duality.map i.op) ≫ 𝟙 _
    simp only [j, op_comp, Category.comp_id]
    simpa using (reassoc_of% he) (HermitianCategory.duality.map i.op)

end Metabolic

/-! ## Split and quadratic Witt groups -/

section SplitAndQuadraticWitt

/-- `StableWittData` for nonsingular `λ`-Hermitian forms with split metabolizers. -/
noncomputable def splitHermitianWittData (lam : Z1Mul R) :
    StableWittData (HermitianFormCat (C := C) R lam) where
  add := hermitianBiprod R
  zero := hermitianZero R lam
  neg := hermitianNeg R
  metabolic := IsSplitMetabolic R
  add_comm X Y := ⟨hermitianBiprodComm R X Y⟩
  add_assoc X Y Z := ⟨hermitianBiprodAssoc R X Y Z⟩
  zero_add X := ⟨hermitianZeroBiprod R X⟩
  add_congr e₁ e₂ := hermitianBiprodCongr R e₁ e₂
  metabolic_zero := isSplitMetabolic_zero (C := C) R lam
  metabolic_self_add_neg := isSplitMetabolic_self_add_neg R
  metabolic_add := isSplitMetabolic_biprod R
  metabolic_of_iso := isSplitMetabolic_of_iso R

/-- `StableWittData` for nonsingular `(λ, Λ)`-quadratic forms (using split metabolizers). -/
noncomputable def quadraticWittData {lam : Z1Mul R} (Λ : FormParameter (C := C) R lam) :
    StableWittData (QuadraticFormCat (C := C) R Λ) where
  add := quadraticBiprod R
  zero := quadraticZero R Λ
  neg := quadraticNeg R
  metabolic := IsQuadraticMetabolic R
  add_comm X Y := ⟨quadraticBiprodComm R X Y⟩
  add_assoc X Y Z := ⟨quadraticBiprodAssoc R X Y Z⟩
  zero_add X := ⟨quadraticZeroBiprod R X⟩
  add_congr e₁ e₂ := quadraticBiprodCongr R e₁ e₂
  metabolic_zero := isQuadraticMetabolic_zero (C := C) R Λ
  metabolic_self_add_neg := isQuadraticMetabolic_self_add_neg R
  metabolic_add := isQuadraticMetabolic_biprod R
  metabolic_of_iso := isQuadraticMetabolic_of_iso R

/-- The split Witt group of `λ`-Hermitian forms in `C`. -/
abbrev SplitHermitianWittGroup (lam : Z1Mul R) : Type (max u v) :=
  GenericWittGroup (splitHermitianWittData (C := C) R lam)

/-- The Witt group of `(λ, Λ)`-quadratic forms in `C` (using split metabolizers). -/
abbrev QuadraticWittGroup {lam : Z1Mul R} (Λ : FormParameter (C := C) R lam) : Type (max u v) :=
  GenericWittGroup (quadraticWittData (C := C) R Λ)

/-- Canonical comparison homomorphism from the quadratic Witt group to the split
Hermitian Witt group, induced by `symmetrizationFunctor`. -/
noncomputable def quadraticWittToSplitWitt {lam : Z1Mul R}
    (Λ : FormParameter (C := C) R lam) :
    QuadraticWittGroup (C := C) R Λ →+ SplitHermitianWittGroup (C := C) R lam where
  toFun := Quotient.lift
    (fun X => GenericWittGroup.mk (splitHermitianWittData (C := C) R lam)
      ((symmetrizationFunctor R Λ).obj X)) (by
        intro X Y ⟨M₁, M₂, h₁, h₂, ⟨e⟩⟩
        apply Quotient.sound
        refine ⟨(symmetrizationFunctor R Λ).obj M₁,
          (symmetrizationFunctor R Λ).obj M₂,
          h₁.toSplitMetabolic R, h₂.toSplitMetabolic R, ⟨?_⟩⟩
        exact eqToIso (symmetrizationFunctor_obj_biprod R X M₁).symm ≪≫
          (symmetrizationFunctor R Λ).mapIso e ≪≫
          eqToIso (symmetrizationFunctor_obj_biprod R Y M₂))
  map_zero' := by
    change GenericWittGroup.mk (splitHermitianWittData (C := C) R lam)
      ((symmetrizationFunctor R Λ).obj (quadraticZero R Λ)) = 0
    rw [symmetrizationFunctor_obj_zero]
    rfl
  map_add' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro X Y
    change GenericWittGroup.mk (splitHermitianWittData (C := C) R lam)
      ((symmetrizationFunctor R Λ).obj (quadraticBiprod R X Y)) =
        GenericWittGroup.mk (splitHermitianWittData (C := C) R lam)
          ((symmetrizationFunctor R Λ).obj X) +
        GenericWittGroup.mk (splitHermitianWittData (C := C) R lam)
          ((symmetrizationFunctor R Λ).obj Y)
    rw [symmetrizationFunctor_obj_biprod]
    rfl

/-- When `R` has a generalized half-unit, `quadraticWittToSplitWitt` is bijective. -/
lemma quadraticWittToSplitWitt_bijective_of_halfUnit {lam : Z1Mul R}
    (Λ : FormParameter (C := C) R lam)
    (hhalf : ∃ r : R, isGeneralizedHalfUnit R r) :
    Function.Bijective (quadraticWittToSplitWitt (C := C) R Λ) := by
  let E := symmetrizationEquivalence_of_halfUnit (C := C) R Λ hhalf
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro X Y hXY
    change GenericWittGroup.mk (splitHermitianWittData (C := C) R lam)
        ((symmetrizationFunctor R Λ).obj X) =
      GenericWittGroup.mk (splitHermitianWittData (C := C) R lam)
        ((symmetrizationFunctor R Λ).obj Y) at hXY
    rw [GenericWittGroup.mk_eq_mk_iff] at hXY
    rcases hXY with ⟨M₁, M₂, hM₁, hM₂, ⟨e⟩⟩
    let N₁ := E.inverse.obj M₁
    let N₂ := E.inverse.obj M₂
    let e₁ : (symmetrizationFunctor R Λ).obj N₁ ≅ M₁ := E.counitIso.app M₁
    let e₂ : (symmetrizationFunctor R Λ).obj N₂ ≅ M₂ := E.counitIso.app M₂
    have hN₁ : IsQuadraticMetabolic R N₁ :=
      (isQuadraticMetabolic_iff_isSplitMetabolic_of_halfUnit R hhalf N₁).2
        (isSplitMetabolic_of_iso R e₁.symm hM₁)
    have hN₂ : IsQuadraticMetabolic R N₂ :=
      (isQuadraticMetabolic_iff_isSplitMetabolic_of_halfUnit R hhalf N₂).2
        (isSplitMetabolic_of_iso R e₂.symm hM₂)
    let A := quadraticBiprod R X N₁
    let B := quadraticBiprod R Y N₂
    let eH : (symmetrizationFunctor R Λ).obj A ≅
        (symmetrizationFunctor R Λ).obj B :=
      eqToIso (symmetrizationFunctor_obj_biprod R X N₁) ≪≫
        hermitianBiprodCongr R (Iso.refl _) e₁ ≪≫ e ≪≫
        hermitianBiprodCongr R (Iso.refl _) e₂.symm ≪≫
        eqToIso (symmetrizationFunctor_obj_biprod R Y N₂).symm
    let eQ : A ≅ B :=
      E.unitIso.app A ≪≫ E.inverse.mapIso eH ≪≫ (E.unitIso.app B).symm
    apply Quotient.sound
    exact ⟨N₁, N₂, hN₁, hN₂, ⟨eQ⟩⟩
  · intro b
    refine Quotient.inductionOn b ?_
    intro Y
    let X := E.inverse.obj Y
    let e : (symmetrizationFunctor R Λ).obj X ≅ Y := E.counitIso.app Y
    refine ⟨GenericWittGroup.mk (quadraticWittData (C := C) R Λ) X, ?_⟩
    change GenericWittGroup.mk (splitHermitianWittData (C := C) R lam)
      ((symmetrizationFunctor R Λ).obj X) =
        GenericWittGroup.mk (splitHermitianWittData (C := C) R lam) Y
    rw [GenericWittGroup.mk_eq_mk_iff]
    exact ⟨hermitianZero R lam, hermitianZero R lam,
      isSplitMetabolic_zero (C := C) R lam,
      isSplitMetabolic_zero (C := C) R lam,
      ⟨hermitianBiprodCongr R e (Iso.refl _)⟩⟩

/-- Canonical isomorphism `QuadraticWittGroup R Λ ≃+ SplitHermitianWittGroup R lam`
when `R` has a generalized half-unit. -/
noncomputable def quadraticWittEquivSplitWitt_of_halfUnit {lam : Z1Mul R}
    (Λ : FormParameter (C := C) R lam)
    (hhalf : ∃ r : R, isGeneralizedHalfUnit R r) :
    QuadraticWittGroup (C := C) R Λ ≃+ SplitHermitianWittGroup (C := C) R lam :=
  AddEquiv.ofBijective (quadraticWittToSplitWitt (C := C) R Λ)
    (quadraticWittToSplitWitt_bijective_of_halfUnit (C := C) R Λ hhalf)

/-- Vanishing of `TateCohomologyZeroAdd R` makes `quadraticWittToSplitWitt` an isomorphism. -/
noncomputable def quadraticWittEquivSplitWitt_of_tateCohomologyZeroAddVanishes
    {lam : Z1Mul R} (Λ : FormParameter (C := C) R lam)
    (hzero : Subsingleton (TateCohomologyZeroAdd R)) :
    QuadraticWittGroup (C := C) R Λ ≃+ SplitHermitianWittGroup (C := C) R lam :=
  quadraticWittEquivSplitWitt_of_halfUnit (C := C) R Λ
    (existsGeneralizedHalfUnit_of_tateCohomologyZeroAddVanishes R hzero)

end SplitAndQuadraticWitt

end NonAbelian

/-! ## Ordinary Witt groups in abelian Hermitian categories -/

section AbelianWitt

variable {C : Type u} [Category.{v} C] [Abelian C] [HermitianCategory C]
variable (R : Type u) [CommRing R] [StarRing R] [Linear R C]
variable [Functor.Additive (HermitianCategory.duality (C := C))]
variable [StarLinearDuality R C]

/-- In an abelian Hermitian category, a `λ`-Hermitian object is metabolic if it admits
a metabolizer `0 ⟶ L ⟶ X.M ⟶ D(L) ⟶ 0` (not necessarily split). -/
def IsMetabolic {lam : Z1Mul R} (X : HermitianObject (C := C) R lam) : Prop :=
  ∃ (L : C) (i : L ⟶ X.M) (hi : i ≫ X.form.val ≫ HermitianCategory.duality.map i.op = 0),
    (hermitianMetabolizerComplex R X i hi).ShortExact

omit [StarLinearDuality R C] in
/-- Every split-metabolic Hermitian object is metabolic when `C` is abelian. -/
lemma IsSplitMetabolic.isMetabolic {lam : Z1Mul R}
    {X : HermitianObject (C := C) R lam} (hX : IsSplitMetabolic R X) :
    IsMetabolic R X := by
  rcases hX with ⟨L, i, hi, ⟨s⟩⟩
  exact ⟨L, i, hi, s.shortExact⟩

omit [StarLinearDuality R C] in
/-- The zero `λ`-Hermitian object is metabolic in an abelian Hermitian category. -/
lemma isMetabolic_zero (lam : Z1Mul R) :
    IsMetabolic R (hermitianZero (C := C) R lam) :=
  (isSplitMetabolic_zero (C := C) R lam).isMetabolic R

omit [StarLinearDuality R C] in
/-- `X ⊞ (-X)` is metabolic in an abelian Hermitian category. -/
lemma isMetabolic_self_add_neg {lam : Z1Mul R}
    (X : HermitianObject (C := C) R lam) :
    IsMetabolic R (hermitianBiprod R X (hermitianNeg R X)) :=
  (isSplitMetabolic_self_add_neg R X).isMetabolic R

omit [StarLinearDuality R C] in
/-- Metabolicity in an abelian Hermitian category is closed under orthogonal direct sums. -/
lemma isMetabolic_biprod {lam : Z1Mul R}
    {X Y : HermitianObject (C := C) R lam}
    (hX : IsMetabolic R X) (hY : IsMetabolic R Y) :
    IsMetabolic R (hermitianBiprod R X Y) := by
  rcases hX with ⟨L₁, i₁, hi₁, hS₁⟩
  rcases hY with ⟨L₂, i₂, hi₂, hS₂⟩
  let i : L₁ ⊞ L₂ ⟶ X.M ⊞ Y.M := biprod.map i₁ i₂
  have hi : i ≫ (hermitianBiprod R X Y).form.val ≫
      HermitianCategory.duality.map i.op = 0 := by
    dsimp [i]
    ext <;>
      simp only [hermitianBiprod, sesqBiprod, Preadditive.comp_add,
        Preadditive.add_comp, Category.assoc, biprod.map_fst_assoc,
        biprod.map_snd_assoc, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
        biprod.inr_fst_assoc, biprod.inr_snd_assoc, Limits.zero_comp,
        Limits.comp_zero, add_zero, zero_add]
    · rw [← Functor.map_comp, ← op_comp, biprod.map_fst,
        op_comp, Functor.map_comp]
      simpa using (reassoc_of% hi₁)
        (HermitianCategory.duality.map (biprod.fst : L₁ ⊞ L₂ ⟶ L₁).op)
    · rw [← Functor.map_comp, ← op_comp, biprod.map_snd,
        op_comp, Functor.map_comp]
      simpa using (reassoc_of% hi₂)
        (HermitianCategory.duality.map (biprod.snd : L₁ ⊞ L₂ ⟶ L₂).op)
  let g₁ := X.form.val ≫ HermitianCategory.duality.map i₁.op
  let g₂ := Y.form.val ≫ HermitianCategory.duality.map i₂.op
  let S := ShortComplex.mk (biprod.map i₁ i₂) (biprod.map g₁ g₂) (by
    ext <;> simp [g₁, g₂, hi₁, hi₂])
  have : Mono i₁ := hS₁.mono_f
  have : Mono i₂ := hS₂.mono_f
  have : Epi g₁ := hS₁.epi_g
  have : Epi g₂ := hS₂.epi_g
  have hExact : S.Exact := by
    apply ShortComplex.exact_of_f_is_kernel S
    let hK₁ := hS₁.fIsKernel
    let hK₂ := hS₂.fIsKernel
    refine IsLimit.mk
      (fun s => biprod.lift
        (hK₁.lift (KernelFork.ofι (Fork.ι s ≫ biprod.fst) (by
          have h := congrArg (fun q => q ≫ (biprod.fst : S.X₃ ⟶ _)) (KernelFork.condition s)
          rw [Limits.zero_comp, Category.assoc] at h
          change Fork.ι s ≫ biprod.map g₁ g₂ ≫ biprod.fst = 0 at h
          rw [biprod.map_fst, ← Category.assoc] at h
          exact h)))
        (hK₂.lift (KernelFork.ofι (Fork.ι s ≫ biprod.snd) (by
          have h := congrArg (fun q => q ≫ (biprod.snd : S.X₃ ⟶ _)) (KernelFork.condition s)
          rw [Limits.zero_comp, Category.assoc] at h
          change Fork.ι s ≫ biprod.map g₁ g₂ ≫ biprod.snd = 0 at h
          rw [biprod.map_snd, ← Category.assoc] at h
          exact h))))
      (fun s j => by
        rcases j with _ | _
        · dsimp [KernelFork.ofι]
          ext
          · simp only [S]
            rw [Category.assoc, biprod.map_fst i₁ i₂, ← Category.assoc]
            erw [biprod.lift_fst, hK₁.fac _ .zero]
            rfl
          · simp only [S]
            rw [Category.assoc, biprod.map_snd i₁ i₂, ← Category.assoc]
            erw [biprod.lift_snd, hK₂.fac _ .zero]
            rfl
        · dsimp [KernelFork.ofι]
          simp)
      (fun s m hm => by
        dsimp [KernelFork.ofι]
        ext
        · apply hK₁.hom_ext
          intro j
          rcases j with _ | _
          · have hfac := hK₁.fac (KernelFork.ofι (Fork.ι s ≫ biprod.fst) (by
              have h := congrArg (fun q => q ≫ (biprod.fst : S.X₃ ⟶ _)) (KernelFork.condition s)
              rw [Limits.zero_comp, Category.assoc] at h
              change Fork.ι s ≫ biprod.map g₁ g₂ ≫ biprod.fst = 0 at h
              rw [biprod.map_fst, ← Category.assoc] at h
              exact h)) .zero
            have hm₀ := congrArg (fun q => q ≫ biprod.fst) (hm .zero)
            dsimp [KernelFork.ofι, S, hermitianMetabolizerComplex] at hfac hm₀ ⊢
            rw [biprod.lift_fst]
            erw [hfac]
            rw [Category.assoc, biprod.map_fst, ← Category.assoc] at hm₀
            exact hm₀
          · dsimp [KernelFork.ofι]
            rw [(hermitianMetabolizerComplex R X i₁ hi₁).zero]
            erw [Limits.comp_zero, Limits.comp_zero]
        · apply hK₂.hom_ext
          intro j
          rcases j with _ | _
          · have hfac := hK₂.fac (KernelFork.ofι (Fork.ι s ≫ biprod.snd) (by
              have h := congrArg (fun q => q ≫ (biprod.snd : S.X₃ ⟶ _)) (KernelFork.condition s)
              rw [Limits.zero_comp, Category.assoc] at h
              change Fork.ι s ≫ biprod.map g₁ g₂ ≫ biprod.snd = 0 at h
              rw [biprod.map_snd, ← Category.assoc] at h
              exact h)) .zero
            have hm₀ := congrArg (fun q => q ≫ biprod.snd) (hm .zero)
            dsimp [KernelFork.ofι, S, hermitianMetabolizerComplex] at hfac hm₀ ⊢
            rw [biprod.lift_snd]
            erw [hfac]
            rw [Category.assoc, biprod.map_snd, ← Category.assoc] at hm₀
            exact hm₀
          · dsimp [KernelFork.ofι]
            rw [(hermitianMetabolizerComplex R Y i₂ hi₂).zero]
            erw [Limits.comp_zero, Limits.comp_zero])
  let eS : S ≅ hermitianMetabolizerComplex R (hermitianBiprod R X Y) i hi := by
    refine ShortComplex.isoMk
      (S₁ := S) (S₂ := hermitianMetabolizerComplex R (hermitianBiprod R X Y) i hi)
      (Iso.refl _) (Iso.refl _) (dualityBiprodIso L₁ L₂).symm ?_ ?_
    · change (𝟙 _) ≫ biprod.map i₁ i₂ = biprod.map i₁ i₂ ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    · ext <;>
        simp [S, i, g₁, g₂, hermitianMetabolizerComplex, hermitianBiprod, sesqBiprod,
          dualityBiprodIso, Preadditive.comp_add, Preadditive.add_comp,
          ← Functor.map_comp, ← op_comp]
  have hExact' : (hermitianMetabolizerComplex R (hermitianBiprod R X Y) i hi).Exact :=
    (ShortComplex.exact_iff_of_iso eS).1 hExact
  have hMono : Mono (hermitianMetabolizerComplex R (hermitianBiprod R X Y) i hi).f :=
    biprod.map_mono i₁ i₂
  have hEpi : Epi (hermitianMetabolizerComplex R (hermitianBiprod R X Y) i hi).g := by
    have h : (hermitianMetabolizerComplex R (hermitianBiprod R X Y) i hi).g =
        S.g ≫ (dualityBiprodIso L₁ L₂).symm.hom := by
      dsimp [hermitianMetabolizerComplex, hermitianBiprod]
      ext <;>
        simp [S, i, g₁, g₂, sesqBiprod,
          dualityBiprodIso, Preadditive.comp_add, Preadditive.add_comp,
          ← Functor.map_comp, ← op_comp]
    rw [h]
    exact epi_comp S.g (dualityBiprodIso L₁ L₂).symm.hom
  exact ⟨L₁ ⊞ L₂, i, hi, ShortComplex.ShortExact.mk' hExact' hMono hEpi⟩

omit [StarLinearDuality R C] in
/-- Metabolicity in an abelian Hermitian category is invariant under isometry. -/
lemma isMetabolic_of_iso {lam : Z1Mul R}
    {X Y : HermitianObject (C := C) R lam} (e : X ≅ Y)
    (hX : IsMetabolic R X) : IsMetabolic R Y := by
  rcases hX with ⟨L, i, hi, hS⟩
  let eM : X.M ≅ Y.M :=
    { hom := e.hom.val
      inv := e.inv.val
      hom_inv_id := congrArg Subtype.val e.hom_inv_id
      inv_hom_id := congrArg Subtype.val e.inv_hom_id }
  let j : L ⟶ Y.M := i ≫ eM.hom
  have he : eM.hom ≫ Y.form.val ≫ HermitianCategory.duality.map eM.hom.op =
      X.form.val := e.hom.property.2
  have hj : j ≫ Y.form.val ≫ HermitianCategory.duality.map j.op = 0 := by
    calc
      j ≫ Y.form.val ≫ HermitianCategory.duality.map j.op =
          i ≫ (eM.hom ≫ Y.form.val ≫ HermitianCategory.duality.map eM.hom.op) ≫
            HermitianCategory.duality.map i.op := by
              simp only [j, op_comp, Functor.map_comp, Category.assoc]
      _ = i ≫ X.form.val ≫ HermitianCategory.duality.map i.op := by rw [he]
      _ = 0 := hi
  let eS : hermitianMetabolizerComplex R X i hi ≅
      hermitianMetabolizerComplex R Y j hj := by
    refine ShortComplex.isoMk
      (S₁ := hermitianMetabolizerComplex R X i hi)
      (S₂ := hermitianMetabolizerComplex R Y j hj)
      (Iso.refl _) eM (Iso.refl _) ?_ ?_
    · change (𝟙 L) ≫ j = i ≫ eM.hom
      simp [j]
    · change eM.hom ≫ (Y.form.val ≫ HermitianCategory.duality.map j.op) =
        (X.form.val ≫ HermitianCategory.duality.map i.op) ≫ 𝟙 _
      simp only [j, op_comp, Functor.map_comp, Category.comp_id]
      simpa using (reassoc_of% he) (HermitianCategory.duality.map i.op)
  have hExact : (hermitianMetabolizerComplex R Y j hj).Exact :=
    (ShortComplex.exact_iff_of_iso eS).1 hS.exact
  have : Mono i := hS.mono_f
  have : IsIso eM.hom := Iso.isIso_hom eM
  have : Mono eM.hom := inferInstance
  have hMono : Mono (hermitianMetabolizerComplex R Y j hj).f :=
    mono_comp i eM.hom
  have hEpi : Epi (hermitianMetabolizerComplex R Y j hj).g := by
    have h : (hermitianMetabolizerComplex R Y j hj).g =
        eM.inv ≫ (hermitianMetabolizerComplex R X i hi).g := by
      dsimp [hermitianMetabolizerComplex]
      rw [Iso.eq_inv_comp]
      simp only [j, op_comp, Functor.map_comp]
      simpa using (reassoc_of% he) (HermitianCategory.duality.map i.op)
    rw [h]
    have : IsIso eM.inv := Iso.isIso_inv eM
    refine ⟨fun {Z} f₁ f₂ hf => ?_⟩
    dsimp [hermitianMetabolizerComplex] at f₁ f₂ hf ⊢
    apply hS.epi_g.left_cancellation
    dsimp [hermitianMetabolizerComplex]
    simp only [Category.assoc] at hf ⊢
    exact (cancel_epi eM.inv).mp hf
  exact ⟨L, j, hj, ShortComplex.ShortExact.mk' hExact hMono hEpi⟩

/-- `StableWittData` for nonsingular `λ`-Hermitian forms with arbitrary metabolizers
in an abelian Hermitian category. -/
noncomputable def hermitianWittData (lam : Z1Mul R) :
    StableWittData (HermitianFormCat (C := C) R lam) where
  add := hermitianBiprod R
  zero := hermitianZero R lam
  neg := hermitianNeg R
  metabolic := IsMetabolic R
  add_comm X Y := ⟨hermitianBiprodComm R X Y⟩
  add_assoc X Y Z := ⟨hermitianBiprodAssoc R X Y Z⟩
  zero_add X := ⟨hermitianZeroBiprod R X⟩
  add_congr e₁ e₂ := hermitianBiprodCongr R e₁ e₂
  metabolic_zero := isMetabolic_zero (C := C) R lam
  metabolic_self_add_neg := isMetabolic_self_add_neg R
  metabolic_add := isMetabolic_biprod R
  metabolic_of_iso := isMetabolic_of_iso R

/-- The ordinary Witt group of `λ`-Hermitian forms in an abelian Hermitian category `C`. -/
abbrev HermitianWittGroup (lam : Z1Mul R) : Type (max u v) :=
  GenericWittGroup (hermitianWittData (C := C) R lam)

/-- Canonical comparison homomorphism from the split Witt group to the ordinary Witt group
when `C` is abelian. -/
noncomputable def splitWittToWitt (lam : Z1Mul R) :
    SplitHermitianWittGroup (C := C) R lam →+ HermitianWittGroup (C := C) R lam where
  toFun := Quotient.lift
    (fun X => GenericWittGroup.mk (hermitianWittData (C := C) R lam) X) (by
      intro X Y ⟨M₁, M₂, h₁, h₂, hIso⟩
      exact Quotient.sound ⟨M₁, M₂, h₁.isMetabolic R, h₂.isMetabolic R, hIso⟩)
  map_zero' := rfl
  map_add' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro X Y
    rfl

end AbelianWitt
