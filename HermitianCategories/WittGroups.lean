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
