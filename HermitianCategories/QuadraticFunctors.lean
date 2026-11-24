/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.CategoryTheory.Linear.LinearFunctor
import HermitianCategories.QuadraticForms
import HermitianCategories.HermitianFunctors

/-!
# Hermitian functors and transport of (λ, Λ)-quadratic forms

This file extends `HermitianFunctors` to `(λ, Λ)`-quadratic forms and their
categories `QuadraticFormCat`.

For a `HermitianFunctor R functor hf eta`, `mapSesqForms` satisfies
`formDual (T q) = eta • T (formDual q)`. Consequently, the twisted adjoint
`q ↦ lam • q†` shifts parameter in the opposite direction `lam ↦ eta⁻¹ * lam`,
sending `LambdaMin R M lam` into `LambdaMin R (functor.obj M) (eta⁻¹ * lam)`
and `LambdaMax R M lam` into `LambdaMax R (functor.obj M) (eta⁻¹ * lam)`.

Given a compatible pair of form parameters `Λ` (for `lam`) and `Λ'` (for
`eta⁻¹ * lam`), transport descends to `QuadraticForm`, preserves nonsingularity
(since `associatedHermitian` scales by the unit `eta`), and induces a functor
`functorQuadraticCategories : QuadraticFormCat R Λ ⥤ QuadraticFormCat R Λ'`.
We also prove faithfulness, fullness/essential surjectivity under form-parameter
reflection, induced equivalences, and scaling of quadratic-form categories.
-/

open CategoryTheory
open Opposite

universe v u

set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false

variable {C : Type u} [Category.{v} C] [HermitianCategory C] [Preadditive C]
variable (R : Type u) [CommRing R] [StarRing R] [Linear R C]
variable [Functor.Additive (HermitianCategory.duality (C := C))]
variable [StarLinearDuality R C]

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D] [HermitianCategory D]
variable [Functor.Additive (HermitianCategory.duality (C := D))]
variable [StarLinearDuality R D]
variable (functor : C ⥤ D) [Functor.Additive functor] [Functor.Linear R functor]

/-! ## Transport of LambdaMin, LambdaMax, and form parameters -/

omit [StarLinearDuality R C] [StarLinearDuality R D] in
/-- `mapSesqForms` sends `LambdaMin R M lam` into `LambdaMin R (functor.obj M) (eta⁻¹ * lam)`.
Given a difference witness `h - lam • h†`, transport its witness `mapSesqForms functor hf h`
and cancel `eta` against `eta⁻¹` via `mapSesqForms_formDual`. -/
lemma mapSesqForms_mem_LambdaMin
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {M : C} {q : Sesq M} (hq : q ∈ LambdaMin R M lam) :
    mapSesqForms functor hf q ∈ LambdaMin R (functor.obj M) (eta⁻¹ * lam) := by
  rw [mem_LambdaMin] at hq ⊢
  obtain ⟨h, rfl⟩ := hq
  refine ⟨mapSesqForms functor hf h, ?_⟩
  rw [mapSesqForms_formDual R functor hf eta hermf]
  simp [mapSesqForms, Functor.map_sub, Functor.map_smul,
    smul_smul, mul_comm, mul_left_comm]

omit [StarLinearDuality R C] [StarLinearDuality R D] in
/-- `mapSesqForms` sends `LambdaMax R M lam` into `LambdaMax R (functor.obj M) (eta⁻¹ * lam)`.
Applying `mapSesqForms` to `q + lam • q† = 0` and rewriting with `mapSesqForms_formDual`
yields the `LambdaMax` condition at parameter `eta⁻¹ * lam`. -/
lemma mapSesqForms_mem_LambdaMax
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {M : C} {q : Sesq M} (hq : q ∈ LambdaMax R M lam) :
    mapSesqForms functor hf q ∈ LambdaMax R (functor.obj M) (eta⁻¹ * lam) := by
  rw [mem_LambdaMax] at hq ⊢
  rw [mapSesqForms_formDual R functor hf eta hermf, smul_smul]
  have ht := congrArg (mapSesqForms functor hf) hq
  simpa [mapSesqForms, Functor.map_add, Functor.map_smul, Linear.comp_smul,
    smul_smul, mul_comm, mul_left_comm, mul_assoc] using ht

/-- Compatibility of form parameters `Λ` and `Λ'` under `functor`:
transporting any form in `Λ.func M` lands in `Λ'.func (functor.obj M)`. -/
def FormParameterCompatible
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (Λ : FormParameter (C := C) R lam)
    (Λ' : FormParameter (C := D) R (eta⁻¹ * lam)) : Prop :=
  ∀ M : C, ∀ q ∈ Λ.func M, mapSesqForms functor hf q ∈ Λ'.func (functor.obj M)

/-- Reflection of form parameters under `functor`:
a form whose transport lies in `Λ'.func (functor.obj M)` already lies in `Λ.func M`. -/
def FormParameterReflects
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (Λ : FormParameter (C := C) R lam)
    (Λ' : FormParameter (C := D) R (eta⁻¹ * lam)) : Prop :=
  ∀ M : C, ∀ q : Sesq M, mapSesqForms functor hf q ∈ Λ'.func (functor.obj M) → q ∈ Λ.func M

namespace FormParameterCompatible

/-- Minimal form parameters are always compatible under any Hermitian functor. -/
lemma minParam
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta) :
    FormParameterCompatible R functor hf lam eta
      (FormParameter.minParam (C := C) R lam)
      (FormParameter.minParam (C := D) R (eta⁻¹ * lam)) := by
  intro M q hq
  exact mapSesqForms_mem_LambdaMin R functor hf lam eta hermf hq

omit [StarLinearDuality R C] in
/-- Any form parameter is compatible with the maximal target form parameter. -/
lemma maxParam
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    (Λ : FormParameter (C := C) R lam) :
    FormParameterCompatible R functor hf lam eta
      Λ (FormParameter.maxParam (C := D) R (eta⁻¹ * lam)) := by
  intro M q hq
  exact mapSesqForms_mem_LambdaMax R functor hf lam eta hermf (Λ.supLambdaMax M hq)

end FormParameterCompatible

/-- A faithful Hermitian functor reflects maximal form parameters:
if `mapSesqForms functor hf q ∈ LambdaMax (eta⁻¹ * lam)`, injectivity of `mapSesqForms`
forces `q + lam • q† = 0`. -/
lemma FormParameterReflects.maxParam
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    [functor.Faithful] :
    FormParameterReflects R functor hf lam eta
      (FormParameter.maxParam (C := C) R lam)
      (FormParameter.maxParam (C := D) R (eta⁻¹ * lam)) := by
  intro M q hq
  rw [FormParameter.maxParam, mem_LambdaMax] at hq ⊢
  -- Rewrite `formDual (mapSesqForms ... q)` back into `mapSesqForms ... (formDual q)`.
  have hq' :
      mapSesqForms functor hf q +
        ((lam : Rˣ) : R) • mapSesqForms functor hf (formDual q) = 0 := by
    rw [mapSesqForms_formDual R functor hf eta hermf] at hq
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hq
  apply mapSesqForms_injective functor hf
  simpa [mapSesqForms, Functor.map_add, Functor.map_smul, Linear.comp_smul]
    using hq'

/-! ## Transport of quadratic forms and nonsingularity -/

/-- Transport `(λ, Λ)`-quadratic forms to `(eta⁻¹ * λ, Λ')`-quadratic forms
by descending `mapSesqFormsHom` using `FormParameterCompatible`. -/
def mapQuadraticForms {M : C}
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ') :
    QuadraticForm R M Λ →+ QuadraticForm R (functor.obj M) Λ' :=
  QuotientAddGroup.lift (Λ.func M)
    ((toQuadraticForm R Λ' (functor.obj M)).comp (mapSesqFormsHom functor M hf))
    (by
      -- Compatibility ensures `Λ.func M` maps into `Λ'.func (functor.obj M)`.
      intro q hq
      change toQuadraticForm R Λ' (functor.obj M) (mapSesqForms functor hf q) = 0
      rw [toQuadraticForm_eq_zero_iff]
      exact hcomp M q hq)

omit [StarLinearDuality R C] [StarLinearDuality R D] [Functor.Linear R functor] in
/-- Unfold `mapQuadraticForms` on a represented quadratic form. -/
@[simp]
lemma mapQuadraticForms_mk {M : C}
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    (q : Sesq M) :
    mapQuadraticForms R functor hf lam eta hcomp (toQuadraticForm R Λ M q) =
      toQuadraticForm R Λ' (functor.obj M) (mapSesqForms functor hf q) := rfl

omit [StarLinearDuality R C] [StarLinearDuality R D] [Functor.Linear R functor] in
/-- Transport of quadratic forms commutes with pullback along morphisms.
Proof by induction on a sesquilinear representative and `mapSesqForms_pullback`. -/
lemma mapQuadraticForms_pullback {M N : C}
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    (f : M ⟶ N) (q : QuadraticForm R N Λ) :
    mapQuadraticForms R functor hf lam eta hcomp (pullbackQuadraticForm R Λ f q) =
      pullbackQuadraticForm R Λ' (functor.map f)
        (mapQuadraticForms R functor hf lam eta hcomp q) := by
  refine QuotientAddGroup.induction_on q ?_
  intro h
  change toQuadraticForm R Λ' (functor.obj M)
      (mapSesqForms functor hf
        (f ≫ h ≫ HermitianCategory.duality.map f.op)) =
    toQuadraticForm R Λ' (functor.obj M)
      (functor.map f ≫ mapSesqForms functor hf h ≫
        HermitianCategory.duality.map (functor.map f).op)
  rw [mapSesqForms_pullback]

/-- `associatedHermitian` of a transported quadratic form equals `eta` times the transported
`associatedHermitian` of the original quadratic form. -/
lemma associatedHermitian_mapQuadraticForms {M : C}
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    (q : QuadraticForm R M Λ) :
    (associatedHermitian R Λ' (functor.obj M)
      (mapQuadraticForms R functor hf lam eta hcomp q)).val =
      ((eta : Rˣ) : R) •
        mapSesqForms functor hf (associatedHermitian R Λ M q).val := by
  refine QuotientAddGroup.induction_on q ?_
  intro h
  change star (((eta⁻¹ * lam : Z1Mul R) : Rˣ) : R) •
      mapSesqForms functor hf h +
      formDual (mapSesqForms functor hf h) =
    ((eta : Rˣ) : R) • mapSesqForms functor hf
      (star ((lam : Rˣ) : R) • h + formDual h)
  -- Since `eta * star eta = 1`, we have `star (eta⁻¹) = eta`.
  have hetaU : star (eta : Rˣ) = (eta : Rˣ)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      ((mem_Z1Mul R (eta : Rˣ)).mp eta.property)
  have hetaInvU : star ((eta : Rˣ)⁻¹) = (eta : Rˣ) := by
    rw [star_inv, hetaU, inv_inv]
  have hetaInv :
      star (((eta : Rˣ)⁻¹ : Rˣ) : R) = ((eta : Rˣ) : R) :=
    congrArg (fun x : Rˣ => (x : R)) hetaInvU
  rw [mapSesqForms_formDual R functor hf eta hermf]
  simp [mapSesqForms, Functor.map_add, Functor.map_smul,
    hetaInv, smul_add, smul_smul, mul_comm]

/-- Transporting a nonsingular `(λ, Λ)`-quadratic form yields a nonsingular
`(eta⁻¹ * λ, Λ')`-quadratic form: `mapNonsingularSesqForm` gives invertibility
of `mapSesqForms`, and scaling by the unit `eta` preserves invertibility. -/
lemma mapNonsingularQuadraticForm {M : C}
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    (q : QuadraticForm R M Λ)
    (hq : isNonSingularQuadraticForm R Λ q) :
    isNonSingularQuadraticForm R Λ'
      (mapQuadraticForms R functor hf lam eta hcomp q) := by
  change IsIso
    (associatedHermitian R Λ' (functor.obj M)
      (mapQuadraticForms R functor hf lam eta hcomp q)).val
  rw [associatedHermitian_mapQuadraticForms R functor hf lam eta hermf hcomp]
  have hm := mapNonsingularSesqForm functor M hf
    (associatedHermitian R Λ M q).val hq
  let : IsIso
      (mapSesqForms functor hf (associatedHermitian R Λ M q).val) := hm
  -- Scale the inverse of `mapSesqForms ...` by `eta⁻¹`.
  refine ⟨⟨(((eta : Rˣ)⁻¹ : Rˣ) : R) •
      inv (mapSesqForms functor hf
        (associatedHermitian R Λ M q).val), ?_, ?_⟩⟩
  · simp [Linear.comp_smul, Linear.smul_comp, smul_smul]
  · simp [Linear.comp_smul, Linear.smul_comp, smul_smul]

/-! ## Induced functors on categories of quadratic forms -/

/-- Cast a quadratic-form category along an equality of parameters `lam1 = lam2`
and a matching pointwise equality of form parameters. -/
def castQuadraticCategories {lam1 lam2 : Z1Mul R} (hlam : lam1 = lam2)
    {Λ₁ : FormParameter (C := C) R lam1}
    {Λ₂ : FormParameter (C := C) R lam2}
    (hΛ : ∀ M : C, Λ₁.func M = Λ₂.func M) :
    QuadraticFormCat (C := C) R Λ₁ ⥤ QuadraticFormCat (C := C) R Λ₂ := by
  subst hlam
  have hEq : Λ₁ = Λ₂ := by
    ext M x
    rw [hΛ M]
  subst hEq
  exact Functor.id _

/-- Transport a nonsingular quadratic object along a compatible Hermitian functor. -/
def mapQuadraticObjects
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    (X : QuadraticObject (C := C) R Λ) :
    QuadraticObject (C := D) R Λ' where
  M := functor.obj X.M
  form := mapQuadraticForms R functor hf lam eta hcomp X.form
  nonsingular := mapNonsingularQuadraticForm R functor hf lam eta hermf hcomp X.form X.nonsingular

/-- Transport a quadratic isometry along a compatible Hermitian functor. -/
def mapQuadraticIsometry
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    {X Y : QuadraticObject (C := C) R Λ}
    (f : X ⟶ Y) :
    mapQuadraticObjects R functor hf lam eta hermf hcomp X ⟶
      mapQuadraticObjects R functor hf lam eta hermf hcomp Y := by
  have : IsIso f.val := f.property.1
  refine ⟨functor.map f.val, functor.map_isIso f.val, ?_⟩
  change pullbackQuadraticForm R Λ' (functor.map f.val)
      (mapQuadraticForms R functor hf lam eta hcomp Y.form) =
    mapQuadraticForms R functor hf lam eta hcomp X.form
  rw [← mapQuadraticForms_pullback, f.property.2]

/-- The induced functor on categories of nonsingular `(λ, Λ)`-quadratic forms. -/
def functorQuadraticCategories
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ') :
    QuadraticFormCat (C := C) R Λ ⥤ QuadraticFormCat (C := D) R Λ' where
  obj := mapQuadraticObjects R functor hf lam eta hermf hcomp
  map := mapQuadraticIsometry R functor hf lam eta hermf hcomp
  map_id X := by
    apply Subtype.ext
    exact functor.map_id X.M
  map_comp f g := by
    apply Subtype.ext
    exact functor.map_comp f.val g.val

/-! ## Equivalences and scaling for quadratic forms -/

/-- Faithfulness of `functor` implies faithfulness of `functorQuadraticCategories`. -/
lemma functorQuadraticCategories_faithful
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    [functor.Faithful] :
    (functorQuadraticCategories R functor hf lam eta hermf hcomp).Faithful where
  map_injective h := by
    apply Subtype.ext
    apply functor.map_injective
    exact congrArg Subtype.val h

/-- A fully faithful Hermitian functor satisfying `FormParameterReflects` induces a full
functor on quadratic-form categories. Reflection makes `mapQuadraticForms` injective,
which reflects the quadratic pullback equation from the target to the source. -/
lemma functorQuadraticCategories_full
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    (hrefl : FormParameterReflects R functor hf lam eta Λ Λ')
    [functor.Full] [functor.Faithful] :
    (functorQuadraticCategories R functor hf lam eta hermf hcomp).Full := by
  -- Reflection of form parameters implies injectivity of `mapQuadraticForms`.
  have hinj : ∀ M : C, Function.Injective
      (mapQuadraticForms R functor hf lam eta hcomp :
        QuadraticForm R M Λ → QuadraticForm R (functor.obj M) Λ') := by
    intro M a b hab
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk'_surjective (Λ.func M) a
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective (Λ.func M) b
    change (mapSesqForms functor hf q :
      Sesq (functor.obj M) ⧸ Λ'.func (functor.obj M)) =
      mapSesqForms functor hf r at hab
    change (q : Sesq M ⧸ Λ.func M) = r
    rw [QuotientAddGroup.eq_iff_sub_mem] at hab ⊢
    apply hrefl M (q - r)
    simpa [mapSesqForms, Functor.map_sub, Functor.map_smul,
      Linear.comp_smul] using hab
  refine ⟨?_⟩
  intro X Y f
  let g := functor.preimage f.val
  have hg : functor.map g = f.val := functor.map_preimage _
  let : IsIso (functor.map g) := by
    rw [hg]
    exact f.property.1
  let : IsIso g := isIso_of_reflects_iso g functor
  have hp : pullbackQuadraticForm R Λ g Y.form = X.form := by
    apply hinj X.M
    rw [mapQuadraticForms_pullback, hg]
    exact f.property.2
  refine ⟨⟨g, inferInstance, hp⟩, ?_⟩
  exact Subtype.ext hg

/-- A compatible equivalence of categories is essentially surjective on nonsingular
quadratic objects. Pull the target quadratic form back to `functor.obj M`, lift a
sesquilinear representative via `preimage`, and reflect nonsingularity through
`associatedHermitian_mapQuadraticForms`. -/
lemma functorQuadraticCategories_essSurj
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    [functor.IsEquivalence] :
    (functorQuadraticCategories R functor hf lam eta hermf hcomp).EssSurj := by
  refine ⟨?_⟩
  intro Y
  let M := functor.objPreimage Y.M
  let e : functor.obj M ≅ Y.M := functor.objObjPreimageIso Y.M
  let : IsIso e.hom := e.isIso_hom
  let qk := pullbackQuadraticForm R Λ' e.hom Y.form
  obtain ⟨k, hk⟩ :=
    QuotientAddGroup.mk'_surjective (Λ'.func (functor.obj M)) qk
  -- Lift `k` along `functor` and undo the comparison isomorphism `hf.nat_iso`.
  let h : Sesq M :=
    functor.preimage (k ≫ hf.nat_iso.inv.app (op M))
  have ht : mapSesqForms functor hf h = k := by
    simp [mapSesqForms, h, Category.assoc]
  let q : QuadraticForm R M Λ := toQuadraticForm R Λ M h
  have hqmap :
      mapQuadraticForms R functor hf lam eta hcomp q = qk := by
    change toQuadraticForm R Λ' (functor.obj M)
      (mapSesqForms functor hf h) = qk
    rw [ht]
    simpa [toQuadraticForm] using hk
  -- `qk` is nonsingular as a pullback of `Y.form` along the isomorphism `e.hom`.
  have hqkns : isNonSingularQuadraticForm R Λ' qk := by
    change IsIso (associatedHermitian R Λ' (functor.obj M) qk).val
    dsimp [qk]
    rw [associatedHermitian_pullback]
    let : IsIso
        (associatedHermitian R Λ' Y.M Y.form).val := Y.nonsingular
    infer_instance
  -- Cancel the unit `eta` and comparison `hf.nat_iso.hom` to reflect `IsIso` to `M`.
  have hscaled : IsIso (((eta : Rˣ) : R) •
      mapSesqForms functor hf
        (associatedHermitian R Λ M q).val) := by
    rw [← associatedHermitian_mapQuadraticForms R functor hf lam eta
      hermf hcomp, hqmap]
    exact hqkns
  let : IsIso (((eta : Rˣ) : R) •
      mapSesqForms functor hf
        (associatedHermitian R Λ M q).val) := hscaled
  have hm : IsIso
      (mapSesqForms functor hf
        (associatedHermitian R Λ M q).val) := by
    refine ⟨⟨((eta : Rˣ) : R) •
      inv (((eta : Rˣ) : R) •
        mapSesqForms functor hf
          (associatedHermitian R Λ M q).val), ?_, ?_⟩⟩
    · rw [Linear.comp_smul, ← Linear.smul_comp]
      exact IsIso.hom_inv_id _
    · rw [Linear.smul_comp, ← Linear.comp_smul]
      exact IsIso.inv_hom_id _
  let : IsIso
      (mapSesqForms functor hf
        (associatedHermitian R Λ M q).val) := hm
  have hc : IsIso
      (functor.map (associatedHermitian R Λ M q).val ≫
        hf.nat_iso.hom.app (op M)) := by
    change IsIso
      (mapSesqForms functor hf
        (associatedHermitian R Λ M q).val)
    infer_instance
  let : IsIso
      (functor.map (associatedHermitian R Λ M q).val ≫
        hf.nat_iso.hom.app (op M)) := hc
  have hfm : IsIso
      (functor.map (associatedHermitian R Λ M q).val) :=
    IsIso.of_isIso_comp_right
      (functor.map (associatedHermitian R Λ M q).val)
      (hf.nat_iso.hom.app (op M))
  let : IsIso
      (functor.map (associatedHermitian R Λ M q).val) := hfm
  have hq : isNonSingularQuadraticForm R Λ q :=
    isIso_of_reflects_iso
      (associatedHermitian R Λ M q).val functor
  let X : QuadraticObject (C := C) R Λ := ⟨M, q, hq⟩
  let f :
      (functorQuadraticCategories R functor hf lam eta hermf hcomp).obj X ⟶
        Y :=
    ⟨e.hom, e.isIso_hom, by
      change pullbackQuadraticForm R Λ' e.hom Y.form =
        mapQuadraticForms R functor hf lam eta hcomp q
      exact hqmap.symm⟩
  exact ⟨X, ⟨asIso f⟩⟩

/-- A linear equivalence equipped with a compatible, reflecting Hermitian comparison
induces an equivalence on categories of nonsingular quadratic forms. -/
lemma functorQuadraticCategoriesIsEquivalence
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    (hrefl : FormParameterReflects R functor hf lam eta Λ Λ')
    [functor.IsEquivalence] :
    (functorQuadraticCategories R functor hf lam eta hermf hcomp).IsEquivalence where
  faithful := functorQuadraticCategories_faithful R functor hf lam eta hermf hcomp
  full := functorQuadraticCategories_full R functor hf lam eta hermf hcomp hrefl
  essSurj := functorQuadraticCategories_essSurj R functor hf lam eta hermf hcomp

/-- Bundle the induced equivalence `QuadraticFormCat R Λ ≌ QuadraticFormCat R Λ'`. -/
noncomputable def equivalenceQuadraticCategories
    (hf : DualityComparison functor) (lam eta : Z1Mul R)
    (hermf : HermitianFunctor R functor hf eta)
    {Λ : FormParameter (C := C) R lam}
    {Λ' : FormParameter (C := D) R (eta⁻¹ * lam)}
    (hcomp : FormParameterCompatible R functor hf lam eta Λ Λ')
    (hrefl : FormParameterReflects R functor hf lam eta Λ Λ')
    [functor.IsEquivalence] :
    QuadraticFormCat (C := C) R Λ ≌ QuadraticFormCat (C := D) R Λ' :=
  letI := functorQuadraticCategoriesIsEquivalence R functor hf lam eta hermf hcomp hrefl
  (functorQuadraticCategories R functor hf lam eta hermf hcomp).asEquivalence

/-- Transport a form parameter along scaling by a unit `s : Rˣ`:
`Λ_scaled M = s • Λ M` is a form parameter for `(scalingParameter R s)⁻¹ * lam`. -/
def scalingFormParameter (s : Rˣ) (lam : Z1Mul R)
    (Λ : FormParameter (C := C) R lam) :
    FormParameter (C := C) R ((scalingParameter R s)⁻¹ * lam) where
  func M := (Λ.func M).map (DistribSMul.toAddMonoidHom (Sesq M) (s : R))
  subLambdaMin := by
    -- Scale a `LambdaMin` witness by `s⁻¹` to land in `Λ.func M`, then multiply by `s`.
    intro M h hh
    rw [mem_LambdaMin] at hh
    obtain ⟨q, rfl⟩ := hh
    let p : Sesq M := ((s⁻¹ : Rˣ) : R) • q
    refine ⟨p - ((lam : Rˣ) : R) • formDual p, ?_, ?_⟩
    · apply Λ.subLambdaMin M
      rw [mem_LambdaMin]
      exact ⟨p, rfl⟩
    · dsimp [p]
      rw [formDual_smul]
      change (s : R) •
        (((s⁻¹ : Rˣ) : R) • q -
          ((lam : Rˣ) : R) •
            (star (((s⁻¹ : Rˣ) : R)) • formDual q)) =
        q - ((((scalingParameter R s)⁻¹ * lam : Z1Mul R) : Rˣ) : R) •
          formDual q
      rw [smul_sub, smul_smul, smul_smul, smul_smul]
      have hs :
          ((s : R) * ((lam : Rˣ) : R) *
            star (((s⁻¹ : Rˣ) : R))) =
          ((((scalingParameter R s)⁻¹ * lam : Z1Mul R) : Rˣ) : R) := by
        simp [scalingParameter]
        ac_rfl
      rw [hs]
      simp
  supLambdaMax := by
    -- Transport `Λ.supLambdaMax` along the scaling Hermitian functor.
    intro M h hh
    obtain ⟨q, hq, rfl⟩ := hh
    simpa using mapSesqForms_mem_LambdaMax R (Functor.id C)
      (scalingFunctorCat R s) lam (scalingParameter R s)
      (scalingFunctorCat_hermitian R s) (Λ.supLambdaMax M hq)
  pullback := by
    -- Pullback commutes with scalar multiplication by `s`.
    intro M N h hh f
    obtain ⟨q, hq, rfl⟩ := hh
    refine
      ⟨f ≫ q ≫ HermitianCategory.duality.map f.op,
        Λ.pullback hq f, ?_⟩
    simp [Linear.comp_smul, Linear.smul_comp]
  smul := by
    -- Commutativity of `R` lets self-adjoint scalars pass through `s • ·`.
    intro M h hh r hr
    obtain ⟨q, hq, rfl⟩ := hh
    refine ⟨r • q, Λ.smul hq hr, ?_⟩
    simp [smul_smul, mul_comm]

/-- Scaling by a unit `s : Rˣ` induces a functor on categories of nonsingular quadratic forms. -/
def scalingQuadraticCategories (s : Rˣ) (lam : Z1Mul R)
    (Λ : FormParameter (C := C) R lam) :
    QuadraticFormCat (C := C) R Λ ⥤
      QuadraticFormCat (C := C) R (scalingFormParameter R s lam Λ) :=
  functorQuadraticCategories R (Functor.id C) (scalingFunctorCat R s)
    lam (scalingParameter R s) (scalingFunctorCat_hermitian R s)
    (by
      intro M q hq
      exact ⟨q, hq, by simp [mapSesqForms, scalingFunctorCat]⟩)

/-- Scaling by a unit `s : Rˣ` is an equivalence of quadratic-form categories. -/
lemma scalingQuadraticIsEquivalence (s : Rˣ) (lam : Z1Mul R)
    (Λ : FormParameter (C := C) R lam) :
    (scalingQuadraticCategories R s lam Λ).IsEquivalence := by
  exact functorQuadraticCategoriesIsEquivalence R (Functor.id C)
    (scalingFunctorCat R s) lam (scalingParameter R s)
    (scalingFunctorCat_hermitian R s)
    (by
      intro M q hq
      simp only [scalingFunctorCat_mapSesq, Functor.id_obj,
        scalingFormParameter]
      exact ⟨q, hq, rfl⟩)
    (by
      -- Cancel `s • ·` with `s⁻¹ • ·` to reflect `scalingFormParameter`.
      intro M q hq
      rw [scalingFunctorCat_mapSesq] at hq
      obtain ⟨h, hh, heq⟩ := hq
      have heq' :=
        congrArg
          (fun k : Sesq M => ((s⁻¹ : Rˣ) : R) • k) heq
      have : h = q := by
        simpa [smul_smul] using heq'
      simpa [this] using hh)
