/-
Copyright (c) 2026 Wojciech Politarczyk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Politarczyk
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Hermitian Categories

This file defines categories with duality, sesquilinear forms, and natural comparisons
of dualities, with ordinary double-dual coherence as a separate requirement.
Comparisons compose by whiskering their natural isomorphisms; the composite
preserves double-dual coherence when both original comparisons do.
`HermitianForms` adds λ-Hermitian forms
and their isometries, using the parameters from `TateCohomology`.

Composition is written in diagrammatic order: `f ≫ g` means first f, then g.
For `D : Cᵒᵖ ⥤ C`, the dual of an object M is `D.obj (op M)`, whereas the dual
of a morphism f is `D.map f.op`. Taking opposites reverses the arrows; D itself
is an ordinary covariant functor whose domain is the opposite category.

Transport of sesquilinear forms requires only a natural comparison of dualities.
Preadditivity additionally gives each space of forms an abelian group structure.
-/

set_option linter.style.emptyLine false
set_option linter.style.docString false
set_option linter.style.longLine false

open CategoryTheory
open Opposite

-- Objects live in universe u and morphisms in universe v; these need not coincide.
universe v u

/-- A category with a duality functor, a double-dual identification, and coherence. -/
class HermitianCategory (C : Type u) [Category.{v} C] where
  /-- The contravariant duality functor (often denoted by * or D). -/
  duality : Cᵒᵖ ⥤ C

  /-- The double-dual identification. `rightOp` turns D into a functor C ⥤ Cᵒᵖ,
  so `duality.rightOp ⋙ duality` has both source and target C. -/
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
`Sesq M` abbreviates the type of sesquilinear forms on M.
--/
abbrev Sesq (M : C) := SesquilinearForm M

/-- A form is nonsingular when its associated morphism M ⟶ D(M) is an isomorphism.
This is a property of the form, distinct from invertibility of an isometry between forms. -/
abbrev isNonSingular {M : C} (f : Sesq M) : Prop :=
  IsIso f

-- To guarantee that Sesq M is an abelian group, we require the category C
-- to be preadditive.
variable [Preadditive C]

/--
Because C is a preadditive category, every Hom-set in C is automatically
an abelian group. `Sesq M` inherits this structure by unfolding its abbreviation.
--/

instance (M : C) : AddCommGroup (Sesq M) :=
  inferInstance

/-! ## Duality preserving functors -/

variable {C : Type u} [Category.{v} C] [HermitianCategory C]
variable {D : Type u} [Category.{v} D] [HermitianCategory D]

/-- A natural comparison between the dualities, without a coherence condition.
The underlying functor is a parameter; this structure supplies its additional data. -/
structure DualityComparison (functor : C ⥤ D) where
  /-- At `op X`, the forward component goes from F(D_C(X)) to D_D(F(X)).
  Here D_C and D_D denote the dualities on C and D respectively. -/
  nat_iso : (HermitianCategory.duality (C := C) ⋙ functor) ≅ functor.op ⋙ (HermitianCategory.duality (C := D))

/-- A comparison satisfying ordinary double-dual coherence.
Use `toDualityComparison` to supply its comparison to the transport constructions. -/
structure DualityPreservingFunctor (functor : C ⥤ D)
    extends DualityComparison functor where
  /-- Both sides go from F(X) to D_D(F(D_C(X))). The left side uses the
  target double-dual map and the dual of the forward comparison; the right side
  uses the image of the source double-dual map and the forward comparison.
  Naturality alone does not impose this condition. -/
  coherence : ∀ X : C,
    (HermitianCategory.doubleDualIso (C := D)).hom.app (functor.obj X) ≫
    (HermitianCategory.duality (C := D)).map (nat_iso.hom.app (op X)).op =
    functor.map ((HermitianCategory.doubleDualIso (C := C)).hom.app X) ≫
    nat_iso.hom.app (op ((HermitianCategory.duality (C := C)).obj (op X)))

/-- Compose comparisons of dualities for F and G.
At X, the forward component is the composite
`G(F(D_C(X))) ⟶ G(D_D(F(X))) ⟶ D_E(G(F(X)))`:
first apply G to F's comparison at X, then use G's comparison at F(X).
Whiskering and associators supply naturality, without any coherence assumptions. -/
def compDualityComparison {E : Type u} [Category.{v} E] [HermitianCategory E]
  (F : C ⥤ D)
  (G : D ⥤ E)
  (hf : DualityComparison F)
  (hg : DualityComparison G) :
  (DualityComparison (F ⋙ G)) := by
    let DC := HermitianCategory.duality (C := C)
    let DD := HermitianCategory.duality (C := D)
    let DE := HermitianCategory.duality (C := E)
    -- Construct the single `nat_iso` field of the comparison.
    refine ⟨?_⟩
    -- Opposites commute definitionally with functor composition.
    change DC ⋙ (F ⋙ G) ≅ (F.op ⋙ G.op) ⋙ DE
    -- Whisker F's comparison by G, then G's comparison by F.op.
    calc DC ⋙ (F ⋙ G)
      _ ≅ (DC ⋙ F) ⋙ G := (Functor.associator DC F G).symm
      _ ≅ (F.op ⋙ DD) ⋙ G := Functor.isoWhiskerRight hf.nat_iso G
      _ ≅ F.op ⋙ (DD ⋙ G) := Functor.associator F.op DD G
      _ ≅ F.op ⋙ (G.op ⋙ DE) := Functor.isoWhiskerLeft F.op hg.nat_iso
      _ ≅ (F.op ⋙ G.op) ⋙ DE := (Functor.associator F.op G.op DE).symm

/-- The forward composite comparison first uses the image of F's comparison, then G's. -/
@[simp]
lemma compDualityComparison_hom_app {E : Type u} [Category.{v} E] [HermitianCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (hf : DualityComparison F) (hg : DualityComparison G)
    (X : Cᵒᵖ) :
    (compDualityComparison F G hf hg).nat_iso.hom.app X =
      G.map (hf.nat_iso.hom.app X) ≫ hg.nat_iso.hom.app (F.op.obj X) := by
  simp [compDualityComparison, Trans.trans]

/-- The inverse composite comparison applies the inverse components in reverse order. -/
@[simp]
lemma compDualityComparison_inv_app {E : Type u} [Category.{v} E] [HermitianCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (hf : DualityComparison F) (hg : DualityComparison G)
    (X : Cᵒᵖ) :
    (compDualityComparison F G hf hg).nat_iso.inv.app X =
      hg.nat_iso.inv.app (F.op.obj X) ≫ G.map (hf.nat_iso.inv.app X) := by
  simp [compDualityComparison, Trans.trans]

/-- The identity functor carries a canonical comparison of dualities.
Identify its opposite with the identity on Cᵒᵖ, then use the unitors to compare
`D ⋙ Id` with `Id ⋙ D`. Both comparison components are identity morphisms. -/
def IdIsDualityComparison : DualityComparison (Functor.id C) := by
  let DC := HermitianCategory.duality (C := C)
  refine ⟨?_⟩
  change DC ⋙ (Functor.id C) ≅ (Functor.id C).op ⋙ DC
  calc DC ⋙ (Functor.id C)
    _ ≅ DC := Functor.rightUnitor DC
    _ ≅ (Functor.id Cᵒᵖ) ⋙ DC := (Functor.leftUnitor DC).symm
    _ ≅ (Functor.id C).op ⋙ DC :=
      Functor.isoWhiskerRight (Functor.opId C).symm DC

/-- The forward component of the identity comparison is an identity morphism. -/
@[simp]
lemma IdIsDualityComparison_hom_app (X : Cᵒᵖ) :
    (IdIsDualityComparison (C := C)).nat_iso.hom.app X =
      𝟙 (HermitianCategory.duality.obj X) := by
  simp [IdIsDualityComparison, Trans.trans]

/-- The inverse component of the identity comparison is an identity morphism. -/
@[simp]
lemma IdIsDualityComparison_inv_app (X : Cᵒᵖ) :
    (IdIsDualityComparison (C := C)).nat_iso.inv.app X =
      𝟙 (HermitianCategory.duality.obj X) := by
  simp [IdIsDualityComparison, Trans.trans]

/-- Compose duality-preserving functors using `compDualityComparison`.
The composite satisfies ordinary double-dual coherence: expand coherence for F
and G, then use naturality of G's comparison at the opposite of F's forward
comparison. No preadditivity or scalar structure is needed. -/
def compDualityPreservingFunctor {E : Type u} [Category.{v} E] [HermitianCategory E]
  (F : C ⥤ D)
  (G : D ⥤ E)
  (hf : DualityPreservingFunctor F)
  (hg : DualityPreservingFunctor G) :
  (DualityPreservingFunctor (F ⋙ G)) := by
    -- Retain the comparison data; the remaining field is its coherence proof.
    let hDC : DualityComparison (F ⋙ G) := compDualityComparison F G hf.toDualityComparison hg.toDualityComparison

    refine { toDualityComparison := hDC, coherence := ?_ }
    intro X
    -- Use the component formulas without unfolding the whiskering construction.
    simp only [hDC, compDualityComparison_hom_app,
      Functor.comp_map, Functor.comp_obj, Functor.op_obj, op_comp, Functor.map_comp]
    -- Naturality moves the dual of F's comparison past G's comparison.
    have hn := hg.nat_iso.hom.naturality (hf.nat_iso.hom.app (op X)).op
    dsimp at hn
    rw [← Category.assoc, hg.coherence, Category.assoc, ← hn,
      ← Category.assoc, ← G.map_comp, hf.coherence, G.map_comp, Category.assoc]

/-- The canonical identity comparison satisfies double-dual coherence.
Its components are identities, so coherence reduces to preservation of identity
morphisms by the duality and the identity laws for composition. -/
def IdIsDualityPreservingFunctor : DualityPreservingFunctor (Functor.id C) := by
  -- Reuse the comparison data and supply only the additional coherence field.
  let idDC : DualityComparison (Functor.id C) := IdIsDualityComparison

  refine { toDualityComparison := idDC, coherence := ?_ }
  intro X
  simp [idDC]

/-! ## Transport of sesquilinear forms along comparisons of dualities -/

/-- Transport a sesquilinear form along a functor with a comparison of dualities.
`F.map h` ends at F(D_C(M)), so the forward comparison changes its target to
D_D(F(M)). The component is evaluated at `op M` because the comparison is
between functors on Cᵒᵖ. This construction itself does not use coherence. -/
def mapSesqForms {M : C} (F : C ⥤ D)
 (hf : DualityComparison F) (h : Sesq M) : Sesq (F.obj M) :=
  (F.map h) ≫ (hf.nat_iso.hom.app (op M))

/-- A faithful functor with a duality comparison transports forms injectively. -/
lemma mapSesqForms_injective (functor : C ⥤ D) (hf : DualityComparison functor) [functor.Faithful]
    {M : C} : Function.Injective (mapSesqForms functor hf (M := M)) := by
  intro h k heq
  -- Cancel the forward comparison, then reflect equality through the faithful functor.
  apply functor.map_injective
  exact (cancel_mono (hf.nat_iso.hom.app (op M))).mp heq

/-- Transport commutes with pullback of sesquilinear forms. -/
lemma mapSesqForms_pullback (functor : C ⥤ D) (hf : DualityComparison functor)
    {M N : C} (f : M ⟶ N) (h : Sesq N) :
    mapSesqForms functor hf (f ≫ h ≫ HermitianCategory.duality.map f.op) =
      functor.map f ≫ mapSesqForms functor hf h ≫
        HermitianCategory.duality.map (functor.map f).op := by
  have hn := hf.nat_iso.hom.naturality f.op
  dsimp at hn
  simp only [mapSesqForms, Functor.map_comp, Category.assoc]
  rw [hn]

variable [Preadditive C] [Preadditive D] (functor : C ⥤ D) [Functor.Additive functor]

/-- Package transport as an additive homomorphism on spaces of forms.
Additivity of the functor and bilinearity of composition give preservation of
zero and addition; double-dual coherence is not required. -/
def mapSesqFormsHom (M : C) (hf : DualityComparison functor) : Sesq M →+ Sesq (functor.obj M) where
  toFun := mapSesqForms functor hf

  map_zero' := by
    unfold mapSesqForms
    rw [Functor.map_zero, CategoryTheory.Limits.zero_comp]

  map_add' := by
    unfold mapSesqForms
    intro x y
    rw [Functor.Additive.map_add, Preadditive.add_comp]

omit [Preadditive C] [Preadditive D] in
/-- Transport preserves nonsingularity: the image of an isomorphism followed
by a forward comparison component is again an isomorphism. -/
lemma mapNonsingularSesqForm (M : C)
    (hf : DualityComparison functor)
    (h : Sesq M) (h_nonsing : isNonSingular h) :
    isNonSingular (mapSesqForms functor hf h) := by
  -- Register the supplied proof so typeclass inference can use preservation
  -- of isomorphisms by functors and closure under composition.
  let _ : IsIso h := h_nonsing
  change IsIso (functor.map h ≫ hf.nat_iso.hom.app (op M))
  infer_instance
