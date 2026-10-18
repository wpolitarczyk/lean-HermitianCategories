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
  /-- At `op X`, the forward component goes from D_D(F(X)) to F(D_C(X)).
  Here D_C and D_D denote the dualities on C and D respectively. -/
  nat_iso : functor.op ⋙ (HermitianCategory.duality (C := D)) ≅ (HermitianCategory.duality (C := C) ⋙ functor)

/-- A comparison satisfying ordinary double-dual coherence.
Use `toDualityComparison` to supply its comparison to the transport constructions. -/
structure DualityPreservingFunctor (functor : C ⥤ D)
    extends DualityComparison functor where
  /-- Both sides go from F(X) to F(D_C²(X)). The right side first uses the
  double-dual map in D, then the dual of the inverse comparison at X, and finally
  the forward comparison at D_C(X). Naturality alone does not impose this condition. -/
  coherence : ∀ X : C,
    functor.map ((HermitianCategory.doubleDualIso (C := C)).hom.app X) =
    (HermitianCategory.doubleDualIso (C := D)).hom.app (functor.obj X) ≫
    (HermitianCategory.duality (C := D)).map (nat_iso.inv.app (op X)).op ≫
    nat_iso.hom.app (op ((HermitianCategory.duality (C := C)).obj (op X)))

/-- Compose comparisons of dualities for F and G.
At X, the forward component is the composite
`D_E(G(F(X))) ⟶ G(D_D(F(X))) ⟶ G(F(D_C(X)))`:
first use G's comparison at F(X), then apply G to F's comparison at X.
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
    change (F.op ⋙ G.op) ⋙ DE ≅ DC ⋙ (F ⋙ G)
    -- Associators align the source and target of the two whiskered comparisons.
    -- Their components are identities; only the comparison maps change the forms.
    calc  (F.op ⋙ G.op) ⋙ DE
      _ ≅ F.op ⋙ (G.op ⋙ DE) := by apply Functor.associator
      -- Evaluate G's comparison on objects and arrows coming from F.op.
      _ ≅ F.op ⋙ (DD ⋙ G) := by apply Functor.isoWhiskerLeft F.op hg.nat_iso
      _ ≅ (F.op ⋙ DD) ⋙ G := by apply Functor.associator
      -- Apply G to the components of F's comparison.
      _ ≅ (DC ⋙ F) ⋙ G := by apply Functor.isoWhiskerRight hf.nat_iso G
      _ ≅ DC ⋙ (F ⋙ G) := by apply Functor.associator

/-- The identity functor carries a canonical comparison of dualities.
Identify its opposite with the identity on Cᵒᵖ, then use the unitors to compare
`Id ⋙ D` with `D ⋙ Id`. Both comparison components are identity morphisms. -/
def IdIsDualityComparison : DualityComparison (Functor.id C) := by
  let DC := HermitianCategory.duality (C := C)
  refine ⟨?_⟩
  change (Functor.id C).op ⋙ DC ≅ DC ⋙ (Functor.id C)
  calc (Functor.id C).op ⋙ DC
    -- Whisker the comparison of opposite identity functors by the duality.
    _ ≅ (Functor.id Cᵒᵖ) ⋙ DC := by apply Functor.isoWhiskerRight (Functor.opId C) DC
    -- Remove the identity on the left and insert it on the right.
    _ ≅ DC                      := by apply Functor.leftUnitor DC
    _ ≅ DC ⋙ (Functor.id C)    := by apply Functor.rightUnitor DC

/-- Compose duality-preserving functors using `compDualityComparison`.
The composite satisfies ordinary double-dual coherence: expand coherence for F
and G, then use naturality of G's comparison at the opposite of F's inverse
comparison. No preadditivity or scalar structure is needed. -/
def compDualityPreservingFunctor {E : Type u} [Category.{v} E] [HermitianCategory E]
  (F : C ⥤ D)
  (G : D ⥤ E)
  (hf : DualityPreservingFunctor F)
  (hg : DualityPreservingFunctor G) :
  (DualityPreservingFunctor (F ⋙ G)) := by
    -- Retain the comparison data; the remaining field is its coherence proof.
    -- A local `let` allows the comparison to be unfolded below.
    let hDC : DualityComparison (F ⋙ G) := compDualityComparison F G hf.toDualityComparison hg.toDualityComparison

    refine { toDualityComparison := hDC, coherence := ?_ }
    intro X
    -- Expand the composite comparison, including the transitivity steps in `calc`.
    dsimp [hDC, compDualityComparison, Trans.trans]
    simp only [Category.id_comp, Category.comp_id]
    -- Apply coherence first for F, then for G.
    rw [hf.coherence, G.map_comp, G.map_comp, hg.coherence]
    simp only [Functor.map_comp, Category.assoc]
    -- Move the dual of F's inverse comparison past G's comparison.
    -- `naturality_assoc` includes the final postcomposition by G's image of
    -- F's comparison at D_C(X), matching the right-associated goal.
    have hn := hg.nat_iso.hom.naturality_assoc
      (hf.nat_iso.inv.app (op X)).op
      (G.map (hf.nat_iso.hom.app
        (op ((HermitianCategory.duality (C := C)).obj (op X)))))
    dsimp at hn
    rw [← hn]

/-- The canonical identity comparison satisfies double-dual coherence.
Its components are identities, so coherence reduces to preservation of identity
morphisms by the duality and the identity laws for composition. -/
def IdIsDualityPreservingFunctor : DualityPreservingFunctor (Functor.id C) := by
  -- Reuse the comparison data and supply only the additional coherence field.
  let idDC : DualityComparison (Functor.id C) := IdIsDualityComparison

  refine { toDualityComparison := idDC, coherence := ?_ }
  intro X
  -- Unfold the comparison and the isomorphism compositions from its `calc` block.
  dsimp [idDC, IdIsDualityComparison, Trans.trans]
  -- The forward and inverse components of `opId` are identities.
  simp only [Functor.opId_hom_app, Functor.opId_inv_app]
  -- Specialize `map_id` to the duality so simplification matches its map expressions.
  -- Opposites of identities and composition with identities then simplify away.
  simp only [(HermitianCategory.duality (C := C)).map_id,
    op_id, Category.comp_id]

/-! ## Transport of sesquilinear forms along comparisons of dualities -/

/-- Transport a sesquilinear form along a functor with a comparison of dualities.
`F.map h` ends at F(D_C(M)), so the inverse comparison changes its target to
D_D(F(M)). The component is evaluated at `op M` because the comparison is
between functors on Cᵒᵖ. This construction itself does not use coherence. -/
def mapSesqForms {M : C} (F : C ⥤ D)
 (hf : DualityComparison F) (h : Sesq M) : Sesq (F.obj M) :=
  (F.map h) ≫ (hf.nat_iso.inv.app (op M))

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
by an inverse comparison component is again an isomorphism. -/
lemma mapNonsingularSesqForm (M : C)
    (hf : DualityComparison functor)
    (h : Sesq M) (h_nonsing : isNonSingular h) :
    isNonSingular (mapSesqForms functor hf h) := by
  -- Register the supplied proof so typeclass inference can use preservation
  -- of isomorphisms by functors and closure under composition.
  let _ : IsIso h := h_nonsing
  change IsIso (functor.map h ≫ hf.nat_iso.inv.app (op M))
  infer_instance
