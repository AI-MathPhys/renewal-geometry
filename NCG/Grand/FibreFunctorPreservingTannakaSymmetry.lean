/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandTannaka
import Mathlib.CategoryTheory.Conj

/-!
# Fibre-functor-preserving finite Tannaka symmetry

This file proves `cor:Tannaka-group-iso` from the data stated in the
Gran-Tensor manuscript.  The categorical step missing from
`NCG.Grand.GrandTannaka` is made explicit: precomposition by a monoidal
equivalence induces an isomorphism on groups of monoidal natural
automorphisms.  Conjugating by the fibre-functor comparison then identifies
the two Tannaka automorphism groups.
-/

noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace NCG

namespace FibreFunctorTannaka



variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- Whiskering a natural isomorphism on the right, in isomorphism form. -/
def natIsoWhiskerRight {F G : C ⥤ D} (α : F ≅ G) (K : D ⥤ E) :
    F ⋙ K ≅ G ⋙ K where
  hom := Functor.whiskerRight α.hom K
  inv := Functor.whiskerRight α.inv K

/-- Precomposition by a monoidal functor, bundled as a functor between
categories of lax-monoidal functors. -/
def precomposeLaxMonoidal (F : C ⥤ D) [F.LaxMonoidal] :
    LaxMonoidalFunctor D E ⥤ LaxMonoidalFunctor C E where
  obj ω := LaxMonoidalFunctor.of (F ⋙ ω.toFunctor)
  map η :=
    { hom := Functor.whiskerLeft F η.hom
      isMonoidal := NatTrans.IsMonoidal.whiskerLeft η.hom }
  map_id ω := by
    apply LaxMonoidalFunctor.hom_ext
    ext X
    rfl
  map_comp η θ := by
    apply LaxMonoidalFunctor.hom_ext
    ext X
    rfl

@[simp]
theorem precomposeLaxMonoidal_map_hom_app (F : C ⥤ D) [F.LaxMonoidal]
    {ω ν : LaxMonoidalFunctor D E} (η : ω ⟶ ν) (X : C) :
    (((precomposeLaxMonoidal (E := E) F).map η).hom.app X) =
      η.hom.app (F.obj X) := rfl

@[simp]
theorem precomposeLaxMonoidal_mapAut_hom_app (F : C ⥤ D) [F.LaxMonoidal]
    (ω : LaxMonoidalFunctor D E) (η : CategoryTheory.Aut ω) (X : C) :
    ((Functor.mapAut ω (precomposeLaxMonoidal (E := E) F) η).hom.hom.app X) =
      η.hom.hom.app (F.obj X) := rfl

/-- The monoidal natural isomorphism which cancels precomposition first by
an equivalence and then by its inverse. -/
def cancelPrecompositionIso (e : C ≌ D) [e.functor.Monoidal]
    [e.inverse.Monoidal] [e.IsMonoidal] (ω : LaxMonoidalFunctor D E) :
    (precomposeLaxMonoidal (E := E) e.inverse).obj
        ((precomposeLaxMonoidal (E := E) e.functor).obj ω) ≅ ω := by
  let α := (Functor.associator e.inverse e.functor ω.toFunctor).symm
  let β := natIsoWhiskerRight e.counitIso ω.toFunctor
  let γ := Functor.leftUnitor ω.toFunctor
  let ω₀ := LaxMonoidalFunctor.of
    ((e.inverse ⋙ e.functor) ⋙ ω.toFunctor)
  let ω₁ := LaxMonoidalFunctor.of ((𝟭 D) ⋙ ω.toFunctor)
  let src := LaxMonoidalFunctor.of
    (e.inverse ⋙ e.functor ⋙ ω.toFunctor)
  let iα : src ≅ ω₀ := by
    letI : src.toFunctor.LaxMonoidal := src.laxMonoidal
    letI : ω₀.toFunctor.LaxMonoidal := ω₀.laxMonoidal
    let hα : NatTrans.IsMonoidal α.hom := by dsimp [α, src, ω₀]; infer_instance
    exact @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ src ω₀ α hα
  let iβ : ω₀ ≅ ω₁ := by
    letI : ω₀.toFunctor.LaxMonoidal := ω₀.laxMonoidal
    letI : ω₁.toFunctor.LaxMonoidal := ω₁.laxMonoidal
    let hβ : NatTrans.IsMonoidal β.hom := by
      dsimp [β, natIsoWhiskerRight, ω₀, ω₁]
      infer_instance
    exact @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ ω₀ ω₁ β hβ
  let iγ : ω₁ ≅ ω := by
    letI : ω₁.toFunctor.LaxMonoidal := ω₁.laxMonoidal
    letI : ω.toFunctor.LaxMonoidal := ω.laxMonoidal
    let hγ : NatTrans.IsMonoidal γ.hom := by dsimp [γ, ω₁]; infer_instance
    exact @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ ω₁ ω γ hγ
  exact iα.trans (iβ.trans iγ)

@[simp]
theorem cancelPrecompositionIso_hom_app (e : C ≌ D) [e.functor.Monoidal]
    [e.inverse.Monoidal] [e.IsMonoidal] (ω : LaxMonoidalFunctor D E) (X : D) :
    (cancelPrecompositionIso e ω).hom.hom.app X =
      ω.map (e.counitIso.hom.app X) := by
  change 𝟙 _ ≫ ω.map (e.counitIso.hom.app X) ≫ 𝟙 _ = _
  simp

@[simp]
theorem cancelPrecompositionIso_inv_app (e : C ≌ D) [e.functor.Monoidal]
    [e.inverse.Monoidal] [e.IsMonoidal] (ω : LaxMonoidalFunctor D E) (X : D) :
    (cancelPrecompositionIso e ω).inv.hom.app X =
      ω.map (e.counitIso.inv.app X) := by
  let i := cancelPrecompositionIso e ω
  let j : ((precomposeLaxMonoidal (E := E) e.inverse).obj
      ((precomposeLaxMonoidal (E := E) e.functor).obj ω)).toFunctor ≅
      ω.toFunctor :=
    { hom := i.hom.hom
      inv := i.inv.hom
      hom_inv_id := by
        simpa only [LaxMonoidalFunctor.comp_hom,
          LaxMonoidalFunctor.id_hom] using
            congrArg (fun f => f.hom) i.hom_inv_id
      inv_hom_id := by
        simpa only [LaxMonoidalFunctor.comp_hom,
          LaxMonoidalFunctor.id_hom] using
            congrArg (fun f => f.hom) i.inv_hom_id }
  letI : IsIso (j.hom.app X) := NatIso.hom_app_isIso j X
  apply (cancel_mono (j.hom.app X)).1
  change j.inv.app X ≫ j.hom.app X =
    ω.map (e.counitIso.inv.app X) ≫ j.hom.app X
  rw [j.inv_hom_id_app]
  simp [j, i, cancelPrecompositionIso_hom_app, ← ω.map_comp]

@[simp]
theorem conjugateLaxAutomorphism_hom_app
    {ω ν : LaxMonoidalFunctor D E} (i : ω ≅ ν)
    (η : CategoryTheory.Aut ω) (X : D) :
    (CategoryTheory.Aut.autMulEquivOfIso i η).hom.hom.app X =
      i.inv.hom.app X ≫ η.hom.hom.app X ≫ i.hom.hom.app X := rfl

/-- Descend a tensor automorphism through a monoidal equivalence, using the
counit to compare the twice-precomposed fibre functor with the original one. -/
def descendAutomorphism (e : C ≌ D) [e.functor.Monoidal]
    [e.inverse.Monoidal] [e.IsMonoidal] (ω : LaxMonoidalFunctor D E)
    (η : CategoryTheory.Aut
      ((precomposeLaxMonoidal (E := E) e.functor).obj ω)) :
    CategoryTheory.Aut ω :=
  CategoryTheory.Aut.autMulEquivOfIso (cancelPrecompositionIso e ω)
    (Functor.mapAut _ (precomposeLaxMonoidal (E := E) e.inverse) η)

@[simp]
theorem descendAutomorphism_hom_app (e : C ≌ D) [e.functor.Monoidal]
    [e.inverse.Monoidal] [e.IsMonoidal] (ω : LaxMonoidalFunctor D E)
    (η : CategoryTheory.Aut
      ((precomposeLaxMonoidal (E := E) e.functor).obj ω)) (X : D) :
    (descendAutomorphism e ω η).hom.hom.app X =
      ω.map (e.counitIso.inv.app X) ≫
        η.hom.hom.app (e.inverse.obj X) ≫
          ω.map (e.counitIso.hom.app X) := by
  rw [descendAutomorphism, conjugateLaxAutomorphism_hom_app,
    cancelPrecompositionIso_inv_app, cancelPrecompositionIso_hom_app,
    precomposeLaxMonoidal_mapAut_hom_app]
  rfl

/-- Precomposition by a monoidal equivalence is an isomorphism on the
automorphism group of every lax-monoidal functor. -/
def automorphismsEquivOfPrecomposition (e : C ≌ D) [e.functor.Monoidal]
    [e.inverse.Monoidal] [e.IsMonoidal] (ω : LaxMonoidalFunctor D E) :
    CategoryTheory.Aut ω ≃* CategoryTheory.Aut
      ((precomposeLaxMonoidal (E := E) e.functor).obj ω) where
  toFun := Functor.mapAut ω (precomposeLaxMonoidal (E := E) e.functor)
  invFun η := descendAutomorphism e ω η
  left_inv η := by
    ext X
    simp only [descendAutomorphism_hom_app,
      precomposeLaxMonoidal_mapAut_hom_app]
    change ω.map (e.counitIso.inv.app X) ≫
        η.hom.hom.app (e.functor.obj (e.inverse.obj X)) ≫
          ω.map (e.counitIso.hom.app X) = η.hom.hom.app X
    have hnat :
        ω.map (e.counitIso.hom.app X) ≫ η.hom.hom.app X =
          η.hom.hom.app (e.functor.obj (e.inverse.obj X)) ≫
            ω.map (e.counitIso.hom.app X) :=
      η.hom.hom.naturality (e.counitIso.hom.app X)
    rw [← hnat]
    simp
  right_inv η := by
    ext X
    simp only [precomposeLaxMonoidal_mapAut_hom_app,
      descendAutomorphism_hom_app]
    change ω.map (e.counitIso.inv.app (e.functor.obj X)) ≫
        η.hom.hom.app (e.inverse.obj (e.functor.obj X)) ≫
          ω.map (e.counitIso.hom.app (e.functor.obj X)) = η.hom.hom.app X
    rw [e.counitInv_app_functor, e.counit_app_functor]
    change ((precomposeLaxMonoidal (E := E) e.functor).obj ω).map
          (e.unitIso.hom.app X) ≫
        η.hom.hom.app ((e.functor ⋙ e.inverse).obj X) ≫
          ((precomposeLaxMonoidal (E := E) e.functor).obj ω).map
            (e.unitIso.inv.app X) = η.hom.hom.app X
    rw [η.hom.hom.naturality_assoc (e.unitIso.hom.app X)]
    simp
  map_mul' η θ := by
    simp

end FibreFunctorTannaka

open TannakaDuality.FiniteGroup

/-- A monoidal equivalence of representation categories, together with a
monoidal comparison of the fibre functors, identifies their tensor
automorphism groups. -/
noncomputable def fibreFunctorAutomorphismEquiv
    {G H : Type} [Group G] [Group H]
    (e : FDRep ℂ G ≌ FDRep ℂ H) [e.functor.Monoidal]
    [e.inverse.Monoidal] [e.IsMonoidal]
    (ι : (FibreFunctorTannaka.precomposeLaxMonoidal
        (E := FGModuleCat ℂ) e.functor).obj (forget ℂ H) ≅ forget ℂ G) :
    CategoryTheory.Aut (forget ℂ H) ≃*
      CategoryTheory.Aut (forget ℂ G) :=
  (FibreFunctorTannaka.automorphismsEquivOfPrecomposition e (forget ℂ H)).trans
    (CategoryTheory.Aut.autMulEquivOfIso ι)

/-- `cor:Tannaka-group-iso` (fibre-functor-preserving duality determines the
symmetry): a symmetric monoidal equivalence
`Rep(G) ≌ Rep(H)` whose pulled-back fibre functor is monoidally isomorphic to
the original fibre functor induces `G ≃* H`.

The manuscript assumes the comparison is unitary.  The algebraic Tannaka
argument only uses its underlying monoidal natural isomorphism, so the theorem
is stated under that weaker hypothesis. -/
noncomputable def fibreFunctorPreservingTannakaGroupIso
    {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : FDRep ℂ G ≌ FDRep ℂ H) [e.functor.Monoidal]
    [e.inverse.Monoidal] [e.IsMonoidal]
    (ι : (FibreFunctorTannaka.precomposeLaxMonoidal
        (E := FGModuleCat ℂ) e.functor).obj (forget ℂ H) ≅ forget ℂ G) :
    G ≃* H :=
  tannaka_group_iso (fibreFunctorAutomorphismEquiv e ι).symm

end NCG
