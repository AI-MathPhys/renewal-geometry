/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CStarAlgebraCompletion

/-!
# Contractive star homomorphisms on C-star completions

This file supplies the morphism half of `CStarAlgebraCompletion`.  A contractive unital
star-algebra homomorphism between normed pre-C-star algebras extends canonically to their
C-star completions.  The extension remains contractive, agrees with the original map on
the dense core, and respects identities and composition.

These are the functoriality lemmas needed to pass local AF embeddings, symmetries, and
dynamics to a quasilocal completion.
-/

noncomputable section

namespace NCG

open UniformSpace UniformSpace.Completion

variable {A B C : Type*}
  [NormedRing A] [StarRing A] [CStarRing A]
  [NormedAlgebra ℂ A] [StarModule ℂ A]
  [NormedRing B] [StarRing B] [CStarRing B]
  [NormedAlgebra ℂ B] [StarModule ℂ B]
  [NormedRing C] [StarRing C] [CStarRing C]
  [NormedAlgebra ℂ C] [StarModule ℂ C]

/-- A contractive unital star-algebra homomorphism between possibly incomplete
normed pre-C-star algebras. -/
structure ContractivePreCStarHom (A B : Type*)
    [NormedRing A] [StarRing A] [CStarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A]
    [NormedRing B] [StarRing B] [CStarRing B]
    [NormedAlgebra ℂ B] [StarModule ℂ B] where
  toStarAlgHom : A →⋆ₐ[ℂ] B
  norm_apply_le : ∀ a : A, ‖toStarAlgHom a‖ ≤ ‖a‖

namespace ContractivePreCStarHom

instance : CoeFun (ContractivePreCStarHom A B) fun _ => A → B :=
  ⟨fun f => f.toStarAlgHom⟩

/-- The contractive homomorphism bundled as a continuous linear map. -/
def toContinuousLinearMap (f : ContractivePreCStarHom A B) : A →L[ℂ] B :=
  f.toStarAlgHom.toLinearMap.mkContinuous 1 fun a => by
    simpa using f.norm_apply_le a

@[simp]
theorem toContinuousLinearMap_apply (f : ContractivePreCStarHom A B) (a : A) :
    f.toContinuousLinearMap a = f a :=
  rfl

theorem continuous (f : ContractivePreCStarHom A B) : Continuous f :=
  f.toContinuousLinearMap.continuous

/-- The underlying ring homomorphism extended to uniform completions. -/
def completionRingHom (f : ContractivePreCStarHom A B) :
    Completion A →+* Completion B :=
  Completion.mapRingHom f.toStarAlgHom.toRingHom f.continuous

@[simp]
theorem completionRingHom_coe (f : ContractivePreCStarHom A B) (a : A) :
    f.completionRingHom (a : Completion A) = (f a : B) := by
  exact Completion.mapRingHom_coe f.continuous a

/-- The canonical unital star-algebra homomorphism between the C-star completions. -/
def completionStarAlgHom (f : ContractivePreCStarHom A B) :
    Completion A →⋆ₐ[ℂ] Completion B where
  __ := f.completionRingHom
  commutes' r := by
    change f.completionRingHom (algebraMap ℂ (Completion A) r) =
      algebraMap ℂ (Completion B) r
    rw [Completion.algebraMap_def, Completion.algebraMap_def,
      completionRingHom_coe]
    exact congrArg ((↑) : B → Completion B) (f.toStarAlgHom.commutes r)
  map_star' x := by
    change f.completionRingHom (star x) = star (f.completionRingHom x)
    induction x using Completion.induction_on with
    | hp =>
        apply isClosed_eq
        · exact Completion.continuous_map.comp continuous_star
        · exact continuous_star.comp Completion.continuous_map
    | ih a =>
        rw [UniformSpace.Completion.coe_star, completionRingHom_coe,
          completionRingHom_coe, map_star,
          ← UniformSpace.Completion.coe_star]

@[simp]
theorem completionStarAlgHom_coe (f : ContractivePreCStarHom A B) (a : A) :
    f.completionStarAlgHom (a : Completion A) = (f a : B) :=
  f.completionRingHom_coe a

theorem completionStarAlgHom_continuous (f : ContractivePreCStarHom A B) :
    Continuous f.completionStarAlgHom :=
  Completion.continuous_map

/-- Contractivity persists on the whole completion. -/
theorem norm_completionStarAlgHom_apply_le (f : ContractivePreCStarHom A B)
    (x : Completion A) : ‖f.completionStarAlgHom x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_le f.completionStarAlgHom_continuous.norm continuous_norm
  | ih a =>
      simpa only [completionStarAlgHom_coe, Completion.norm_coe] using
        f.norm_apply_le a

/-- Composition of contractive pre-C-star homomorphisms. -/
def comp (g : ContractivePreCStarHom B C)
    (f : ContractivePreCStarHom A B) : ContractivePreCStarHom A C where
  toStarAlgHom := g.toStarAlgHom.comp f.toStarAlgHom
  norm_apply_le a := (g.norm_apply_le (f a)).trans (f.norm_apply_le a)

@[simp]
theorem comp_apply (g : ContractivePreCStarHom B C)
    (f : ContractivePreCStarHom A B) (a : A) :
    g.comp f a = g (f a) :=
  rfl

/-- Completion is functorial: it preserves composition exactly. -/
theorem completionStarAlgHom_comp (g : ContractivePreCStarHom B C)
    (f : ContractivePreCStarHom A B) :
    (g.comp f).completionStarAlgHom =
      g.completionStarAlgHom.comp f.completionStarAlgHom := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (g.comp f).completionStarAlgHom_continuous
      · exact g.completionStarAlgHom_continuous.comp
          f.completionStarAlgHom_continuous
  | ih a => simp

/-- The identity contractive pre-C-star homomorphism. -/
def id (A : Type*) [NormedRing A] [StarRing A] [CStarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A] : ContractivePreCStarHom A A where
  toStarAlgHom := StarAlgHom.id ℂ A
  norm_apply_le _ := le_rfl

@[simp]
theorem id_apply (a : A) : id A a = a :=
  rfl

/-- Completion preserves the identity exactly. -/
@[simp]
theorem completionStarAlgHom_id :
    (id A).completionStarAlgHom = StarAlgHom.id ℂ (Completion A) := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (id A).completionStarAlgHom_continuous
      · exact continuous_id
  | ih a => simp

end ContractivePreCStarHom

end NCG
