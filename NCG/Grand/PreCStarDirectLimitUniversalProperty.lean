/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PreCStarDirectLimit
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The C-star universal property of completed direct limits

An isometric directed system of C-star algebras has an algebraic direct limit whose completion
was constructed in `NCG.Grand.PreCStarDirectLimit`. This file proves that the completion has the
expected categorical universal property: every compatible cone of star-algebra homomorphisms
into a C-star algebra factors through it uniquely. Consequently any two C-star inductive limits
of the same system are canonically star-algebra equivalent.
-/

open scoped CStarAlgebra

noncomputable section

namespace NCG.PreCStarDirectLimit

open UniformSpace UniformSpace.Completion

universe u v w

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type v}
variable [∀ i, CStarAlgebra (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f]

/-- A compatible cone from the stages of a directed system into a C-star algebra. -/
structure CompatibleCStarCone (B : Type w) [CStarAlgebra B] where
  /-- The map from each stage to the cone point. -/
  map : ∀ i, A i →⋆ₐ[ℂ] B
  /-- The stage maps commute with the connecting maps. -/
  compatible : ∀ i j (hij : i ≤ j) (a : A i),
    map j (f i j hij a) = map i a

namespace CompatibleCStarCone

variable {f}
variable {B : Type w} [CStarAlgebra B]
variable (C : CompatibleCStarCone f B)

/-- The star-algebra homomorphism induced on the algebraic direct limit. -/
def algebraicStarAlgHom : AlgebraicLimit f →⋆ₐ[ℂ] B where
  __ := DirectLimit.Algebra.lift A (fun i j hij ↦ f i j hij) B
    (fun i ↦ (C.map i).toAlgHom) C.compatible
  map_star' a := by
    induction a using DirectLimit.induction with
    | _ i a =>
        change C.map i (star a) = star (C.map i a)
        exact map_star (C.map i) a

omit [IsometricSystem f] in
@[simp]
theorem algebraicStarAlgHom_of (i : ι) (a : A i) :
    C.algebraicStarAlgHom (of f i a) = C.map i a :=
  rfl

/-- The algebraic factorization is contractive, even though its domain need not be complete. -/
theorem norm_algebraicStarAlgHom_apply_le (a : AlgebraicLimit f) :
    ‖C.algebraicStarAlgHom a‖ ≤ ‖a‖ := by
  induction a using DirectLimit.induction with
  | _ i a =>
      simpa only [← of_apply, algebraicStarAlgHom_of, norm_of] using
        NonUnitalStarAlgHom.norm_apply_le (C.map i) a

/-- The algebraic factorization is continuous. -/
theorem continuous_algebraicStarAlgHom : Continuous C.algebraicStarAlgHom := by
  let g : AlgebraicLimit f →L[ℂ] B :=
    C.algebraicStarAlgHom.toLinearMap.mkContinuous 1 fun a ↦ by
      change ‖C.algebraicStarAlgHom a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using C.norm_algebraicStarAlgHom_apply_le a
  exact g.continuous

/-- The ring-homomorphism extension of the algebraic factorization to the completion. -/
private def completionRingHom : Completion f →+* B :=
  Completion.extensionHom C.algebraicStarAlgHom.toRingHom
    C.continuous_algebraicStarAlgHom

private theorem continuous_completionRingHom : Continuous C.completionRingHom :=
  Completion.continuous_extension

/-- A compatible C-star cone factors through the completed direct limit. -/
def completionLift : Completion f →⋆ₐ[ℂ] B where
  __ := C.completionRingHom
  commutes' r := by
    rw [Completion.algebraMap_def]
    exact (Completion.extensionHom_coe C.algebraicStarAlgHom.toRingHom
      C.continuous_algebraicStarAlgHom (algebraMap ℂ (AlgebraicLimit f) r)).trans
        (C.algebraicStarAlgHom.commutes r)
  map_star' a := by
    induction a using Completion.induction_on with
    | hp =>
        exact isClosed_eq
          (C.continuous_completionRingHom.comp continuous_star)
          (continuous_star.comp C.continuous_completionRingHom)
    | ih a =>
        rw [Completion.coe_star]
        change
          Completion.extensionHom C.algebraicStarAlgHom.toRingHom
              C.continuous_algebraicStarAlgHom ((star a : AlgebraicLimit f) : Completion f) =
            star (Completion.extensionHom C.algebraicStarAlgHom.toRingHom
              C.continuous_algebraicStarAlgHom (a : Completion f))
        rw [Completion.extensionHom_coe, Completion.extensionHom_coe]
        exact map_star C.algebraicStarAlgHom a

/-- The completed factorization is continuous. -/
theorem continuous_completionLift : Continuous C.completionLift :=
  C.continuous_completionRingHom

@[simp]
theorem completionLift_coe (a : AlgebraicLimit f) :
    C.completionLift (a : Completion f) = C.algebraicStarAlgHom a :=
  Completion.extensionHom_coe C.algebraicStarAlgHom.toRingHom
    C.continuous_algebraicStarAlgHom a

@[simp]
theorem completionLift_completionOf (i : ι) (a : A i) :
    C.completionLift (completionOf f i a) = C.map i a := by
  rw [completionOf_apply, completionLift_coe, algebraicStarAlgHom_of]

/-- The completed factorization is the unique continuous star-algebra homomorphism agreeing
with the cone on every stage. -/
theorem completionLift_unique (g : Completion f →⋆ₐ[ℂ] B)
    (hg : ∀ i (a : A i), g (completionOf f i a) = C.map i a) :
    g = C.completionLift := by
  apply StarAlgHom.ext
  exact congrFun <| Completion.ext (map_continuous g) C.continuous_completionLift fun a ↦ by
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (fun i j hij ↦ f i j hij) a
    exact (hg i x).trans (C.completionLift_completionOf i x).symm

end CompatibleCStarCone

/-- The canonical cone into the completed direct limit. -/
def completionCone : CompatibleCStarCone f (Completion f) where
  map := completionOf f
  compatible i j hij a := by
    rw [completionOf_apply, completionOf_apply]
    congr 1
    exact DirectLimit.Algebra.of_f hij a

/-- A cone is a C-star inductive limit when it has the expected existence and uniqueness
property for compatible cones into arbitrary C-star algebras. -/
structure IsCStarInductiveLimit {B : Type w} [CStarAlgebra B]
    (C : CompatibleCStarCone f B) where
  /-- Every compatible cone factors through the proposed limit. -/
  lift : ∀ {D : Type w} [CStarAlgebra D], CompatibleCStarCone f D → B →⋆ₐ[ℂ] D
  /-- The factorization agrees with each stage map. -/
  fac : ∀ {D : Type w} [CStarAlgebra D] (E : CompatibleCStarCone f D)
    (i : ι) (a : A i), lift E (C.map i a) = E.map i a
  /-- The factorization is unique. -/
  uniq : ∀ {D : Type w} [CStarAlgebra D] (E : CompatibleCStarCone f D)
    (g : B →⋆ₐ[ℂ] D), (∀ i (a : A i), g (C.map i a) = E.map i a) → g = lift E

/-- The completed algebraic direct limit satisfies the C-star inductive-limit universal
property. -/
def completionCone_isCStarInductiveLimit : IsCStarInductiveLimit f (completionCone f) where
  lift E := E.completionLift
  fac E i a := E.completionLift_completionOf i a
  uniq E g hg := E.completionLift_unique g hg

namespace IsCStarInductiveLimit

variable {f}
variable {B : Type w} [CStarAlgebra B]
variable {D : Type w} [CStarAlgebra D]
variable {C : CompatibleCStarCone f B} {E : CompatibleCStarCone f D}

/-- The canonical map between two C-star inductive limits of the same directed system. -/
def canonicalHom (hC : IsCStarInductiveLimit f C) : B →⋆ₐ[ℂ] D :=
  hC.lift E

omit [IsDirectedOrder ι] [Nonempty ι]
  [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f] in
@[simp]
theorem canonicalHom_map (hC : IsCStarInductiveLimit f C) (i : ι) (a : A i) :
    hC.canonicalHom (E := E) (C.map i a) = E.map i a :=
  hC.fac E i a

/-- Any two C-star inductive limits of the same system are canonically star-algebra
equivalent. -/
def canonicalStarAlgEquiv (hC : IsCStarInductiveLimit f C)
    (hE : IsCStarInductiveLimit f E) : B ≃⋆ₐ[ℂ] D := by
  let forward : B →⋆ₐ[ℂ] D := hC.canonicalHom (E := E)
  let backward : D →⋆ₐ[ℂ] B := hE.canonicalHom (E := C)
  have hcomp_left : backward.comp forward = hC.lift C := by
    apply hC.uniq C
    intro i a
    change hE.lift C (hC.lift E (C.map i a)) = C.map i a
    rw [hC.fac E i a, hE.fac C i a]
  have hid_left : StarAlgHom.id ℂ B = hC.lift C := by
    apply hC.uniq C
    intro i a
    rfl
  have hinv_to : backward.comp forward = .id ℂ B := hcomp_left.trans hid_left.symm
  have hcomp_right : forward.comp backward = hE.lift E := by
    apply hE.uniq E
    intro i a
    change hC.lift E (hE.lift C (E.map i a)) = E.map i a
    rw [hE.fac C i a, hC.fac E i a]
  have hid_right : StarAlgHom.id ℂ D = hE.lift E := by
    apply hE.uniq E
    intro i a
    rfl
  have hto_inv : forward.comp backward = .id ℂ D := hcomp_right.trans hid_right.symm
  exact StarAlgEquiv.ofStarAlgHom forward backward hinv_to hto_inv

omit [IsDirectedOrder ι] [Nonempty ι]
  [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f] in
@[simp]
theorem canonicalStarAlgEquiv_apply_stage (hC : IsCStarInductiveLimit f C)
    (hE : IsCStarInductiveLimit f E) (i : ι) (a : A i) :
    hC.canonicalStarAlgEquiv hE (C.map i a) = E.map i a := by
  change hC.lift E (C.map i a) = E.map i a
  exact hC.fac E i a

end IsCStarInductiveLimit

end NCG.PreCStarDirectLimit
