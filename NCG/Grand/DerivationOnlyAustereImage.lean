/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact derivation-only image and sharp anchor rank

This file proves the finite linear-algebra content of `thm:GT-NCG-austere-image`.
The commutator derivation and the declared grading/reality signs are represented
by linear constraint maps.  Their common kernel is the compatible commutant
anchor space.  We identify the complete affine solution fibre, prove that
orthogonal centering is its unique minimum-Hilbert--Schmidt-norm point, and
show that exactly the real dimension of the anchor space is necessary and
sufficient for calibrated scalar coordinates.
-/

namespace NCG.DerivationOnlyAustereImage

variable {V DerivData SignData : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [AddCommGroup DerivData] [Module ℝ DerivData]
variable [AddCommGroup SignData] [Module ℝ SignData]

/-- The self-adjoint compatible commutant anchor space: changes invisible to
both the commutator derivation and all declared linear grading/reality signs. -/
def compatibleAnchor (derivation : V →ₗ[ℝ] DerivData)
    (signs : V →ₗ[ℝ] SignData) : Submodule ℝ V :=
  derivation.ker ⊓ signs.ker

/-- Two implementers have the same derivation and declared signs. -/
def SameMarkedDerivation (derivation : V →ₗ[ℝ] DerivData)
    (signs : V →ₗ[ℝ] SignData) (D X : V) : Prop :=
  derivation X = derivation D ∧ signs X = signs D

/-- The centered derivation-only representative `D - P_c D`. -/
noncomputable def centeredRepresentative
    (derivation : V →ₗ[ℝ] DerivData) (signs : V →ₗ[ℝ] SignData)
    (D : V) : V :=
  D - (compatibleAnchor derivation signs).starProjection D

section Fibre

variable (derivation : V →ₗ[ℝ] DerivData) (signs : V →ₗ[ℝ] SignData)

/-- Equality of all marked derivation data is exactly membership of the
difference in the compatible anchor space. -/
theorem sameMarkedDerivation_iff_sub_mem (D X : V) :
    SameMarkedDerivation derivation signs D X ↔
      X - D ∈ compatibleAnchor derivation signs := by
  simp [SameMarkedDerivation, compatibleAnchor, sub_eq_zero]

/-- The complete solution set is the affine fibre `D + c`. -/
theorem complete_solution_fibre (D X : V) :
    SameMarkedDerivation derivation signs D X ↔
      ∃ c : compatibleAnchor derivation signs, X = D + c := by
  rw [sameMarkedDerivation_iff_sub_mem]
  constructor
  · intro h
    exact ⟨⟨X - D, h⟩, by simp⟩
  · rintro ⟨c, rfl⟩
    simpa using c.property

/-- The centered representative lies in the same marked derivation fibre. -/
theorem centered_sameMarkedDerivation (D : V) :
    SameMarkedDerivation derivation signs D
      (centeredRepresentative derivation signs D) := by
  rw [sameMarkedDerivation_iff_sub_mem]
  change D - (compatibleAnchor derivation signs).starProjection D - D ∈
    compatibleAnchor derivation signs
  convert (compatibleAnchor derivation signs).neg_mem
    ((compatibleAnchor derivation signs).starProjection_apply_mem D) using 1 <;> abel

/-- Centering removes exactly the compatible-anchor projection. -/
theorem centered_anchor_projection_eq_zero (D : V) :
    (compatibleAnchor derivation signs).starProjection
      (centeredRepresentative derivation signs D) = 0 := by
  rw [centeredRepresentative, map_sub]
  rw [Submodule.starProjection_eq_self_iff.mpr
    ((compatibleAnchor derivation signs).starProjection_apply_mem D), sub_self]

/-- Hence the centered representative is orthogonal to the entire anchor
space. -/
theorem centered_mem_anchor_orthogonal (D : V) :
    centeredRepresentative derivation signs D ∈
      (compatibleAnchor derivation signs)ᗮ := by
  exact (Submodule.starProjection_apply_eq_zero_iff
    (K := compatibleAnchor derivation signs)).mp
    (centered_anchor_projection_eq_zero derivation signs D)

/-- Every point in the affine fibre has the same orthogonal-complement
projection, namely the centered representative. -/
theorem orthogonal_projection_eq_centered {D X : V}
    (hX : SameMarkedDerivation derivation signs D X) :
    (compatibleAnchor derivation signs)ᗮ.starProjection X =
      centeredRepresentative derivation signs D := by
  let C := compatibleAnchor derivation signs
  let Dc := centeredRepresentative derivation signs D
  have hsub : X - D ∈ C :=
    (sameMarkedDerivation_iff_sub_mem derivation signs D X).mp hX
  have hproj : (C.starProjection D : V) ∈ C := C.starProjection_apply_mem D
  have hdiff : X - Dc ∈ C := by
    change X - (D - C.starProjection D) ∈ C
    convert C.add_mem hsub hproj using 1 <;> abel
  have hzero : Cᗮ.starProjection (X - Dc) = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff (K := Cᗮ)).mpr
    exact C.le_orthogonal_orthogonal hdiff
  have hDc : Dc ∈ Cᗮ := centered_mem_anchor_orthogonal derivation signs D
  calc
    Cᗮ.starProjection X = Cᗮ.starProjection ((X - Dc) + Dc) := by congr 1; abel
    _ = Cᗮ.starProjection (X - Dc) + Cᗮ.starProjection Dc := by rw [map_add]
    _ = 0 + Dc := by rw [hzero, Submodule.starProjection_eq_self_iff.mpr hDc]
    _ = Dc := zero_add _

/-- Orthogonal centering is norm-minimal in the full affine fibre. -/
theorem centered_norm_minimal {D X : V}
    (hX : SameMarkedDerivation derivation signs D X) :
    ‖centeredRepresentative derivation signs D‖ ≤ ‖X‖ := by
  rw [← orthogonal_projection_eq_centered derivation signs hX]
  exact (compatibleAnchor derivation signs)ᗮ.norm_starProjection_apply_le X

/-- Equality in the minimum-norm estimate forces the centered point; thus the
minimum representative is unique. -/
theorem centered_norm_eq_iff {D X : V}
    (hX : SameMarkedDerivation derivation signs D X) :
    ‖X‖ = ‖centeredRepresentative derivation signs D‖ ↔
      X = centeredRepresentative derivation signs D := by
  let C := compatibleAnchor derivation signs
  let Dc := centeredRepresentative derivation signs D
  have hproj : Cᗮ.starProjection X = Dc :=
    orthogonal_projection_eq_centered derivation signs hX
  constructor
  · intro hnorm
    have hmem : X ∈ Cᗮ := (Cᗮ.mem_iff_norm_starProjection X).mpr (by
      rw [hproj, hnorm])
    calc
      X = Cᗮ.starProjection X := (Submodule.starProjection_eq_self_iff.mpr hmem).symm
      _ = Dc := hproj
  · rintro rfl
    rfl

end Fibre

section Anchors

variable (derivation : V →ₗ[ℝ] DerivData) (signs : V →ₗ[ℝ] SignData)

/-- The sharp anchor rank `q_S`. -/
noncomputable def anchorRank : ℕ :=
  Module.finrank ℝ (compatibleAnchor derivation signs)

/-- Any injective bank of `m` real scalar anchors needs at least `q_S`
coordinates. -/
theorem anchor_count_lower_bound {m : ℕ}
    (A : compatibleAnchor derivation signs →ₗ[ℝ] (Fin m → ℝ))
    (hA : Function.Injective A) :
    anchorRank (derivation := derivation) (signs := signs) ≤ m := by
  have hdim := A.finrank_le_finrank_of_injective hA
  simpa [anchorRank, Module.finrank_fin_fun] using hdim

/-- Exactly `q_S` scalar coordinates suffice. -/
noncomputable def sharpAnchorCoordinates :
    compatibleAnchor derivation signs ≃ₗ[ℝ]
      (Fin (anchorRank (derivation := derivation) (signs := signs)) → ℝ) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun]
    rfl)

theorem sharpAnchorCoordinates_injective :
    Function.Injective (sharpAnchorCoordinates derivation signs) :=
  (sharpAnchorCoordinates derivation signs).injective

/-- Fewer than `q_S` scalar anchors necessarily leave a nontrivial fibre. -/
theorem fewer_anchors_not_injective {m : ℕ}
    (hm : m < anchorRank (derivation := derivation) (signs := signs))
    (A : compatibleAnchor derivation signs →ₗ[ℝ] (Fin m → ℝ)) :
    ¬ Function.Injective A := by
  intro hA
  exact (not_le_of_gt hm) (anchor_count_lower_bound derivation signs A hA)

/-- No single finite scalar budget covers finite packets of every dimension. -/
theorem no_fixed_finite_anchor_budget (budget : ℕ) :
    budget < Module.finrank ℝ (Fin (budget + 1) → ℝ) := by
  simp [Module.finrank_fin_fun]

end Anchors

/-- Bundled exact conclusion of `thm:GT-NCG-austere-image`. -/
theorem derivation_only_austere_image
    (derivation : V →ₗ[ℝ] DerivData) (signs : V →ₗ[ℝ] SignData) (D : V) :
    (∀ X, SameMarkedDerivation derivation signs D X ↔
      ∃ c : compatibleAnchor derivation signs, X = D + c) ∧
    SameMarkedDerivation derivation signs D
      (centeredRepresentative derivation signs D) ∧
    (∀ X, SameMarkedDerivation derivation signs D X →
      ‖centeredRepresentative derivation signs D‖ ≤ ‖X‖) ∧
    (∀ X, SameMarkedDerivation derivation signs D X →
      (‖X‖ = ‖centeredRepresentative derivation signs D‖ ↔
        X = centeredRepresentative derivation signs D)) ∧
    Function.Injective (sharpAnchorCoordinates derivation signs) ∧
    (∀ {m} (A : compatibleAnchor derivation signs →ₗ[ℝ] (Fin m → ℝ)),
      Function.Injective A →
        anchorRank (derivation := derivation) (signs := signs) ≤ m) := by
  exact ⟨complete_solution_fibre derivation signs D,
    centered_sameMarkedDerivation derivation signs D,
    fun X hX => centered_norm_minimal derivation signs hX,
    fun X hX => centered_norm_eq_iff derivation signs hX,
    sharpAnchorCoordinates_injective derivation signs,
    fun A hA => anchor_count_lower_bound derivation signs A hA⟩

end NCG.DerivationOnlyAustereImage
