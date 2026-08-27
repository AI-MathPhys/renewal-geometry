/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTSourceKernel
import NCG.Grand.JointSourceRangeUnitary

/-!
# Minimal source-kernel uniqueness

The source-kernel existence and rank theorem is combined here with the exact
equal-Gram range unitary.  A source-minimal carrier is its generated source
range, so this is precisely the single global unitary which simultaneously
fixes every profile column.  The probability-rescaling freedom is also made
literal at the weighted profile level.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- Rescale a profile when a faithful probability weight is changed, keeping
its weighted synthesis column fixed. -/
noncomputable def probabilityRescaledProfile {Ω H E : Type*}
    (ν ν' : Ω → ℝ) (S : Ω → Matrix H E ℂ) (ω : Ω) : Matrix H E ℂ :=
  ((Real.sqrt (ν ω) / Real.sqrt (ν' ω) : ℝ) : ℂ) • S ω

/-- The rescaled profile has exactly the same weighted synthesis column. -/
theorem probabilityRescaledProfile_weighted_eq {Ω H E : Type*}
    (ν ν' : Ω → ℝ) (S : Ω → Matrix H E ℂ)
    (hν : ∀ ω, 0 < ν ω) (hν' : ∀ ω, 0 < ν' ω) (ω : Ω) :
    ((Real.sqrt (ν' ω) : ℝ) : ℂ) •
        probabilityRescaledProfile ν ν' S ω =
      ((Real.sqrt (ν ω) : ℝ) : ℂ) • S ω := by
  rw [probabilityRescaledProfile, smul_smul]
  congr 1
  norm_cast
  field_simp [ne_of_gt (Real.sqrt_pos.2 (hν' ω))]

/-- Weighted block kernel written as the Gram of weighted profile columns. -/
noncomputable def weightedSourceKernelBlock {Ω H E : Type*} [Fintype H]
    (ν : Ω → ℝ) (S : Ω → Matrix H E ℂ) (ω η : Ω) : Matrix E E ℂ :=
  (((Real.sqrt (ν ω) * Real.sqrt (ν η) : ℝ) : ℂ)) •
    ((S ω)ᴴ * S η)

theorem weightedSourceKernelBlock_eq_weightedGram {Ω H E : Type*} [Fintype H]
    (ν : Ω → ℝ) (S : Ω → Matrix H E ℂ) (ω η : Ω) :
    weightedSourceKernelBlock ν S ω η =
      (((Real.sqrt (ν ω) : ℝ) : ℂ) • S ω)ᴴ *
        (((Real.sqrt (ν η) : ℝ) : ℂ) • S η) := by
  simp only [weightedSourceKernelBlock, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  congr 1
  norm_cast
  ring

/-- Faithful probability changes with the compensating profile rescaling leave
every mixed block of the source kernel unchanged. -/
theorem weightedSourceKernel_probability_independent {Ω H E : Type*} [Fintype H]
    (ν ν' : Ω → ℝ) (S : Ω → Matrix H E ℂ)
    (hν : ∀ ω, 0 < ν ω) (hν' : ∀ ω, 0 < ν' ω) (ω η : Ω) :
    weightedSourceKernelBlock ν'
        (probabilityRescaledProfile ν ν' S) ω η =
      weightedSourceKernelBlock ν S ω η := by
  rw [weightedSourceKernelBlock_eq_weightedGram,
    weightedSourceKernelBlock_eq_weightedGram,
    probabilityRescaledProfile_weighted_eq ν ν' S hν hν' ω,
    probabilityRescaledProfile_weighted_eq ν ν' S hν hν' η]

/-- Full source-minimal kernel theorem: canonical realization, rank minimality
and attainment, followed by the unique global source-fixing unitary between
any two generated realizations. -/
theorem source_kernel_realization_minimal_unique
    {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (hK : K.PosSemidef) :
    K = (CFC.sqrt K)ᴴ * CFC.sqrt K
    ∧ (∀ {c : Type} [Fintype c] (S : Matrix c n ℂ),
        K = Sᴴ * S → K.rank ≤ Fintype.card c)
    ∧ (CFC.sqrt K).rank = K.rank
    ∧ (∀ {h h' : Type} [Fintype h] [Fintype h']
        (S : Matrix h n ℂ) (T : Matrix h' n ℂ),
        K = Sᴴ * S → K = Tᴴ * T →
        ∃! U : LinearMap.range S.mulVecLin ≃ₗ[ℂ]
          LinearMap.range T.mulVecLin,
          (∀ u : n → ℂ,
            U (S.mulVecLin.rangeRestrict u) = T.mulVecLin.rangeRestrict u)
          ∧ (∀ x y : LinearMap.range S.mulVecLin,
            star (x : h → ℂ) ⬝ᵥ (y : h → ℂ) =
              star (U x : h' → ℂ) ⬝ᵥ (U y : h' → ℂ))) := by
  obtain ⟨hreal, hfloor, hattain⟩ := gt_source_kernel_realization K hK
  refine ⟨hreal, hfloor, hattain, ?_⟩
  intro h h' _ _ S T hS hT
  exact joint_source_unique_range_unitary S T (hS.symm.trans hT)

end NCG
