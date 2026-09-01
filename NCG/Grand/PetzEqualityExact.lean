/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PetzUnconditionalExact
import NCG.Grand.StinespringDilationExact
import QICLean.Channel.Schwarz.WeylSupportPetzRecovery
import QICLean.Analysis.IsometricCompression

/-!
# Equality in finite-dimensional data processing and Petz recovery

This module closes the equality direction of the finite Petz sufficiency
theorem for a Kraus-presented channel.  It bridges the matrix conventions of
this project to QICLean's proved support-domain equality theorem for a partial
trace, using a right-environment Stinespring dilation.
-/

open Matrix Finset
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace Petz

open NCG.QRE

variable {n m κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

/-! ### Compatibility of the two finite spectral calculi -/

theorem matFun_eq_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : matFun hA f = hA.cfc f := by
  rw [hA.cfc_eq]
  rfl

theorem matLog_eq_CFC_log {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matLog hA = CFC.log A := by
  rw [matLog, matFun_eq_cfc, CFC.log]

theorem relEntropy_eq_quantumRelativeEntropy
    {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy hρ hσ = Matrix.quantumRelativeEntropy ρ σ := by
  unfold relEntropy Matrix.quantumRelativeEntropy
  rw [matLog_eq_CFC_log hρ, matLog_eq_CFC_log hσ]

/-! ### Stinespring dilation with the environment in the right factor -/

/-- The stacked Kraus column, with output index first and environment index
second so QICLean's right partial trace is literally the channel. -/
def stineColRight (K : κ → Matrix m n ℂ) : Matrix (m × κ) n ℂ :=
  Matrix.of fun p j => K p.2 p.1 j

omit [Fintype n] [DecidableEq m] [DecidableEq κ] in
theorem stineColRight_isometry (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (stineColRight K)ᴴ * stineColRight K = 1 := by
  ext a b
  have h := congrArg (fun M : Matrix n n ℂ => M a b) hK
  simp only [Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at h
  rw [Matrix.mul_apply]
  rw [show (1 : Matrix n n ℂ) a b = ∑ i, ∑ c, star (K i c a) * K i c b
    from h.symm]
  rw [Fintype.sum_prod_type]
  rfl

/-- Isometric conjugation into the output-environment product. -/
def stineConjRight (K : κ → Matrix m n ℂ) (ρ : Matrix n n ℂ) :
    Matrix (m × κ) (m × κ) ℂ :=
  stineColRight K * ρ * (stineColRight K)ᴴ

omit [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype κ] [DecidableEq κ] in
theorem stineConjRight_isHermitian (K : κ → Matrix m n ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (stineConjRight K ρ).IsHermitian := by
  unfold stineConjRight Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hρ.eq, Matrix.mul_assoc]

theorem stineConjRight_posSemidef (K : κ → Matrix m n ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (stineConjRight K ρ).PosSemidef := by
  exact hρ.mul_mul_conjTranspose_same (stineColRight K)

omit [DecidableEq n] [DecidableEq m] [DecidableEq κ] in
theorem partialTraceRight_stineConjRight
    (K : κ → Matrix m n ℂ) (ρ : Matrix n n ℂ) :
    Matrix.partialTraceRight (stineConjRight K ρ) = kraus K ρ := by
  ext a b
  simp only [Matrix.partialTraceRight_apply, stineConjRight,
    stineColRight, kraus, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype κ] [DecidableEq κ] in
theorem stineConjRight_support_of_posDef
    (K : κ → Matrix m n ℂ) {ρ σ : Matrix n n ℂ}
    (hσ : σ.PosDef) (v : m × κ → ℂ)
    (hv : (stineConjRight K σ) *ᵥ v = 0) :
    (stineConjRight K ρ) *ᵥ v = 0 := by
  let V := stineColRight K
  have hσv : σ *ᵥ (Vᴴ *ᵥ v) = 0 := by
    have h := congrArg (fun w => Vᴴ *ᵥ w) hv
    simpa only [stineConjRight, V, Matrix.mulVec_mulVec,
      Matrix.mul_assoc] using h
  have hv0 : Vᴴ *ᵥ v = 0 :=
    Matrix.mulVec_injective_of_isUnit hσ.isUnit hσv
  simp only [stineConjRight, V, Matrix.mulVec_mulVec, hv0,
    Matrix.mulVec_zero]

end Petz
end NCG
