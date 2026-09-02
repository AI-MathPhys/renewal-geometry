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
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace NCG
namespace Petz

open NCG.QRE

variable {n m κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

/-! ### Compatibility of the two finite spectral calculi -/

theorem matFun_eq_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : matFun hA f = hA.cfc f := by
  rfl

theorem matLog_eq_CFC_log {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matLog hA = CFC.log A := by
  rw [matLog, matFun_eq_cfc, CFC.log, hA.cfc_eq]

theorem relEntropy_eq_quantumRelativeEntropy
    {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy hρ hσ = quantumRelativeEntropy ρ σ := by
  unfold relEntropy quantumRelativeEntropy
  rw [matLog_eq_CFC_log hρ, matLog_eq_CFC_log hσ]

theorem sqrtMat_eq_CFC_sqrt {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    sqrtMat hA.1 = CFC.sqrt A := by
  unfold sqrtMat
  rw [matFun_eq_cfc]
  symm
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg, cfcₙ_eq_cfc,
    hA.1.cfc_eq]

theorem invSqrtMat_eq_supportInvSqrt {A : Matrix n n ℂ}
    (hA : A.PosDef) :
    invSqrtMat hA.1 = hA.posSemidef.supportInvSqrt := by
  unfold invSqrtMat matFun Matrix.PosSemidef.supportInvSqrt
  congr 2
  funext i
  have hi : hA.1.eigenvalues i ≠ 0 := ne_of_gt (hA.eigenvalues_pos i)
  simp [hi]

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
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [stineColRight, Matrix.of_apply, Matrix.conjTranspose_apply]

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

omit [DecidableEq n] [DecidableEq m] [DecidableEq κ] in
theorem stineConjRight_posSemidef (K : κ → Matrix m n ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (stineConjRight K ρ).PosSemidef := by
  exact hρ.mul_mul_conjTranspose_same (stineColRight K)

omit [DecidableEq n] [Fintype m] [DecidableEq m] [DecidableEq κ] in
theorem partialTraceRight_stineConjRight
    (K : κ → Matrix m n ℂ) (ρ : Matrix n n ℂ) :
    Matrix.partialTraceRight (stineConjRight K ρ) = kraus K ρ := by
  ext a b
  simp only [Matrix.partialTraceRight_apply, stineConjRight,
    stineColRight, kraus, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [Fintype n] [DecidableEq n] in
/-- Compressing a left-factor operator through the Stinespring column gives
the Kraus adjoint action. -/
theorem stineColRight_compress_leftKronecker
    (K : κ → Matrix m n ℂ) (A : Matrix m m ℂ) :
    (stineColRight K)ᴴ * Matrix.leftKroneckerEmbed (n := κ) A *
        stineColRight K =
      ∑ i, (K i)ᴴ * A * K i := by
  classical
  ext a b
  simp [Matrix.mul_apply, stineColRight,
    Matrix.leftKroneckerEmbed_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.sum_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

omit [DecidableEq m] [DecidableEq κ] in
theorem stineConjRight_support_of_posDef
    (K : κ → Matrix m n ℂ) {ρ σ : Matrix n n ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hσ : σ.PosDef)
    (v : m × κ → ℂ)
    (hv : (stineConjRight K σ) *ᵥ v = 0) :
    (stineConjRight K ρ) *ᵥ v = 0 := by
  let V := stineColRight K
  have hV : Vᴴ * V = 1 := stineColRight_isometry K hK
  have hv' : V *ᵥ (σ *ᵥ (Vᴴ *ᵥ v)) = 0 := by
    simpa only [stineConjRight, V, ← Matrix.mulVec_mulVec,
      Matrix.mul_assoc] using hv
  have hσv : σ *ᵥ (Vᴴ *ᵥ v) = 0 := by
    have h := congrArg (fun w => Vᴴ *ᵥ w) hv'
    have h' : (Vᴴ * (V * (σ * Vᴴ))) *ᵥ v = 0 := by
      simpa only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] using h
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul] at h'
    simpa only [Matrix.mulVec_mulVec] using h'
  have hv0 : Vᴴ *ᵥ v = 0 := by
    apply Matrix.mulVec_injective_of_isUnit hσ.isUnit
    simpa only [Matrix.mulVec_zero] using hσv
  unfold stineConjRight
  rw [← Matrix.mulVec_mulVec, hv0, Matrix.mulVec_zero]

theorem quantumRelativeEntropy_stineConjRight
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    quantumRelativeEntropy (stineConjRight K ρ) (stineConjRight K σ) =
      quantumRelativeEntropy ρ σ := by
  rw [← relEntropy_eq_quantumRelativeEntropy
      (stineConjRight_isHermitian K hρ)
      (stineConjRight_isHermitian K hσ),
    ← relEntropy_eq_quantumRelativeEntropy hρ hσ]
  exact relEntropy_isometry hρ hσ (stineColRight_isometry K hK) _ _

theorem stineConjRight_cfc_sqrt
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    (stineConjRight_posSemidef K hσ).1.cfc Real.sqrt =
      stineColRight K * sqrtMat hσ.1 * (stineColRight K)ᴴ := by
  let V := stineColRight K
  have hV : Vᴴ * V = 1 := stineColRight_isometry K hK
  rw [← (stineConjRight_posSemidef K hσ).1.cfc_eq]
  change cfc Real.sqrt (V * σ * Vᴴ) = V * sqrtMat hσ.1 * Vᴴ
  rw [Matrix.cfc_conj_isometry_of_zero hσ.1 Real.sqrt Real.sqrt_zero V hV,
    hσ.1.cfc_eq]
  rfl

/-- The raw partial-trace Petz map of the Stinespring pair, compressed back
to the input space, is exactly this project's Kraus-form Petz map. -/
theorem compress_partialTraceRightPetzMap_stineConjRight
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    {σ : Matrix n n ℂ} (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (y : Matrix m m ℂ) :
    let hσd := stineConjRight_posSemidef K hσ.posSemidef
    (stineColRight K)ᴴ *
        Matrix.partialTraceRightPetzMap (stineConjRight K σ) hσd y *
          stineColRight K =
      petz K hσ hbar y := by
  dsimp only
  let V := stineColRight K
  let S := sqrtMat hσ.1
  let B := invSqrtMat hbar.1 * y * invSqrtMat hbar.1
  let E := Matrix.leftKroneckerEmbed (n := κ) B
  have hV : Vᴴ * V = 1 := stineColRight_isometry K hK
  have hsqrt :
      (stineConjRight_posSemidef K hσ.posSemidef).1.cfc Real.sqrt =
        V * S * Vᴴ := by
    simpa only [V, S] using
      stineConjRight_cfc_sqrt K hK hσ.posSemidef
  have hptr : Matrix.partialTraceRight (stineConjRight K σ) =
      kraus K σ := partialTraceRight_stineConjRight K σ
  rw [Matrix.partialTraceRightPetzMap_apply, hsqrt]
  have hinv :
      (Matrix.PosSemidef.partialTraceRight
        (stineConjRight_posSemidef K hσ.posSemidef)).supportInvSqrt =
          invSqrtMat hbar.1 := by
    unfold Matrix.PosSemidef.supportInvSqrt
    rw [← (Matrix.PosSemidef.partialTraceRight
      (stineConjRight_posSemidef K hσ.posSemidef)).1.cfc_eq,
      hptr, hbar.1.cfc_eq]
    exact (invSqrtMat_eq_supportInvSqrt hbar).symm
  rw [hinv]
  change Vᴴ * ((V * S * Vᴴ) * E * (V * S * Vᴴ)) * V =
    petz K hσ hbar y
  calc
    Vᴴ * ((V * S * Vᴴ) * E * (V * S * Vᴴ)) * V =
        (Vᴴ * V) * S * (Vᴴ * E * V) * S * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    _ = S * (Vᴴ * E * V) * S := by rw [hV]; simp
    _ = petz K hσ hbar y := by
      rw [stineColRight_compress_leftKronecker]
      rfl

/-! ### Equality in data processing -/

/-- **Petz equality theorem for a finite Kraus channel.**  Saturation of data
processing implies exact recovery by the reference-state Petz map. -/
theorem deltaDPI_eq_zero_implies_petz_recovery
    [Nonempty κ] (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef)
    (hzero : deltaDPI K hρ.1 hσ.1 (kraus_isHermitian K hρ.1)
      (kraus_isHermitian K hσ.1) = 0) :
    petz K hσ hbar (kraus K ρ) = ρ := by
  let ρd := stineConjRight K ρ
  let σd := stineConjRight K σ
  have hρd : ρd.PosSemidef := stineConjRight_posSemidef K hρ
  have hσd : σd.PosSemidef :=
    stineConjRight_posSemidef K hσ.posSemidef
  have hchannel :
      quantumRelativeEntropy ρ σ =
        quantumRelativeEntropy (kraus K ρ) (kraus K σ) := by
    rw [← relEntropy_eq_quantumRelativeEntropy hρ.1 hσ.1,
      ← relEntropy_eq_quantumRelativeEntropy
        (kraus_isHermitian K hρ.1) (kraus_isHermitian K hσ.1)]
    exact sub_eq_zero.mp hzero
  have heq :
      quantumRelativeEntropy ρd σd =
        quantumRelativeEntropy (Matrix.partialTraceRight ρd)
          (Matrix.partialTraceRight σd) := by
    rw [show ρd = stineConjRight K ρ from rfl,
      show σd = stineConjRight K σ from rfl,
      quantumRelativeEntropy_stineConjRight K hK hρ.1 hσ.1,
      partialTraceRight_stineConjRight K ρ,
      partialTraceRight_stineConjRight K σ]
    exact hchannel
  have hsupp : ∀ v : m × κ → ℂ, σd *ᵥ v = 0 → ρd *ᵥ v = 0 := by
    intro v hv
    exact stineConjRight_support_of_posDef K hK hσ v hv
  have hdilation :=
    Matrix.partialTraceRightPetzMap_eq_of_relativeEntropy_eq_general_support
      hρd hσd hsupp heq
  have hcompressed := congrArg
    (fun X : Matrix (m × κ) (m × κ) ℂ =>
      (stineColRight K)ᴴ * X * stineColRight K) hdilation
  rw [show Matrix.partialTraceRight ρd = kraus K ρ by
      exact partialTraceRight_stineConjRight K ρ,
    compress_partialTraceRightPetzMap_stineConjRight K hK hσ hbar,
    show ρd = stineConjRight K ρ from rfl,
    stineConjRight] at hcompressed
  rw [Matrix.conjTranspose_mul_mul_mul_conjTranspose_mul_of_isometry
    (stineColRight K) (stineColRight_isometry K hK) ρ] at hcompressed
  exact hcompressed

/-- **QS.3, fully unconditional:** equality in finite-dimensional data
processing holds exactly when the Petz map recovers the input state. -/
theorem deltaDPI_eq_zero_iff_petz_recovery
    [Nonempty κ] (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (hbar : (kraus K σ).PosDef) :
    deltaDPI K hρ.1 hσ.1 (kraus_isHermitian K hρ.1)
        (kraus_isHermitian K hσ.1) = 0 ↔
      petz K hσ hbar (kraus K ρ) = ρ :=
  ⟨deltaDPI_eq_zero_implies_petz_recovery K hK hρ hσ hbar,
    recovery_deltaDPI_eq_zero_proved K hK hρ hσ hbar⟩

end Petz
end NCG
