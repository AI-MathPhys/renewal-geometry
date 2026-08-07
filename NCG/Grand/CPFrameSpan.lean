/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Physical CP branches span each Choi coordinate space
  (`lem:CP-frame-span`, Gran-Tensor manuscript)

* `cp_frame_span`: every Hermitian coordinate is a real
  combination `M = s•A - t•B` of two positive semidefinite
  operators of real trace at most one — the spectral
  positive/negative split followed by trace normalization
  (`psd_trace_normalize`).  Hence the real span of the
  trace-normalized positive Choi cone is the full Hermitian
  coordinate space and a finite basis of physical branches
  exists.

Rendering disclosed: the Choi coordinate space `E_k` is
rendered as the Hermitian matrices of the finite carrier; the
manuscript's trace-nonincreasing condition `Tr_{2k-1}M ⪯ I` is
rendered by the dominating scalar normalization `Tr M ≤ 1`
(positive rescaling, which does not change the real span);
extraction of a finite basis from a spanning cone is
finite-dimensional bookkeeping.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Positive rescaling of a positive semidefinite matrix to
real trace at most one. -/
lemma psd_trace_normalize {k : Type*} [Fintype k]
    (A : Matrix k k ℂ) (hA : A.PosSemidef) :
    ∃ (s : ℝ) (A' : Matrix k k ℂ), 0 ≤ s ∧ A'.PosSemidef
      ∧ (A'.trace).re ≤ 1 ∧ A = s • A' := by
  have htr : 0 ≤ (A.trace).re := by
    have h := (RCLike.le_iff_re_im.mp hA.trace_nonneg).1
    simpa using h
  set c : ℝ := (A.trace).re + 1 with hc
  have hcpos : 0 < c := by
    rw [hc]
    linarith
  have hinv : (0 : ℝ) ≤ c⁻¹ := by positivity
  refine ⟨c, c⁻¹ • A, hcpos.le, hA.smul hinv, ?_, ?_⟩
  · rw [Matrix.trace_smul]
    have hre : ((c⁻¹ • A.trace : ℂ)).re = c⁻¹ * (A.trace).re := by
      rw [Complex.real_smul, Complex.mul_re]
      simp
    rw [hre]
    have hle : c⁻¹ * (A.trace).re ≤ c⁻¹ * c := by
      apply mul_le_mul_of_nonneg_left _ hinv
      rw [hc]
      linarith
    rwa [inv_mul_cancel₀ hcpos.ne'] at hle
  · rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]

/-- `lem:CP-frame-span`: every Hermitian coordinate is a real
combination of two trace-normalized positive branches. -/
theorem cp_frame_span {k : Type*} [Fintype k]
    (M : Matrix k k ℂ) (hM : M.IsHermitian) :
    ∃ (A B : Matrix k k ℂ) (s t : ℝ),
      A.PosSemidef ∧ B.PosSemidef
      ∧ (A.trace).re ≤ 1 ∧ (B.trace).re ≤ 1
      ∧ 0 ≤ s ∧ 0 ≤ t ∧ M = s • A - t • B := by
  classical
  set V := hM.eigenvectorUnitary with hV
  set e := hM.eigenvalues with he
  set Dp : Matrix k k ℂ :=
    Matrix.diagonal (fun i => ((max (e i) 0 : ℝ) : ℂ))
    with hDp
  set Dn : Matrix k k ℂ :=
    Matrix.diagonal (fun i => ((max (-e i) 0 : ℝ) : ℂ))
    with hDn
  have hDpPSD : Dp.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((max (e i) 0 : ℝ) : ℂ)
    rw [← Complex.ofReal_zero]
    exact Complex.real_le_real.mpr (le_max_right _ _)
  have hDnPSD : Dn.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((max (-e i) 0 : ℝ) : ℂ)
    rw [← Complex.ofReal_zero]
    exact Complex.real_le_real.mpr (le_max_right _ _)
  set Mp : Matrix k k ℂ := (V : Matrix k k ℂ) * Dp
      * (star (V : Matrix k k ℂ)) with hMp
  set Mn : Matrix k k ℂ := (V : Matrix k k ℂ) * Dn
      * (star (V : Matrix k k ℂ)) with hMn
  have hMpPSD : Mp.PosSemidef := by
    rw [hMp, Matrix.star_eq_conjTranspose]
    exact hDpPSD.mul_mul_conjTranspose_same _
  have hMnPSD : Mn.PosSemidef := by
    rw [hMn, Matrix.star_eq_conjTranspose]
    exact hDnPSD.mul_mul_conjTranspose_same _
  have hsplit : M = Mp - Mn := by
    have hdiag : Dp - Dn
        = Matrix.diagonal (RCLike.ofReal ∘ e) := by
      rw [hDp, hDn, Matrix.diagonal_sub]
      congr 1
      funext i
      change (((max (e i) 0 : ℝ) : ℂ))
          - (((max (-e i) 0 : ℝ) : ℂ)) = ((e i : ℝ) : ℂ)
      rw [← Complex.ofReal_sub]
      congr 1
      rcases le_or_gt 0 (e i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right h.le, max_eq_left (by linarith)]
        ring
    have hspec := hM.spectral_theorem
    rw [hspec, Unitary.conjStarAlgAut_apply, hMp, hMn, ← hdiag,
      Matrix.mul_sub, Matrix.sub_mul]
  obtain ⟨s, A, hs, hAPSD, hAtr, hAeq⟩ :=
    psd_trace_normalize Mp hMpPSD
  obtain ⟨t, B, ht, hBPSD, hBtr, hBeq⟩ :=
    psd_trace_normalize Mn hMnPSD
  exact ⟨A, B, s, t, hAPSD, hBPSD, hAtr, hBtr, hs, ht,
    by rw [hsplit, hAeq, hBeq]⟩

end NCG
