/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ChoiPurityHeadTailCertificate
import NCG.Grand.ChoiVectorReshaping
import NCG.Grand.SquarePolarUnitaryApproximation
import NCG.Grand.RobustChoiHeadTail

/-!
# Robust unitary approximation from Choi purity

This module assembles the spectral head--tail certificate, the trace-preserving
Choi marginal, the singular-safe polar approximation, and the rank-one trace
norm estimate.  It proves the robust branch of
`thm:SMST-channel-unitarity-branches` with the manuscript's exact constant.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace NCG
namespace RobustChoiPurityUnitary

open HermitianRankOneTraceNorm
open Upstream.PrimitiveWeight
open ChoiVectorReshaping

variable {d : ℕ}

/-- A positive trace-preserving Choi matrix of purity defect
`δ = d² - Tr(J²)` is within trace norm `2√δ + δ/d` of the Choi matrix
of a unitary channel. -/
theorem exists_unitary_of_choi_purity
    (hd : 0 < d)
    (J : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (hJ : J.PosSemidef)
    (htrace : J.trace.re = (d : ℝ))
    (hTP : choiMarginal J = (1 : Matrix (Fin d) (Fin d) ℂ)) :
    let δ : ℝ := (d : ℝ) ^ 2 - (J * J).trace.re
    ∃ U : Matrix (Fin d) (Fin d) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      trNorm (J - pureOuter (matrixVector U)) ≤
        2 * Real.sqrt δ + δ / d := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  letI : Nonempty (Fin (d * d)) :=
    Fin.pos_iff_nonempty.mp (Nat.mul_pos hd hd)
  let dr : ℝ := d
  let δ : ℝ := dr ^ 2 - (J * J).trace.re
  dsimp only
  have hdr : 0 < dr := by
    simpa [dr] using (Nat.cast_pos.mpr hd : (0 : ℝ) < d)
  rcases ChoiPurityHeadTailCertificate.exists_choi_purity_head_tail
      hJ hdr htrace with ⟨k, x, T, hk, hsplit, hT, hx, htail⟩
  let A : Matrix (Fin d) (Fin d) ℂ := vectorMatrix x
  have hmargSplit : choiMarginal J = A * Aᴴ + choiMarginal T := by
    rw [hsplit, choiMarginal_add, choiMarginal_pureOuter]
  have hdefMarg : 1 - A * Aᴴ = choiMarginal T := by
    rw [← hTP, hmargSplit]
    abel
  have hcontract : (1 - A * Aᴴ).PosSemidef := by
    rw [hdefMarg]
    exact choiMarginal_posSemidef hT
  have hdefTrace : (1 - A * Aᴴ).trace.re = T.trace.re := by
    rw [hdefMarg, trace_choiMarginal]
  rcases SquarePolarUnitaryApproximation.exists_unitary_frobenius_close
      A hcontract with ⟨U, hUtU, hUUt, hclose⟩
  have hcloseδ : hsFrobSq (A - U) ≤ δ / dr := by
    calc
      hsFrobSq (A - U) ≤ (1 - A * Aᴴ).trace.re := hclose
      _ = T.trace.re := hdefTrace
      _ ≤ δ / dr := htail
  have hTnon : 0 ≤ T.trace.re :=
    (Complex.nonneg_iff.mp hT.trace_nonneg).1
  have hdiv : 0 ≤ δ / dr := le_trans hTnon htail
  have hδ : 0 ≤ δ := by
    have hm := mul_nonneg hdiv hdr.le
    rwa [div_mul_cancel₀ δ hdr.ne'] at hm
  let y : EuclideanSpace ℂ (Fin (d * d)) := matrixVector U
  have hy2 : ‖y‖ ^ 2 = dr := by
    change ‖matrixVector U‖ ^ 2 = dr
    rw [norm_sq_matrixVector, hsFrobSq_eq_re_trace, hUtU]
    simp [dr]
  have hyEq : ‖y‖ = Real.sqrt dr := by
    calc
      ‖y‖ = Real.sqrt (‖y‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg y)).symm
      _ = Real.sqrt dr := by rw [hy2]
  have hxvec : matrixVector A = x := by
    exact matrixVector_vectorMatrix x
  have hxy2 : ‖x - y‖ ^ 2 ≤ δ / dr := by
    change ‖x - matrixVector U‖ ^ 2 ≤ δ / dr
    rw [← hxvec, norm_sub_matrixVector_sq]
    exact hcloseδ
  have hsd : Real.sqrt dr ≠ 0 := (Real.sqrt_pos.2 hdr).ne'
  have hquot : 0 ≤ Real.sqrt δ / Real.sqrt dr :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hquot2 : (Real.sqrt δ / Real.sqrt dr) ^ 2 = δ / dr := by
    rw [div_pow, Real.sq_sqrt hδ, Real.sq_sqrt hdr.le]
  have hxy : ‖x - y‖ ≤ Real.sqrt δ / Real.sqrt dr := by
    apply (sq_le_sq₀ (norm_nonneg _) hquot).mp
    rw [hquot2]
    exact hxy2
  refine ⟨U, hUtU, hUUt, ?_⟩
  exact RobustChoiHeadTail.scaled_head_tail_trNorm_bound
    J T x y hdr hδ hsplit hT hx hyEq.le hxy htail

end RobustChoiPurityUnitary
end NCG
