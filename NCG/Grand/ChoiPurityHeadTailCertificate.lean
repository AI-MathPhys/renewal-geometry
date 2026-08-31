/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ChoiPuritySpectralTail
import NCG.Grand.HermitianSpectralRankOneHead

/-!
# Positive Choi purity head--tail certificate

Combining the finite purity inequality with the literal rank-one spectral
decomposition produces the complete spectral half of the robust
channel-unitarity argument: a positive Choi matrix of trace `d` has a leading
rank-one vector of norm at most `sqrt d`, and its positive discarded tail has
trace at most the normalized purity defect.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace ChoiPurityHeadTailCertificate

open HermitianRankOneTraceNorm
open HermitianSpectralRankOneHead
open ChoiPuritySpectralTail
open Upstream.PrimitiveWeight

variable {m : ℕ}

/-- Exact spectral certificate underlying the robust Choi-purity branch. -/
theorem exists_choi_purity_head_tail
    {J : Matrix (Fin m) (Fin m) ℂ} [Nonempty (Fin m)]
    (hJ : J.PosSemidef) {d : ℝ} (hd : 0 < d)
    (htrace : J.trace.re = d) :
    ∃ (k : Fin m) (x : EuclideanSpace ℂ (Fin m))
      (T : Matrix (Fin m) (Fin m) ℂ),
      (∀ i, hJ.1.eigenvalues i ≤ hJ.1.eigenvalues k) ∧
      J = pureOuter x + T ∧
      T.PosSemidef ∧
      ‖x‖ ≤ Real.sqrt d ∧
      T.trace.re ≤ (d ^ 2 - (J * J).trace.re) / d := by
  obtain ⟨k, x, T, hk, hsplit, hT, hx2, hTtrace⟩ :=
    exists_max_eigen_head_tail hJ
  have htail0 : 0 ≤ T.trace.re := by
    exact (Complex.nonneg_iff.mp (psd_trace_nonneg hT)).1
  have hlam_le : hJ.1.eigenvalues k ≤ d := by
    rw [htrace] at hTtrace
    linarith
  have hx_le : ‖x‖ ≤ Real.sqrt d := by
    have hsqrt := Real.sqrt_le_sqrt hlam_le
    rw [← hx2] at hsqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)] using hsqrt
  have htail := psd_purity_tail_bound hJ k hd hk htrace
  have htailTraceEq : T.trace.re = d - hJ.1.eigenvalues k := by
    rw [hTtrace, htrace]
  rw [← htailTraceEq] at htail
  exact ⟨k, x, T, hk, hsplit, hT, hx_le, htail⟩

end ChoiPurityHeadTailCertificate
end NCG
