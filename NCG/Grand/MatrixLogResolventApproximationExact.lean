/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LogResolventKernelExact

/-!
# Spectral resolvent approximation of a matrix-log trace pairing

Applying the normalized scalar resolvent primitive through the Hermitian
functional calculus gives a finite-cutoff matrix logarithm.  Its pairing with
an arbitrary Hermitian matrix converges to the corresponding pairing with the
repository's `matLog`.
-/

open Matrix Finset Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A v : Matrix n n ℂ}

/-- Pairing with the finite-cutoff spectral resolvent approximation of the
matrix logarithm. -/
noncomputable def truncatedMatrixLogPairing (v : Matrix n n ℂ)
    (hA : A.IsHermitian) (R : ℝ) : ℝ :=
  ((v * matFun hA (fun a => truncatedLogKernel a R)).trace).re

/-- Eigenbasis expansion of the truncated matrix-log pairing. -/
theorem truncatedMatrixLogPairing_eq_sum (hv : v.IsHermitian)
    (hA : A.IsHermitian) (R : ℝ) :
    truncatedMatrixLogPairing v hA R =
      ∑ i, ∑ j, hv.eigenvalues i *
        truncatedLogKernel (hA.eigenvalues j) R *
        Complex.normSq (overlap hv hA i j) := by
  unfold truncatedMatrixLogPairing
  exact trace_mul_matFun_re hv hA _

/-- Spectral expansion of the trace pairing with a resolvent. -/
theorem trace_mul_resolvent_re_eq_sum (hv : v.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) :
    (Matrix.trace (v * resolvent hA s)).re =
      ∑ i, ∑ j, hv.eigenvalues i * (hA.eigenvalues j + s)⁻¹ *
        Complex.normSq (overlap hv hA i j) := by
  unfold resolvent
  exact trace_mul_matFun_re hv hA _

/-- Pointwise eigenbasis assembly of the normalized resolvent difference. -/
theorem sum_log_resolvent_diff_eq_trace (hv : v.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) :
    (∑ i, ∑ j, hv.eigenvalues i *
        ((1 + s)⁻¹ - (hA.eigenvalues j + s)⁻¹) *
        Complex.normSq (overlap hv hA i j)) =
      v.trace.re * (1 + s)⁻¹ -
        (Matrix.trace (v * resolvent hA s)).re := by
  have hrow : ∀ i, ∑ j, Complex.normSq (overlap hv hA i j) = 1 :=
    sum_normSq_row (overlap_mul_star hv hA)
  have htrace : v.trace.re = ∑ i, hv.eigenvalues i := by
    rw [hv.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  rw [trace_mul_resolvent_re_eq_sum hv hA, htrace]
  have hexp : (∑ i, hv.eigenvalues i) * (1 + s)⁻¹ =
      ∑ i, ∑ j, hv.eigenvalues i * (1 + s)⁻¹ *
        Complex.normSq (overlap hv hA i j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum, hrow i, mul_one]
  rw [hexp, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The spectral cutoff pairing is exactly the integral of the normalized
matrix-resolvent trace difference. -/
theorem truncatedMatrixLogPairing_eq_integral (hv : v.IsHermitian)
    (hA : A.PosDef) {R : ℝ} (hR : 0 ≤ R) :
    truncatedMatrixLogPairing v hA.1 R =
      ∫ s in (0 : ℝ)..R,
        v.trace.re * (1 + s)⁻¹ -
          (Matrix.trace (v * resolvent hA.1 s)).re := by
  rw [truncatedMatrixLogPairing_eq_sum hv hA.1]
  have hint : ∀ i j, IntervalIntegrable
      (fun s : ℝ => hv.eigenvalues i *
        ((1 + s)⁻¹ - (hA.1.eigenvalues j + s)⁻¹) *
        Complex.normSq (overlap hv hA.1 i j)) volume 0 R := by
    intro i j
    exact ((log_resolvent_diff_integrable (hA.eigenvalues_pos j) hR).const_mul
      (hv.eigenvalues i)).mul_const _
  calc
    (∑ i, ∑ j, hv.eigenvalues i *
        truncatedLogKernel (hA.1.eigenvalues j) R *
        Complex.normSq (overlap hv hA.1 i j)) =
      ∑ i, ∑ j, ∫ s in (0 : ℝ)..R, hv.eigenvalues i *
        ((1 + s)⁻¹ - (hA.1.eigenvalues j + s)⁻¹) *
        Complex.normSq (overlap hv hA.1 i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [truncatedLogKernel_eq_integral_sub
            (hA.eigenvalues_pos j) hR,
            ← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_mul_const]
    _ = ∫ s in (0 : ℝ)..R,
        ∑ i, ∑ j, hv.eigenvalues i *
          ((1 + s)⁻¹ - (hA.1.eigenvalues j + s)⁻¹) *
          Complex.normSq (overlap hv hA.1 i j) := by
          rw [intervalIntegral.integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [intervalIntegral.integral_finsetSum]
            exact fun j hj => hint i j
          · intro i hi
            have hs := IntervalIntegrable.sum Finset.univ fun j hj => hint i j
            refine hs.congr ?_
            intro s hs
            simp
    _ = ∫ s in (0 : ℝ)..R,
        v.trace.re * (1 + s)⁻¹ -
          (Matrix.trace (v * resolvent hA.1 s)).re := by
          apply intervalIntegral.integral_congr
          intro s hs
          exact sum_log_resolvent_diff_eq_trace hv hA.1 s

/-- The finite-cutoff pairing converges to the exact spectral matrix-log
pairing at every faithful base matrix. -/
theorem tendsto_truncatedMatrixLogPairing (hv : v.IsHermitian)
    (hA : A.PosDef) :
    Tendsto (fun R : ℝ => truncatedMatrixLogPairing v hA.1 R) atTop
      (𝓝 ((Matrix.trace (v * matLog hA.1)).re)) := by
  rw [show (Matrix.trace (v * matLog hA.1)).re =
      ∑ i, ∑ j, hv.eigenvalues i * Real.log (hA.1.eigenvalues j) *
        Complex.normSq (overlap hv hA.1 i j) by
    unfold matLog
    exact trace_mul_matFun_re hv hA.1 _]
  simp_rw [truncatedMatrixLogPairing_eq_sum hv hA.1]
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact ((tendsto_const_nhds.mul
    (tendsto_truncatedLogKernel (hA.eigenvalues_pos j))).mul
      tendsto_const_nhds)

end QRE
end NCG
