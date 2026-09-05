/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineMatrixLogMixedDerivativeExact

/-!
# Trace normalization of the BKM form

Scaling a faithful matrix along its own radial direction identifies the
mixed BKM pairing with the ordinary real trace.
-/

open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 800000 in
-- Comparing the imported mixed derivative with the functional-calculus
-- scaling identity requires a larger elaboration budget.
/-- Pairing a faithful base itself with a tangent in the mixed BKM form
returns the real trace of that tangent. -/
theorem mixedBkmForm_base_eq_trace {A d : Matrix n n ℂ}
    (hA : A.PosDef) (hd : d.IsHermitian) :
    mixedBkmForm hA.1 A d = d.trace.re := by
  let F : ℝ → ℝ := fun u =>
    (Matrix.trace
      (d * matLog (affineMatrix_isHermitian hA.1 hA.1 u))).re
  have hpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, (A + u • A).PosDef := by
    intro u hu
    have hc : 0 < 1 + u := by linarith [hu.1]
    have heq : A + u • A = (1 + u) • A := by module
    rw [heq]
    exact hA.smul hc
  have hmix : HasDerivAt F (mixedBkmForm hA.1 d A) 0 := by
    have hraw := affineMatrixLogPairing_mixed_hasDerivAt
      (w := d) (σ := A) (d := A) (A := -1) (B := 1) (u := 0)
      hd hA.1 hA.1 hpos
      (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
    simpa only [zero_smul, add_zero] using hraw
  have hscalar : HasDerivAt
      (fun u : ℝ => Real.log (1 + u) * d.trace.re +
        (Matrix.trace (d * matLog hA.1)).re)
      d.trace.re 0 := by
    have hlog := hasDerivAt_log_shift
      (show 0 < (1 : ℝ) + 0 by norm_num)
    have hlog' : HasDerivAt (fun u : ℝ => Real.log (1 + u)) 1 0 := by
      simpa only [add_zero, inv_one] using hlog
    have hraw := (hlog'.const_mul d.trace.re).const_add
      (Matrix.trace (d * matLog hA.1)).re
    have hfun :
        (fun u : ℝ => (Matrix.trace (d * matLog hA.1)).re +
          d.trace.re * Real.log (1 + u)) =
        (fun u : ℝ => Real.log (1 + u) * d.trace.re +
          (Matrix.trace (d * matLog hA.1)).re) := by
      funext u
      ring
    rw [← hfun]
    exact hraw.congr_deriv (by ring)
  have hevent : ∀ᶠ u in 𝓝 (0 : ℝ), F u =
      Real.log (1 + u) * d.trace.re +
        (Matrix.trace (d * matLog hA.1)).re := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with u hu
    have hc : 0 < 1 + u := by linarith [hu.1]
    have heq : A + u • A = (1 + u) • A := by module
    let hcA : ((1 + u) • A).IsHermitian := (hA.smul hc).1
    have hlog := matLog_pos_smul hA hc hcA
    have hcongr : matLog (affineMatrix_isHermitian hA.1 hA.1 u) =
        matLog hcA := by
      exact matLog_congr heq
        (affineMatrix_isHermitian hA.1 hA.1 u) hcA
    unfold F
    rw [hcongr, hlog]
    simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re,
      Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul,
      Matrix.mul_one]
    rw [Complex.mul_re]
    simp
  have hscalar' : HasDerivAt F d.trace.re 0 :=
    hscalar.congr_of_eventuallyEq hevent
  have hderEq : mixedBkmForm hA.1 d A = d.trace.re :=
    hmix.unique hscalar'
  exact (mixedBkmForm_symm hA.1 A d).trans hderEq

end QRE
end NCG
