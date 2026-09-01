/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BkmTraceNormalizationExact
import NCG.Grand.RelativeEntropyBkmHessianExact

/-!
# Affine trace-entropy derivatives

The derivative of `Re Tr(A log A)` along a faithful affine Hermitian path is
`Re Tr(d) + Re Tr(d log A)`.  The proof uses the mixed matrix-log derivative
and the trace normalization of the BKM form.
-/

open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ d : Matrix n n ℂ}

/-- Trace entropy along the affine Hermitian path `σ + u d`. -/
noncomputable def affineTraceEntropy
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (u : ℝ) : ℝ :=
  (Matrix.trace ((σ + u • d) *
    matLog (affineMatrix_isHermitian hσ hd u))).re

/-- Exact first derivative of trace entropy along a faithful affine path. -/
theorem affineTraceEntropy_hasDerivAt
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {A B t : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef)
    (ht : t ∈ Set.Ioo A B) :
    HasDerivAt (affineTraceEntropy hσ hd)
      (d.trace.re +
        (Matrix.trace (d *
          matLog (affineMatrix_isHermitian hσ hd t))).re) t := by
  let At : Matrix n n ℂ := σ + t • d
  let hAt : At.IsHermitian := affineMatrix_isHermitian hσ hd t
  have hAtPos : At.PosDef := hpos t ht
  have hbaseRaw := affineMatrixLogPairing_mixed_hasDerivAt
    (w := At) (σ := σ) (d := d) (A := A) (B := B) (u := t)
    hAt hσ hd hpos ht
  have hbase : HasDerivAt
      (fun u : ℝ =>
        (Matrix.trace (At *
          matLog (affineMatrix_isHermitian hσ hd u))).re)
      d.trace.re t := by
    exact hbaseRaw.congr_deriv
      (mixedBkmForm_base_eq_trace hAtPos hd)
  have htangent := affineMatrixLogPairing_mixed_hasDerivAt
    (w := d) (σ := σ) (d := d) (A := A) (B := B) (u := t)
    hd hσ hd hpos ht
  have hfactor : HasDerivAt (fun u : ℝ => u - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hproductRaw := hfactor.mul htangent
  have hproduct : HasDerivAt
      (fun u : ℝ => (u - t) *
        (Matrix.trace (d *
          matLog (affineMatrix_isHermitian hσ hd u))).re)
      (Matrix.trace (d *
        matLog (affineMatrix_isHermitian hσ hd t))).re t := by
    exact hproductRaw.congr_deriv (by ring)
  have hsum := hbase.add hproduct
  have hfun :
      (fun u : ℝ =>
        (Matrix.trace (At *
          matLog (affineMatrix_isHermitian hσ hd u))).re +
        (u - t) * (Matrix.trace (d *
          matLog (affineMatrix_isHermitian hσ hd u))).re) =
      affineTraceEntropy hσ hd := by
    funext u
    have hdecomp : σ + u • d = At + (u - t) • d := by
      unfold At
      module
    have hmul :
        (σ + u • d) * matLog (affineMatrix_isHermitian hσ hd u) =
        (At + (u - t) • d) *
          matLog (affineMatrix_isHermitian hσ hd u) :=
      congrArg (fun X =>
        X * matLog (affineMatrix_isHermitian hσ hd u)) hdecomp
    unfold affineTraceEntropy
    rw [hmul]
    simp only [Matrix.add_mul, Matrix.trace_add, Complex.add_re,
      Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul]
    unfold At
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hfun]
  exact hsum

end QRE
end NCG
