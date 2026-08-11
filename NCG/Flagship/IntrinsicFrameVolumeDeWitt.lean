/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Flagship.DeWittInverse
import NCG.Flagship.SpectralWard
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Intrinsic frame volume and DeWitt signature

This module completes `thm:DeWitt` at an arbitrary faithful spatial metric.
The `normDet` of a finite-dimensional frame map is the norm of its top
exterior power, so `spatialFrame_exteriorVolume_sq_eq_gramDet` is precisely
the missing exterior-volume/Gram-determinant identity.  The remaining results
write the normalized negative determinant Hessian as the DeWitt form and
transport its signature from the identity frame by an explicit whitening
congruence.
-/

open Matrix

namespace NCG

/-- The squared norm of the top exterior power of a three-leg frame is the
determinant of its physical Gram matrix.  `LinearMap.normDet` is Mathlib's
basis-independent norm of the top exterior power. -/
theorem spatialFrame_exteriorVolume_sq_eq_gramDet
    {U H : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (E : U →ₗ[ℝ] H) (b : OrthonormalBasis (Fin 3) ℝ U)
    (q : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : q = Matrix.gram ℝ (fun i => E (b i))) :
    E.normDet ^ 2 = q.det := by
  have hvolume := E.normDet_sq_eq_det_gram b
  simpa [hq] using hvolume

/-- The DeWitt bilinear form at a faithful metric. -/
noncomputable def intrinsicDeWittForm
    (q h k : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Matrix.trace (q⁻¹ * h * (q⁻¹ * k)) -
    Matrix.trace (q⁻¹ * h) * Matrix.trace (q⁻¹ * k)

/-- The normalized negative Hessian of determinant is exactly the intrinsic
DeWitt form at every invertible metric, not only at the identity frame. -/
theorem normalizedNegativeDeterminantHessian_eq_intrinsicDeWitt
    (q h k : Matrix (Fin 3) (Fin 3) ℝ) (hq : IsUnit q.det) :
    -(deriv (fun t : ℝ =>
        deriv (fun s : ℝ => (q + s • h + t • k).det) 0) 0) / q.det =
      intrinsicDeWittForm q h k := by
  rw [hessian_det q h k hq]
  unfold intrinsicDeWittForm
  have hq0 : q.det ≠ 0 := isUnit_iff_ne_zero.mp hq
  field_simp
  ring

/-- Whitening by `W`, with `WᵀW = q⁻¹`, carries the intrinsic DeWitt form to
the normalized trace form.  This is the congruence that preserves the full
signature at arbitrary positive metrics. -/
theorem intrinsicDeWittForm_whiteningCongruence
    (q W h k : Matrix (Fin 3) (Fin 3) ℝ)
    (hW : Wᵀ * W = q⁻¹) :
    intrinsicDeWittForm q h k =
      Matrix.trace ((W * h * Wᵀ) * (W * k * Wᵀ)) -
        Matrix.trace (W * h * Wᵀ) * Matrix.trace (W * k * Wᵀ) := by
  have htrace (a : Matrix (Fin 3) (Fin 3) ℝ) :
      Matrix.trace (q⁻¹ * a) = Matrix.trace (W * a * Wᵀ) := by
    rw [← hW]
    simp only [Matrix.mul_assoc]
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm Wᵀ (W * a))
  have htraceProduct :
      Matrix.trace (q⁻¹ * h * (q⁻¹ * k)) =
        Matrix.trace ((W * h * Wᵀ) * (W * k * Wᵀ)) := by
    rw [← hW]
    simp only [Matrix.mul_assoc]
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm Wᵀ (W * (h * (Wᵀ * (W * k)))))
  unfold intrinsicDeWittForm
  rw [htraceProduct, htrace h, htrace k]

/-- Every nonzero symmetric traceless whitened perturbation is a positive
DeWitt direction at the original metric. -/
theorem intrinsicDeWittForm_positive_on_whitenedTraceless
    (q W h : Matrix (Fin 3) (Fin 3) ℝ)
    (hW : Wᵀ * W = q⁻¹)
    (hsymmetric : (W * h * Wᵀ)ᵀ = W * h * Wᵀ)
    (htraceless : Matrix.trace (W * h * Wᵀ) = 0)
    (hnonzero : W * h * Wᵀ ≠ 0) :
    0 < intrinsicDeWittForm q h h := by
  rw [intrinsicDeWittForm_whiteningCongruence q W h h hW]
  simpa only [pow_two] using
    (ward_traceless_pos (W * h * Wᵀ) hsymmetric htraceless hnonzero)

/-- The metric-scaling line is the unique negative trace direction; its
quadratic value is `-6 c²` in three dimensions. -/
theorem intrinsicDeWittForm_metricLine
    (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : IsUnit q.det) (c : ℝ) :
    intrinsicDeWittForm q (c • q) (c • q) = -6 * c ^ 2 := by
  have hqinverse : q⁻¹ * q = 1 := Matrix.nonsing_inv_mul q hq
  unfold intrinsicDeWittForm
  simp only [Matrix.mul_smul, hqinverse, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    Matrix.smul_mul]
  push_cast
  ring

/-- In particular every nonzero metric-scaling perturbation is negative. -/
theorem intrinsicDeWittForm_metricLine_negative
    (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : IsUnit q.det)
    (c : ℝ) (hc : c ≠ 0) :
    intrinsicDeWittForm q (c • q) (c • q) < 0 := by
  rw [intrinsicDeWittForm_metricLine q hq c]
  nlinarith [sq_pos_of_ne_zero hc]

end NCG
