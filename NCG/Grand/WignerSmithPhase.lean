/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandDelay
import NCG.Upstream.DetDerivative

/-!
# Jacobi formula for the Wigner--Smith phase

The matrix positivity calculation lives in `GrandDelay`. This module supplies
the missing determinant/argument derivative used by `thm:positive-delay`.
-/

open Matrix

namespace NCG

/-- Right-handed Jacobi--Liouville formula. If `S' = S R`, then
`(det S)' = det(S) tr(R)`. -/
theorem jacobi_det_right {n : ℕ}
    {S : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {Sd R : Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (hS : ∀ i j, HasDerivAt (fun x => S x i j) (Sd i j) t)
    (hflow : Sd = S t * R) :
    HasDerivAt (fun x => (S x).det) ((S t).det * R.trace) t := by
  have hdet := hasDerivAt_det hS
  rw [hflow, ← Matrix.mul_assoc, Matrix.adjugate_mul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul] at hdet
  exact hdet

/-- The derivative of a chosen local smooth phase lift of `det S` is the trace
of the Wigner--Smith generator. A phase lift is the branch-safe formalization
of `arg (det S)` on a pole-free interval. -/
theorem wignerSmith_phase_derivative {n : ℕ}
    {S : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {Sd Q : Matrix (Fin n) (Fin n) ℂ} {t phaseSlope : ℝ}
    (hS : ∀ i j, HasDerivAt (fun x => S x i j) (Sd i j) t)
    (hflow : Sd = S t * (Complex.I • Q))
    (phase : ℝ → ℝ) (hphase : ∀ x,
      Complex.exp ((phase x : ℂ) * Complex.I) = (S x).det)
    (hphaseDeriv : HasDerivAt phase phaseSlope t) :
    (phaseSlope : ℂ) = Q.trace := by
  have hdet : HasDerivAt (fun x => (S x).det)
      ((S t).det * (Complex.I • Q).trace) t :=
    jacobi_det_right hS hflow
  have hphaseComplex : HasDerivAt (fun x : ℝ => (phase x : ℂ))
      (phaseSlope : ℂ) t := by
    simpa using hphaseDeriv.ofReal_comp
  have hinner : HasDerivAt
      (fun x : ℝ => (phase x : ℂ) * Complex.I)
      ((phaseSlope : ℂ) * Complex.I) t :=
    hphaseComplex.mul_const Complex.I
  have hexp : HasDerivAt
      (fun x : ℝ => Complex.exp ((phase x : ℂ) * Complex.I))
      ((phaseSlope : ℂ) *
        (Complex.exp ((phase t : ℂ) * Complex.I) * Complex.I)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hinner.cexp
  have hdet' : HasDerivAt
      (fun x : ℝ => Complex.exp ((phase x : ℂ) * Complex.I))
      ((S t).det * (Complex.I • Q).trace) t :=
    hdet.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => hphase x)
  have hder := hexp.unique hdet'
  rw [← hphase t, Matrix.trace_smul, smul_eq_mul] at hder
  have hexp_ne : Complex.exp ((phase t : ℂ) * Complex.I) ≠ 0 :=
    Complex.exp_ne_zero _
  apply (mul_left_cancel₀ (mul_ne_zero hexp_ne Complex.I_ne_zero))
  calc
    Complex.exp ((phase t : ℂ) * Complex.I) * Complex.I * phaseSlope =
        (phaseSlope : ℂ) *
          (Complex.exp ((phase t : ℂ) * Complex.I) * Complex.I) := by ring
    _ = Complex.exp ((phase t : ℂ) * Complex.I) *
        (Complex.I * Q.trace) := hder
    _ = Complex.exp ((phase t : ℂ) * Complex.I) * Complex.I * Q.trace := by ring

end NCG
