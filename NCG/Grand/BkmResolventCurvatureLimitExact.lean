/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MatrixResolventPathDerivativeExact

/-!
# The BKM form as the improper resolvent curvature integral

This file assembles the scalar resolvent-kernel limit coordinatewise in the
eigenbasis of a faithful matrix.  It proves that the truncated integral of
the noncommutative resolvent curvature converges exactly to the BKM quadratic
form.  Together with `trace_resolvent_affine_hasDerivAt`, this is the
improper-integral part of the path-Hessian calculation needed for
`cor:accepted-BKM-loss`.
-/

open Matrix Finset Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v : Matrix n n ℂ}

/-- The resolvent curvature integrated up to the finite cutoff `R`. -/
noncomputable def truncatedResolventCurvature (hσ : σ.IsHermitian)
    (v : Matrix n n ℂ) (R : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..R, sForm hσ v s

/-- Continuity of the resolvent curvature on every finite nonnegative
cutoff interval at a faithful base. -/
theorem sForm_continuousOn_Icc (hσ : σ.PosDef) (hv : v.IsHermitian)
    (R : ℝ) :
    ContinuousOn (fun s : ℝ => sForm hσ.1 v s) (Set.Icc 0 R) := by
  simp_rw [sForm_eq_sum hσ.1 hv]
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_finsetSum
  intro j hj
  apply continuousOn_const.mul
  apply ContinuousOn.mul
  · apply ContinuousOn.inv₀ (continuousOn_const.add continuousOn_id)
    intro s hs
    exact ne_of_gt (add_pos_of_pos_of_nonneg (hσ.eigenvalues_pos j) hs.1)
  · apply ContinuousOn.inv₀ (continuousOn_const.add continuousOn_id)
    intro s hs
    exact ne_of_gt (add_pos_of_pos_of_nonneg (hσ.eigenvalues_pos i) hs.1)

/-- Finite-cutoff interval integrability of the BKM resolvent curvature. -/
theorem sForm_intervalIntegrable (hσ : σ.PosDef) (hv : v.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun s : ℝ => sForm hσ.1 v s) volume 0 R := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hR]
  exact sForm_continuousOn_Icc hσ hv R

/-- At a nonnegative cutoff, truncated curvature is the finite eigenbasis sum
of the corresponding scalar truncated resolvent integrals. -/
theorem truncatedResolventCurvature_eq_sum (hσ : σ.PosDef)
    (hv : v.IsHermitian) {R : ℝ} (hR : 0 ≤ R) :
    truncatedResolventCurvature hσ.1 v R =
      ∑ i, ∑ j, Complex.normSq (tangentIn hσ.1 v i j) *
        (∫ s in (0 : ℝ)..R,
          (hσ.1.eigenvalues j + s)⁻¹ *
            (hσ.1.eigenvalues i + s)⁻¹) := by
  unfold truncatedResolventCurvature
  simp_rw [sForm_eq_sum hσ.1 hv]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
    · intro j hj
      simpa only [mul_inv] using (resolvent_prod_integrable
        (hσ.eigenvalues_pos j) (hσ.eigenvalues_pos i) hR).const_mul
          (Complex.normSq (tangentIn hσ.1 v i j))
  · intro i hi
    have hint := IntervalIntegrable.sum Finset.univ fun j hj => by
        simpa only [mul_inv] using (resolvent_prod_integrable
          (hσ.eigenvalues_pos j) (hσ.eigenvalues_pos i) hR).const_mul
            (Complex.normSq (tangentIn hσ.1 v i j))
    refine hint.congr ?_
    intro s hs
    simp

/-- **Improper resolvent-curvature identity.**  For a faithful base point and
a Hermitian tangent, integrating `Re Tr(v R_s v R_s)` up to `R` converges to
the BKM quadratic form as `R → ∞`. -/
theorem tendsto_truncatedResolventCurvature (hσ : σ.PosDef)
    (hv : v.IsHermitian) :
    Tendsto (fun R : ℝ => truncatedResolventCurvature hσ.1 v R) atTop
      (𝓝 (bkmForm hσ.1 v)) := by
  have hsum : Tendsto
      (fun R : ℝ =>
        ∑ i, ∑ j, Complex.normSq (tangentIn hσ.1 v i j) *
          (∫ s in (0 : ℝ)..R,
            (hσ.1.eigenvalues j + s)⁻¹ *
              (hσ.1.eigenvalues i + s)⁻¹)) atTop
      (𝓝 (∑ i, ∑ j, Complex.normSq (tangentIn hσ.1 v i j) *
        bkmKernel (hσ.1.eigenvalues j) (hσ.1.eigenvalues i))) := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    simpa only [mul_inv] using (tendsto_integral_resolvent
      (hσ.eigenvalues_pos j) (hσ.eigenvalues_pos i)).const_mul
        (Complex.normSq (tangentIn hσ.1 v i j))
  have hcurv : Tendsto (fun R : ℝ => truncatedResolventCurvature hσ.1 v R)
      atTop
      (𝓝 (∑ i, ∑ j, Complex.normSq (tangentIn hσ.1 v i j) *
        bkmKernel (hσ.1.eigenvalues j) (hσ.1.eigenvalues i))) := by
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (truncatedResolventCurvature_eq_sum hσ hv hR).symm
  have hfinal :
      (∑ i, ∑ j, Complex.normSq (tangentIn hσ.1 v i j) *
        bkmKernel (hσ.1.eigenvalues j) (hσ.1.eigenvalues i)) =
        bkmForm hσ.1 v := by
    unfold bkmForm
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [bkmKernel_symm]
  rw [← hfinal]
  exact hcurv

end QRE
end NCG
