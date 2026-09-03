/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StrongInterpolationConvergenceExact
import NCG.Upstream.DetDerivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Determinant-volume convergence and first variation

The determinant coframe density is a bounded alternating four-linear
expression.  This file proves that strong coframe convergence passes through
that density and records the exact Jacobi first-variation identity at the
identity coframe.  These are the determinant-volume pieces of the localized
Palatini insertion.
-/

open Filter Topology Polynomial

noncomputable section

namespace NCG.PalatiniDeterminantVolume

variable {K E V : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup V] [NormedSpace K V]

/-- Strong convergence passes through a bounded four-linear diagonal. -/
theorem tendsto_diagonal_fourLinear
    {ι : Type*} {l : Filter ι}
    (volume : E →L[K] (E →L[K] (E →L[K] (E →L[K] V))))
    (coframe : ι → E) (coframeLimit : E)
    (hcoframe : Tendsto coframe l (𝓝 coframeLimit)) :
    Tendsto
      (fun i ↦ volume (coframe i) (coframe i) (coframe i) (coframe i)) l
      (𝓝 (volume coframeLimit coframeLimit coframeLimit coframeLimit)) := by
  have h1 : Tendsto (fun i ↦ volume (coframe i)) l (𝓝 (volume coframeLimit)) :=
    volume.continuous.continuousAt.tendsto.comp hcoframe
  have h2 : Tendsto (fun i ↦ volume (coframe i) (coframe i)) l
      (𝓝 (volume coframeLimit coframeLimit)) :=
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (h1.prodMk_nhds hcoframe)
  have h3 : Tendsto (fun i ↦ volume (coframe i) (coframe i) (coframe i)) l
      (𝓝 (volume coframeLimit coframeLimit coframeLimit)) :=
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (h2.prodMk_nhds hcoframe)
  exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (h3.prodMk_nhds hcoframe)

/-- A supplied L2--L6 interpolation bound gives the strong intermediate
coframe convergence needed by the determinant-volume term. -/
theorem determinantVolume_tendsto_of_coframe_interpolation
    {ι : Type*} {l : Filter ι}
    (volume : E →L[K] (E →L[K] (E →L[K] (E →L[K] V))))
    (coframe : ι → E) (coframeLimit : E)
    (lowError : ι → ℝ) (C theta : ℝ)
    (hC : 0 ≤ C) (htheta : 0 < theta)
    (hlow : Tendsto lowError l (𝓝 0))
    (hinterpolation : ∀ i,
      ‖coframe i - coframeLimit‖ ≤ C * (lowError i) ^ theta) :
    Tendsto
      (fun i ↦ volume (coframe i) (coframe i) (coframe i) (coframe i)) l
      (𝓝 (volume coframeLimit coframeLimit coframeLimit coframeLimit)) := by
  apply tendsto_diagonal_fourLinear volume coframe coframeLimit
  exact NCG.StrongInterpolationConvergence.tendsto_of_norm_interpolation
    coframe coframeLimit lowError C theta hC htheta hlow hinterpolation

/-- Jacobi's determinant variation at the identity: the coefficient linear in
`t` in `det(I + tM)` is `trace M`.  This is the pointwise algebraic core of
the cosmological determinant-volume variation. -/
theorem determinant_firstVariation_at_identity
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    (derivative <| Matrix.det
      (1 + (X : ℝ[X]) • M.map C)).eval 0 = Matrix.trace M :=
  Matrix.derivative_det_one_add_X_smul M

/-- Jacobi's determinant-volume variation at an arbitrary invertible
coframe: `D det_e[h] = det(e) trace(e⁻¹ h)`.  This is the pointwise
away-from-identity bridge needed for the cosmological insertion. -/
theorem determinant_firstVariation_at_invertible
    {n : ℕ} (e h : Matrix (Fin n) (Fin n) ℝ) (hdet : e.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (e + t • h).det)
      (e.det * Matrix.trace (e⁻¹ * h)) 0 := by
  have hentries : ∀ i j,
      HasDerivAt (fun t : ℝ => (e + t • h) i j) (h i j) 0 := by
    intro i j
    simpa [Pi.smul_apply, smul_eq_mul] using
      ((hasDerivAt_id (x := 0)).mul_const (h i j)).const_add (e i j)
  refine (NCG.hasDerivAt_det hentries).congr_deriv ?_
  simp only [zero_smul, add_zero]
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hdet, one_mul]

end NCG.PalatiniDeterminantVolume
