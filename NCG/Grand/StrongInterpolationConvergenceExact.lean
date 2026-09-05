/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Strong convergence from an interpolation estimate

This file isolates the convergence step shared by the Palatini, ADM, and
stress/current limit arguments.  A domain-specific Hölder interpolation bound
of the form `mid ≤ C low^theta`, with `theta>0`, upgrades convergence in the
low norm to convergence in the intermediate norm.  A second theorem passes
that convergence through a bounded bilinear product.
-/

open Filter Topology

noncomputable section

namespace NCG.StrongInterpolationConvergence

/-- The exponent arithmetic used in the Palatini proof.  If `p > 3/2`, then
twice its Hölder-conjugate exponent lies strictly between `2` and `6`. -/
theorem palatini_conjugate_exponent_range (p : ℝ) (hp : 3 / 2 < p) :
    2 < 2 * p / (p - 1) ∧ 2 * p / (p - 1) < 6 := by
  have hpone : 1 < p := by linarith
  have hden : 0 < p - 1 := sub_pos.mpr hpone
  constructor
  · exact (lt_div_iff₀ hden).2 (by linarith)
  · exact (div_lt_iff₀ hden).2 (by linarith)

/-- A uniform interpolation estimate upgrades a vanishing low norm to a
vanishing intermediate norm. -/
theorem tendsto_zero_of_interpolation
    {ι : Type*} {l : Filter ι}
    (low intermediate : ι → ℝ) (C theta : ℝ)
    (hC : 0 ≤ C) (htheta : 0 < theta)
    (hlow : Tendsto low l (𝓝 0))
    (hintermediate : ∀ i, 0 ≤ intermediate i)
    (hestimate : ∀ i, intermediate i ≤ C * (low i) ^ theta) :
    Tendsto intermediate l (𝓝 0) := by
  have hpow : Tendsto (fun i => (low i) ^ theta) l (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 theta (Or.inr htheta.le)).tendsto.comp hlow
    change Tendsto (fun i => (low i) ^ theta) l (𝓝 ((0 : ℝ) ^ theta)) at h
    simpa only [Real.zero_rpow htheta.ne'] using h
  have hmajor : Tendsto (fun i => C * (low i) ^ theta) l (𝓝 0) := by
    convert tendsto_const_nhds.mul hpow using 1 <;> simp
  exact squeeze_zero hintermediate hestimate hmajor

variable {K E F : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F]

/-- Strong convergence passes through the diagonal of every bounded bilinear
map.  This is the abstract `e_X wedge e_X → e wedge e` step. -/
theorem tendsto_diagonal_bilinear
    {ι : Type*} {l : Filter ι}
    (B : E →L[K] (E →L[K] F)) (x : ι → E) (xlim : E)
    (hx : Tendsto x l (𝓝 xlim)) :
    Tendsto (fun i => B (x i) (x i)) l (𝓝 (B xlim xlim)) := by
  have hB : Tendsto (fun i => B (x i)) l (𝓝 (B xlim)) :=
    B.continuous.continuousAt.tendsto.comp hx
  have hpair : Tendsto (fun i => (B (x i), x i)) l (𝓝 (B xlim, xlim)) :=
    hB.prodMk_nhds hx
  exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp hpair

/-- Combining scalar interpolation control with a norm realization gives
strong convergence in the intermediate normed space. -/
theorem tendsto_of_norm_interpolation
    {ι : Type*} {l : Filter ι}
    (x : ι → E) (xlim : E) (low : ι → ℝ) (C theta : ℝ)
    (hC : 0 ≤ C) (htheta : 0 < theta)
    (hlow : Tendsto low l (𝓝 0))
    (hestimate : ∀ i, ‖x i - xlim‖ ≤ C * (low i) ^ theta) :
    Tendsto x l (𝓝 xlim) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact tendsto_zero_of_interpolation low (fun i => ‖x i - xlim‖)
    C theta hC htheta hlow (fun i => norm_nonneg _) hestimate

end NCG.StrongInterpolationConvergence
