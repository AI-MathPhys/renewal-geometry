/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WeakSpaceProductConvergence

/-!
# Weak--strong convergence for bilinear pairings

A bounded bilinear pairing is continuous when its first input converges
strongly and its norm-bounded second input converges weakly.  This is the
functional-analytic product passage used by the Palatini curvature insertion
and by later stress/current limit arguments.
-/

open Filter Topology

noncomputable section

namespace NCG.WeakStrongBilinearPairing

variable {K E F : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F]

/-- Strong convergence in the first variable and bounded weak convergence in
the second variable pass through every bounded bilinear scalar pairing. -/
theorem tendsto_of_strong_of_bounded_weak
    {ι : Type*} {l : Filter ι}
    (B : E →L[K] (F →L[K] K))
    (x : ι → E) (xlim : E) (y : ι → F) (ylim : F)
    (C : ℝ) (hC : 0 ≤ C) (hyBound : ∀ i, ‖y i‖ ≤ C)
    (hx : Tendsto x l (𝓝 xlim))
    (hy : Tendsto (fun i => toWeakSpace K F (y i)) l
      (𝓝 (toWeakSpace K F ylim))) :
    Tendsto (fun i => B (x i) (y i)) l (𝓝 (B xlim ylim)) := by
  have hdx : Tendsto (fun i => ‖x i - xlim‖) l (𝓝 0) := by
    have hconst : Tendsto (fun _ : ι => xlim) l (𝓝 xlim) :=
      tendsto_const_nhds
    simpa using (hx.sub hconst).norm
  have hmajor : Tendsto (fun i => (‖B‖ * ‖x i - xlim‖) * C) l (𝓝 0) := by
    convert ((tendsto_const_nhds.mul hdx).mul tendsto_const_nhds) using 1 <;>
      simp
  have hfirstNorm : Tendsto (fun i => ‖B (x i - xlim) (y i)‖) l (𝓝 0) := by
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hmajor
    calc
      ‖B (x i - xlim) (y i)‖
          ≤ ‖B (x i - xlim)‖ * ‖y i‖ := (B (x i - xlim)).le_opNorm _
      _ ≤ ‖B (x i - xlim)‖ * C :=
        mul_le_mul_of_nonneg_left (hyBound i) (norm_nonneg _)
      _ ≤ (‖B‖ * ‖x i - xlim‖) * C :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) hC
  have hfirst : Tendsto (fun i => B (x i - xlim) (y i)) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hfirstNorm
  have hsecond : Tendsto (fun i => B xlim (y i)) l (𝓝 (B xlim ylim)) :=
    NCG.tendsto_apply_of_tendsto_toWeakSpace hy (B xlim)
  have hsum := hfirst.add hsecond
  convert hsum using 1
  · funext i
    calc
      B (x i) (y i) = B ((x i - xlim) + xlim) (y i) := by
        rw [sub_add_cancel]
      _ = B (x i - xlim) (y i) + B xlim (y i) := by
        rw [map_add, ContinuousLinearMap.add_apply]
  · simp

end NCG.WeakStrongBilinearPairing
