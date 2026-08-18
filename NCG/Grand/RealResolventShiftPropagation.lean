/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventShiftPropagation

/-!
# Propagation between real resolvent shifts on `RCLike` Hilbert spaces

This is the real-spectral-parameter form of the second-resolvent-identity argument.  It applies
uniformly to real and complex Hilbert spaces.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Strong convergence at one real resolvent shift propagates to another real shift. -/
theorem StrongOperatorConverges.realResolventShift
    (Rn : ℝ → ∀ n, Hn n →L[K] Hn n) (R : ℝ → H →L[K] H)
    (a b : ℝ)
    (hdense : J.IsAsymptoticallyDense)
    (ha : J.StrongOperatorConverges J (Rn a) (R a))
    (C : ℝ) (hbBound : ∀ n, ‖Rn b n‖ ≤ C)
    (hstage : ∀ n,
      Rn b n - Rn a n = (((a - b : ℝ) : K)) • ((Rn b n).comp (Rn a n)))
    (hlimit :
      R a - R b = (((b - a : ℝ) : K)) • ((R a).comp (R b))) :
    J.StrongOperatorConverges J (Rn b) (R b) := by
  intro x xlim hx
  let zlim : H := xlim + (((a - b : ℝ) : K)) • R b xlim
  obtain ⟨z, hz⟩ := hdense zlim
  have haz : J.StronglyConverges (fun n ↦ Rn a n (z n)) (R a zlim) :=
    ha z zlim hz
  have hRaz : R a zlim = R b xlim := by
    have hid := DFunLike.congr_fun hlimit xlim
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] at hid
    rw [show R a zlim = R a xlim + (((a - b : ℝ) : K)) • R a (R b xlim) by
      simp [zlim]]
    apply sub_eq_zero.mp
    calc
      (R a xlim + (((a - b : ℝ) : K)) • R a (R b xlim)) - R b xlim =
          (R a xlim - R b xlim) +
            (((a - b : ℝ) : K)) • R a (R b xlim) := by abel
      _ = (((b - a : ℝ) : K)) • R a (R b xlim) +
            (((a - b : ℝ) : K)) • R a (R b xlim) := by rw [hid]
      _ = 0 := by rw [← add_smul]; norm_num
  let w : ∀ n, Hn n := fun n ↦
    x n - z n + (((a - b : ℝ) : K)) • Rn a n (z n)
  have hw : J.StronglyConverges w 0 := by
    have hraw := (hx.sub J hz).add J (haz.smul J (((a - b : ℝ) : K)))
    have hzero :
        xlim - zlim + (((a - b : ℝ) : K)) • R a zlim = 0 := by
      dsimp [zlim]
      rw [hRaz]
      abel
    simpa only [hzero] using hraw
  have hBw : J.StronglyConverges (fun n ↦ Rn b n (w n)) 0 :=
    stronglyConverges_zero_of_uniform_operator_bound J (Rn b) w hw C hbBound
  have hdiff : ∀ n,
      Rn b n (x n) - Rn a n (z n) = Rn b n (w n) := by
    intro n
    have hid := DFunLike.congr_fun (hstage n) (z n)
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] at hid
    calc
      Rn b n (x n) - Rn a n (z n) =
          Rn b n (x n) - Rn b n (z n) +
            (Rn b n (z n) - Rn a n (z n)) := by abel
      _ = Rn b n (x n) - Rn b n (z n) +
            (((a - b : ℝ) : K)) • Rn b n (Rn a n (z n)) := by rw [hid]
      _ = Rn b n (w n) := by simp [w]
  have hdiffZero :
      J.StronglyConverges
        (fun n ↦ Rn b n (x n) - Rn a n (z n)) 0 := by
    simpa only [hdiff] using hBw
  have hout := hdiffZero.add J haz
  simpa only [sub_add_cancel, zero_add, hRaz] using hout

/-- For real resolvent parameters, convergence at one shift implies convergence at every shift
under the second resolvent identities and stage-uniform bounds. -/
theorem StrongOperatorConverges.allRealResolventShifts
    (Rn : ℝ → ∀ n, Hn n →L[K] Hn n) (R : ℝ → H →L[K] H)
    (a : ℝ)
    (hdense : J.IsAsymptoticallyDense)
    (ha : J.StrongOperatorConverges J (Rn a) (R a))
    (hbound : ∀ b, ∃ C : ℝ, ∀ n, ‖Rn b n‖ ≤ C)
    (hstage : ∀ a b n,
      Rn b n - Rn a n = (((a - b : ℝ) : K)) • ((Rn b n).comp (Rn a n)))
    (hlimit : ∀ a b,
      R a - R b = (((b - a : ℝ) : K)) • ((R a).comp (R b))) :
    ∀ b, J.StrongOperatorConverges J (Rn b) (R b) := by
  intro b
  obtain ⟨C, hbBound⟩ := hbound b
  exact StrongOperatorConverges.realResolventShift J Rn R a b
    hdense ha C hbBound (hstage a b) (hlimit a b)

end NCG.VaryingHilbert.System
