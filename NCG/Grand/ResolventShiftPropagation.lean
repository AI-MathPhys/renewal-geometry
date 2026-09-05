/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco

/-!
# Propagation of strong resolvent convergence between shifts

The second resolvent identity propagates varying-space strong convergence from one spectral
shift to another.  The proof only needs asymptotic density of the stage spaces and a uniform
operator-norm bound at the target shift.  This is the abstract `one, hence every` mechanism in
the Mosco--resolvent theorem.
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

/-- Strong convergence is closed under subtraction of dependent sequences. -/
theorem StronglyConverges.sub
    {x y : ∀ n, Hn n} {a b : H}
    (hx : J.StronglyConverges x a) (hy : J.StronglyConverges y b) :
    J.StronglyConverges (fun n ↦ x n - y n) (a - b) := by
  simpa only [StronglyConverges, map_sub] using Filter.Tendsto.sub hx hy

/-- A uniformly operator-norm bounded family sends a strongly null moving sequence to a
strongly null sequence. -/
theorem stronglyConverges_zero_of_uniform_operator_bound
    (Tn : ∀ n, Hn n →L[K] Hn n) (x : ∀ n, Hn n)
    (hx : J.StronglyConverges x 0)
    (C : ℝ) (hT : ∀ n, ‖Tn n‖ ≤ C) :
    J.StronglyConverges (fun n ↦ Tn n (x n)) 0 := by
  have hxnorm : Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 0) := by
    have := hx.norm
    simpa [StronglyConverges] using this
  rw [StronglyConverges, tendsto_zero_iff_norm_tendsto_zero]
  have hupper : ∀ n, ‖J.embedding n (Tn n (x n))‖ ≤ C * ‖x n‖ := by
    intro n
    rw [LinearIsometry.norm_map]
    exact (ContinuousLinearMap.le_opNorm (Tn n) (x n)).trans
      (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _))
  have hmul :
      Tendsto (fun n ↦ C * ‖x n‖) atTop (𝓝 (C * 0)) :=
    tendsto_const_nhds.mul hxnorm
  exact squeeze_zero (fun n ↦ norm_nonneg _) hupper (by simpa using hmul)

/-- Strong convergence of a resolvent family at one shift propagates to a second shift.  The
two displayed identities are the two orientations of the second resolvent identity needed by
the changing-space proof. -/
theorem StrongOperatorConverges.resolventShift
    (Rn : K → ∀ n, Hn n →L[K] Hn n) (R : K → H →L[K] H)
    (a b : K)
    (hdense : J.IsAsymptoticallyDense)
    (ha : J.StrongOperatorConverges J (Rn a) (R a))
    (C : ℝ) (hbBound : ∀ n, ‖Rn b n‖ ≤ C)
    (hstage : ∀ n,
      Rn b n - Rn a n = (a - b) • ((Rn b n).comp (Rn a n)))
    (hlimit :
      R a - R b = (b - a) • ((R a).comp (R b))) :
    J.StrongOperatorConverges J (Rn b) (R b) := by
  intro x xlim hx
  let zlim : H := xlim + (a - b) • R b xlim
  obtain ⟨z, hz⟩ := hdense zlim
  have haz : J.StronglyConverges (fun n ↦ Rn a n (z n)) (R a zlim) :=
    ha z zlim hz
  have hRaz : R a zlim = R b xlim := by
    have hid := DFunLike.congr_fun hlimit xlim
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] at hid
    rw [show R a zlim = R a xlim + (a - b) • R a (R b xlim) by
      simp [zlim]]
    apply sub_eq_zero.mp
    calc
      (R a xlim + (a - b) • R a (R b xlim)) - R b xlim =
          (R a xlim - R b xlim) + (a - b) • R a (R b xlim) := by abel
      _ = (b - a) • R a (R b xlim) + (a - b) • R a (R b xlim) := by rw [hid]
      _ = 0 := by rw [← add_smul]; simp
  let w : ∀ n, Hn n := fun n ↦
    x n - z n + (a - b) • Rn a n (z n)
  have hw : J.StronglyConverges w 0 := by
    have hraw := (hx.sub J hz).add J (haz.smul J (a - b))
    have hzero : xlim - zlim + (a - b) • R a zlim = 0 := by
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
            (a - b) • Rn b n (Rn a n (z n)) := by rw [hid]
      _ = Rn b n (w n) := by simp [w]
  have hdiffZero :
      J.StronglyConverges
        (fun n ↦ Rn b n (x n) - Rn a n (z n)) 0 := by
    simpa only [hdiff] using hBw
  have hout := hdiffZero.add J haz
  simpa only [sub_add_cancel, zero_add, hRaz] using hout

/-- If the resolvent identity and a stage-uniform norm bound hold at every target parameter,
strong convergence at one parameter implies strong convergence at every parameter. -/
theorem StrongOperatorConverges.allResolventShifts
    (Rn : K → ∀ n, Hn n →L[K] Hn n) (R : K → H →L[K] H)
    (a : K)
    (hdense : J.IsAsymptoticallyDense)
    (ha : J.StrongOperatorConverges J (Rn a) (R a))
    (hbound : ∀ b, ∃ C : ℝ, ∀ n, ‖Rn b n‖ ≤ C)
    (hstage : ∀ a b n,
      Rn b n - Rn a n = (a - b) • ((Rn b n).comp (Rn a n)))
    (hlimit : ∀ a b,
      R a - R b = (b - a) • ((R a).comp (R b))) :
    ∀ b, J.StrongOperatorConverges J (Rn b) (R b) := by
  intro b
  obtain ⟨C, hbBound⟩ := hbound b
  exact StrongOperatorConverges.resolventShift J Rn R a b
    hdense ha C hbBound (hstage a b) (hlimit a b)

end NCG.VaryingHilbert.System
