/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertRadonRiesz
import NCG.Grand.VaryingHilbertStrongBoundedness
import NCG.Grand.VaryingHilbertWeakStrongPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Adjoint convergence from convergence of output norms

For operators on asymptotically dense varying Hilbert spaces, strong convergence of the original
operators already forces weak convergence of adjoint outputs.  If the adjoint-output norms also
converge, varying-space Radon--Riesz upgrades this to strong convergence of the adjoint family.
This isolates the Hilbert-space core used by normal and other norm-controlled operator classes.
-/

open Filter Set Topology
open scoped InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Strong operator convergence, asymptotic density, and convergence of every moving
adjoint-output norm imply strong operator convergence of the adjoints. -/
theorem StrongOperatorConverges.adjoint_of_norm_tendsto
    (J : System (K := K) (H := H) (Hn := Hn))
    {Tn : ∀ n, Hn n →L[K] Hn n} {T : H →L[K] H}
    (hT : J.StrongOperatorConverges J Tn T)
    (hdense : J.IsAsymptoticallyDense)
    (hadjointNorm : ∀ (x : ∀ n, Hn n) (xlim : H),
      J.StronglyConverges x xlim →
        Tendsto
          (fun n ↦ ‖ContinuousLinearMap.adjoint (Tn n) (x n)‖) atTop
          (𝓝 ‖ContinuousLinearMap.adjoint T xlim‖)) :
    J.StrongOperatorConverges J
      (fun n ↦ ContinuousLinearMap.adjoint (Tn n))
      (ContinuousLinearMap.adjoint T) := by
  intro x xlim hx
  have hnorm := hadjointNorm x xlim hx
  have hrange : Bornology.IsBounded
      (range fun n ↦ ‖ContinuousLinearMap.adjoint (Tn n) (x n)‖) :=
    Metric.isBounded_range_of_tendsto _ hnorm
  obtain ⟨C, _hCpos, hC⟩ := hrange.exists_pos_norm_le
  have hAdjBound : ∀ n,
      ‖ContinuousLinearMap.adjoint (Tn n) (x n)‖ ≤ C := by
    intro n
    simpa using hC ‖ContinuousLinearMap.adjoint (Tn n) (x n)‖ ⟨n, rfl⟩
  have hweak : J.WeaklyConverges
      (fun n ↦ ContinuousLinearMap.adjoint (Tn n) (x n))
      (ContinuousLinearMap.adjoint T xlim) := by
    intro y
    obtain ⟨yn, hyn⟩ := hdense y
    have hTyn := hT yn y hyn
    obtain ⟨D, _hDpos, hDx⟩ := hx.exists_pos_uniform_norm_bound J
    have hpair :
        Tendsto
          (fun n ↦ inner K (J.embedding n (x n))
            (J.embedding n (Tn n (yn n)))) atTop
          (𝓝 (inner K xlim (T y))) :=
      hx.weak.inner_strong J hTyn D hDx
    have hmove :
        Tendsto
          (fun n ↦ inner K
            (J.embedding n (ContinuousLinearMap.adjoint (Tn n) (x n)))
            (J.embedding n (yn n))) atTop
          (𝓝 (inner K (ContinuousLinearMap.adjoint T xlim) y)) := by
      convert hpair using 1
      · funext n
        rw [J.embedding n |>.inner_map_map,
          J.embedding n |>.inner_map_map]
        exact (Tn n).adjoint_inner_left (yn n) (x n)
      · exact congrArg nhds (T.adjoint_inner_left y xlim)
    have hynDiff :
        Tendsto (fun n ↦ ‖y - J.embedding n (yn n)‖) atTop (𝓝 0) := by
      simpa [StronglyConverges, norm_sub_rev,
        tendsto_iff_norm_sub_tendsto_zero] using hyn
    have herror :
        Tendsto
          (fun n ↦ inner K
            (J.embedding n (ContinuousLinearMap.adjoint (Tn n) (x n)))
            (y - J.embedding n (yn n))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n ↦ C * ‖y - J.embedding n (yn n)‖) ?_ ?_
      · intro n
        calc
          ‖inner K
              (J.embedding n (ContinuousLinearMap.adjoint (Tn n) (x n)))
              (y - J.embedding n (yn n))‖ ≤
              ‖J.embedding n (ContinuousLinearMap.adjoint (Tn n) (x n))‖ *
                ‖y - J.embedding n (yn n)‖ := norm_inner_le_norm _ _
          _ ≤ C * ‖y - J.embedding n (yn n)‖ := by
            gcongr
            simpa using hAdjBound n
      · simpa using (tendsto_const_nhds.mul hynDiff :
          Tendsto (fun n ↦ C * ‖y - J.embedding n (yn n)‖) atTop (𝓝 (C * 0)))
    have hsum := hmove.add herror
    convert hsum using 1
    · funext n
      rw [← inner_add_right]
      simp
    · simp
  exact hweak.strong_of_norm J hnorm

end NCG.VaryingHilbert.System
