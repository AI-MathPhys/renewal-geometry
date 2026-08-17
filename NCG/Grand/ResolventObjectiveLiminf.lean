/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertWeakNormLowerSemicontinuity
import NCG.Grand.VaryingHilbertResolventObjective
import NCG.Grand.VaryingHilbertWeakStrongPairing
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Liminf inequality for varying-space resolvent objectives

The Mosco form liminf, weak lower semicontinuity of the squared norm, and convergence of the
weak--strong source pairing combine into the liminf inequality for the full resolvent objective.
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

/-- The ordinary form liminf inequality implies the full resolvent-objective liminf inequality
along bounded weakly convergent vectors and bounded strongly convergent sources. -/
theorem resolventObjective_le_liminf
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (f x : ∀ n, Hn n) (flim xlim : H)
    (C F Q : ℝ)
    (hweak : J.WeaklyConverges x xlim)
    (hf : J.StronglyConverges f flim)
    (hxBound : ∀ n, ‖x n‖ ≤ C) (hfBound : ∀ n, ‖f n‖ ≤ F)
    (hqNonneg : ∀ n, 0 ≤ q n (x n)) (hqUpper : ∀ n, q n (x n) ≤ Q)
    (hqLiminf : qlim xlim ≤ liminf (fun n ↦ q n (x n)) atTop) :
    resolventObjective (K := K) qlim lam flim xlim ≤
      liminf (fun n ↦ resolventObjective (K := K) (q n) lam (f n) (x n)) atTop := by
  let a : ℕ → ℝ := fun n ↦ q n (x n)
  let b : ℕ → ℝ := fun n ↦ lam * ‖x n‖ ^ 2
  let c : ℕ → ℝ := fun n ↦ -2 * RCLike.re (inner K (x n) (f n))
  have hC : 0 ≤ C := (norm_nonneg (x 0)).trans (hxBound 0)
  have hF : 0 ≤ F := (norm_nonneg (f 0)).trans (hfBound 0)
  have haLower : IsBoundedUnder (· ≥ ·) atTop a :=
    isBoundedUnder_of ⟨0, hqNonneg⟩
  have haUpper : IsBoundedUnder (· ≤ ·) atTop a :=
    isBoundedUnder_of ⟨Q, hqUpper⟩
  have hbLower : IsBoundedUnder (· ≥ ·) atTop b := by
    refine isBoundedUnder_of ⟨0, fun n ↦ ?_⟩
    exact mul_nonneg hlam.le (sq_nonneg ‖x n‖)
  have hbUpper : IsBoundedUnder (· ≤ ·) atTop b := by
    refine isBoundedUnder_of ⟨lam * C ^ 2, fun n ↦ ?_⟩
    dsimp [b]
    gcongr
    exact hxBound n
  have hpairAbs : ∀ n, |RCLike.re (inner K (x n) (f n))| ≤ C * F := by
    intro n
    calc
      |RCLike.re (inner K (x n) (f n))| ≤ ‖inner K (x n) (f n)‖ :=
        RCLike.abs_re_le_norm _
      _ ≤ ‖x n‖ * ‖f n‖ := norm_inner_le_norm _ _
      _ ≤ C * F := mul_le_mul (hxBound n) (hfBound n) (norm_nonneg _) hC
  have hcLower : IsBoundedUnder (· ≥ ·) atTop c := by
    refine isBoundedUnder_of ⟨-2 * (C * F), fun n ↦ ?_⟩
    dsimp [c]
    have := hpairAbs n
    rw [abs_le] at this
    nlinarith
  have hcUpper : IsBoundedUnder (· ≤ ·) atTop c := by
    refine isBoundedUnder_of ⟨2 * (C * F), fun n ↦ ?_⟩
    dsimp [c]
    have := hpairAbs n
    rw [abs_le] at this
    nlinarith
  have hnormSq := hweak.norm_sq_le_liminf J C hxBound
  let normsSq : ℕ → ℝ := fun n ↦ ‖x n‖ ^ 2
  have hsLower : IsBoundedUnder (· ≥ ·) atTop normsSq :=
    isBoundedUnder_of ⟨0, fun n ↦ sq_nonneg ‖x n‖⟩
  have hsUpper : IsBoundedUnder (· ≤ ·) atTop normsSq := by
    refine isBoundedUnder_of ⟨C ^ 2, fun n ↦ ?_⟩
    dsimp [normsSq]
    nlinarith [norm_nonneg (x n), hxBound n]
  have hscaleMonotone : Monotone (fun t : ℝ ↦ lam * t) := fun _ _ h ↦
    mul_le_mul_of_nonneg_left h hlam.le
  have hscale := hscaleMonotone.map_liminf_of_continuousAt normsSq
    (by fun_prop) hsUpper.isCobounded_flip hsLower
  have hbLiminf : lam * ‖xlim‖ ^ 2 ≤ liminf b atTop := by
    calc
      lam * ‖xlim‖ ^ 2 ≤ lam * liminf normsSq atTop :=
        mul_le_mul_of_nonneg_left (by simpa [normsSq] using hnormSq) hlam.le
      _ = liminf b atTop := by simpa [b, normsSq, Function.comp_def] using hscale
  have hpair := hweak.inner_strong J hf C hxBound
  have hinnerRe : Tendsto (fun n ↦ RCLike.re (inner K (x n) (f n))) atTop
      (𝓝 (RCLike.re (inner K xlim flim))) := by
    have hre := RCLike.reCLM.continuous.continuousAt.tendsto.comp hpair
    simpa only [Function.comp_def, LinearIsometry.inner_map_map,
      RCLike.reCLM_apply] using hre
  have hcTendsto : Tendsto c atTop
      (𝓝 (-2 * RCLike.re (inner K xlim flim))) := by
    simpa [c] using hinnerRe.const_mul (-2)
  have habLiminf : liminf a atTop + liminf b atTop ≤ liminf (a + b) atTop :=
    le_liminf_add haLower haUpper hbLower hbUpper.isCobounded_flip
  have habLower : IsBoundedUnder (· ≥ ·) atTop (a + b) :=
    isBoundedUnder_ge_add haLower hbLower
  have habUpper : IsBoundedUnder (· ≤ ·) atTop (a + b) :=
    isBoundedUnder_le_add haUpper hbUpper
  have habcLiminf : liminf (a + b) atTop + liminf c atTop ≤
      liminf ((a + b) + c) atTop :=
    le_liminf_add habLower habUpper hcLower hcUpper.isCobounded_flip
  calc
    resolventObjective (K := K) qlim lam flim xlim =
        qlim xlim + lam * ‖xlim‖ ^ 2 +
          (-2 * RCLike.re (inner K xlim flim)) := by
      simp [resolventObjective]
      ring
    _ ≤ liminf a atTop + liminf b atTop + liminf c atTop := by
      apply add_le_add
      · exact add_le_add hqLiminf hbLiminf
      · exact le_of_eq hcTendsto.liminf_eq.symm
    _ ≤ liminf (a + b) atTop + liminf c atTop :=
      add_le_add habLiminf le_rfl
    _ ≤ liminf ((a + b) + c) atTop := habcLiminf
    _ = liminf (fun n ↦ resolventObjective (K := K)
        (q n) lam (f n) (x n)) atTop := by
      congr 1
      funext n
      simp [a, b, c, resolventObjective]
      ring

end NCG.VaryingHilbert.System
