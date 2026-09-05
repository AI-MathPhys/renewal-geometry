/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Weak lower semicontinuity of the norm on varying Hilbert spaces

A uniformly bounded weakly convergent dependent sequence satisfies the usual Hilbert-space
lower bound on its norm.  The proof tests weak convergence against the limit vector and applies
Cauchy--Schwarz in the common carrier.
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

/-- Weak convergence and a uniform norm bound imply the norm liminf inequality. -/
theorem WeaklyConverges.norm_le_liminf
    {x : ∀ n, Hn n} {xlim : H}
    (hweak : J.WeaklyConverges x xlim)
    (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C) :
    ‖xlim‖ ≤ liminf (fun n ↦ ‖x n‖) atTop := by
  have hnormBoundedAbove : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ ‖x n‖) :=
    isBoundedUnder_of ⟨C, hbound⟩
  have hnormCoboundedBelow : IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ ‖x n‖) :=
    hnormBoundedAbove.isCobounded_flip
  by_cases hxlim : xlim = 0
  · subst xlim
    simpa using le_liminf_of_le hnormCoboundedBelow
      (Eventually.of_forall fun n ↦ norm_nonneg (x n))
  have hxlimPos : 0 < ‖xlim‖ := norm_pos_iff.mpr hxlim
  let u : ℕ → ℝ := fun n ↦
    RCLike.re (inner K (J.embedding n (x n)) xlim) / ‖xlim‖
  have hinnerRe : Tendsto
      (fun n ↦ RCLike.re (inner K (J.embedding n (x n)) xlim)) atTop
      (𝓝 (RCLike.re (inner K xlim xlim))) :=
    RCLike.reCLM.continuous.continuousAt.tendsto.comp (hweak xlim)
  have huTendsto : Tendsto u atTop (𝓝 ‖xlim‖) := by
    have hquot := hinnerRe.div_const ‖xlim‖
    convert hquot using 1
    rw [inner_self_eq_norm_sq]
    field_simp
  have huLe : ∀ n, u n ≤ ‖x n‖ := by
    intro n
    apply (div_le_iff₀ hxlimPos).2
    calc
      RCLike.re (inner K (J.embedding n (x n)) xlim) ≤
          ‖inner K (J.embedding n (x n)) xlim‖ := RCLike.re_le_norm _
      _ ≤ ‖J.embedding n (x n)‖ * ‖xlim‖ := norm_inner_le_norm _ _
      _ = ‖x n‖ * ‖xlim‖ := by rw [LinearIsometry.norm_map]
  calc
    ‖xlim‖ = liminf u atTop := huTendsto.liminf_eq.symm
    _ ≤ liminf (fun n ↦ ‖x n‖) atTop :=
      liminf_le_liminf (Eventually.of_forall huLe)
        huTendsto.isBoundedUnder_ge hnormCoboundedBelow

/-- The squared norm inherits the weak liminf inequality. -/
theorem WeaklyConverges.norm_sq_le_liminf
    {x : ∀ n, Hn n} {xlim : H}
    (hweak : J.WeaklyConverges x xlim)
    (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C) :
    ‖xlim‖ ^ 2 ≤ liminf (fun n ↦ ‖x n‖ ^ 2) atTop := by
  let norms : ℕ → ℝ := fun n ↦ ‖x n‖
  let g : ℝ → ℝ := fun t ↦ (max t 0) ^ 2
  have hnormBoundedAbove : IsBoundedUnder (· ≤ ·) atTop norms :=
    isBoundedUnder_of ⟨C, hbound⟩
  have hnormBoundedBelow : IsBoundedUnder (· ≥ ·) atTop norms :=
    isBoundedUnder_of ⟨0, fun n ↦ norm_nonneg (x n)⟩
  have hnormCoboundedBelow : IsCoboundedUnder (· ≥ ·) atTop norms :=
    hnormBoundedAbove.isCobounded_flip
  have hliminfNonneg : 0 ≤ liminf norms atTop :=
    le_liminf_of_le hnormCoboundedBelow
      (Eventually.of_forall fun n ↦ norm_nonneg (x n))
  have hgMonotone : Monotone g := by
    intro a b hab
    dsimp [g]
    have hmax : max a 0 ≤ max b 0 := max_le_max hab le_rfl
    nlinarith [le_max_right a 0, le_max_right b 0]
  have hmap := hgMonotone.map_liminf_of_continuousAt norms
    (by fun_prop) hnormCoboundedBelow hnormBoundedBelow
  have hnormLower : ‖xlim‖ ≤ liminf norms atTop := by
    simpa [norms] using hweak.norm_le_liminf J C hbound
  calc
    ‖xlim‖ ^ 2 ≤ (liminf norms atTop) ^ 2 := by
      nlinarith [norm_nonneg xlim]
    _ = g (liminf norms atTop) := by simp [g, max_eq_left hliminfNonneg]
    _ = liminf (g ∘ norms) atTop := hmap
    _ = liminf (fun n ↦ ‖x n‖ ^ 2) atTop := by
      congr 1
      funext n
      simp [g, norms]

end NCG.VaryingHilbert.System
