/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Nondegenerate critical-point shadowing (`prop:critical-shadowing`, Einstein–SM
action closure)

The frozen-Newton contraction argument of the proposition, on an arbitrary complete
real normed space `X` (the gauge-fixed finite-dimensional physical slice `X_h` with its
positive slice inner product).  Given the finite Euler map `F : X → X` with derivative
`F'` on the ball `closedBall x₀ r` and the hypotheses

* (S1) `‖F x₀‖ ≤ C₀ h`;
* (S2) `B` is a two-sided inverse of `F' x₀` with `‖B‖ ≤ M`;
* (S3) `‖F' x - F' y‖ ≤ L ‖x - y‖` on the ball;

the frozen-Newton map `T x = x - B (F x)` is a contraction of the Newton ball
`closedBall x₀ ρ`, `ρ = 2 M C₀ h`, into itself as soon as `ρ ≤ r` and `M L ρ ≤ 1/2`
(the explicit form of "for sufficiently small `h`"), so it has a unique fixed point
there, which is the unique zero of `F` in the Newton ball
(`exists_unique_zero_in_newton_ball`, **`eq:critical-shadowing`**).  With (S4), the
local Lipschitz reconstruction bound, and the `O(h)` sampling distance
`d_K(R_h x₀, z_*) ≤ C_S h` inherited from `prop:smooth-sampling`, the reconstruction of
the exact critical point is `O(h)` from `z_*` (`reconstruction_dist_le`).

The mean-value inequality replaces the paper's Taylor estimate: the derivative of `T`
on the Newton ball is `B ∘ (F' x₀ - F' x)`, of norm at most `M L ρ`, which gives the
contraction constant `M L ρ ≤ 1/2` and the self-map bound
`‖T x - x₀‖ ≤ M L ρ · ρ + M C₀ h ≤ ρ`.
-/

open Metric Set Filter Topology

namespace RenewalGeometry.CriticalShadowing

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The frozen-Newton map `T x = x - B (F x)`. -/
def newtonMap (F : X → X) (B : X →L[ℝ] X) (x : X) : X := x - B (F x)

/-- Hypotheses (S1)–(S3) of `prop:critical-shadowing` on the ball `closedBall x₀ r`,
together with the smallness conditions on the Newton radius `ρ = 2 M C₀ h`. -/
structure Hypotheses (F : X → X) (F' : X → X →L[ℝ] X) (B : X →L[ℝ] X) (x₀ : X)
    (r M L C₀ h : ℝ) : Prop where
  /-- `M, L, C₀, h ≥ 0` -/
  M_nonneg : 0 ≤ M
  L_nonneg : 0 ≤ L
  C₀_nonneg : 0 ≤ C₀
  h_nonneg : 0 ≤ h
  /-- `F` is differentiable on the ball with derivative `F'` -/
  hasFDerivAt : ∀ x ∈ closedBall x₀ r, HasFDerivAt F (F' x) x
  /-- (S1) -/
  residual : ‖F x₀‖ ≤ C₀ * h
  /-- (S2): `B` is a left inverse of `F' x₀` -/
  left_inv : B.comp (F' x₀) = ContinuousLinearMap.id ℝ X
  /-- (S2): `B` is a right inverse of `F' x₀` -/
  right_inv : (F' x₀).comp B = ContinuousLinearMap.id ℝ X
  /-- (S2): `‖B‖ ≤ M` -/
  norm_B : ‖B‖ ≤ M
  /-- (S3) -/
  lipschitz_deriv : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
    ‖F' x - F' y‖ ≤ L * ‖x - y‖
  /-- the Newton ball lies in the ball of hypotheses -/
  newton_le : 2 * M * C₀ * h ≤ r
  /-- smallness of `h`: `M L ρ ≤ 1/2` -/
  small : M * L * (2 * M * C₀ * h) ≤ 1 / 2

variable {F : X → X} {F' : X → X →L[ℝ] X} {B : X →L[ℝ] X} {x₀ : X} {r M L C₀ h : ℝ}

/-- The Newton radius `ρ = 2 M C₀ h`. -/
def newtonRadius (M C₀ h : ℝ) : ℝ := 2 * M * C₀ * h

theorem newtonRadius_nonneg (H : Hypotheses F F' B x₀ r M L C₀ h) :
    0 ≤ newtonRadius M C₀ h := by
  unfold newtonRadius
  have := H.M_nonneg; have := H.C₀_nonneg; have := H.h_nonneg
  positivity

theorem newtonBall_subset (H : Hypotheses F F' B x₀ r M L C₀ h) :
    closedBall x₀ (newtonRadius M C₀ h) ⊆ closedBall x₀ r :=
  closedBall_subset_closedBall H.newton_le

/-- The derivative of the frozen-Newton map at `x` is `B ∘ (F' x₀ - F' x)`. -/
theorem hasFDerivAt_newtonMap (H : Hypotheses F F' B x₀ r M L C₀ h)
    {x : X} (hx : x ∈ closedBall x₀ r) :
    HasFDerivAt (newtonMap F B) (B.comp (F' x₀ - F' x)) x := by
  have h1 : HasFDerivAt (fun y => y - B (F y))
      (ContinuousLinearMap.id ℝ X - B.comp (F' x)) x :=
    (hasFDerivAt_id x).sub (B.hasFDerivAt.comp x (H.hasFDerivAt x hx))
  have h2 : ContinuousLinearMap.id ℝ X - B.comp (F' x) = B.comp (F' x₀ - F' x) := by
    rw [ContinuousLinearMap.comp_sub, H.left_inv]
  rw [h2] at h1
  exact h1

/-- Lipschitz bound for the frozen-Newton map on the Newton ball, with constant
`M L ρ`. -/
theorem newtonMap_dist_le (H : Hypotheses F F' B x₀ r M L C₀ h)
    {x y : X} (hx : x ∈ closedBall x₀ (newtonRadius M C₀ h))
    (hy : y ∈ closedBall x₀ (newtonRadius M C₀ h)) :
    ‖newtonMap F B y - newtonMap F B x‖ ≤ (M * L * newtonRadius M C₀ h) * ‖y - x‖ := by
  have hsub := newtonBall_subset H
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := newtonMap F B) (f' := fun z => B.comp (F' x₀ - F' z))
    (s := closedBall x₀ (newtonRadius M C₀ h)) (fun z hz => ?_) (fun z hz => ?_)
    (convex_closedBall _ _) hx hy
  · exact (hasFDerivAt_newtonMap H (hsub hz)).hasFDerivWithinAt
  · calc ‖B.comp (F' x₀ - F' z)‖ ≤ ‖B‖ * ‖F' x₀ - F' z‖ := B.opNorm_comp_le _
      _ ≤ M * (L * ‖x₀ - z‖) :=
          mul_le_mul H.norm_B (H.lipschitz_deriv x₀ (mem_closedBall_self
              (le_trans (newtonRadius_nonneg H) H.newton_le)) z (hsub hz))
            (norm_nonneg _) H.M_nonneg
      _ ≤ M * (L * newtonRadius M C₀ h) := by
          have hz' : ‖x₀ - z‖ ≤ newtonRadius M C₀ h := by
            rw [← dist_eq_norm, dist_comm]; exact mem_closedBall.1 hz
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hz' H.L_nonneg) H.M_nonneg
      _ = M * L * newtonRadius M C₀ h := by ring

/-- The frozen-Newton map sends the Newton ball into itself. -/
theorem newtonMap_mapsTo (H : Hypotheses F F' B x₀ r M L C₀ h) :
    MapsTo (newtonMap F B) (closedBall x₀ (newtonRadius M C₀ h))
      (closedBall x₀ (newtonRadius M C₀ h)) := by
  intro x hx
  have hρ := newtonRadius_nonneg H
  have hx0 : x₀ ∈ closedBall x₀ (newtonRadius M C₀ h) := mem_closedBall_self hρ
  have h1 := newtonMap_dist_le H hx0 hx
  have h2 : ‖newtonMap F B x₀ - x₀‖ ≤ M * C₀ * h := by
    calc ‖newtonMap F B x₀ - x₀‖ = ‖B (F x₀)‖ := by
          rw [newtonMap, sub_sub_cancel_left, norm_neg]
      _ ≤ ‖B‖ * ‖F x₀‖ := B.le_opNorm _
      _ ≤ M * (C₀ * h) := mul_le_mul H.norm_B H.residual (norm_nonneg _) H.M_nonneg
      _ = M * C₀ * h := by ring
  rw [mem_closedBall, dist_eq_norm]
  have hxn : ‖x - x₀‖ ≤ newtonRadius M C₀ h := by
    rw [← dist_eq_norm]; exact mem_closedBall.1 hx
  have hsmall := H.small
  have hK : 0 ≤ M * L * newtonRadius M C₀ h := by
    have := H.M_nonneg; have := H.L_nonneg; positivity
  calc ‖newtonMap F B x - x₀‖
      ≤ ‖newtonMap F B x - newtonMap F B x₀‖ + ‖newtonMap F B x₀ - x₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (M * L * newtonRadius M C₀ h) * ‖x - x₀‖ + M * C₀ * h := add_le_add h1 h2
    _ ≤ (M * L * newtonRadius M C₀ h) * newtonRadius M C₀ h + M * C₀ * h := by gcongr
    _ ≤ (1 / 2) * newtonRadius M C₀ h + M * C₀ * h := by
        gcongr
        simpa [newtonRadius] using hsmall
    _ = newtonRadius M C₀ h := by unfold newtonRadius; ring

/-- **`prop:critical-shadowing`, existence and uniqueness (`eq:critical-shadowing`).**
Under (S1)–(S3) and the smallness conditions, there is exactly one zero of the finite
Euler map `F` in the Newton ball `‖x - x₀‖ ≤ 2 M C₀ h`. -/
theorem exists_unique_zero_in_newton_ball (H : Hypotheses F F' B x₀ r M L C₀ h) :
    ∃! xs : X, xs ∈ closedBall x₀ (2 * M * C₀ * h) ∧ F xs = 0 := by
  have hρ := newtonRadius_nonneg H
  have hmaps := newtonMap_mapsTo H
  have hcomplete : IsComplete (closedBall x₀ (newtonRadius M C₀ h)) :=
    (isClosed_closedBall).isComplete
  set K : ℝ := M * L * newtonRadius M C₀ h with hKdef
  have hK0 : 0 ≤ K := by
    have := H.M_nonneg; have := H.L_nonneg; positivity
  have hK1 : K ≤ 1 / 2 := by simpa [hKdef, newtonRadius] using H.small
  have hcontr : ContractingWith ⟨K, hK0⟩
      (hmaps.restrict (newtonMap F B) _ _) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · change K < 1
      linarith
    · simp only [MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm, NNReal.coe_mk]
      exact newtonMap_dist_le H y.2 x.2
  obtain ⟨y, hy, hfix, -, -⟩ := hcontr.exists_fixedPoint' hcomplete hmaps
    (mem_closedBall_self hρ) (edist_ne_top _ _)
  -- a fixed point of the Newton map is a zero of `F`
  have hzero : ∀ z, newtonMap F B z = z → F z = 0 := by
    intro z hz
    have hBz : B (F z) = 0 := by
      have : z - B (F z) = z := hz
      rwa [sub_eq_self] at this
    have : F z = (F' x₀).comp B (F z) := by rw [H.right_inv]; rfl
    rw [this, ContinuousLinearMap.comp_apply, hBz, map_zero]
  refine ⟨y, ⟨hy, hzero y hfix⟩, ?_⟩
  rintro z ⟨hz, hFz⟩
  have hzfix : newtonMap F B z = z := by
    rw [newtonMap, hFz, map_zero, sub_zero]
  have hyfix : newtonMap F B y = y := hfix
  have h1 := newtonMap_dist_le H hy hz
  rw [hzfix, hyfix] at h1
  have : ‖z - y‖ ≤ 0 := by nlinarith [norm_nonneg (z - y)]
  have := le_antisymm this (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this

/-- **`prop:critical-shadowing`, reconstruction clause.**  With the locally Lipschitz
reconstruction (S4) and the `O(h)` sampling distance `d_K(R_h x₀, z_*) ≤ C_S h` of
`prop:smooth-sampling`, every zero of `F` in the Newton ball reconstructs within
`(2 C_R M C₀ + C_S) h` of the smooth critical configuration `z_*`. -/
theorem reconstruction_dist_le {Z : Type*} [PseudoMetricSpace Z]
    (H : Hypotheses F F' B x₀ r M L C₀ h)
    (Rh : X → Z) (zstar : Z) (CR CS : ℝ) (hCR : 0 ≤ CR)
    (hRLip : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (Rh x) (Rh y) ≤ CR * ‖x - y‖)
    (hsamp : dist (Rh x₀) zstar ≤ CS * h)
    {xs : X} (hxs : xs ∈ closedBall x₀ (2 * M * C₀ * h)) :
    dist (Rh xs) zstar ≤ (2 * CR * M * C₀ + CS) * h := by
  have hsub := newtonBall_subset H
  have hx0 : x₀ ∈ closedBall x₀ r :=
    mem_closedBall_self (le_trans (newtonRadius_nonneg H) H.newton_le)
  calc dist (Rh xs) zstar ≤ dist (Rh xs) (Rh x₀) + dist (Rh x₀) zstar := dist_triangle _ _ _
    _ ≤ CR * ‖xs - x₀‖ + CS * h := add_le_add (hRLip xs (hsub hxs) x₀ hx0) hsamp
    _ ≤ CR * (2 * M * C₀ * h) + CS * h := by
        gcongr
        rw [← dist_eq_norm]; exact mem_closedBall.1 hxs
    _ = (2 * CR * M * C₀ + CS) * h := by ring

end RenewalGeometry.CriticalShadowing
