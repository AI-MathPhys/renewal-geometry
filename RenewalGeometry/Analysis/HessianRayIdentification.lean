/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.DerivBoundBootstrap
import RenewalGeometry.Analysis.NormalizedMeanMapRoot

/-!
# Identifying Hessians along rays (generic)

Small generic tools used to identify the quadratic jet of the reduced mean map with the quadratic
mean jet of the original constraint map (`thm:supp-action-prepared-chart`):

* `eq_of_ray_bounds`: if `φ(s) = s² q + O(s³)`, `ψ(s) = s² q' + O(s³)` and `φ - ψ = O(s³)` as
  `s ↓ 0`, then `q = q'`.
* `taylor_of_derivBound`: a function with uniform bounds on its first three derivatives on a ball
  satisfies all hypotheses of `NormalizedMeanRoot.ray_second_order` with `DΘ = Df`, `D2 = D²f`.
* `ray_of_ball`: the ball form of the second-order Taylor bound gives the ray form.
* `fderiv_fderiv_apply_eq_of_eventuallyEq`: the second derivative of a component of `G` at `0`
  equals the second derivative of `m` at `e 0` along `e`, whenever `G_c =ᶠ m ∘ e` near `0` for a
  continuous linear equivalence `e`.
-/

open Filter Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.HessianRay

open IteratedDerivBounds UniformDerivBounds

variable {E E' W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ W] in
/-- If `‖q - q'‖ ≤ K s` for all small `s > 0`, then `q = q'`. -/
theorem eq_of_norm_le_mul {q q' : W} {K s0 : ℝ} (hs0 : 0 < s0)
    (h : ∀ s, 0 < s → s < s0 → ‖q - q'‖ ≤ K * s) : q = q' := by
  by_contra hne
  have hd : 0 < ‖q - q'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set d := ‖q - q'‖
  set s := min (s0 / 2) (d / (2 * (|K| + 1)))
  have hK1 : 0 < |K| + 1 := by positivity
  have hs : 0 < s := lt_min (by linarith) (by positivity)
  have hss : s < s0 := (min_le_left _ _).trans_lt (by linarith)
  have h1 := h s hs hss
  have h2 : K * s ≤ |K| * s := mul_le_mul_of_nonneg_right (le_abs_self K) hs.le
  have h3 : |K| * s ≤ (|K| + 1) * (d / (2 * (|K| + 1))) :=
    mul_le_mul (by linarith) (min_le_right _ _) hs.le hK1.le
  have h4 : (|K| + 1) * (d / (2 * (|K| + 1))) = d / 2 := by field_simp
  linarith

/-- **Uniqueness of the quadratic coefficient along a ray.** -/
theorem eq_of_ray_bounds {φ ψ : ℝ → W} {q q' : W} {K s0 : ℝ} (hs0 : 0 < s0)
    (hφ : ∀ s, 0 < s → s < s0 → ‖φ s - s ^ 2 • q‖ ≤ K * s ^ 3)
    (hψ : ∀ s, 0 < s → s < s0 → ‖ψ s - s ^ 2 • q'‖ ≤ K * s ^ 3)
    (hφψ : ∀ s, 0 < s → s < s0 → ‖φ s - ψ s‖ ≤ K * s ^ 3) : q = q' := by
  refine eq_of_norm_le_mul (K := 3 * K) hs0 fun s hs hss => ?_
  have hs2 : 0 < s ^ 2 := by positivity
  have hmain : ‖s ^ 2 • (q - q')‖ ≤ 3 * K * s ^ 3 := by
    have e : s ^ 2 • (q - q') = (ψ s - s ^ 2 • q') - (φ s - s ^ 2 • q) + (φ s - ψ s) := by
      rw [smul_sub]; abel
    rw [e]
    calc ‖(ψ s - s ^ 2 • q') - (φ s - s ^ 2 • q) + (φ s - ψ s)‖
        ≤ ‖ψ s - s ^ 2 • q'‖ + ‖φ s - s ^ 2 • q‖ + ‖φ s - ψ s‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ K * s ^ 3 + K * s ^ 3 + K * s ^ 3 :=
          add_le_add (add_le_add (hψ s hs hss) (hφ s hs hss)) (hφψ s hs hss)
      _ = 3 * K * s ^ 3 := by ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs2] at hmain
  have : s ^ 2 * ‖q - q'‖ ≤ s ^ 2 * (3 * K * s) := by
    calc s ^ 2 * ‖q - q'‖ ≤ 3 * K * s ^ 3 := hmain
      _ = s ^ 2 * (3 * K * s) := by ring
  exact le_of_mul_le_mul_left this hs2

/-- **The second-order Taylor hypotheses from uniform derivative bounds.**  If `‖Dᵏf‖ ≤ K`
(`k ≤ 3`) on `B(0, ρ)`, then on `B(0, ρ)`: `f` and `Df` have derivatives `Df`, `D²f`; `D²f` is
`K`-Lipschitz at `0`; `D²f(0)` is symmetric with `‖D²f(0)‖ ≤ K`. -/
theorem taylor_of_derivBound {f : E → W} {ρ K : ℝ} (hf : DerivBound f (ball (0 : E) ρ) 3 K) :
    (∀ x ∈ ball (0 : E) ρ, HasFDerivAt f (fderiv ℝ f x) x) ∧
    (∀ x ∈ ball (0 : E) ρ, HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x) ∧
    (∀ x ∈ ball (0 : E) ρ, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) 0‖ ≤ K * ‖x‖) ∧
    (0 < ρ → ∀ u v, fderiv ℝ (fderiv ℝ f) 0 u v = fderiv ℝ (fderiv ℝ f) 0 v u) ∧
    (0 < ρ → ‖fderiv ℝ (fderiv ℝ f) 0‖ ≤ K) := by
  have h1 : DerivBound (fderiv ℝ f) (ball (0 : E) ρ) 2 K := hf.fderiv (K := 2) isOpen_ball
  refine ⟨fun x hx => ((hf.contDiffAt isOpen_ball hx).differentiableAt (by simp)).hasFDerivAt,
    fun x hx => ((h1.contDiffAt isOpen_ball hx).differentiableAt (by simp)).hasFDerivAt,
    fun x hx => ?_, fun hρ u v => ?_, fun hρ => ?_⟩
  · have h0 : (0 : E) ∈ ball (0 : E) ρ := mem_ball_self ((norm_nonneg x).trans_lt
      (mem_ball_zero_iff.mp hx))
    have := norm_fderiv_fderiv_sub_le_of_derivBound (K := 0) hf isOpen_ball (convex_ball 0 ρ) hx h0
    simpa using this
  · have hc := hf.contDiffAt isOpen_ball (mem_ball_self hρ)
    have hs := hc.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    exact hs u v
  · have := h1.bound 0 (mem_ball_self hρ) 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this

/-- The second-order Taylor bound of a function with uniform order-three bounds and vanishing
constant and linear jets: `‖f x - ½ D²f(0)(x, x)‖ ≤ K ‖x‖³` on `B(0, ρ)`. -/
theorem taylor_bound_of_derivBound {f : E → W} {ρ K : ℝ} (hf : DerivBound f (ball (0 : E) ρ) 3 K)
    (hK : 0 ≤ K) (h0 : f 0 = 0) (hd0 : fderiv ℝ f 0 = 0) :
    ∀ x ∈ ball (0 : E) ρ, ‖f x - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 x x‖ ≤ K * ‖x‖ ^ 3 := by
  intro x hx
  have hρ : 0 < ρ := (norm_nonneg x).trans_lt (mem_ball_zero_iff.mp hx)
  obtain ⟨hΘ, hDΘ, hL, hsymm, -⟩ := taylor_of_derivBound hf
  exact (NormalizedMeanRoot.ray_second_order hΘ hDΘ hL hK h0 hd0 (hsymm hρ)).2 x hx

/-- The ball form of the second-order Taylor bound gives the ray form. -/
theorem ray_of_ball {f : E → W} {B : E →L[ℝ] E →L[ℝ] W} {ρ K : ℝ}
    (h : ∀ x ∈ ball (0 : E) ρ, ‖f x - (1 / 2 : ℝ) • B x x‖ ≤ K * ‖x‖ ^ 3) (v : E) :
    ∀ s, 0 < s → s < ρ / (‖v‖ + 1) →
      ‖f (s • v) - s ^ 2 • ((1 / 2 : ℝ) • B v v)‖ ≤ (K * ‖v‖ ^ 3) * s ^ 3 := by
  intro s hs hss
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have hsv : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hin : s • v ∈ ball (0 : E) ρ := by
    rw [mem_ball_zero_iff, hsv]
    have : s * (‖v‖ + 1) < ρ := by
      have := (lt_div_iff₀ hv1).mp hss; linarith
    nlinarith [norm_nonneg v]
  have e : (1 / 2 : ℝ) • B (s • v) (s • v) = s ^ 2 • ((1 / 2 : ℝ) • B v v) := by
    simp only [map_smul, smul_apply, smul_smul]
    congr 1; ring
  have := h _ hin
  rw [e, hsv] at this
  calc _ ≤ K * (s * ‖v‖) ^ 3 := this
    _ = (K * ‖v‖ ^ 3) * s ^ 3 := by ring

/-- **Second derivatives of a component through a linear change of variables.**  If the
component `x ↦ G x c` agrees near `0` with `m ∘ e` for a continuous linear equivalence `e`, and `G`
is `C²` at `0`, then `D²G(0)(u, v)_c = D²m(e 0)(e u, e v)`. -/
theorem fderiv_fderiv_apply_eq_of_eventuallyEq {ι : Type*} [Fintype ι] {G : E → ι → ℝ}
    {m : E' → ℝ} (e : E ≃L[ℝ] E') (c : ι) (hG : ContDiffAt ℝ 2 G 0)
    (heq : (fun x => G x c) =ᶠ[𝓝 0] fun x => m (e x)) (u v : E) :
    fderiv ℝ (fderiv ℝ G) 0 u v c = fderiv ℝ (fderiv ℝ m) (e 0) (e u) (e v) := by
  have h1 : iteratedFDeriv ℝ 2 (fun x => G x c) 0 =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) c).compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2 G 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) c).iteratedFDeriv_comp_left hG
      le_rfl
  have h2 : iteratedFDeriv ℝ 2 (fun x => G x c) 0 = iteratedFDeriv ℝ 2 (m ∘ e) 0 :=
    (heq.iteratedFDeriv ℝ 2).eq_of_nhds
  have h3 : iteratedFDeriv ℝ 2 (m ∘ e) 0 =
      (iteratedFDeriv ℝ 2 m (e 0)).compContinuousLinearMap fun _ => (e : E →L[ℝ] E') := by
    have := e.iteratedFDerivWithin_comp_right m uniqueDiffOn_univ (mem_univ (e 0)) 2
    simpa [iteratedFDerivWithin_univ] using this
  have hL := congrArg (fun T => T ![u, v]) h1
  have hR := congrArg (fun T => T ![u, v]) (h2.trans h3)
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.proj_apply, iteratedFDeriv_two_apply] at hL
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply,
    ContinuousLinearEquiv.coe_coe] at hR
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hL hR
  rw [← hL, hR]

end RenewalGeometry.HessianRay
