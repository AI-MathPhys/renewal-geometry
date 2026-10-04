/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Continuous partial derivatives imply `C¹`

Generic infrastructure (no renewal notions).  On an open set `U ⊂ ℝⁿ` (`Fin n → ℝ`, sup norm),
a function whose partial derivatives `∂ᵢf` exist at every point of `U` and are continuous on `U`
is Fréchet differentiable on `U` with `Df(x)h = Σᵢ hᵢ ∂ᵢf(x)`, hence `C¹`
(`hasFDerivAt_of_partials`, `contDiffOn_one_of_partials`); if moreover the partial derivatives are
themselves `C¹`, `f` is `C²` (`contDiffOn_two_of_partials`).  Proof: telescoping along the
coordinate directions and the one-dimensional mean value inequality.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

noncomputable section

namespace RenewalGeometry.PartialC1

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The partial sum `P_k h = Σ_{i < k} hᵢ eᵢ`. -/
def psum (k : ℕ) (h : Fin n → ℝ) : Fin n → ℝ := fun i => if (i : ℕ) < k then h i else 0

theorem psum_zero (h : Fin n → ℝ) : psum 0 h = 0 := by
  funext i; simp [psum]

theorem psum_n (h : Fin n → ℝ) : psum n h = h := by
  funext i; simp [psum, i.isLt]

theorem psum_succ (k : Fin n) (h : Fin n → ℝ) :
    psum (k + 1) h = psum k h + h k • Pi.single k 1 := by
  funext i
  simp only [psum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hik : i = k
  · subst hik; simp
  · have : (i : ℕ) ≠ k := fun h' => hik (Fin.ext h')
    rw [Pi.single_eq_of_ne hik, mul_zero, add_zero]
    by_cases hlt : (i : ℕ) < k
    · rw [if_pos (by omega), if_pos hlt]
    · rw [if_neg (by omega), if_neg hlt]

/-- The candidate derivative `h ↦ Σᵢ hᵢ vᵢ`. -/
def partialCLM (v : Fin n → F) : (Fin n → ℝ) →L[ℝ] F :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).smulRight (v i)

theorem partialCLM_apply (v : Fin n → F) (h : Fin n → ℝ) : partialCLM v h = ∑ i, h i • v i := by
  simp [partialCLM]

theorem continuous_partialCLM : Continuous (partialCLM (F := F) (n := n)) := by
  unfold partialCLM
  refine continuous_finset_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) F
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).continuous.comp
    (continuous_apply i)

/-- Derivative along a coordinate line at a shifted base point. -/
theorem hasDerivAt_line_shift {f : (Fin n → ℝ) → F} {g : (Fin n → ℝ) → F} {i : Fin n}
    {p : Fin n → ℝ} {s : ℝ}
    (hd : HasDerivAt (fun t : ℝ => f ((p + s • Pi.single i 1) + t • Pi.single i 1))
      (g (p + s • Pi.single i 1)) 0) :
    HasDerivAt (fun t : ℝ => f (p + t • Pi.single i 1)) (g (p + s • Pi.single i 1)) s := by
  have h1 : HasDerivAt (fun t : ℝ => f ((p + s • Pi.single i 1) + t • Pi.single i 1))
      (g (p + s • Pi.single i 1)) (s - s) := by rw [sub_self]; exact hd
  refine (h1.comp_sub_const s s).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  congr 1
  rw [add_assoc, ← add_smul, add_sub_cancel]

/-- **Continuous partial derivatives give the Fréchet derivative.** -/
theorem hasFDerivAt_of_partials {U : Set (Fin n → ℝ)} (hU : IsOpen U) {f : (Fin n → ℝ) → F}
    {g : Fin n → (Fin n → ℝ) → F} (hg : ∀ i, ContinuousOn (g i) U)
    (hd : ∀ i, ∀ x ∈ U, HasDerivAt (fun t : ℝ => f (x + t • Pi.single i 1)) (g i x) 0)
    {x : Fin n → ℝ} (hx : x ∈ U) : HasFDerivAt f (partialCLM fun i => g i x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  set ε' := ε / (n + 1)
  have hε' : 0 < ε' := by positivity
  have hcont : ∀ᶠ y in 𝓝 x, ∀ i, ‖g i y - g i x‖ < ε' := by
    refine eventually_all.mpr fun i => ?_
    have := ((hg i).continuousAt (hU.mem_nhds hx)).eventually
      (Metric.ball_mem_nhds (g i x) hε')
    filter_upwards [this] with y hy
    rwa [dist_eq_norm] at hy
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hcont.and (hU.mem_nhds hx))
  filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℝ) hδ] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  -- telescoping
  have htel : f (x + h) - f x = ∑ k : Fin n, (f (x + psum (k + 1) h) - f (x + psum k h)) := by
    have := Finset.sum_range_sub (fun k => f (x + psum k h)) n
    rw [psum_n, psum_zero, add_zero] at this
    rw [← this, ← Fin.sum_univ_eq_sum_range (fun k => f (x + psum (k + 1) h) - f (x + psum k h))]
  have hL : (partialCLM fun i => g i x) h = ∑ k : Fin n, h k • g k x := partialCLM_apply _ _
  rw [htel, hL, ← Finset.sum_sub_distrib]
  -- each term
  have hterm : ∀ k : Fin n, ‖f (x + psum (k + 1) h) - f (x + psum k h) - h k • g k x‖ ≤
      ε' * |h k| := by
    intro k
    set p := x + psum k h
    set φ : ℝ → F := fun s => f (p + s • Pi.single k 1) - s • g k x
    set S := uIcc (0 : ℝ) (h k)
    have hmem : ∀ s ∈ S, p + s • Pi.single k 1 ∈ Metric.ball x δ := by
      intro s hs
      rw [Metric.mem_ball, dist_eq_norm]
      have e1 : p + s • Pi.single k 1 - x = psum k h + s • Pi.single k 1 := by
        simp only [p]; abel
      rw [e1]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg h)).mpr fun i => ?_) hh
      have hs' : |s| ≤ |h k| := by
        rcases le_total 0 (h k) with hk | hk
        · have hs : s ∈ uIcc 0 (h k) := hs
          rw [uIcc_of_le hk] at hs
          rw [abs_of_nonneg hs.1, abs_of_nonneg hk]; exact hs.2
        · have hs : s ∈ uIcc 0 (h k) := hs
          rw [uIcc_of_ge hk] at hs
          rw [abs_of_nonpos hs.2, abs_of_nonpos hk]; linarith [hs.1]
      simp only [psum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hik : i = k
      · subst hik; simp only [lt_irrefl, if_false, Pi.single_eq_same, mul_one, zero_add,
          Real.norm_eq_abs]
        exact hs'.trans (norm_le_pi_norm h i)
      · rw [Pi.single_eq_of_ne hik, mul_zero, add_zero]
        split_ifs
        · exact norm_le_pi_norm h i
        · simp
    have hder : ∀ s ∈ S, HasDerivWithinAt φ (g k (p + s • Pi.single k 1) - g k x) S s := by
      intro s hs
      have hy := (hball _ (hmem s hs)).2
      have h1 := hasDerivAt_line_shift (hd k _ hy)
      exact (h1.sub ((hasDerivAt_id s).smul_const (g k x) |>.congr_deriv (by simp))).hasDerivWithinAt
    have hbound : ∀ s ∈ S, ‖g k (p + s • Pi.single k 1) - g k x‖ ≤ ε' := fun s hs =>
      ((hball _ (hmem s hs)).1 k).le
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_uIcc 0 (h k))
      left_mem_uIcc right_mem_uIcc
    have e2 : x + psum (k + 1) h = p + h k • Pi.single k 1 := by
      rw [psum_succ]; simp only [p]; abel
    rw [e2]
    have e3 : φ (h k) - φ 0 = f (p + h k • Pi.single k 1) - f p - h k • g k x := by
      simp only [φ, zero_smul, add_zero, sub_zero]; abel
    rw [← e3]
    simpa [Real.norm_eq_abs] using hmv
  calc ‖∑ k : Fin n, (f (x + psum (k + 1) h) - f (x + psum k h) - h k • g k x)‖
      ≤ ∑ k : Fin n, ε' * |h k| := (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hterm k)
    _ ≤ ∑ _k : Fin n, ε' * ‖h‖ := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm h k) hε'.le
    _ = n * ε' * ‖h‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact (mul_assoc _ _ _).symm
    _ ≤ ε * ‖h‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simp only [ε']
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **Continuous partial derivatives imply `C¹`.** -/
theorem contDiffOn_one_of_partials {U : Set (Fin n → ℝ)} (hU : IsOpen U) {f : (Fin n → ℝ) → F}
    {g : Fin n → (Fin n → ℝ) → F} (hg : ∀ i, ContinuousOn (g i) U)
    (hd : ∀ i, ∀ x ∈ U, HasDerivAt (fun t : ℝ => f (x + t • Pi.single i 1)) (g i x) 0) :
    ContDiffOn ℝ 1 f U := by
  have hf := fun x (hx : x ∈ U) => hasFDerivAt_of_partials hU hg hd hx
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  have hc : ContinuousOn (fun x => partialCLM fun i => g i x) U :=
    continuous_partialCLM.comp_continuousOn (continuousOn_pi.mpr hg)
  exact hc.congr fun x hx => (hf x hx).fderiv

/-- **Partial derivatives that are themselves `C¹` give `C²`.** -/
theorem contDiffOn_two_of_partials {U : Set (Fin n → ℝ)} (hU : IsOpen U) {f : (Fin n → ℝ) → F}
    {g : Fin n → (Fin n → ℝ) → F} (hg : ∀ i, ContDiffOn ℝ 1 (g i) U)
    (hd : ∀ i, ∀ x ∈ U, HasDerivAt (fun t : ℝ => f (x + t • Pi.single i 1)) (g i x) 0) :
    ContDiffOn ℝ 2 f U := by
  have hf := fun x (hx : x ∈ U) =>
    hasFDerivAt_of_partials hU (fun i => (hg i).continuousOn) hd hx
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have hc : ContDiffOn ℝ 1 (fun x => partialCLM fun i => g i x) U := by
    unfold partialCLM
    refine ContDiffOn.sum fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) F
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).contDiff.comp_contDiffOn
      (hg i)
  exact hc.congr fun x hx => (hf x hx).fderiv

end RenewalGeometry.PartialC1
