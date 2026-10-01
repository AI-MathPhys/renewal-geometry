/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One-dimensional Sobolev bounds in time (scalar form)

Infrastructure for `lem:supp-law-cost-control` (emergent-spacetime manuscript): the
one-dimensional Sobolev estimate `sup_t ‖f(t)‖ ≤ C_T (‖f‖_{L²_t} + ‖∂_t f‖_{L²_t})` for a
Hilbert-seminorm-valued path, reduced to a scalar statement about `φ = ‖f‖²`.

* `sup_le_of_abs_deriv_le`: if `φ ≥ 0` is differentiable on `[0, T]` (`T > 0`) with
  `|φ'| ≤ 2 √φ b` for a continuous `b`, then for every `t ∈ [0, T]`
  `φ(t) ≤ (T⁻¹ + 1) ∫_0^T φ + ∫_0^T b²`.  (Proof: `|φ'| ≤ φ + b²`, so `φ ± ∫_0^· (φ + b²)` is
  monotone; compare with a minimum point `t₀` of `φ`, where `T φ(t₀) ≤ ∫_0^T φ`.)
* `sqrt_sup_le_of_abs_deriv_le`: the square-root form
  `√φ(t) ≤ √(T⁻¹ + 1) (∫_0^T φ)^{1/2} + (∫_0^T b²)^{1/2}`.
* `integral_le_of_integral_sq_le`: the elementary `L¹ ≤ L²` bound on a bounded interval,
  `∫_0^t g ≤ M (1 + t) / 2` whenever `g` is continuous and `∫_0^t g² ≤ M²`.
-/

open Set MeasureTheory intervalIntegral

namespace RenewalGeometry.TimeSobolev

noncomputable section

/-- **One-dimensional Sobolev bound (scalar form).**  Let `T > 0`, `φ ≥ 0` differentiable on
`[0, T]` and `b` continuous on `[0, T]` with `|φ'| ≤ 2 √φ b`.  Then for every `t ∈ [0, T]`,
`φ(t) ≤ (T⁻¹ + 1) ∫_0^T φ + ∫_0^T b²`. -/
theorem sup_le_of_abs_deriv_le {φ φ' b : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (φ' t) t) (hφ0 : ∀ t ∈ Icc 0 T, 0 ≤ φ t)
    (hbd : ∀ t ∈ Icc 0 T, |φ' t| ≤ 2 * Real.sqrt (φ t) * b t)
    (hb : ContinuousOn b (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, φ t ≤ (T⁻¹ + 1) * (∫ τ in (0)..T, φ τ) + ∫ τ in (0)..T, b τ ^ 2 := by
  have hφc : ContinuousOn φ (Icc 0 T) := fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  set g : ℝ → ℝ := fun τ => φ τ + b τ ^ 2
  have hgc : ContinuousOn g (Icc 0 T) := hφc.add (hb.pow 2)
  have hg0 : ∀ τ ∈ Icc 0 T, 0 ≤ g τ := fun τ hτ => add_nonneg (hφ0 τ hτ) (sq_nonneg _)
  -- `|φ'| ≤ g`
  have hφg : ∀ τ ∈ Icc 0 T, |φ' τ| ≤ g τ := by
    intro τ hτ
    refine (hbd τ hτ).trans ?_
    have hs := Real.sq_sqrt (hφ0 τ hτ)
    have := sq_nonneg (Real.sqrt (φ τ) - b τ)
    simp only [g]
    nlinarith
  have hgi : ∀ u ∈ Icc 0 T, IntervalIntegrable g volume 0 u := fun u hu =>
    (hgc.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1
  set G : ℝ → ℝ := fun u => ∫ τ in (0)..u, g τ
  have hGc : ContinuousOn G (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := g) (a := 0)
      (b := T) (by rw [uIcc_of_le hT.le]; exact hgc.integrableOn_Icc)
    rwa [uIcc_of_le hT.le] at this
  have hGd : ∀ τ ∈ Ioo 0 T, HasDerivAt G (g τ) τ := fun τ hτ =>
    intervalIntegral.integral_hasDerivAt_right (hgi τ (Ioo_subset_Icc_self hτ))
      (hgc.mono Ioo_subset_Icc_self |>.stronglyMeasurableAtFilter isOpen_Ioo τ hτ)
      (hgc.continuousAt (Icc_mem_nhds hτ.1 hτ.2))
  -- `φ + G` is monotone and `φ - G` is antitone
  have hmono : MonotoneOn (fun u => φ u + G u) (Icc 0 T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) (hφc.add hGc) ?_ ?_
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact ((hφ τ (Ioo_subset_Icc_self hτ)).add (hGd τ hτ)).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      rw [((hφ τ (Ioo_subset_Icc_self hτ)).fun_add (hGd τ hτ)).deriv]
      have := neg_abs_le (φ' τ)
      have := hφg τ (Ioo_subset_Icc_self hτ)
      linarith
  have hanti : AntitoneOn (fun u => φ u - G u) (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (hφc.sub hGc) ?_ ?_
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact ((hφ τ (Ioo_subset_Icc_self hτ)).sub (hGd τ hτ)).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      rw [((hφ τ (Ioo_subset_Icc_self hτ)).fun_sub (hGd τ hτ)).deriv]
      have := le_abs_self (φ' τ)
      have := hφg τ (Ioo_subset_Icc_self hτ)
      linarith
  -- `G` is monotone, `0 ≤ G ≤ G T`
  have hGmono : ∀ u ∈ Icc 0 T, ∀ u' ∈ Icc 0 T, u ≤ u' → G u ≤ G u' := by
    intro u hu u' hu' huu'
    have e : G u' = G u + ∫ τ in u..u', g τ := by
      simp only [G]
      rw [intervalIntegral.integral_add_adjacent_intervals (hgi u hu)]
      exact (hgc.mono (Icc_subset_Icc hu.1 hu'.2)).intervalIntegrable_of_Icc huu'
    rw [e]
    have : 0 ≤ ∫ τ in u..u', g τ :=
      intervalIntegral.integral_nonneg huu' fun τ hτ => hg0 τ ⟨hu.1.trans hτ.1, hτ.2.trans hu'.2⟩
    linarith
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  -- a minimum point of `φ`
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT.le) hφc
  have hφi : IntervalIntegrable φ volume 0 T := hφc.intervalIntegrable_of_Icc hT.le
  have hbi : IntervalIntegrable (fun τ => b τ ^ 2) volume 0 T :=
    (hb.pow 2).intervalIntegrable_of_Icc hT.le
  have hmin_int : T * φ t₀ ≤ ∫ τ in (0)..T, φ τ := by
    have h := intervalIntegral.integral_mono_on hT.le intervalIntegrable_const hφi
      (fun τ hτ => (hmin hτ : φ t₀ ≤ φ τ))
    simpa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using h
  have hφt₀ : φ t₀ ≤ T⁻¹ * ∫ τ in (0)..T, φ τ := by
    rw [inv_mul_eq_div, le_div_iff₀ hT]; linarith
  have hGT : G T = (∫ τ in (0)..T, φ τ) + ∫ τ in (0)..T, b τ ^ 2 :=
    intervalIntegral.integral_add hφi hbi
  have hTmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  intro t ht
  have hφt : φ t ≤ φ t₀ + G T := by
    rcases le_total t₀ t with h | h
    · have h1 := hanti ht₀ ht h
      have h2 := hGmono t ht T hTmem ht.2
      have h3 := hGmono 0 h0mem t₀ ht₀ ht₀.1
      simp only at h1
      linarith
    · have h1 := hmono ht ht₀ h
      have h2 := hGmono t₀ ht₀ T hTmem ht₀.2
      have h3 := hGmono 0 h0mem t ht ht.1
      simp only at h1
      linarith
  rw [hGT] at hφt
  have : (T⁻¹ + 1) * (∫ τ in (0)..T, φ τ) = T⁻¹ * (∫ τ in (0)..T, φ τ) + ∫ τ in (0)..T, φ τ := by
    ring
  linarith

/-- **One-dimensional Sobolev bound, square-root form**:
`√φ(t) ≤ √(T⁻¹ + 1) · (∫_0^T φ)^{1/2} + (∫_0^T b²)^{1/2}`. -/
theorem sqrt_sup_le_of_abs_deriv_le {φ φ' b : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (φ' t) t) (hφ0 : ∀ t ∈ Icc 0 T, 0 ≤ φ t)
    (hbd : ∀ t ∈ Icc 0 T, |φ' t| ≤ 2 * Real.sqrt (φ t) * b t)
    (hb : ContinuousOn b (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, Real.sqrt (φ t) ≤ Real.sqrt (T⁻¹ + 1) * Real.sqrt (∫ τ in (0)..T, φ τ) +
      Real.sqrt (∫ τ in (0)..T, b τ ^ 2) := by
  intro t ht
  have h := sup_le_of_abs_deriv_le hT hφ hφ0 hbd hb t ht
  have hA : 0 ≤ ∫ τ in (0)..T, φ τ := intervalIntegral.integral_nonneg hT.le fun τ hτ => hφ0 τ hτ
  have hB : 0 ≤ ∫ τ in (0)..T, b τ ^ 2 := intervalIntegral.integral_nonneg hT.le fun τ _ =>
    sq_nonneg _
  have hc : 0 ≤ T⁻¹ + 1 := by positivity
  calc Real.sqrt (φ t) ≤ Real.sqrt ((T⁻¹ + 1) * (∫ τ in (0)..T, φ τ) + ∫ τ in (0)..T, b τ ^ 2) :=
        Real.sqrt_le_sqrt h
    _ ≤ Real.sqrt ((T⁻¹ + 1) * (∫ τ in (0)..T, φ τ)) + Real.sqrt (∫ τ in (0)..T, b τ ^ 2) := by
        rw [Real.sqrt_le_left (by positivity)]
        have h1 := Real.sq_sqrt (mul_nonneg hc hA)
        have h2 := Real.sq_sqrt hB
        have h3 := mul_nonneg (Real.sqrt_nonneg ((T⁻¹ + 1) * ∫ τ in (0)..T, φ τ))
          (Real.sqrt_nonneg (∫ τ in (0)..T, b τ ^ 2))
        nlinarith
    _ = _ := by rw [Real.sqrt_mul hc]

/-- **`L¹ ≤ L²` on a bounded interval** (elementary form): if `g` is continuous on `[0, t]`
and `∫_0^t g² ≤ M²` with `M ≥ 0`, then `∫_0^t g ≤ M (1 + t) / 2`. -/
theorem integral_le_of_integral_sq_le {g : ℝ → ℝ} {t M : ℝ} (ht : 0 ≤ t)
    (hg : ContinuousOn g (Icc 0 t))
    (hM0 : 0 ≤ M) (hM : ∫ τ in (0)..t, g τ ^ 2 ≤ M ^ 2) :
    ∫ τ in (0)..t, g τ ≤ M * (1 + t) / 2 := by
  have hgi : IntervalIntegrable g volume 0 t := hg.intervalIntegrable_of_Icc ht
  have hg2i : IntervalIntegrable (fun τ => g τ ^ 2) volume 0 t :=
    (hg.pow 2).intervalIntegrable_of_Icc ht
  -- for every `l > 0`
  have key : ∀ lam > 0, ∫ τ in (0)..t, g τ ≤ M ^ 2 / (2 * lam) + lam * t / 2 := by
    intro lam hlam
    have hpt : ∀ τ ∈ Icc 0 t, g τ ≤ g τ ^ 2 / (2 * lam) + lam / 2 := by
      intro τ _
      rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (g τ - lam)]
    have h1 := intervalIntegral.integral_mono_on ht hgi
      ((hg2i.div_const (2 * lam)).add intervalIntegrable_const) hpt
    rw [intervalIntegral.integral_add (hg2i.div_const _) intervalIntegrable_const,
      intervalIntegral.integral_div, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    have h2 : (∫ τ in (0)..t, g τ ^ 2) / (2 * lam) ≤ M ^ 2 / (2 * lam) :=
      div_le_div_of_nonneg_right hM (by positivity)
    linarith
  by_contra hcon
  push Not at hcon
  set I := ∫ τ in (0)..t, g τ
  -- choose the parameter `M + η` with `η > 0` small
  set η : ℝ := (I - M * (1 + t) / 2) / (1 + t)
  have hη : 0 < η := div_pos (by linarith) (by linarith)
  have h := key (M + η) (by linarith)
  have h1 : M ^ 2 / (2 * (M + η)) ≤ (M + η) / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : (M + η) / 2 + (M + η) * t / 2 = M * (1 + t) / 2 + η * (1 + t) / 2 := by ring
  have h3 : η * (1 + t) = I - M * (1 + t) / 2 := by
    simp only [η]; field_simp
  nlinarith

end

end RenewalGeometry.TimeSobolev
