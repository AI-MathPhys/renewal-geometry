/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CWGap
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Deriv

/-!
# The exact Curie–Weiss orientation phase diagram

Covers `thm:cw-phase-diagram` from `manuscripts/renewal_emergence/renewal_emergence.tex`: the binary
entropy `s(m)`, the orientation pressure
`Ψ_{λ,h}(m) = s(m) + λm²/2 + hm`, its derivative
`Ψ' = λm + h − artanh m` on `(-1,1)`, and

* (i) for `0 ≤ λ ≤ 1` the unique maximizer of `Ψ_{λ,0}` on `[-1,1]`
  is `m = 0`;
* (ii) for `λ > 1` the global maximizers are exactly `{-m⋆, m⋆}`
  where `m⋆` is the unique positive root of `m = tanh(λm)`;
* for `h ≠ 0` the global maximizer is unique, has the sign of `h`,
  lies in the open unit interval, and satisfies
  `m = tanh(λm + h)` (uniqueness via strict convexity of
  `artanh m − λm` on the positive axis);
* the maximizers converge to `±m⋆` as `h → 0±` (supercritical).
-/

namespace NCG.Upstream

open Real Set Filter

/-! ## Entropy and pressure -/

/-- The binary orientation entropy `s(m)`. -/
noncomputable def cwEntropy (m : ℝ) : ℝ :=
  Real.negMulLog ((1 + m) / 2) + Real.negMulLog ((1 - m) / 2)

/-- The orientation pressure functional `Ψ_{λ,h}`. -/
noncomputable def cwPressure (lam h m : ℝ) : ℝ :=
  cwEntropy m + lam / 2 * m ^ 2 + h * m

theorem cwEntropy_even (m : ℝ) : cwEntropy (-m) = cwEntropy m := by
  unfold cwEntropy
  rw [show (1 + -m) / 2 = (1 - m) / 2 from by ring,
    show (1 - -m) / 2 = (1 + m) / 2 from by ring]
  ring

theorem cwPressure_even (lam m : ℝ) :
    cwPressure lam 0 (-m) = cwPressure lam 0 m := by
  unfold cwPressure
  rw [cwEntropy_even]
  ring

/-- Reflection identity: `Ψ_{λ,h}(-m) = Ψ_{λ,h}(m) - 2hm`. -/
theorem cwPressure_reflect (lam h m : ℝ) :
    cwPressure lam h (-m) = cwPressure lam h m - 2 * h * m := by
  unfold cwPressure
  rw [cwEntropy_even]
  ring

theorem cwPressure_neg_field (lam h m : ℝ) :
    cwPressure lam (-h) (-m) = cwPressure lam h m := by
  unfold cwPressure
  rw [cwEntropy_even]
  ring

theorem continuous_cwPressure (lam h : ℝ) :
    Continuous (cwPressure lam h) := by
  unfold cwPressure cwEntropy
  fun_prop

/-! ## The derivative `Ψ' = λm + h − artanh m` -/

theorem cwEntropy_hasDerivAt {m : ℝ} (hm : m ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt cwEntropy (-Real.artanh m) m := by
  have hp : (0 : ℝ) < (1 + m) / 2 := by
    have := hm.1
    linarith
  have hq : (0 : ℝ) < (1 - m) / 2 := by
    have := hm.2
    linarith
  have h1 : HasDerivAt (fun x : ℝ => (1 + x) / 2) (1 / 2) m := by
    have := ((hasDerivAt_id m).const_add (1 : ℝ)).div_const (2 : ℝ)
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) / 2) (-(1 / 2)) m := by
    have h := ((hasDerivAt_id m).const_sub (1 : ℝ)).div_const (2 : ℝ)
    have he : (-1 : ℝ) / 2 = -(1 / 2) := by norm_num
    rw [he] at h
    exact h
  have H1 : HasDerivAt (fun x : ℝ => Real.negMulLog ((1 + x) / 2))
      ((-Real.log ((1 + m) / 2) - 1) * (1 / 2)) m := by
    exact HasDerivAt.comp m
      (Real.hasDerivAt_negMulLog (x := (1 + m) / 2) hp.ne') h1
  have H2 : HasDerivAt (fun x : ℝ => Real.negMulLog ((1 - x) / 2))
      ((-Real.log ((1 - m) / 2) - 1) * (-(1 / 2))) m := by
    exact HasDerivAt.comp m
      (Real.hasDerivAt_negMulLog (x := (1 - m) / 2) hq.ne') h2
  have H := H1.add H2
  have hval : (-Real.log ((1 + m) / 2) - 1) * (1 / 2)
      + (-Real.log ((1 - m) / 2) - 1) * (-(1 / 2))
      = -Real.artanh m := by
    rw [Real.artanh_eq_half_log ⟨hm.1.le, hm.2.le⟩]
    have harg : (1 + m) / (1 - m) = ((1 + m) / 2) / ((1 - m) / 2) := by
      rw [div_div_div_cancel_right₀]
      exact two_ne_zero
    rw [harg, Real.log_div hp.ne' hq.ne']
    ring
  rw [hval] at H
  exact H

theorem cwPressure_hasDerivAt (lam h : ℝ) {m : ℝ}
    (hm : m ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (cwPressure lam h)
      (lam * m + h - Real.artanh m) m := by
  have Hq : HasDerivAt (fun x : ℝ => lam / 2 * x ^ 2)
      (lam / 2 * (2 * m)) m := by
    have := (hasDerivAt_pow 2 m).const_mul (lam / 2)
    simpa using this
  have Hl : HasDerivAt (fun x : ℝ => h * x) h m := by
    have := (hasDerivAt_id m).const_mul h
    simpa using this
  have H := ((cwEntropy_hasDerivAt hm).add Hq).add Hl
  have hval : -Real.artanh m + lam / 2 * (2 * m) + h
      = lam * m + h - Real.artanh m := by ring
  rw [hval] at H
  exact H

/-! ## Comparison inequalities from the gap module -/

theorem lt_artanh {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    m < Real.artanh m := by
  have h1 : 0 < Real.artanh m := Real.artanh_pos hm
  have h2 := tanh_lt_self h1
  rwa [Real.tanh_artanh ⟨by linarith [hm.1], hm.2⟩] at h2

/-- Below the oriented root: `artanh m < λm`. -/
theorem artanh_lt_mul_of_lt_root {lam mstar : ℝ} (_hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m : ℝ}
    (hm : m ∈ Ioo (0 : ℝ) mstar) : Real.artanh m < lam * m := by
  have hm1 : m < 1 := lt_trans hm.2 hmstar.2
  have hmm : m ∈ Ioo (0 : ℝ) 1 := ⟨hm.1, hm1⟩
  have hy : 0 < Real.artanh m := Real.artanh_pos hmm
  have hystar : Real.artanh m < Real.artanh mstar :=
    Real.artanh_lt_artanh (by linarith [hm.1]) hmstar.2 hm.2
  have hc := comparison_strictMonoOn (mem_Ioi.mpr hy)
    (mem_Ioi.mpr (lt_trans hy hystar)) hystar
  simp only at hc
  rw [comparison_at_fix hmstar hfix] at hc
  have hmm' : m ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hm.1], hm1⟩
  have htan : Real.tanh (Real.artanh m) = m := Real.tanh_artanh hmm'
  have hcp := Real.cosh_pos (Real.artanh m)
  have hsinh : Real.sinh (Real.artanh m)
      = m * Real.cosh (Real.artanh m) := by
    have h1 := Real.tanh_eq_sinh_div_cosh (Real.artanh m)
    rw [htan] at h1
    field_simp at h1
    linarith [h1]
  rw [hsinh] at hc
  rw [div_lt_iff₀ (mul_pos hm.1 hcp)] at hc
  nlinarith [hcp]

/-- Above the oriented root: `λm < artanh m`. -/
theorem mul_lt_artanh_of_root_lt {lam mstar : ℝ} (_hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m : ℝ}
    (hm : m ∈ Ioo mstar (1 : ℝ)) : lam * m < Real.artanh m := by
  have hm0 : 0 < m := lt_trans hmstar.1 hm.1
  have hystar : Real.artanh mstar < Real.artanh m :=
    Real.artanh_lt_artanh (by linarith [hmstar.1]) hm.2 hm.1
  have hy : 0 < Real.artanh mstar := Real.artanh_pos hmstar
  have hc := comparison_strictMonoOn (mem_Ioi.mpr hy)
    (mem_Ioi.mpr (lt_trans hy hystar)) hystar
  simp only at hc
  rw [comparison_at_fix hmstar hfix] at hc
  have hmm' : m ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hm.2⟩
  have htan : Real.tanh (Real.artanh m) = m := Real.tanh_artanh hmm'
  have hcp := Real.cosh_pos (Real.artanh m)
  have hsinh : Real.sinh (Real.artanh m)
      = m * Real.cosh (Real.artanh m) := by
    have h1 := Real.tanh_eq_sinh_div_cosh (Real.artanh m)
    rw [htan] at h1
    field_simp at h1
    linarith [h1]
  rw [hsinh] at hc
  rw [lt_div_iff₀ (mul_pos hm0 hcp)] at hc
  nlinarith [hcp]

/-! ## Zero field, part (i): subcritical unique maximizer -/

/-- **Theorem `thm:cw-phase-diagram` (i)**: for `0 ≤ λ ≤ 1` the
pressure has its unique maximum on `[-1,1]` at the unoriented point. -/
theorem cw_phase_subcritical {lam : ℝ} (_hlam0 : 0 ≤ lam)
    (hlam : lam ≤ 1) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (hne : m ≠ 0) :
    cwPressure lam 0 m < cwPressure lam 0 0 := by
  have hanti : StrictAntiOn (cwPressure lam 0) (Icc 0 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuous_cwPressure lam 0).continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(cwPressure_hasDerivAt lam 0
      ⟨by linarith [hx.1], hx.2⟩).deriv]
    have h1 := lt_artanh ⟨hx.1, hx.2⟩
    nlinarith [hx.1]
  have key : ∀ m' ∈ Ioc (0 : ℝ) 1,
      cwPressure lam 0 m' < cwPressure lam 0 0 := by
    intro m' hm'
    exact hanti ⟨le_refl 0, zero_le_one⟩ ⟨hm'.1.le, hm'.2⟩ hm'.1
  rcases lt_trichotomy m 0 with hneg | h0 | hpos
  · have h2 := key (-m) ⟨by linarith, by linarith [hm.1]⟩
    rwa [cwPressure_even] at h2
  · exact absurd h0 hne
  · exact key m ⟨hpos, hm.2⟩

/-! ## Zero field, part (ii): supercritical maximizers `±m⋆` -/

section Supercritical

variable {lam mstar : ℝ}

theorem cw_mono_below (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) :
    StrictMonoOn (cwPressure lam 0) (Icc 0 mstar) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_cwPressure lam 0).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(cwPressure_hasDerivAt lam 0
    ⟨by linarith [hx.1], by linarith [hx.2, hmstar.2]⟩).deriv]
  have := artanh_lt_mul_of_lt_root hlam hmstar hfix ⟨hx.1, hx.2⟩
  linarith

theorem cw_anti_above (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) :
    StrictAntiOn (cwPressure lam 0) (Icc mstar 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_cwPressure lam 0).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(cwPressure_hasDerivAt lam 0
    ⟨by linarith [hx.1, hmstar.1], hx.2⟩).deriv]
  have := mul_lt_artanh_of_root_lt hlam hmstar hfix ⟨hx.1, hx.2⟩
  linarith

/-- **Theorem `thm:cw-phase-diagram` (ii), maximality**: the
oriented roots dominate the pressure. -/
theorem cw_phase_supercritical_le (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) :
    cwPressure lam 0 m ≤ cwPressure lam 0 mstar := by
  have key : ∀ m' ∈ Icc (0 : ℝ) 1,
      cwPressure lam 0 m' ≤ cwPressure lam 0 mstar := by
    intro m' hm'
    rcases le_total m' mstar with hle | hge
    · rcases eq_or_lt_of_le hle with heq | hlt
      · rw [heq]
      · exact (cw_mono_below hlam hmstar hfix ⟨hm'.1, hle⟩
          ⟨hmstar.1.le, le_refl mstar⟩ hlt).le
    · rcases eq_or_lt_of_le hge with heq | hlt
      · rw [← heq]
      · exact (cw_anti_above hlam hmstar hfix
          ⟨le_refl _, hmstar.2.le⟩ ⟨hge, hm'.2⟩ hlt).le
  rcases le_total 0 m with hpos | hneg
  · exact key m ⟨hpos, hm.2⟩
  · have h2 := key (-m) ⟨by linarith, by linarith [hm.1]⟩
    rwa [cwPressure_even] at h2

/-- **Theorem `thm:cw-phase-diagram` (ii), exactness**: equality
holds only at the two oriented roots. -/
theorem cw_phase_supercritical_eq_iff (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) :
    cwPressure lam 0 m = cwPressure lam 0 mstar
      ↔ m = mstar ∨ m = -mstar := by
  constructor
  · intro heq
    have key : ∀ m' ∈ Icc (0 : ℝ) 1, m' ≠ mstar →
        cwPressure lam 0 m' < cwPressure lam 0 mstar := by
      intro m' hm' hne
      rcases lt_trichotomy m' mstar with hlt | he | hgt
      · exact cw_mono_below hlam hmstar hfix ⟨hm'.1, hlt.le⟩
          ⟨hmstar.1.le, le_refl mstar⟩ hlt
      · exact absurd he hne
      · exact cw_anti_above hlam hmstar hfix
          ⟨le_refl _, hmstar.2.le⟩ ⟨hgt.le, hm'.2⟩ hgt
    rcases le_total 0 m with hpos | hneg
    · left
      by_contra hne
      exact absurd heq (ne_of_lt (key m ⟨hpos, hm.2⟩ hne))
    · right
      by_contra hne
      have hne' : -m ≠ mstar := fun hc => hne (by linarith [hc])
      have h2 := key (-m) ⟨by linarith, by linarith [hm.1]⟩ hne'
      rw [cwPressure_even] at h2
      exact absurd heq (ne_of_lt h2)
  · rintro (rfl | rfl)
    · rfl
    · exact cwPressure_even lam mstar

end Supercritical

/-! ## Differentiability of `artanh` and strict convexity of the
gap defect -/

theorem continuousOn_artanh :
    ContinuousOn Real.artanh (Ioo (-1 : ℝ) 1) := by
  have hsub : ∀ m ∈ Ioo (-1 : ℝ) 1,
      Real.artanh m = 1 / 2 * Real.log ((1 + m) / (1 - m)) :=
    fun m hm => Real.artanh_eq_half_log ⟨hm.1.le, hm.2.le⟩
  refine ContinuousOn.congr ?_ hsub
  refine ContinuousOn.mul continuousOn_const ?_
  refine ContinuousOn.log ?_ ?_
  · refine ContinuousOn.div
      ((continuous_const.add continuous_id).continuousOn)
      ((continuous_const.sub continuous_id).continuousOn) ?_
    intro m hm
    have h9 : m < 1 := hm.2
    intro hc
    have h10 := sub_eq_zero.mp hc
    linarith
  · intro m hm
    have : (0 : ℝ) < (1 + m) / (1 - m) :=
      div_pos (by linarith [hm.1]) (by linarith [hm.2])
    exact this.ne'

theorem tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc := Real.cosh_pos x
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    hc.ne'
  have heq : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  have hval : (Real.cosh x * Real.cosh x
      - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2
      = 1 / Real.cosh x ^ 2 := by
    have h2 := Real.cosh_sq_sub_sinh_sq x
    congr 1
    nlinarith
  rw [hval] at h
  exact h

theorem artanh_hasDerivAt {m : ℝ} (hm : m ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - m ^ 2)) m := by
  have hcont : ContinuousAt Real.artanh m :=
    continuousOn_artanh.continuousAt (Ioo_mem_nhds hm.1 hm.2)
  have hd := tanh_hasDerivAt (Real.artanh m)
  have hcp := Real.cosh_pos (Real.artanh m)
  have hne : (1 : ℝ) / Real.cosh (Real.artanh m) ^ 2 ≠ 0 := by
    positivity
  have hfg : ∀ᶠ y in nhds m, Real.tanh (Real.artanh y) = y := by
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with y hy
    exact Real.tanh_artanh hy
  have H := HasDerivAt.of_local_left_inverse hcont hd hne hfg
  have h1m : (0 : ℝ) < 1 - m ^ 2 := by nlinarith [hm.1, hm.2]
  have hval : (1 / Real.cosh (Real.artanh m) ^ 2)⁻¹
      = 1 / (1 - m ^ 2) := by
    rw [Real.cosh_artanh hm, div_pow, one_pow,
      Real.sq_sqrt h1m.le, one_div_one_div, one_div]
  rw [hval] at H
  exact H

/-- The gap defect `ψ(m) = artanh m − λm`. -/
noncomputable def gapDefect (lam m : ℝ) : ℝ := Real.artanh m - lam * m

theorem gapDefect_hasDerivAt (lam : ℝ) {m : ℝ}
    (hm : m ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (gapDefect lam) (1 / (1 - m ^ 2) - lam) m := by
  have Hl : HasDerivAt (fun x : ℝ => lam * x) lam m := by
    have h := (hasDerivAt_id m).const_mul lam
    simpa using h
  exact (artanh_hasDerivAt hm).sub Hl

theorem continuousOn_gapDefect (lam : ℝ) {a b : ℝ} (ha : -1 < a)
    (hb : b < 1) : ContinuousOn (gapDefect lam) (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · have hsub : Icc a b ⊆ Ioo (-1 : ℝ) 1 := fun x hx =>
      ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    exact ((continuousOn_artanh.sub
      ((continuous_const.mul continuous_id).continuousOn)).mono hsub)
  · rw [Icc_eq_empty (not_le.mpr hab)]
    exact continuousOn_empty _

/-- The gap defect is strictly convex on any `[0, b] ⊂ [0, 1)`. -/
theorem gapDefect_strictConvexOn (lam : ℝ) {b : ℝ} (_hb0 : 0 ≤ b)
    (hb : b < 1) :
    StrictConvexOn ℝ (Icc (0 : ℝ) b) (gapDefect lam) := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _)
    (continuousOn_gapDefect lam (by norm_num) hb) ?_
  rw [interior_Icc]
  intro x hx y hy hxy
  have hxm : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hx.1], lt_trans hx.2 hb⟩
  have hym : y ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hy.1], lt_trans hy.2 hb⟩
  rw [(gapDefect_hasDerivAt lam hxm).deriv,
    (gapDefect_hasDerivAt lam hym).deriv]
  have h1x : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hxm.1, hxm.2]
  have h1y : (0 : ℝ) < 1 - y ^ 2 := by nlinarith [hym.1, hym.2]
  have hsq : x ^ 2 < y ^ 2 := by nlinarith [hx.1, hy.1]
  have := one_div_lt_one_div_of_lt h1y (by linarith : 1 - y ^ 2 < 1 - x ^ 2)
  linarith

/-! ## The field case `h ≠ 0`: unique signed maximizer -/

section Field

variable {lam h : ℝ}

/-- Any global maximizer at positive field is strictly positive,
interior, and solves the mean-field equation. -/
theorem cw_field_max_properties (hlam0 : 0 ≤ lam) (hh : 0 < h)
    {m₀ : ℝ} (hm₀ : m₀ ∈ Icc (-1 : ℝ) 1)
    (hmax : IsMaxOn (cwPressure lam h) (Icc (-1 : ℝ) 1) m₀) :
    0 < m₀ ∧ m₀ < 1
      ∧ Real.tanh (lam * m₀ + h) = m₀
      ∧ gapDefect lam m₀ = h := by
  -- not negative
  have hnonneg : 0 ≤ m₀ := by
    by_contra hneg
    push Not at hneg
    have h1 := hmax (show -m₀ ∈ Icc (-1 : ℝ) 1 from
      ⟨by linarith [hm₀.2], by linarith [hm₀.1]⟩)
    simp only [Set.mem_setOf_eq] at h1
    rw [cwPressure_reflect] at h1
    nlinarith [h1]
  -- not zero: Ψ increases on [0, tanh (h/2)]
  set a : ℝ := Real.tanh (h / 2) with ha_def
  have ha0 : 0 < a := by
    rw [ha_def, ← Real.tanh_zero]
    exact tanh_strictMono (by linarith)
  have ha1 : a < 1 := Real.tanh_lt_one _
  have hart_a : Real.artanh a = h / 2 := Real.artanh_tanh _
  have hmono0 : StrictMonoOn (cwPressure lam h) (Icc 0 a) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (continuous_cwPressure lam h).continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    have hxm : x ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1], lt_trans hx.2 ha1⟩
    rw [(cwPressure_hasDerivAt lam h hxm).deriv]
    have hart_lt : Real.artanh x < h / 2 := by
      rw [← hart_a]
      exact Real.artanh_lt_artanh (by linarith [hx.1]) ha1 hx.2
    nlinarith [hx.1, hlam0]
  have hne0 : m₀ ≠ 0 := by
    intro hzero
    have h2 := hmax (show a ∈ Icc (-1 : ℝ) 1 from
      ⟨by linarith, ha1.le⟩)
    have h3 := hmono0 ⟨le_refl 0, ha0.le⟩ ⟨ha0.le, le_refl a⟩ ha0
    rw [← hzero] at h3
    simp only [Set.mem_setOf_eq] at h2
    linarith [h2, h3]
  have hpos : 0 < m₀ := lt_of_le_of_ne hnonneg (Ne.symm hne0)
  -- not the right endpoint: Ψ decreases on [tanh(λ+h), 1]
  set b : ℝ := Real.tanh (lam + h) with hb_def
  have hb0 : 0 < b := by
    rw [hb_def, ← Real.tanh_zero]
    exact tanh_strictMono (by linarith)
  have hb1 : b < 1 := Real.tanh_lt_one _
  have hart_b : Real.artanh b = lam + h := Real.artanh_tanh _
  have hanti1 : StrictAntiOn (cwPressure lam h) (Icc b 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuous_cwPressure lam h).continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    have hxm : x ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1, hb0], hx.2⟩
    rw [(cwPressure_hasDerivAt lam h hxm).deriv]
    have hart_gt : lam + h < Real.artanh x := by
      rw [← hart_b]
      exact Real.artanh_lt_artanh (by linarith [hb0]) hx.2 hx.1
    nlinarith [hx.2, hlam0, hxm.1]
  have hne1 : m₀ ≠ 1 := by
    intro hone
    have h2 := hmax (show b ∈ Icc (-1 : ℝ) 1 from
      ⟨by linarith, hb1.le⟩)
    have h3 := hanti1 ⟨le_refl b, hb1.le⟩ ⟨hb1.le, le_refl 1⟩ hb1
    rw [← hone] at h3
    simp only [Set.mem_setOf_eq] at h2
    linarith [h2, h3]
  have hlt1 : m₀ < 1 := lt_of_le_of_ne hm₀.2 hne1
  -- interior maximum: critical point
  have hloc : IsLocalMax (cwPressure lam h) m₀ :=
    hmax.isLocalMax (Icc_mem_nhds (by linarith) hlt1)
  have hcrit := hloc.hasDerivAt_eq_zero
    (cwPressure_hasDerivAt lam h ⟨by linarith, hlt1⟩)
  have hgap : gapDefect lam m₀ = h := by
    unfold gapDefect
    linarith [hcrit]
  refine ⟨hpos, hlt1, ?_, hgap⟩
  have hart : Real.artanh m₀ = lam * m₀ + h := by
    unfold gapDefect at hgap
    linarith
  rw [← hart, Real.tanh_artanh ⟨by linarith, hlt1⟩]

/-- **Theorem `thm:cw-phase-diagram` (field case)**: at `h > 0` the
global maximizer is unique. -/
theorem cw_field_max_unique (hlam0 : 0 ≤ lam) (hh : 0 < h)
    {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Icc (-1 : ℝ) 1)
    (hm₂ : m₂ ∈ Icc (-1 : ℝ) 1)
    (hmax₁ : IsMaxOn (cwPressure lam h) (Icc (-1 : ℝ) 1) m₁)
    (hmax₂ : IsMaxOn (cwPressure lam h) (Icc (-1 : ℝ) 1) m₂) :
    m₁ = m₂ := by
  by_contra hne
  wlog hlt : m₁ < m₂ generalizing m₁ m₂
  · exact this hm₂ hm₁ hmax₂ hmax₁ (Ne.symm hne)
      (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  obtain ⟨hp₁, hl₁, -, hg₁⟩ :=
    cw_field_max_properties hlam0 hh hm₁ hmax₁
  obtain ⟨hp₂, hl₂, -, hg₂⟩ :=
    cw_field_max_properties hlam0 hh hm₂ hmax₂
  -- strict convexity of the gap defect on [0, m₂] forces ψ < h
  -- strictly between the two critical values
  have hconv := gapDefect_strictConvexOn lam
    (b := m₂) hp₂.le hl₂
  have hbetween : ∀ x ∈ Ioo m₁ m₂, gapDefect lam x < h := by
    intro x hx
    set t : ℝ := (m₂ - x) / (m₂ - m₁) with ht_def
    have hd : (0 : ℝ) < m₂ - m₁ := by linarith
    have ht0 : 0 < t := div_pos (by linarith [hx.2]) hd
    have ht1 : t < 1 := by
      rw [ht_def, div_lt_one hd]
      linarith [hx.1]
    have hsum : t + (1 - t) = 1 := by ring
    have hxrep : t * m₁ + (1 - t) * m₂ = x := by
      rw [ht_def]
      field_simp
      ring
    have hcc := hconv.2 (show m₁ ∈ Icc (0 : ℝ) m₂ from
        ⟨hp₁.le, hlt.le⟩)
      (show m₂ ∈ Icc (0 : ℝ) m₂ from ⟨hp₂.le, le_refl _⟩)
      (by intro hc; exact absurd hc (by linarith [hlt]))
      ht0 (by linarith) hsum
    simp only [smul_eq_mul] at hcc
    rw [hxrep, hg₁, hg₂] at hcc
    calc gapDefect lam x < t * h + (1 - t) * h := hcc
      _ = h := by ring
  -- so the pressure increases strictly on [m₁, m₂]
  have hmono : StrictMonoOn (cwPressure lam h) (Icc m₁ m₂) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (continuous_cwPressure lam h).continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    have hxm : x ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1, hp₁], lt_trans hx.2 hl₂⟩
    rw [(cwPressure_hasDerivAt lam h hxm).deriv]
    have := hbetween x hx
    unfold gapDefect at this
    linarith
  have h5 := hmono ⟨le_refl m₁, hlt.le⟩ ⟨hlt.le, le_refl m₂⟩ hlt
  have h6 := hmax₁ hm₂
  simp only [Set.mem_setOf_eq] at h6
  linarith [h5, h6]

/-- Existence of a global maximizer. -/
theorem cw_max_exists (lam h : ℝ) :
    ∃ m₀ ∈ Icc (-1 : ℝ) 1,
      IsMaxOn (cwPressure lam h) (Icc (-1 : ℝ) 1) m₀ :=
  isCompact_Icc.exists_isMaxOn ⟨0, by norm_num⟩
    (continuous_cwPressure lam h).continuousOn

/-- **Theorem `thm:cw-phase-diagram` (field case, packaged)**: for
`h > 0` there is a unique global maximizer; it is strictly positive,
interior, and solves `m = tanh(λm + h)`. -/
theorem cw_phase_field (hlam0 : 0 ≤ lam) (hh : 0 < h) :
    ∃! m₀ : ℝ, m₀ ∈ Icc (-1 : ℝ) 1
      ∧ IsMaxOn (cwPressure lam h) (Icc (-1 : ℝ) 1) m₀ := by
  obtain ⟨m₀, hm₀, hmax⟩ := cw_max_exists lam h
  refine ⟨m₀, ⟨hm₀, hmax⟩, ?_⟩
  rintro m₁ ⟨hm₁, hmax₁⟩
  exact cw_field_max_unique hlam0 hh hm₁ hm₀ hmax₁ hmax

/-- Negative field by reflection: maximizers at `-h` are exactly the
negatives of maximizers at `h`. -/
theorem cw_field_reflect (lam h : ℝ) {m₀ : ℝ}
    (_hm₀ : m₀ ∈ Icc (-1 : ℝ) 1)
    (hmax : IsMaxOn (cwPressure lam h) (Icc (-1 : ℝ) 1) m₀) :
    IsMaxOn (cwPressure lam (-h)) (Icc (-1 : ℝ) 1) (-m₀) := by
  intro x hx
  have h1 := hmax (show -x ∈ Icc (-1 : ℝ) 1 from
    ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  simp only [Set.mem_setOf_eq] at h1 ⊢
  calc cwPressure lam (-h) x = cwPressure lam h (-x) := by
        rw [← cwPressure_neg_field lam h (-x), neg_neg]
    _ ≤ cwPressure lam h m₀ := h1
    _ = cwPressure lam (-h) (-m₀) :=
        (cwPressure_neg_field lam h m₀).symm

end Field

/-! ## The `h → 0` limits of the field maximizers -/

section FieldLimit

variable {lam mstar : ℝ}

/-- **Theorem `thm:cw-phase-diagram` (one-sided limits)**: as
`h ↓ 0` the unique positive-field maximizer converges to `m⋆`. -/
theorem cw_field_limit (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) :
    ∀ ε > (0 : ℝ), ∃ h₀ > (0 : ℝ), ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ m₀ ∈ Icc (-1 : ℝ) 1,
        IsMaxOn (cwPressure lam h) (Icc (-1 : ℝ) 1) m₀ →
          |m₀ - mstar| < ε := by
  intro ε hε
  -- shrink ε below m⋆ so the negative window is out of reach
  set ε' : ℝ := min ε mstar with hε'_def
  have hε'0 : 0 < ε' := lt_min hε hmstar.1
  have hε'm : ε' ≤ mstar := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set K : Set ℝ := Icc (-1 : ℝ) 1 \
    (Ioo (mstar - ε') (mstar + ε') ∪ Ioo (-mstar - ε') (-mstar + ε'))
    with hK_def
  have hKcomp : IsCompact K :=
    isCompact_Icc.diff (IsOpen.union isOpen_Ioo isOpen_Ioo)
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- every admissible point is in one of the windows
    refine ⟨1, one_pos, fun h hh0 hh1 m₀ hm₀ hmax => ?_⟩
    obtain ⟨hp₀, -, -, -⟩ :=
      cw_field_max_properties (by linarith) hh0 hm₀ hmax
    have hmem : m₀ ∉ K := by
      rw [hKe]
      exact Set.notMem_empty m₀
    rw [hK_def] at hmem
    simp only [Set.mem_sdiff, Set.mem_union, not_and, not_not] at hmem
    rcases hmem hm₀ with hw | hw
    · have habs : |m₀ - mstar| < ε' :=
        abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
      exact lt_of_lt_of_le habs hε'ε
    · exfalso
      have := hw.2
      linarith [hp₀, hε'm]
  · -- positive gap between the maximum and the off-window supremum
    obtain ⟨xK, hxK, hxKmax⟩ := hKcomp.exists_isMaxOn hKne
      (continuous_cwPressure lam 0).continuousOn
    have hxK_ne : xK ≠ mstar ∧ xK ≠ -mstar := by
      constructor
      · intro hc
        have := hxK.2
        rw [hc] at this
        exact this (Or.inl ⟨by linarith, by linarith⟩)
      · intro hc
        have := hxK.2
        rw [hc] at this
        exact this (Or.inr ⟨by linarith, by linarith⟩)
    have hgap : cwPressure lam 0 xK < cwPressure lam 0 mstar := by
      rcases lt_or_eq_of_le (cw_phase_supercritical_le hlam hmstar
        hfix hxK.1) with hlt | heq
      · exact hlt
      · exfalso
        rcases (cw_phase_supercritical_eq_iff hlam hmstar hfix
          hxK.1).mp heq with hc | hc
        · exact hxK_ne.1 hc
        · exact hxK_ne.2 hc
    set δ : ℝ := cwPressure lam 0 mstar - cwPressure lam 0 xK
      with hδ_def
    have hδ0 : 0 < δ := by
      rw [hδ_def]
      linarith
    refine ⟨δ / 2, by linarith, fun h hh0 hh1 m₀ hm₀ hmax => ?_⟩
    obtain ⟨hp₀, hl₀, -, -⟩ :=
      cw_field_max_properties (by linarith) hh0 hm₀ hmax
    have hnotK : m₀ ∉ K := by
      intro hmK
      have h1 : cwPressure lam h m₀
          = cwPressure lam 0 m₀ + h * m₀ := by
        unfold cwPressure
        ring
      have h2 : cwPressure lam h mstar
          = cwPressure lam 0 mstar + h * mstar := by
        unfold cwPressure
        ring
      have h3 := hxKmax hmK
      simp only [Set.mem_setOf_eq] at h3
      have h4 := hmax (show mstar ∈ Icc (-1 : ℝ) 1 from
        ⟨by linarith [hmstar.1], hmstar.2.le⟩)
      simp only [Set.mem_setOf_eq] at h4
      have h5 : h * m₀ ≤ h := by nlinarith [hm₀.2]
      have h6 : 0 ≤ h * mstar := mul_nonneg hh0.le hmstar.1.le
      -- Ψ_h(m₀) ≤ Ψ₀(xK) + h < Ψ₀(m⋆) ≤ Ψ_h(m⋆) ≤ Ψ_h(m₀)
      nlinarith [h1, h2, h3, h4]
    rw [hK_def] at hnotK
    simp only [Set.mem_sdiff, Set.mem_union, not_and, not_not] at hnotK
    rcases hnotK hm₀ with hw | hw
    · have habs : |m₀ - mstar| < ε' :=
        abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
      exact lt_of_lt_of_le habs hε'ε
    · exfalso
      have := hw.2
      linarith [hp₀, hε'm]

/-- The `h ↑ 0` limit: maximizers converge to `-m⋆`, by reflection. -/
theorem cw_field_limit_neg (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) :
    ∀ ε > (0 : ℝ), ∃ h₀ > (0 : ℝ), ∀ h : ℝ, -h₀ < h → h < 0 →
      ∀ m₀ ∈ Icc (-1 : ℝ) 1,
        IsMaxOn (cwPressure lam h) (Icc (-1 : ℝ) 1) m₀ →
          |m₀ + mstar| < ε := by
  intro ε hε
  obtain ⟨h₀, hh₀, hkey⟩ := cw_field_limit hlam hmstar hfix ε hε
  refine ⟨h₀, hh₀, fun h hh0 hh1 m₀ hm₀ hmax => ?_⟩
  have hrefl := cw_field_reflect lam h hm₀ hmax
  have h2 := hkey (-h) (by linarith) (by linarith) (-m₀)
    ⟨by linarith [hm₀.2], by linarith [hm₀.1]⟩ hrefl
  have h3 : -m₀ - mstar = -(m₀ + mstar) := by ring
  rw [h3, abs_neg] at h2
  exact h2

end FieldLimit

end NCG.Upstream
