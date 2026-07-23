/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Curie–Weiss gap equation and dynamical branch selection

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`, the self-consistency core of
`thm:cw-phase-diagram` and the full content of
`thm:cw-dynamical-selection`:

* subcritical (`λ ≤ 1`): the only fixed point of `m ↦ tanh(λm)` in
  `(-1,1)` is `m = 0`;
* supercritical (`λ > 1`): there is a unique positive fixed point
  `m⋆ ∈ (0,1)`, the full fixed-point set is `{-m⋆, 0, m⋆}`;
* selection: for any seed in `(0, m⋆)` the mean-field iteration
  increases strictly and converges to `m⋆`; for seeds in `(m⋆, 1)`
  it decreases to `m⋆` — the unoriented point `0` is not selected;
* stability: the linearization coefficient `λ(1 - m⋆²)` is `< 1`.

All monotonicity inputs are routed through the strictly increasing
comparison function `y ↦ y·cosh y / sinh y` on `(0,∞)`, whose
derivative sign reduces to `sinh y · cosh y > y`.
-/

namespace NCG.Upstream

open Real Set Filter

/-! ## Elementary hyperbolic comparisons -/

theorem continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh
    fun x => (Real.cosh_pos x).ne'

theorem tanh_strictMono : StrictMono Real.tanh := by
  intro x y hxy
  by_contra hle
  push Not at hle
  have h2 : Real.artanh (Real.tanh y) ≤ Real.artanh (Real.tanh x) :=
    Real.artanh_le_artanh (Real.neg_one_lt_tanh y)
      (Real.tanh_lt_one x) hle
  rw [Real.artanh_tanh, Real.artanh_tanh] at h2
  exact absurd hxy (not_lt.mpr h2)

theorem sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) :
    Real.sinh x < x * Real.cosh x := by
  have hmono : StrictMonoOn
      (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun t ht => ?_
    · exact ((continuous_id.mul Real.continuous_cosh).sub
        Real.continuous_sinh).continuousOn
    · rw [interior_Ici, mem_Ioi] at ht
      have hd : HasDerivAt
          (fun t : ℝ => t * Real.cosh t - Real.sinh t)
          (1 * Real.cosh t + t * Real.sinh t - Real.cosh t) t :=
        ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
          (Real.hasDerivAt_sinh t)
      rw [hd.deriv]
      have hsimp : 1 * Real.cosh t + t * Real.sinh t - Real.cosh t
          = t * Real.sinh t := by ring
      rw [hsimp]
      exact mul_pos ht (Real.sinh_pos_iff.mpr ht)
  have h1 := hmono (le_refl (0 : ℝ)) (le_of_lt hx) hx
  simp only [Real.cosh_zero, Real.sinh_zero, zero_mul, sub_zero] at h1
  linarith

theorem tanh_lt_self {x : ℝ} (hx : 0 < x) : Real.tanh x < x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos x)]
  exact sinh_lt_mul_cosh hx

theorem lt_sinh_mul_cosh {y : ℝ} (hy : 0 < y) :
    y < Real.sinh y * Real.cosh y := by
  have h1 : 2 * y < Real.sinh (2 * y) :=
    Real.self_lt_sinh_iff.mpr (by linarith)
  rw [Real.sinh_two_mul] at h1
  linarith

/-- The comparison function `y ↦ y·cosh y / sinh y = y / tanh y` is
strictly increasing on `(0,∞)`. -/
theorem comparison_strictMonoOn :
    StrictMonoOn (fun y : ℝ => y * Real.cosh y / Real.sinh y)
      (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi _) ?_ fun y hy => ?_
  · refine ContinuousOn.div
      ((continuous_id.mul Real.continuous_cosh).continuousOn)
      (Real.continuous_sinh.continuousOn) ?_
    intro z hz
    exact (Real.sinh_pos_iff.mpr hz).ne'
  · rw [interior_Ioi, mem_Ioi] at hy
    have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
    have hd : HasDerivAt
        (fun y : ℝ => y * Real.cosh y / Real.sinh y)
        (((1 * Real.cosh y + y * Real.sinh y) * Real.sinh y
          - (y * Real.cosh y) * Real.cosh y) / (Real.sinh y) ^ 2)
        y :=
      (((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y))).div
        (Real.hasDerivAt_sinh y) hs
    rw [hd.deriv]
    apply div_pos
    · have hone := Real.cosh_sq_sub_sinh_sq y
      have h2 := lt_sinh_mul_cosh hy
      nlinarith
    · exact pow_pos (Real.sinh_pos_iff.mpr hy) 2

/-! ## The gap equation -/

/-- **Theorem `thm:cw-phase-diagram` (i) / `thm:cw-dynamical-selection`
(subcritical fixed points)**: for `λ ≤ 1` the only self-consistent
orientation in `(-1,1)` is the unoriented one. -/
theorem gap_subcritical {lam : ℝ} (hlam : lam ≤ 1) {m : ℝ}
    (_hm : m ∈ Ioo (-1 : ℝ) 1)
    (hfix : Real.tanh (lam * m) = m) : m = 0 := by
  have key : ∀ m' : ℝ, 0 < m' → Real.tanh (lam * m') = m' → False := by
    intro m' hm' hfix'
    by_cases hl0 : lam ≤ 0
    · have hx : lam * m' ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨hl0, hm'.le⟩)
      have h1 : Real.tanh (lam * m') ≤ Real.tanh 0 :=
        tanh_strictMono.le_iff_le.mpr hx
      rw [Real.tanh_zero, hfix'] at h1
      linarith
    · push Not at hl0
      have h1 := tanh_lt_self (mul_pos hl0 hm')
      rw [hfix'] at h1
      nlinarith
  rcases lt_trichotomy m 0 with hneg | h0 | hpos
  · exfalso
    refine key (-m) (by linarith) ?_
    rw [show lam * -m = -(lam * m) from by ring, Real.tanh_neg, hfix]
  · exact h0
  · exact absurd hfix (fun h => key m hpos h)

/-- Fixed points in `(0,1)` solve `artanh m = λm`, and conversely. -/
theorem fix_iff_artanh {lam m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    Real.tanh (lam * m) = m ↔ Real.artanh m = lam * m := by
  constructor
  · intro hfix
    conv_lhs => rw [← hfix]
    rw [Real.artanh_tanh]
  · intro hart
    rw [← hart, Real.tanh_artanh ⟨by linarith [hm.1], hm.2⟩]

/-- At a positive fixed point the comparison function takes the
value `λ`. -/
theorem comparison_at_fix {lam m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * m) = m) :
    Real.artanh m * Real.cosh (Real.artanh m)
      / Real.sinh (Real.artanh m) = lam := by
  have hart : Real.artanh m = lam * m :=
    (fix_iff_artanh hm).mp hfix
  have hmm : m ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hm.1], hm.2⟩
  have htan : Real.tanh (Real.artanh m) = m := Real.tanh_artanh hmm
  rw [Real.tanh_eq_sinh_div_cosh] at htan
  have hcp := Real.cosh_pos (Real.artanh m)
  have hsinh : Real.sinh (Real.artanh m)
      = m * Real.cosh (Real.artanh m) := by
    field_simp at htan
    linarith [htan]
  rw [hsinh, hart]
  have hm0 : m ≠ 0 := hm.1.ne'
  field_simp

/-- **Theorem `thm:cw-phase-diagram` (ii), existence and uniqueness
of the oriented root**: for `λ > 1` the gap equation `m = tanh(λm)`
has exactly one solution in `(0,1)`. -/
theorem gap_supercritical {lam : ℝ} (hlam : 1 < lam) :
    ∃! m : ℝ, m ∈ Ioo (0 : ℝ) 1 ∧ Real.tanh (lam * m) = m := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hden : (0 : ℝ) < 2 * lam - 1 := by linarith
  set a : ℝ := (lam - 1) / (2 * lam - 1) with ha_def
  have ha0 : 0 < a := div_pos (by linarith) hden
  have ha1 : a < 1 := by
    rw [ha_def, div_lt_one hden]
    linarith
  have h1ma : 1 - a = lam / (2 * lam - 1) := by
    rw [ha_def, eq_div_iff hden.ne', sub_mul,
      div_mul_cancel₀ _ hden.ne', one_mul]
    ring
  have h1ma0 : 0 < 1 - a := by linarith
  -- ψ(a) < 0 via the logarithmic bound on artanh
  have hb1 : Real.log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + a by linarith)
    linarith
  have hb2 : -Real.log (1 - a) ≤ a / (1 - a) := by
    have hinv : (0 : ℝ) < (1 - a)⁻¹ := by positivity
    have h3 := Real.log_le_sub_one_of_pos hinv
    rw [Real.log_inv] at h3
    have heq : (1 - a)⁻¹ - 1 = a / (1 - a) := by
      rw [inv_eq_one_div, div_sub' h1ma0.ne', div_eq_div_iff h1ma0.ne' h1ma0.ne']
      ring
    linarith [heq ▸ h3]
  have hart_a : Real.artanh a
      = 1 / 2 * (Real.log (1 + a) - Real.log (1 - a)) := by
    rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
      Real.log_div (by linarith) (by linarith)]
  have hcomp : (2 * lam - 1) / lam < 2 * lam - 1 := by
    rw [div_lt_iff₀ hlam0]
    nlinarith
  have hfrac : 1 / (1 - a) = (2 * lam - 1) / lam := by
    rw [h1ma, one_div_div]
  have h2 : 1 / 2 * (a + a / (1 - a)) < lam * a := by
    have h5 : a / (1 - a) = a * (1 / (1 - a)) := by
      rw [mul_one_div]
    rw [h5, hfrac]
    nlinarith
  have hψa : Real.artanh a < lam * a := by
    rw [hart_a]
    have : 1 / 2 * (Real.log (1 + a) - Real.log (1 - a))
        ≤ 1 / 2 * (a + a / (1 - a)) := by linarith
    linarith
  -- ψ(b) > 0 with b = tanh(λ+1)
  set b : ℝ := Real.tanh (lam + 1) with hb_def
  have hbmem : b ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · rw [hb_def, ← Real.tanh_zero]
      exact tanh_strictMono (by linarith)
    · exact Real.tanh_lt_one _
  have hart_b : Real.artanh b = lam + 1 := Real.artanh_tanh _
  have hψb : lam * b < Real.artanh b := by
    rw [hart_b]
    nlinarith [hbmem.2, hbmem.1]
  -- a < b
  have hab : a < b := by
    have h6 : Real.artanh a < Real.artanh b := by
      rw [hart_b]
      nlinarith [ha1]
    exact (Real.artanh_lt_artanh_iff
      ⟨by linarith, by linarith⟩
      ⟨by linarith [hbmem.1], hbmem.2⟩).mp h6
  -- continuity of ψ on [a,b]
  have hcont : ContinuousOn
      (fun m : ℝ => Real.artanh m - lam * m) (Icc a b) := by
    have hsub : ∀ m ∈ Icc a b,
        Real.artanh m - lam * m
          = 1 / 2 * Real.log ((1 + m) / (1 - m)) - lam * m := by
      intro m hmm
      rw [Real.artanh_eq_half_log
        ⟨by linarith [hmm.1], by linarith [hmm.2, hbmem.2]⟩]
    refine ContinuousOn.congr ?_ fun m hmm => hsub m hmm
    refine ContinuousOn.sub ?_
      ((continuous_const.mul continuous_id).continuousOn)
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.log ?_ ?_
    · refine ContinuousOn.div
        ((continuous_const.add continuous_id).continuousOn)
        ((continuous_const.sub continuous_id).continuousOn) ?_
      intro m hmm
      have h9 : m < 1 := lt_of_le_of_lt hmm.2 hbmem.2
      intro hc
      have h10 := sub_eq_zero.mp hc
      linarith
    · intro m hmm
      have hm1 : m < 1 := lt_of_le_of_lt hmm.2 hbmem.2
      have hm0 : 0 < m := lt_of_lt_of_le ha0 hmm.1
      have : (0 : ℝ) < (1 + m) / (1 - m) :=
        div_pos (by linarith) (by linarith)
      exact this.ne'
  -- IVT
  have hivt := intermediate_value_Ioo (le_of_lt hab) hcont
  have h0mem : (0 : ℝ) ∈ Ioo (Real.artanh a - lam * a)
      (Real.artanh b - lam * b) := ⟨by linarith, by linarith⟩
  obtain ⟨mstar, hmstar_mem, hmstar_eq⟩ := hivt h0mem
  have hmstar : mstar ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_trans ha0 hmstar_mem.1, lt_trans hmstar_mem.2 hbmem.2⟩
  have hart_star : Real.artanh mstar = lam * mstar := by
    have := hmstar_eq
    simp only at this
    linarith [this]
  have hfix_star : Real.tanh (lam * mstar) = mstar :=
    (fix_iff_artanh hmstar).mpr hart_star
  -- uniqueness via the comparison function
  have huniq : ∀ m₁ m₂ : ℝ, m₁ ∈ Ioo (0 : ℝ) 1 → m₂ ∈ Ioo (0 : ℝ) 1
      → Real.tanh (lam * m₁) = m₁ → Real.tanh (lam * m₂) = m₂
      → m₁ < m₂ → False := by
    intro m₁ m₂ hm₁ hm₂ hf₁ hf₂ hlt
    have hy₁ : 0 < Real.artanh m₁ := Real.artanh_pos hm₁
    have hylt : Real.artanh m₁ < Real.artanh m₂ :=
      Real.artanh_lt_artanh (by linarith [hm₁.1]) hm₂.2 hlt
    have hc := comparison_strictMonoOn (mem_Ioi.mpr hy₁)
      (mem_Ioi.mpr (lt_trans hy₁ hylt)) hylt
    simp only at hc
    rw [comparison_at_fix hm₁ hf₁, comparison_at_fix hm₂ hf₂] at hc
    exact lt_irrefl _ hc
  refine ⟨mstar, ⟨hmstar, hfix_star⟩, ?_⟩
  rintro m' ⟨hm', hfix'⟩
  rcases lt_trichotomy m' mstar with hlt | heq | hgt
  · exact absurd (huniq m' mstar hm' hmstar hfix' hfix_star hlt) id
  · exact heq
  · exact absurd (huniq mstar m' hmstar hm' hfix_star hfix' hgt) id

/-- **Theorem `thm:cw-phase-diagram` (ii), fixed-point set**: for
`λ > 1` the self-consistent orientations in `(-1,1)` are exactly
`{-m⋆, 0, m⋆}`. -/
theorem gap_supercritical_classification {lam : ℝ} (hlam : 1 < lam)
    {mstar : ℝ} (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m : ℝ}
    (hm : m ∈ Ioo (-1 : ℝ) 1)
    (hfm : Real.tanh (lam * m) = m) :
    m = 0 ∨ m = mstar ∨ m = -mstar := by
  obtain ⟨m₀, -, huniq⟩ := gap_supercritical hlam
  have hstar_eq : mstar = m₀ := huniq mstar ⟨hmstar, hfix⟩
  rcases lt_trichotomy m 0 with hneg | h0 | hpos
  · have hneg_fix : Real.tanh (lam * (-m)) = -m := by
      rw [show lam * -m = -(lam * m) from by ring, Real.tanh_neg,
        hfm]
    have hmem : -m ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith, by linarith [hm.1]⟩
    have := huniq (-m) ⟨hmem, hneg_fix⟩
    right; right
    rw [hstar_eq]
    linarith [this]
  · exact Or.inl h0
  · have hmem : m ∈ Ioo (0 : ℝ) 1 := ⟨hpos, hm.2⟩
    have := huniq m ⟨hmem, hfm⟩
    right; left
    rw [hstar_eq, this]

/-! ## Dynamical selection of the oriented branch -/

section Selection

variable {lam mstar : ℝ}

/-- Below the oriented root the mean-field map increases strictly
and stays below the root. -/
theorem map_mem_below (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m : ℝ}
    (hm : m ∈ Ioo (0 : ℝ) mstar) :
    m < Real.tanh (lam * m)
      ∧ Real.tanh (lam * m) ∈ Ioo (0 : ℝ) mstar := by
  have hm1 : m < 1 := lt_trans hm.2 hmstar.2
  have hmm : m ∈ Ioo (0 : ℝ) 1 := ⟨hm.1, hm1⟩
  have hy : 0 < Real.artanh m := Real.artanh_pos hmm
  have hystar : Real.artanh m < Real.artanh mstar :=
    Real.artanh_lt_artanh (by linarith [hm.1]) hmstar.2 hm.2
  -- comparison: artanh m / m < artanh m⋆ / m⋆ = λ
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
  -- from hc: artanh m * cosh / sinh < λ, i.e. artanh m < λ m
  have hart_lt : Real.artanh m < lam * m := by
    rw [hsinh] at hc
    have hm0 : (0 : ℝ) < m := hm.1
    rw [div_lt_iff₀ (mul_pos hm.1 hcp)] at hc
    nlinarith [hcp]
  constructor
  · have := tanh_strictMono hart_lt
    rwa [htan] at this
  · constructor
    · rw [← Real.tanh_zero]
      exact tanh_strictMono
        (mul_pos (show (0 : ℝ) < lam by linarith) hm.1)
    · rw [← hfix]
      exact tanh_strictMono (by nlinarith [hm.2, hlam])

/-- Above the oriented root the mean-field map decreases strictly
and stays above the root. -/
theorem map_mem_above (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m : ℝ}
    (hm : m ∈ Ioo mstar 1) :
    Real.tanh (lam * m) < m
      ∧ Real.tanh (lam * m) ∈ Ioo mstar (1 : ℝ) := by
  have hm0 : 0 < m := lt_trans hmstar.1 hm.1
  have hmm : m ∈ Ioo (0 : ℝ) 1 := ⟨hm0, hm.2⟩
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
  have hsp : 0 < Real.sinh (Real.artanh m) :=
    Real.sinh_pos_iff.mpr (lt_trans hy hystar)
  have hsinh : Real.sinh (Real.artanh m)
      = m * Real.cosh (Real.artanh m) := by
    have h1 := Real.tanh_eq_sinh_div_cosh (Real.artanh m)
    rw [htan] at h1
    field_simp at h1
    linarith [h1]
  have hart_gt : lam * m < Real.artanh m := by
    rw [hsinh] at hc
    rw [lt_div_iff₀ (mul_pos hm0 hcp)] at hc
    nlinarith [hcp]
  constructor
  · have := tanh_strictMono hart_gt
    rwa [htan] at this
  · constructor
    · rw [← hfix]
      exact tanh_strictMono (by nlinarith [hm.1, hlam])
    · exact Real.tanh_lt_one _

/-- **Theorem `thm:cw-dynamical-selection` (ascent to the oriented
branch)**: from any seed in `(0, m⋆)`, the mean-field iteration is
strictly increasing and converges to `m⋆` — the unoriented fixed
point is dynamically rejected. -/
theorem selection_from_below (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m₀ : ℝ}
    (hm₀ : m₀ ∈ Ioo (0 : ℝ) mstar) :
    (∀ n, (fun m => Real.tanh (lam * m))^[n] m₀
        < (fun m => Real.tanh (lam * m))^[n + 1] m₀)
    ∧ Tendsto (fun n => (fun m => Real.tanh (lam * m))^[n] m₀)
        atTop (nhds mstar) := by
  set F : ℝ → ℝ := fun m => Real.tanh (lam * m) with hF
  set u : ℕ → ℝ := fun n => F^[n] m₀ with hu
  have hmem : ∀ n, u n ∈ Ioo (0 : ℝ) mstar := by
    intro n
    induction n with
    | zero => exact hm₀
    | succ k ih =>
      have := (map_mem_below hlam hmstar hfix ih).2
      simp only [hu, Function.iterate_succ_apply']
      exact this
  have hstep : ∀ n, u n < u (n + 1) := by
    intro n
    have h1 := (map_mem_below hlam hmstar hfix (hmem n)).1
    simp only [hu, Function.iterate_succ_apply']
    exact h1
  have hmono : Monotone u := monotone_nat_of_le_succ
    fun n => (hstep n).le
  have hbdd : BddAbove (Set.range u) := by
    refine ⟨mstar, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (hmem n).2.le
  have hconv := tendsto_atTop_ciSup hmono hbdd
  set L : ℝ := ⨆ n, u n with hL
  have hL_le : L ≤ mstar :=
    ciSup_le fun n => (hmem n).2.le
  have hL_ge : m₀ ≤ L := le_ciSup hbdd 0
  -- the limit is a fixed point
  have hcontF : Continuous F :=
    continuous_tanh.comp (continuous_const.mul continuous_id)
  have h1 : Tendsto (fun n => u (n + 1)) atTop (nhds L) :=
    hconv.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => F (u n)) atTop (nhds (F L)) :=
    (hcontF.tendsto L).comp hconv
  have hsucc : (fun n => u (n + 1)) = fun n => F (u n) := by
    funext n
    simp only [hu]
    exact Function.iterate_succ_apply' F n m₀
  rw [hsucc] at h1
  have hFL : F L = L := tendsto_nhds_unique h2 h1
  have hLmem : L ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le hm₀.1 hL_ge,
      lt_of_le_of_lt hL_le hmstar.2⟩
  obtain ⟨m', -, huniq⟩ := gap_supercritical hlam
  have hLstar : L = mstar := by
    have e1 := huniq L ⟨hLmem, hFL⟩
    have e2 := huniq mstar ⟨hmstar, hfix⟩
    rw [e1, e2]
  exact ⟨hstep, hLstar ▸ hconv⟩

/-- **Theorem `thm:cw-dynamical-selection` (descent to the oriented
branch)**: from any seed in `(m⋆, 1)` the iteration decreases
strictly and converges to `m⋆`. -/
theorem selection_from_above (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {m₀ : ℝ}
    (hm₀ : m₀ ∈ Ioo mstar (1 : ℝ)) :
    (∀ n, (fun m => Real.tanh (lam * m))^[n + 1] m₀
        < (fun m => Real.tanh (lam * m))^[n] m₀)
    ∧ Tendsto (fun n => (fun m => Real.tanh (lam * m))^[n] m₀)
        atTop (nhds mstar) := by
  set F : ℝ → ℝ := fun m => Real.tanh (lam * m) with hF
  set u : ℕ → ℝ := fun n => F^[n] m₀ with hu
  have hmem : ∀ n, u n ∈ Ioo mstar (1 : ℝ) := by
    intro n
    induction n with
    | zero => exact hm₀
    | succ k ih =>
      have := (map_mem_above hlam hmstar hfix ih).2
      simp only [hu, Function.iterate_succ_apply']
      exact this
  have hstep : ∀ n, u (n + 1) < u n := by
    intro n
    have h1 := (map_mem_above hlam hmstar hfix (hmem n)).1
    simp only [hu, Function.iterate_succ_apply']
    exact h1
  have hanti : Antitone u := antitone_nat_of_succ_le
    fun n => (hstep n).le
  have hbdd : BddBelow (Set.range u) := by
    refine ⟨mstar, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (hmem n).1.le
  have hconv := tendsto_atTop_ciInf hanti hbdd
  set L : ℝ := ⨅ n, u n with hL
  have hL_ge : mstar ≤ L :=
    le_ciInf fun n => (hmem n).1.le
  have hL_le : L ≤ m₀ := ciInf_le hbdd 0
  have hcontF : Continuous F :=
    continuous_tanh.comp (continuous_const.mul continuous_id)
  have h1 : Tendsto (fun n => u (n + 1)) atTop (nhds L) :=
    hconv.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => F (u n)) atTop (nhds (F L)) :=
    (hcontF.tendsto L).comp hconv
  have hsucc : (fun n => u (n + 1)) = fun n => F (u n) := by
    funext n
    simp only [hu]
    exact Function.iterate_succ_apply' F n m₀
  rw [hsucc] at h1
  have hFL : F L = L := tendsto_nhds_unique h2 h1
  have hLmem : L ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le hmstar.1 hL_ge,
      lt_of_le_of_lt hL_le hm₀.2⟩
  obtain ⟨m', -, huniq⟩ := gap_supercritical hlam
  have hLstar : L = mstar := by
    have e1 := huniq L ⟨hLmem, hFL⟩
    have e2 := huniq mstar ⟨hmstar, hfix⟩
    rw [e1, e2]
  exact ⟨hstep, hLstar ▸ hconv⟩

/-- **Theorem `thm:cw-dynamical-selection` (linear stability)**: at
the oriented root the linearization coefficient `λ(1 - m⋆²)` of the
mean-field map is strictly less than one. -/
theorem selection_stability (hlam : 1 < lam)
    (hmstar : mstar ∈ Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) :
    lam * (1 - mstar ^ 2) < 1 := by
  set y : ℝ := Real.artanh mstar with hy_def
  have hy : 0 < y := Real.artanh_pos hmstar
  have hart : y = lam * mstar := (fix_iff_artanh hmstar).mp hfix
  have hmm : mstar ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hmstar.1], hmstar.2⟩
  have htan : Real.tanh y = mstar := Real.tanh_artanh hmm
  have hcp := Real.cosh_pos y
  have hsinh : Real.sinh y = mstar * Real.cosh y := by
    have h1 := Real.tanh_eq_sinh_div_cosh y
    rw [htan] at h1
    field_simp at h1
    linarith [h1]
  have hone : (1 - mstar ^ 2) * Real.cosh y ^ 2 = 1 := by
    have h2 := Real.cosh_sq_sub_sinh_sq y
    have hs2 : Real.sinh y ^ 2 = mstar ^ 2 * Real.cosh y ^ 2 := by
      rw [hsinh]
      ring
    linear_combination h2 + hs2
  have hm0 : (0 : ℝ) < mstar := hmstar.1
  have hkey := lt_sinh_mul_cosh hy
  -- y < sinh y cosh y = m⋆ cosh² y, so λ(1-m⋆²)·m⋆ = y(1-m⋆²) < m⋆
  have h6 : y * (1 - mstar ^ 2) < mstar := by
    rw [hsinh] at hkey
    nlinarith [hone, hcp]
  have h5 : lam * (1 - mstar ^ 2) * mstar = y * (1 - mstar ^ 2) := by
    rw [hart]
    ring
  nlinarith [h5, h6, hm0]

end Selection

end NCG.Upstream
