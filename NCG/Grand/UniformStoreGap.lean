/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exponential dwell and a uniform cutoff gap
  (`cor:uniform-store-gap`, Gran-Tensor manuscript)

* `exp_dwell_multiplier`: the exponential-dwell cosine
  multiplier is exactly
  `φ_λ(ω) = ∫₀^∞ λe^{-λt} cos(ωt) dt = λ²/(λ²+ω²)`.
* `uniform_store_gap`: under uniform cutoff bounds `δ_X ≥ δ₀`
  and `λ_X ≤ λ₁`, the multiplier is bounded by
  `1 - γ₀ = λ₁²/(λ₁²+δ₀²)`, and hence any contraction rate below
  it decays like `(1-γ₀)ⁿ`.

The operator clause
`‖R_Xⁿ - E_{L_X}‖ ≤ (1-γ₀)ⁿ`, obtained from the exact
score--dwell spectral norm identity, is proved for every natural power in
`NCG.Grand.UniformStoreGapOperatorBound`.
-/

open Real MeasureTheory Filter

namespace NCG

/-- The exponential-dwell cosine multiplier. -/
theorem exp_dwell_multiplier (lam om : ℝ) (hlam : 0 < lam) :
    ∫ t in Set.Ioi (0 : ℝ),
      lam * Real.exp (-lam * t) * Real.cos (om * t)
    = lam ^ 2 / (lam ^ 2 + om ^ 2) := by
  have hD : lam ^ 2 + om ^ 2 ≠ 0 := by positivity
  -- the antiderivative
  set F : ℝ → ℝ := fun t =>
    Real.exp (-lam * t)
      * (om * Real.sin (om * t) - lam * Real.cos (om * t))
      / (lam ^ 2 + om ^ 2) with hF
  have hderiv : ∀ t : ℝ,
      HasDerivAt F
        (Real.exp (-lam * t) * Real.cos (om * t)) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => -lam * s) (-lam) t := by
      simpa using (hasDerivAt_id t).const_mul (-lam)
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-lam * s))
        (Real.exp (-lam * t) * -lam) t := hlin.exp
    have homt : HasDerivAt (fun s : ℝ => om * s) om t := by
      simpa using (hasDerivAt_id t).const_mul om
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (om * s))
        (Real.cos (om * t) * om) t :=
      (Real.hasDerivAt_sin (om * t)).comp t homt
    have hcos : HasDerivAt (fun s : ℝ => Real.cos (om * s))
        (-Real.sin (om * t) * om) t :=
      (Real.hasDerivAt_cos (om * t)).comp t homt
    have hg : HasDerivAt
        (fun s : ℝ => om * Real.sin (om * s)
          - lam * Real.cos (om * s))
        (om * (Real.cos (om * t) * om)
          - lam * (-Real.sin (om * t) * om)) t :=
      (hsin.const_mul om).sub (hcos.const_mul lam)
    have hmul := (hexp.mul hg).div_const (lam ^ 2 + om ^ 2)
    refine hmul.congr_deriv ?_
    field_simp
    ring
  have hlimF : Tendsto F atTop (nhds 0) := by
    have hexp0 : Tendsto (fun t : ℝ => Real.exp (-lam * t))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
        Tendsto.const_mul_atTop hlam tendsto_id
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero).comp h1
      refine h2.congr fun t => ?_
      simp [neg_mul]
    have hbound : ∀ t : ℝ, ‖F t‖
        ≤ Real.exp (-lam * t)
          * ((|om| + |lam|) / (lam ^ 2 + om ^ 2)) := by
      intro t
      have hDpos : (0 : ℝ) < lam ^ 2 + om ^ 2 := by positivity
      have hin : |om * Real.sin (om * t)
          - lam * Real.cos (om * t)| ≤ |om| + |lam| := by
        calc |om * Real.sin (om * t) - lam * Real.cos (om * t)|
            ≤ |om * Real.sin (om * t)|
              + |lam * Real.cos (om * t)| := abs_sub _ _
          _ ≤ |om| * 1 + |lam| * 1 := by
              rw [abs_mul, abs_mul]
              gcongr
              · exact Real.abs_sin_le_one _
              · exact Real.abs_cos_le_one _
          _ = |om| + |lam| := by ring
      rw [hF]
      rw [norm_eq_abs, abs_div, abs_mul, Real.abs_exp,
        abs_of_pos hDpos]
      rw [div_le_iff₀ hDpos]
      calc Real.exp (-lam * t)
            * |om * Real.sin (om * t) - lam * Real.cos (om * t)|
          ≤ Real.exp (-lam * t) * (|om| + |lam|) :=
            mul_le_mul_of_nonneg_left hin (Real.exp_nonneg _)
        _ = Real.exp (-lam * t) * ((|om| + |lam|)
              / (lam ^ 2 + om ^ 2)) * (lam ^ 2 + om ^ 2) := by
            field_simp
    refine squeeze_zero_norm hbound ?_
    have := hexp0.mul_const ((|om| + |lam|) / (lam ^ 2 + om ^ 2))
    simpa using this
  have hint : IntegrableOn
      (fun t : ℝ => Real.exp (-lam * t) * Real.cos (om * t))
      (Set.Ioi (0 : ℝ)) := by
    have hexpint : IntegrableOn
        (fun t : ℝ => Real.exp (-lam * t))
        (Set.Ioi (0 : ℝ)) := exp_neg_integrableOn_Ioi 0 hlam
    have h1 : Integrable
        (fun t : ℝ => Real.cos (om * t) * Real.exp (-lam * t))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      MeasureTheory.Integrable.bdd_mul (c := 1) hexpint
        ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs]
          exact Real.abs_cos_le_one _)
    exact h1.congr (Filter.EventuallyEq.of_eq (by
      funext t
      ring))
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := F) (fun x _ => hderiv x) hint hlimF
  have hF0 : F 0 = -lam / (lam ^ 2 + om ^ 2) := by
    rw [hF]
    simp
  rw [show (fun t : ℝ =>
      lam * Real.exp (-lam * t) * Real.cos (om * t))
      = fun t : ℝ =>
        lam * (Real.exp (-lam * t) * Real.cos (om * t)) from by
    funext t
    ring]
  rw [MeasureTheory.integral_const_mul, hmain, hF0]
  field_simp
  ring

/-- `cor:uniform-store-gap`: the uniform multiplier maximum
`1 - γ₀ = λ₁²/(λ₁²+δ₀²)` and the resulting power decay. -/
theorem uniform_store_gap (lam lam1 om d0 : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ lam1) (hd0 : 0 < d0)
    (hom : d0 ≤ |om|) :
    (lam ^ 2 / (lam ^ 2 + om ^ 2)
      ≤ lam1 ^ 2 / (lam1 ^ 2 + d0 ^ 2))
    ∧ (1 - d0 ^ 2 / (lam1 ^ 2 + d0 ^ 2)
        = lam1 ^ 2 / (lam1 ^ 2 + d0 ^ 2))
    ∧ (∀ (r : ℝ) (n : ℕ), 0 ≤ r →
        r ≤ 1 - d0 ^ 2 / (lam1 ^ 2 + d0 ^ 2) →
        r ^ n ≤ (1 - d0 ^ 2 / (lam1 ^ 2 + d0 ^ 2)) ^ n) := by
  have hlam1p : 0 < lam1 := lt_of_lt_of_le hlam hlam1
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : lam ^ 2 ≤ lam1 ^ 2 := by nlinarith
    have h2 : d0 ^ 2 ≤ om ^ 2 := by
      have := sq_abs om
      nlinarith [abs_nonneg om]
    nlinarith [mul_le_mul h1 h2 (by positivity)
      (by positivity : (0 : ℝ) ≤ lam1 ^ 2)]
  · field_simp
    ring
  · intro r n hr hle
    exact pow_le_pow_left₀ hr hle n

end NCG
