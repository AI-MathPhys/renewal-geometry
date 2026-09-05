/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Gravity.MittagLeffler

/-!
# The Volterra layer of the Mittag-Leffler relaxation
  (`prop:deficiency-subordination`, GR_emergence)

The missing analytic step of the fractional dark-energy cluster: the
Mittag-Leffler relaxation profile solves the Caputo equation in its
equivalent Volterra form.

* `real_beta_convolution` — the real Beta convolution identity
  `∫₀ᵗ s^{β-1}(t-s)^{α-1} ds = t^{α+β-1}·Γ(α)Γ(β)/Γ(α+β)`,
  obtained from Mathlib's complex `betaIntegral_scaled` and
  `Gamma_mul_Gamma_eq_betaIntegral` by descending along
  `Complex.ofReal`;
* `ml_volterra` — term-by-term Beta integration of the convergent
  Mittag-Leffler series (interchange justified by summable integral
  norms against the Gautschi bound) gives the linear Volterra
  equation
  `E_α(-λtᵅ) = 1 - (λ/Γ(α))·∫₀ᵗ (t-s)^{α-1} E_α(-λsᵅ) ds`,
  which is the Caputo relaxation equation
  `D^α y = -λy`, `y = y₀E_α(-λtᵅ)` of
  `prop:deficiency-subordination` in integrated form.
-/

namespace NCG

open Real MeasureTheory intervalIntegral

/-- The real Beta convolution identity on `[0, t]`. -/
theorem real_beta_convolution {al be t : ℝ} (hal : 0 < al)
    (hbe : 0 < be) (ht : 0 < t) :
    ∫ s in (0 : ℝ)..t, s ^ (be - 1) * (t - s) ^ (al - 1)
      = t ^ (al + be - 1) *
        (Real.Gamma al * Real.Gamma be / Real.Gamma (al + be)) := by
  -- complexify the integral
  have hcongr : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      ((s ^ (be - 1) * (t - s) ^ (al - 1) : ℝ) : ℂ)
        = (s : ℂ) ^ ((be : ℂ) - 1) * ((t : ℂ) - s) ^ ((al : ℂ) - 1) := by
    intro s hs
    rw [Set.uIcc_of_le ht.le] at hs
    obtain ⟨hs0, hst⟩ := hs
    push_cast
    rw [Complex.ofReal_cpow hs0,
      Complex.ofReal_cpow (show (0 : ℝ) ≤ t - s by linarith)]
    push_cast
    ring_nf
  have hC : ((∫ s in (0 : ℝ)..t,
      s ^ (be - 1) * (t - s) ^ (al - 1) : ℝ) : ℂ)
      = ∫ s in (0 : ℝ)..t,
        (s : ℂ) ^ ((be : ℂ) - 1) * ((t : ℂ) - s) ^ ((al : ℂ) - 1) := by
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr hcongr
  have hscaled := Complex.betaIntegral_scaled ((be : ℂ)) ((al : ℂ)) ht
  have hGG := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (be : ℂ)) (t := (al : ℂ)) (by simpa using hbe)
    (by simpa using hal)
  have hGne : Complex.Gamma ((be : ℂ) + al) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith)
  have hbeta : Complex.betaIntegral (be : ℂ) (al : ℂ)
      = Complex.Gamma (be : ℂ) * Complex.Gamma (al : ℂ) /
        Complex.Gamma ((be : ℂ) + al) := by
    rw [eq_div_iff hGne]
    linear_combination -hGG
  have hkey : ((∫ s in (0 : ℝ)..t,
      s ^ (be - 1) * (t - s) ^ (al - 1) : ℝ) : ℂ)
      = (t : ℂ) ^ ((be : ℂ) + al - 1) *
        (Complex.Gamma (be : ℂ) * Complex.Gamma (al : ℂ) /
          Complex.Gamma ((be : ℂ) + al)) := by
    rw [hC, hscaled, hbeta]
  -- descend to ℝ
  have hpow : (t : ℂ) ^ ((be : ℂ) + al - 1)
      = ((t ^ (be + al - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht.le]
    push_cast
    ring_nf
  rw [hpow, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_add, Complex.Gamma_ofReal] at hkey
  have hreal : (∫ s in (0 : ℝ)..t, s ^ (be - 1) * (t - s) ^ (al - 1))
      = t ^ (be + al - 1) *
        (Real.Gamma be * Real.Gamma al / Real.Gamma (be + al)) := by
    exact_mod_cast hkey
  rw [hreal, add_comm be al]
  ring_nf

/-- The Volterra summand family. -/
noncomputable def volterraF (al lam t : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  (t - s) ^ (al - 1) *
    ((-lam) ^ n * s ^ (al * n) / Real.Gamma (al * n + 1))

/-- Pointwise series form of the Volterra integrand. -/
theorem volterra_integrand_series {al lam t : ℝ} (s : ℝ)
    (hs : 0 ≤ s) :
    (t - s) ^ (al - 1) * mittagLeffler al 1 (-(lam * s ^ al))
      = ∑' n, volterraF al lam t n s := by
  unfold mittagLeffler volterraF
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hpow : (-(lam * s ^ al)) ^ n = (-lam) ^ n * s ^ (al * n) := by
    rw [show -(lam * s ^ al) = -lam * s ^ al by ring, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (s ^ al) n, ← Real.rpow_mul hs]
  rw [hpow]

/-- Each Volterra summand is interval integrable. -/
theorem volterraF_intervalIntegrable {al lam t : ℝ} (hal : 0 < al)
    (_ht : 0 < t) (n : ℕ) :
    IntervalIntegrable (volterraF al lam t n)
      MeasureTheory.volume 0 t := by
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ (al - 1))
      MeasureTheory.volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (al - 1))
      MeasureTheory.volume 0 t := by
    have h := h0.comp_sub_left t
    simpa using h.symm
  have hcont : ContinuousOn
      (fun s : ℝ =>
        (-lam) ^ n * s ^ (al * n) / Real.Gamma (al * n + 1))
      (Set.uIcc 0 t) := by
    apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    intro s _
    exact (Real.continuousAt_rpow_const s (al * n)
      (Or.inr (by positivity))).continuousWithinAt
  exact h1.mul_continuousOn hcont

/-- The Beta value of each Volterra summand. -/
theorem volterraF_integral {al lam t : ℝ} (hal : 0 < al)
    (ht : 0 < t) (n : ℕ) :
    ∫ s in (0 : ℝ)..t, volterraF al lam t n s
      = Real.Gamma al * ((-lam) ^ n * (t ^ al) ^ (n + 1)
          / Real.Gamma (al * (n + 1) + 1)) := by
  have hbe : (0 : ℝ) < al * n + 1 := by positivity
  have hc : ∫ s in (0 : ℝ)..t, volterraF al lam t n s
      = (-lam) ^ n / Real.Gamma (al * n + 1) *
        ∫ s in (0 : ℝ)..t,
          s ^ (al * n + 1 - 1) * (t - s) ^ (al - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    unfold volterraF
    rw [show al * n + 1 - 1 = al * n by ring]
    ring
  rw [hc, real_beta_convolution hal hbe ht]
  have hGn : Real.Gamma (al * n + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos hbe).ne'
  have hexp : t ^ (al + (al * n + 1) - 1) = (t ^ al) ^ (n + 1) := by
    rw [← Real.rpow_natCast (t ^ al) (n + 1), ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring
  have hGarg : al + (al * ↑n + 1) = al * (↑n + 1) + 1 := by
    ring
  rw [hexp, hGarg]
  field_simp

/-- Summability of the integral norms (Gautschi domination). -/
theorem volterraF_norm_summable {al lam t : ℝ} (hal : 0 < al)
    (ht : 0 < t) :
    Summable fun n : ℕ =>
      ∫ s in (0 : ℝ)..t, ‖volterraF al lam t n s‖ := by
  have hval : ∀ n : ℕ,
      ∫ s in (0 : ℝ)..t, ‖volterraF al lam t n s‖
        = Real.Gamma al * ((|lam| * t ^ al) ^ n /
            Real.Gamma (al * n + (al + 1))) * t ^ al := by
    intro n
    have hbe : (0 : ℝ) < al * n + 1 := by positivity
    have hc : ∫ s in (0 : ℝ)..t, ‖volterraF al lam t n s‖
        = |lam| ^ n / Real.Gamma (al * n + 1) *
          ∫ s in (0 : ℝ)..t,
            s ^ (al * n + 1 - 1) * (t - s) ^ (al - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht.le] at hs
      dsimp only
      unfold volterraF
      rw [show al * n + 1 - 1 = al * n by ring]
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_pow,
        abs_neg,
        abs_of_nonneg (Real.rpow_nonneg
          (by linarith [hs.2] : (0 : ℝ) ≤ t - s) _),
        abs_of_nonneg (Real.rpow_nonneg hs.1 _),
        abs_of_pos (Real.Gamma_pos_of_pos hbe)]
      ring
    rw [hc, real_beta_convolution hal hbe ht]
    have hGn : Real.Gamma (al * n + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos hbe).ne'
    have hexp : t ^ (al + (al * n + 1) - 1)
        = t ^ (al * n) * t ^ al := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have hlam : (|lam| * t ^ al) ^ n = |lam| ^ n * t ^ (al * n) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast (t ^ al) n, ← Real.rpow_mul ht.le,
        mul_comm al (n : ℝ)]
    have hGarg : al + (al * n + 1) = al * n + (al + 1) := by ring
    rw [hexp, hGarg, hlam]
    field_simp
  apply Summable.congr _ (fun n => (hval n).symm)
  apply Summable.mul_right
  apply Summable.mul_left
  exact mlSummable hal (by linarith) (|lam| * t ^ al)

/-- `prop:deficiency-subordination` (Volterra form): the
Mittag-Leffler relaxation profile solves the linear Volterra
equation — the integrated Caputo relaxation equation
`D^α y = -λ y`, `y(t) = y₀ E_α(-λtᵅ)`. -/
theorem ml_volterra {al lam t : ℝ} (hal : 0 < al) (ht : 0 < t) :
    mittagLeffler al 1 (-(lam * t ^ al))
      = 1 - lam / Real.Gamma al *
          ∫ s in (0 : ℝ)..t,
            (t - s) ^ (al - 1) *
              mittagLeffler al 1 (-(lam * s ^ al)) := by
  have hGal : Real.Gamma al ≠ 0 := (Real.Gamma_pos_of_pos hal).ne'
  -- rewrite the integrand as a series
  have hcongr : ∫ s in (0 : ℝ)..t,
      (t - s) ^ (al - 1) * mittagLeffler al 1 (-(lam * s ^ al))
      = ∫ s in (0 : ℝ)..t, ∑' n, volterraF al lam t n s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.le] at hs
    exact volterra_integrand_series s hs.1
  -- interchange sum and integral
  have hexch : ∫ s in (0 : ℝ)..t, ∑' n, volterraF al lam t n s
      = ∑' n, ∫ s in (0 : ℝ)..t, volterraF al lam t n s := by
    rw [intervalIntegral.integral_of_le ht.le]
    rw [← MeasureTheory.integral_tsum_of_summable_integral_norm]
    · apply tsum_congr
      intro n
      rw [intervalIntegral.integral_of_le ht.le]
    · intro n
      exact ((volterraF_intervalIntegrable hal ht n).1)
    · have hn := volterraF_norm_summable (lam := lam) hal ht
      apply Summable.congr hn
      intro n
      rw [intervalIntegral.integral_of_le ht.le]
  rw [hcongr, hexch, tsum_congr (volterraF_integral hal ht)]
  -- assemble via the index shift
  have hsum0 : Summable (fun n : ℕ =>
      (-(lam * t ^ al)) ^ n / Real.Gamma (al * n + 1)) :=
    mlSummable hal one_pos (-(lam * t ^ al))
  have hshift := hsum0.tsum_eq_zero_add
  push_cast at hshift
  unfold mittagLeffler
  rw [hshift]
  have hc0 : (-(lam * t ^ al)) ^ (0 : ℕ)
      / Real.Gamma (al * 0 + 1) = 1 := by
    simp [Real.Gamma_one]
  rw [hc0]
  have hterm : ∀ n : ℕ,
      (-(lam * t ^ al)) ^ (n + 1) / Real.Gamma (al * (n + 1) + 1)
        = -(lam / Real.Gamma al *
            (Real.Gamma al * ((-lam) ^ n * (t ^ al) ^ (n + 1)
              / Real.Gamma (al * (n + 1) + 1)))) := by
    intro n
    have hpow : (-(lam * t ^ al)) ^ (n + 1)
        = -lam * (-lam) ^ n * (t ^ al) ^ (n + 1) := by
      rw [show -(lam * t ^ al) = -lam * t ^ al by ring, mul_pow,
        pow_succ (-lam) n]
      ring
    rw [hpow]
    field_simp
  rw [tsum_congr hterm, tsum_neg, ← tsum_mul_left]
  ring

/-! ## The two-parameter resolvent kernel `t^{α-1}E_{α,α}(-λtᵅ)` -/

/-- Integrability of the doubly singular Beta integrand. -/
theorem beta_integrand_intervalIntegrable {p q t : ℝ} (hp : -1 < p)
    (hq : -1 < q) (ht : 0 < t) :
    IntervalIntegrable (fun s : ℝ => s ^ p * (t - s) ^ q)
      MeasureTheory.volume 0 t := by
  apply IntervalIntegrable.trans (b := t / 2)
  · have h1 : IntervalIntegrable (fun s : ℝ => s ^ p)
        MeasureTheory.volume 0 (t / 2) :=
      intervalIntegral.intervalIntegrable_rpow' hp
    apply h1.mul_continuousOn
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    have hne : t - s ≠ 0 := by
      have := hs.2
      intro h
      nlinarith
    exact ((Real.continuousAt_rpow_const (t - s) q
      (Or.inl hne)).comp
        ((continuous_const.sub continuous_id).continuousAt)).continuousWithinAt
  · have h2 : IntervalIntegrable (fun s : ℝ => (t - s) ^ q)
        MeasureTheory.volume (t / 2) t := by
      have h0 : IntervalIntegrable (fun x : ℝ => x ^ q)
          MeasureTheory.volume 0 (t / 2) :=
        intervalIntegral.intervalIntegrable_rpow' hq
      have h := h0.comp_sub_left t
      have he1 : t - t / 2 = t / 2 := by ring
      have he2 : t - 0 = t := by ring
      rw [he1, he2] at h
      exact h.symm
    apply h2.continuousOn_mul
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    have hne : s ≠ 0 := by
      have := hs.1
      intro h
      nlinarith
    exact (Real.continuousAt_rpow_const s p
      (Or.inl hne)).continuousWithinAt

/-- The resolvent summand family. -/
noncomputable def volterraK (al lam t : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  (t - s) ^ (al - 1) *
    ((-lam) ^ n * s ^ (al * n + al - 1) / Real.Gamma (al * n + al))

/-- Pointwise series form of the resolvent integrand on `(0, t]`. -/
theorem volterraK_series {al lam t : ℝ} (s : ℝ) (hs : 0 < s) :
    (t - s) ^ (al - 1) *
        (s ^ (al - 1) * mittagLeffler al al (-(lam * s ^ al)))
      = ∑' n, volterraK al lam t n s := by
  unfold mittagLeffler volterraK
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hpow : (-(lam * s ^ al)) ^ n = (-lam) ^ n * s ^ (al * n) := by
    rw [show -(lam * s ^ al) = -lam * s ^ al by ring, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (s ^ al) n, ← Real.rpow_mul hs.le]
  rw [hpow]
  have hmerge : s ^ (al - 1) * s ^ (al * n)
      = s ^ (al * n + al - 1) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  field_simp
  rw [show al * ((n : ℝ) + 1) - 1 = al * n + al - 1 by ring, ← hmerge]
  ring

/-- Integrability of each resolvent summand. -/
theorem volterraK_intervalIntegrable {al lam t : ℝ} (hal : 0 < al)
    (ht : 0 < t) (n : ℕ) :
    IntervalIntegrable (volterraK al lam t n)
      MeasureTheory.volume 0 t := by
  have hexp : (-1 : ℝ) < al * n + al - 1 := by
    nlinarith [mul_nonneg hal.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hbase : IntervalIntegrable
      (fun s : ℝ => s ^ (al * n + al - 1) * (t - s) ^ (al - 1))
      MeasureTheory.volume 0 t :=
    beta_integrand_intervalIntegrable hexp (by linarith) ht
  have h := hbase.const_mul ((-lam) ^ n / Real.Gamma (al * n + al))
  have heq : volterraK al lam t n = fun s =>
      (-lam) ^ n / Real.Gamma (al * n + al) *
        (s ^ (al * n + al - 1) * (t - s) ^ (al - 1)) := by
    funext s
    unfold volterraK
    ring
  rw [heq]
  exact h

/-- The Beta value of each resolvent summand. -/
theorem volterraK_integral {al lam t : ℝ} (hal : 0 < al)
    (ht : 0 < t) (n : ℕ) :
    ∫ s in (0 : ℝ)..t, volterraK al lam t n s
      = Real.Gamma al * ((-lam) ^ n * t ^ (al * (n + 1) + al - 1)
          / Real.Gamma (al * (n + 1) + al)) := by
  have hbe : (0 : ℝ) < al * n + al := by positivity
  have hc : ∫ s in (0 : ℝ)..t, volterraK al lam t n s
      = (-lam) ^ n / Real.Gamma (al * n + al) *
        ∫ s in (0 : ℝ)..t,
          s ^ (al * n + al - 1) * (t - s) ^ (al - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    unfold volterraK
    ring
  have hbeta := real_beta_convolution hal hbe ht
  rw [show al * (n : ℝ) + al - 1 = (al * n + al) - 1 by ring] at hc
  rw [hc, hbeta]
  have hGn : Real.Gamma (al * n + al) ≠ 0 :=
    (Real.Gamma_pos_of_pos hbe).ne'
  have hexp : al + (al * n + al) - 1 = al * (n + 1) + al - 1 := by
    ring
  have hGarg : al + (al * n + al) = al * (n + 1) + al := by
    ring
  rw [hexp, hGarg]
  field_simp

/-- Summability of the resolvent integral norms. -/
theorem volterraK_norm_summable {al lam t : ℝ} (hal : 0 < al)
    (ht : 0 < t) :
    Summable fun n : ℕ =>
      ∫ s in (0 : ℝ)..t, ‖volterraK al lam t n s‖ := by
  have hval : ∀ n : ℕ,
      ∫ s in (0 : ℝ)..t, ‖volterraK al lam t n s‖
        = Real.Gamma al * ((|lam| * t ^ al) ^ n /
            Real.Gamma (al * n + 2 * al)) * t ^ (2 * al - 1) := by
    intro n
    have hbe : (0 : ℝ) < al * n + al := by positivity
    have hc : ∫ s in (0 : ℝ)..t, ‖volterraK al lam t n s‖
        = |lam| ^ n / Real.Gamma (al * n + al) *
          ∫ s in (0 : ℝ)..t,
            s ^ ((al * n + al) - 1) * (t - s) ^ (al - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht.le] at hs
      dsimp only
      unfold volterraK
      rw [show al * (n : ℝ) + al - 1 = (al * n + al) - 1 by ring]
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_pow,
        abs_neg,
        abs_of_nonneg (Real.rpow_nonneg
          (by linarith [hs.2] : (0 : ℝ) ≤ t - s) _),
        abs_of_nonneg (Real.rpow_nonneg hs.1 _),
        abs_of_pos (Real.Gamma_pos_of_pos hbe)]
      ring
    rw [hc, real_beta_convolution hal hbe ht]
    have hGn : Real.Gamma (al * n + al) ≠ 0 :=
      (Real.Gamma_pos_of_pos hbe).ne'
    have hexp : t ^ (al + (al * n + al) - 1)
        = t ^ (al * n) * t ^ (2 * al - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have hlam : (|lam| * t ^ al) ^ n = |lam| ^ n * t ^ (al * n) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast (t ^ al) n, ← Real.rpow_mul ht.le,
        mul_comm al (n : ℝ)]
    have hGarg : al + (al * n + al) = al * n + 2 * al := by ring
    rw [hexp, hGarg, hlam]
    field_simp
  apply Summable.congr _ (fun n => (hval n).symm)
  apply Summable.mul_right
  apply Summable.mul_left
  exact mlSummable hal (by linarith) (|lam| * t ^ al)

/-- `thm:irreversible-crossing-threshold` (kernel layer): the
two-parameter Mittag-Leffler resolvent kernel
`t^{α-1}E_{α,α}(-λtᵅ)` of the driven threshold equation solves the
resolvent Volterra identity
`Γ(α)·t^{α-1}E_{α,α}(-λtᵅ) = t^{α-1} - λ∫₀ᵗ(t-s)^{α-1}·
s^{α-1}E_{α,α}(-λsᵅ) ds`. -/
theorem mlKernel_volterra {al lam t : ℝ} (hal : 0 < al)
    (ht : 0 < t) :
    Real.Gamma al *
        (t ^ (al - 1) * mittagLeffler al al (-(lam * t ^ al)))
      = t ^ (al - 1) - lam *
          ∫ s in (0 : ℝ)..t,
            (t - s) ^ (al - 1) *
              (s ^ (al - 1) * mittagLeffler al al (-(lam * s ^ al))) := by
  have hGal : Real.Gamma al ≠ 0 := (Real.Gamma_pos_of_pos hal).ne'
  -- series form + interchange over the open interval
  have hexch : ∫ s in (0 : ℝ)..t,
      (t - s) ^ (al - 1) *
        (s ^ (al - 1) * mittagLeffler al al (-(lam * s ^ al)))
      = ∑' n, ∫ s in (0 : ℝ)..t, volterraK al lam t n s := by
    rw [intervalIntegral.integral_of_le ht.le]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (g := fun s => ∑' n, volterraK al lam t n s)
      (fun s hs => volterraK_series s hs.1)]
    rw [← MeasureTheory.integral_tsum_of_summable_integral_norm]
    · apply tsum_congr
      intro n
      rw [intervalIntegral.integral_of_le ht.le]
    · intro n
      exact ((volterraK_intervalIntegrable hal ht n).1)
    · have hn := volterraK_norm_summable (lam := lam) hal ht
      apply Summable.congr hn
      intro n
      rw [intervalIntegral.integral_of_le ht.le]
  rw [hexch, tsum_congr (volterraK_integral hal ht)]
  -- LHS series and index shift
  have hsum0 : Summable (fun n : ℕ =>
      (-(lam * t ^ al)) ^ n / Real.Gamma (al * n + al)) :=
    mlSummable hal hal (-(lam * t ^ al))
  have hlhs : Real.Gamma al *
      (t ^ (al - 1) * mittagLeffler al al (-(lam * t ^ al)))
      = Real.Gamma al * ∑' n : ℕ,
          (-lam) ^ n * t ^ (al * n + al - 1)
            / Real.Gamma (al * n + al) := by
    unfold mittagLeffler
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr
    intro n
    have hpow : (-(lam * t ^ al)) ^ n = (-lam) ^ n * t ^ (al * n) := by
      rw [show -(lam * t ^ al) = -lam * t ^ al by ring, mul_pow]
      congr 1
      rw [← Real.rpow_natCast (t ^ al) n, ← Real.rpow_mul ht.le]
    rw [hpow]
    have hmerge : t ^ (al - 1) * t ^ (al * n)
        = t ^ (al * n + al - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    field_simp
    rw [show al * ((n : ℝ) + 1) - 1 = al * n + al - 1 by ring, ← hmerge]
    ring
  rw [hlhs]
  -- shift the summable series
  have hsum1 : Summable (fun n : ℕ =>
      (-lam) ^ n * t ^ (al * n + al - 1)
        / Real.Gamma (al * n + al)) := by
    have h := hsum0.mul_right (t ^ (al - 1))
    apply Summable.congr h
    intro n
    have hpow : (-(lam * t ^ al)) ^ n = (-lam) ^ n * t ^ (al * n) := by
      rw [show -(lam * t ^ al) = -lam * t ^ al by ring, mul_pow]
      congr 1
      rw [← Real.rpow_natCast (t ^ al) n, ← Real.rpow_mul ht.le]
    rw [hpow]
    have hmerge : t ^ (al * n) * t ^ (al - 1)
        = t ^ (al * ((n : ℝ) + 1) - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    field_simp
    rw [← hmerge]
    ring
  rw [tsum_mul_left]
  have hshift := hsum1.tsum_eq_zero_add
  push_cast at hshift
  rw [hshift]
  have hf0 : (-lam) ^ (0 : ℕ) * t ^ (al * 0 + al - 1)
      / Real.Gamma (al * 0 + al) = t ^ (al - 1) / Real.Gamma al := by
    norm_num
  rw [hf0]
  have hsucc : ∀ n : ℕ,
      (-lam) ^ (n + 1) * t ^ (al * ((n : ℝ) + 1) + al - 1)
        / Real.Gamma (al * ((n : ℝ) + 1) + al)
      = -lam * ((-lam) ^ n * t ^ (al * ((n : ℝ) + 1) + al - 1)
          / Real.Gamma (al * ((n : ℝ) + 1) + al)) := by
    intro n
    rw [pow_succ]
    ring
  rw [tsum_congr hsucc, tsum_mul_left]
  field_simp
  ring

end NCG
