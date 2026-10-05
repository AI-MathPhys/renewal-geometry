/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticSourceSobolevUpgrade
import RenewalGeometry.Analysis.SobolevBoxCrEmbedding

/-!
# Exponential Fourier decay from analytic derivative growth, and the logarithmic upgrade

Generic infrastructure (no renewal notions) for `lem:log-source-upgrade` and the strip step of
`thm:native-source` (Einstein–Standard-Model action-closure manuscript).  The manuscript obtains
the coefficient decay `|f̂(t,ℓ)| ≤ A e^{-a|ℓ|₁/K}` by spatial contour shifting in a complex strip of
width `a/K`.  The same decay follows, without complexification, from derivative bounds of
analytic growth along the coordinate directions,
`‖∂ᵢᵖ g‖_∞ ≤ A p! Rᵖ` for every `p` (`R ∼ K`), by integrating by parts `p` times and optimising
`p ∼ |ℓᵢ|/R`.  For compositions of analytic coefficient maps with band-limited fields these bounds
are supplied by `AnalyticGevrey.exists_gevrey_comp`.

## Main results

* `norm_mFourierCoeff_le_of_bound`: `|F̂(n)| ≤ sup |F|` on the torus.
* `norm_mFourierCoeff_mul_pow_le`: for a smooth `ℤ^d`-periodic `g` with `‖∂ᵢᵖ g‖_∞ ≤ M`,
  `|ĝ(n)| (2π|nᵢ|)ᵖ ≤ M`.
* `le_of_gevrey_family`: `X (2πN)ᵖ ≤ A p! Rᵖ` for all `p` implies `X ≤ e A e^{-2πN/(eR)}`.
* **`norm_mFourierCoeff_le_of_gevrey`**: `‖∂ᵢᵖ g‖_∞ ≤ A p! Rᵖ` for all `i`, `p` implies
  `|ĝ(n)| ≤ e A exp(-(2π/(eR)) |n|_∞)`.
* **`log_source_upgrade_of_decay`**: the statement of `lem:log-source-upgrade` with the
  coefficient decay `|f̂(t,n)| ≤ A e^{-(a/K)|n|_∞}` (`0 < a ≤ 1`) as hypothesis in place of the strip
  extension (same proof as `AnalyticSourceUpgrade.log_source_upgrade`).
-/

open Complex MeasureTheory Filter Topology Set UnitAddTorus
open scoped Real BigOperators ENNReal Nat ContDiff

namespace RenewalGeometry.GevreyFourier

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

open TorusSobolev StripFourier SobolevBoxCr AnalyticSourceUpgrade

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Fourier coefficients and sup bounds -/

/-- `|F̂(n)| ≤ M` when `|F| ≤ M` (probability measure on the torus). -/
theorem norm_mFourierCoeff_le_of_bound {F : UnitAddTorus d → ℂ} {M : ℝ}
    (hF : ∀ x, ‖F x‖ ≤ M) (n : d → ℤ) : ‖mFourierCoeff F n‖ ≤ M := by
  unfold mFourierCoeff
  have hM : ∀ x, ‖mFourier (-n) x • F x‖ ≤ M := fun x => by
    rw [norm_smul, norm_mFourier_apply, one_mul]; exact hF x
  refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hM)).trans ?_
  simp

/-- **Integration by parts `p` times**: for smooth `ℤ^d`-periodic `g` with
`‖Dᵖg(y)(eᵢ, …, eᵢ)‖ ≤ M` everywhere, `|ĝ(n)| (2π|nᵢ|)ᵖ ≤ M`. -/
theorem norm_mFourierCoeff_mul_pow_le {g : (d → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : SobolevBoxCr.IsPeriodic g) (i : d) (p : ℕ) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ p g y (fun _ => Pi.single i 1)‖ ≤ M) (n : d → ℤ) :
    ‖mFourierCoeff (descendFun g) n‖ * (2 * π * |(n i : ℝ)|) ^ p ≤ M := by
  have hg' : ContDiff ℝ ∞ g := hg
  have hc := mFourierCoeff_descend_iterPd hg' hp (fun _ : Fin p => i) n
  rw [symbol_idx_const] at hc
  have hb : ∀ x, ‖descendFun (iterPd g (fun _ : Fin p => i)) x‖ ≤ M := by
    intro x
    unfold descendFun
    rw [← iteratedFDeriv_single hg' (fun _ : Fin p => i)]
    exact hM _
  have h1 := norm_mFourierCoeff_le_of_bound hb n
  rw [hc, norm_mul, norm_pow] at h1
  have h2 : ‖(2 * π * Complex.I * (n i : ℂ))‖ = 2 * π * |(n i : ℝ)| := by
    have : (2 * π * Complex.I * (n i : ℂ)) = ((2 * π * n i : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [h2] at h1
  linarith [mul_comm (‖mFourierCoeff (descendFun g) n‖) ((2 * π * |(n i : ℝ)|) ^ p)]

/-! ### Optimisation over the number of integrations by parts -/

/-- `X (2πN)ᵖ ≤ A p! Rᵖ` for every `p` implies `X ≤ e A exp(-2πN/(eR))`. -/
theorem le_of_gevrey_family {X A R N : ℝ} (hR : 0 < R) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (h : ∀ p : ℕ, X * (2 * π * N) ^ p ≤ A * p ! * R ^ p) :
    X ≤ Real.exp 1 * A * Real.exp (-(2 * π * N / (Real.exp 1 * R))) := by
  set a : ℝ := 2 * π * N / R with ha
  have ha0 : 0 ≤ a := by positivity
  set p : ℕ := ⌊a / Real.exp 1⌋₊ with hpdef
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hp1 : (p : ℝ) ≤ a / Real.exp 1 := Nat.floor_le (by positivity)
  have hp2 : a / Real.exp 1 < p + 1 := Nat.lt_floor_add_one _
  have hX := h p
  -- `p! ≤ pᵖ`
  have hfac : (p ! : ℝ) ≤ (p : ℝ) ^ p := by exact_mod_cast Nat.factorial_le_pow p
  have hexp_arg : 2 * π * N / (Real.exp 1 * R) = a / Real.exp 1 := by
    simp only [a]; field_simp
  rw [hexp_arg]
  by_cases hN0 : N = 0
  · have h0 := h 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one] at h0
    have : a = 0 := by simp [a, hN0]
    rw [this, zero_div, neg_zero, Real.exp_zero, mul_one]
    have : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    nlinarith
  have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
  have hbase : 0 < 2 * π * N := by positivity
  -- `X ≤ A p! (R/(2πN))ᵖ ≤ A (p/a)ᵖ ≤ A e^{-p}`
  have hX' : X ≤ A * p ! * (1 / a) ^ p := by
    have hpow : 0 < (2 * π * N) ^ p := pow_pos hbase p
    have e1 : A * p ! * (1 / a) ^ p = A * p ! * R ^ p / (2 * π * N) ^ p := by
      simp only [a]; rw [one_div_div, div_pow]; ring
    rw [e1, le_div_iff₀ hpow]
    exact hX
  have hpa : (p : ℝ) / a ≤ 1 / Real.exp 1 := by
    have hapos : 0 < a := by positivity
    rw [div_le_div_iff₀ hapos he]
    have := (le_div_iff₀ he).mp hp1
    linarith
  have h3 : (p ! : ℝ) * (1 / a) ^ p ≤ (1 / Real.exp 1) ^ p := by
    calc (p ! : ℝ) * (1 / a) ^ p ≤ (p : ℝ) ^ p * (1 / a) ^ p := by gcongr
      _ = ((p : ℝ) / a) ^ p := by rw [← mul_pow, mul_one_div]
      _ ≤ (1 / Real.exp 1) ^ p := by gcongr
  have h4 : (1 / Real.exp 1) ^ p = Real.exp (-(p : ℝ)) := by
    rw [one_div, inv_pow, ← Real.exp_nat_mul, mul_one, Real.exp_neg]
  have h5 : Real.exp (-(p : ℝ)) ≤ Real.exp 1 * Real.exp (-(a / Real.exp 1)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc X ≤ A * p ! * (1 / a) ^ p := hX'
    _ = A * ((p ! : ℝ) * (1 / a) ^ p) := by ring
    _ ≤ A * (Real.exp 1 * Real.exp (-(a / Real.exp 1))) :=
        mul_le_mul_of_nonneg_left (h3.trans (h4 ▸ h5)) hA
    _ = Real.exp 1 * A * Real.exp (-(a / Real.exp 1)) := by ring

/-- **Exponential Fourier decay from analytic derivative growth**: if a smooth `ℤ^d`-periodic `g`
has `‖Dᵖg(y)(eᵢ, …, eᵢ)‖ ≤ A p! Rᵖ` for every direction `i`, order `p` and point `y`, then
`|ĝ(n)| ≤ e A exp(-(2π/(eR)) |n|_∞)`. -/
theorem norm_mFourierCoeff_le_of_gevrey [Nonempty d] {g : (d → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : SobolevBoxCr.IsPeriodic g) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hb : ∀ (i : d) (p : ℕ) (y : d → ℝ),
      ‖iteratedFDeriv ℝ p g y (fun _ => Pi.single i 1)‖ ≤ A * p ! * R ^ p) (n : d → ℤ) :
    ‖mFourierCoeff (descendFun g) n‖ ≤
      Real.exp 1 * A * Real.exp (-((2 * π / (Real.exp 1 * R)) * linfNorm n)) := by
  obtain ⟨i, hi⟩ := exists_eq_linfNorm n
  have h := le_of_gevrey_family (X := ‖mFourierCoeff (descendFun g) n‖) (N := |(n i : ℝ)|) hR
    (abs_nonneg _) hA fun p => norm_mFourierCoeff_mul_pow_le hg hp i p (hb i p) n
  have hl : ((linfNorm n : ℕ) : ℝ) = |(n i : ℝ)| := by
    rw [← hi, Nat.cast_natAbs, Int.cast_abs]
  rw [hl]
  have e : 2 * π * |(n i : ℝ)| / (Real.exp 1 * R) = 2 * π / (Real.exp 1 * R) * |(n i : ℝ)| := by
    ring
  rw [← e]
  exact h

/-! ### The logarithmic upgrade from coefficient decay -/

/-- **`lem:log-source-upgrade` from coefficient decay** (`eq:log-source-upgrade`), `ε > 0`.  Fix
`0 < a ≤ 1`, an integer `j` and a finite measure `μ` of times.  There is `C > 0` such that for every
family of continuous slices `f(t) : 𝕋^d → ℂ` with `|f̂(t,n)| ≤ A e^{-(a/K)|n|_∞}`, `K ≥ 1`, and
`∫_I ∫_{𝕋^d} |f|² ≤ ε²`, every slice is in `H^j` and
`‖f‖²_{L²_t H^j_x} ≤ (C ε K^j [1 + log(2 + C A K^{j+d}/ε)]^j)²`. -/
theorem log_source_upgrade_of_decay [Nonempty d] {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : α → C(UnitAddTorus d, ℂ)) (A K ε : ℝ), 0 ≤ A → 1 ≤ K → 0 < ε →
      (∀ t n, ‖mFourierCoeff (f t) n‖ ≤ A * Real.exp (-((a / K) * linfNorm n))) →
      ∫⁻ t, ENNReal.ofReal (∫ x, ‖f t x‖ ^ 2) ∂μ ≤ ENNReal.ofReal (ε ^ 2) →
      (∀ t, MemH (j : ℝ) (f t)) ∧
        ∫⁻ t, ENNReal.ofReal (sobSq (j : ℝ) (f t)) ∂μ ≤
          ENNReal.ofReal ((C * ε * K ^ j *
            (1 + Real.log (2 + C * A * K ^ (j + Fintype.card d) / ε)) ^ j) ^ 2) := by
  set D := Fintype.card d with hD
  set a' := a with ha'def
  have ha' : 0 < a' := ha
  have ha'1 : a' ≤ 1 := ha1
  set T : ℝ := (μ univ).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  set M := tailConst j D
  have hM : 0 ≤ M := tailConst_nonneg j D
  set X : ℝ := T * M * (1 / a') ^ (2 * j + D)
  have hX : 0 ≤ X := by positivity
  set C₀ : ℝ := Real.sqrt X + 1
  set C₁ : ℝ := 1 + 16 * π ^ 2 * D / a' ^ 2
  have hC₁ : 1 ≤ C₁ := by
    have : 0 ≤ 16 * π ^ 2 * (D : ℝ) / a' ^ 2 := by positivity
    linarith
  set C₂ : ℝ := Real.sqrt (C₁ ^ j + 1)
  have hC₀ : 0 < C₀ := by positivity
  refine ⟨max C₀ C₂, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro f A K ε hA hK hε hc hL2
  set C := max C₀ C₂
  have hK0 : 0 < K := by linarith
  set Y : ℝ := 2 + C * A * K ^ (j + D) / ε
  have hY : 2 ≤ Y := by
    have : 0 ≤ C * A * K ^ (j + D) / ε := by
      have : 0 ≤ C := le_trans hC₀.le (le_max_left _ _)
      positivity
    linarith
  set Λ : ℝ := 1 + Real.log Y
  have hΛ : 1 ≤ Λ := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Y); linarith
  set γ : ℝ := a' / K
  have hγ0 : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := by rw [div_le_one hK0]; linarith
  set B : ℝ := 2 * K * Λ / a'
  have hγB : γ * B = 2 * Λ := by simp only [γ, B]; field_simp
  obtain ⟨hmem, hsplit⟩ := lintegral_sobSq_le_split μ (fun t => ⇑(f t)) (B := B) hγ0 hγ1 hc j
  refine ⟨hmem, hsplit.trans ?_⟩
  have h0 : ∫⁻ t, ENNReal.ofReal (sobSq 0 (⇑(f t))) ∂μ ≤ ENNReal.ofReal (ε ^ 2) := by
    simp_rw [sobSq_zero_eq_integral_continuous]; exact hL2
  have hμ : μ univ = ENNReal.ofReal T := (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm
  set W : ℝ := (1 + 4 * π ^ 2 * (D * B ^ 2)) ^ j
  set R : ℝ := A ^ 2 * Real.exp (-(γ * B)) * (M * (1 / γ) ^ (2 * j + D))
  have hW : 0 ≤ W := by positivity
  have hR : 0 ≤ R := by positivity
  have hKΛ : 1 ≤ K * Λ := by nlinarith
  have hWb : W ≤ C₁ ^ j * (K * Λ) ^ (2 * j) := by
    have hbase : 1 + 4 * π ^ 2 * (D * B ^ 2) ≤ C₁ * (K * Λ) ^ 2 := by
      have hB2 : B ^ 2 = 4 * (K * Λ) ^ 2 / a' ^ 2 := by simp only [B]; field_simp; ring
      rw [hB2]
      have h1 : (1 : ℝ) ≤ (K * Λ) ^ 2 := one_le_pow₀ hKΛ
      have e : 4 * π ^ 2 * (D * (4 * (K * Λ) ^ 2 / a' ^ 2)) =
          16 * π ^ 2 * D / a' ^ 2 * (K * Λ) ^ 2 := by field_simp; ring
      rw [e]; simp only [C₁]; nlinarith
    calc W ≤ (C₁ * (K * Λ) ^ 2) ^ j := pow_le_pow_left₀ (by positivity) hbase j
      _ = C₁ ^ j * (K * Λ) ^ (2 * j) := by rw [mul_pow, ← pow_mul, mul_comm 2 j]
  have hexpΛ : C₀ * A * K ^ (j + D) ≤ ε * Real.exp Λ := by
    have h1 : Real.exp Λ = Real.exp 1 * Y := by
      simp only [Λ]; rw [Real.exp_add, Real.exp_log (by linarith)]
    have h2 : C * A * K ^ (j + D) ≤ ε * Y := by
      simp only [Y]; rw [mul_add, mul_div_cancel₀ _ hε.ne']; nlinarith
    have h3 : C₀ * A * K ^ (j + D) ≤ C * A * K ^ (j + D) := by
      gcongr; exact le_max_left _ _
    have h4 : ε * Y ≤ ε * Real.exp Λ := by
      rw [h1]; have := Real.add_one_le_exp 1
      have : Y ≤ Real.exp 1 * Y := by nlinarith
      exact mul_le_mul_of_nonneg_left this hε.le
    linarith
  have hTR : T * R ≤ ε ^ 2 := by
    set E : ℝ := Real.exp (-(2 * Λ))
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hEE : Real.exp Λ ^ 2 * E = 1 := by
      simp only [E]; rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hsq : (C₀ * A * K ^ (j + D)) ^ 2 ≤ (ε * Real.exp Λ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hexpΛ 2
    have h1 : C₀ ^ 2 * (A ^ 2 * K ^ (2 * j + 2 * D) * E) ≤ ε ^ 2 := by
      have e1 : C₀ ^ 2 * (A ^ 2 * K ^ (2 * j + 2 * D) * E) = (C₀ * A * K ^ (j + D)) ^ 2 * E := by
        rw [show 2 * j + 2 * D = (j + D) * 2 by ring, pow_mul]; ring
      have e2 : (ε * Real.exp Λ) ^ 2 * E = ε ^ 2 := by rw [mul_pow, mul_assoc, hEE, mul_one]
      rw [e1, ← e2]; exact mul_le_mul_of_nonneg_right hsq hE
    have hXC : X ≤ C₀ ^ 2 := by
      have := Real.sq_sqrt hX
      have : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
      simp only [C₀]; nlinarith
    have hKp : K ^ (2 * j + D) ≤ K ^ (2 * j + 2 * D) := pow_le_pow_right₀ hK (by omega)
    have eR : T * R = X * (K ^ (2 * j + D) * (A ^ 2 * E)) := by
      simp only [R, X, E, γ]; rw [hγB]
      rw [one_div_div, div_pow, one_div_pow, div_eq_mul_one_div (K ^ (2 * j + D))]; ring
    rw [eR]
    calc X * (K ^ (2 * j + D) * (A ^ 2 * E))
        ≤ C₀ ^ 2 * (K ^ (2 * j + 2 * D) * (A ^ 2 * E)) := by gcongr
      _ = C₀ ^ 2 * (A ^ 2 * K ^ (2 * j + 2 * D) * E) := by ring
      _ ≤ ε ^ 2 := h1
  have hfinal : W * ε ^ 2 + T * R ≤ (C * ε * K ^ j * Λ ^ j) ^ 2 := by
    have hKΛj : 1 ≤ (K * Λ) ^ (2 * j) := one_le_pow₀ hKΛ
    have hC2 : C₁ ^ j + 1 ≤ C ^ 2 := by
      have h1 : C₂ ^ 2 = C₁ ^ j + 1 := Real.sq_sqrt (by positivity)
      have h2 : C₂ ≤ C := le_max_right _ _
      have h3 : 0 ≤ C₂ := Real.sqrt_nonneg _
      nlinarith
    have e : (C * ε * K ^ j * Λ ^ j) ^ 2 = C ^ 2 * (K * Λ) ^ (2 * j) * ε ^ 2 := by
      rw [show 2 * j = j * 2 by ring, pow_mul, mul_pow]; ring
    rw [e]
    have hε2 : 0 ≤ ε ^ 2 := by positivity
    calc W * ε ^ 2 + T * R ≤ C₁ ^ j * (K * Λ) ^ (2 * j) * ε ^ 2 + ε ^ 2 := by
          gcongr
      _ ≤ C₁ ^ j * (K * Λ) ^ (2 * j) * ε ^ 2 + (K * Λ) ^ (2 * j) * ε ^ 2 := by
          gcongr; nlinarith
      _ = (C₁ ^ j + 1) * (K * Λ) ^ (2 * j) * ε ^ 2 := by ring
      _ ≤ C ^ 2 * (K * Λ) ^ (2 * j) * ε ^ 2 := by gcongr
  calc ENNReal.ofReal W * ∫⁻ t, ENNReal.ofReal (sobSq 0 (⇑(f t))) ∂μ + μ univ * ENNReal.ofReal R
      ≤ ENNReal.ofReal W * ENNReal.ofReal (ε ^ 2) + ENNReal.ofReal T * ENNReal.ofReal R := by
        rw [hμ]; gcongr
    _ = ENNReal.ofReal (W * ε ^ 2 + T * R) := by
        rw [← ENNReal.ofReal_mul hW, ← ENNReal.ofReal_mul hT,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal

end

end RenewalGeometry.GevreyFourier
