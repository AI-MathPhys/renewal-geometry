/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact arithmetic Grand-Tensor readouts
  (`thm:arithmetic-grand-readouts`, flagship manuscript)

For heat-affine prime ports `𝒫(θ) = Σ' n, a n e^{2πinθ}` with
absolutely summable coefficients:

* circle-character orthogonality
  `∫₀¹ e^{2πikθ} dθ = δ_{k,0}` (`integral_circle_char`);
* the boxed normal quadratic block
  `∫₀¹ 𝒫_a(θ) conj(𝒫_b(θ)) e^{-2πihθ} dθ = Σ_{m-n=h} a_m conj(b_n)`
  (`grand_readout_normal`): absolute convergence permits the
  double expansion and termwise integration, and Fourier
  orthogonality imposes `m = n + h`;
* the boxed anomalous quadratic block
  `∫₀¹ 𝒫_a(θ) 𝒫_b(θ) e^{-2πiNθ} dθ = Σ_{m+n=N} a_m b_n`
  (`grand_readout_anomalous`), collapsing to the finite
  antidiagonal.

Hence fixed differences and fixed sums are different tensor
grades of one port family, exactly as boxed.  The closing remark
(no purely algebraic implication from the order-one inequality to
either order-two bound) is the manuscript's prose example.
-/

open Complex MeasureTheory Set

namespace NCG

/-- Circle-character orthogonality on `(0,1]`. -/
theorem integral_circle_char (k : ℤ) :
    (∫ θ in Ioc (0 : ℝ) 1,
      Complex.exp (2 * Real.pi * I * k * θ))
      = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp only [Int.cast_zero, mul_zero, zero_mul,
      Complex.exp_zero]
    rw [setIntegral_const]
    have h1 : volume.real (Ioc (0 : ℝ) 1) = 1 := by
      rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by norm_num)]
      norm_num
    rw [h1, one_smul]
    simp
  · rw [if_neg hk]
    have hle : (0 : ℝ) ≤ 1 := by norm_num
    have hc : (2 * (Real.pi : ℂ) * I * k) ≠ 0 := by
      have hπ : (Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      have hkC : ((k : ℂ)) ≠ 0 := by exact_mod_cast hk
      simp [hπ, hkC, Complex.I_ne_zero]
    have h2 := integral_exp_mul_complex
      (a := (0 : ℝ)) (b := (1 : ℝ)) hc
    have h3 : (∫ θ in Ioc (0 : ℝ) 1,
        Complex.exp (2 * Real.pi * I * k * θ))
        = ∫ θ in (0 : ℝ)..1,
            Complex.exp (2 * (Real.pi : ℂ) * I * k * θ) := by
      rw [intervalIntegral.integral_of_le hle]
    rw [h3, h2]
    have h4 : Complex.exp
        (2 * (Real.pi : ℂ) * I * k * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * I * k * ((1 : ℝ) : ℂ))
          = (k : ℂ) * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h4, show (2 * (Real.pi : ℂ) * I * k * ((0 : ℝ) : ℂ))
        = 0 by push_cast; ring,
      Complex.exp_zero, sub_self, zero_div]

/-- Unit-modulus of the circle characters. -/
theorem norm_circle_char (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- Norm of a general integer circle character. -/
theorem norm_circle_char' (k : ℤ) (θ : ℝ) :
    ‖Complex.exp (2 * Real.pi * I * k * θ)‖ = 1 := by
  have h1 : (2 * (Real.pi : ℂ) * I * k * θ)
      = ((2 * Real.pi * k * θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h1, norm_circle_char]

/-- `thm:arithmetic-grand-readouts`, boxed normal block:
termwise integration and Fourier orthogonality impose `m = n+h`.
The absolutely convergent double expansion of the port product
enters as the displayed pointwise identity `hpt`. -/
theorem grand_readout_normal (a b : ℕ → ℂ) (h : ℕ)
    (F : ℝ → ℂ)
    (ha : Summable fun n => ‖a n‖)
    (hb : Summable fun n => ‖b n‖)
    (hpt : ∀ θ ∈ Ioc (0 : ℝ) 1, F θ
      = ∑' p : ℕ × ℕ, a p.1 * (starRingEnd ℂ) (b p.2)
          * Complex.exp (2 * Real.pi * I
            * (((p.1 : ℤ) - p.2 - h : ℤ)) * θ)) :
    ∫ θ in Ioc (0 : ℝ) 1, F θ
      = ∑' n, a (n + h) * (starRingEnd ℂ) (b n) := by
  classical
  rw [setIntegral_congr_fun measurableSet_Ioc hpt]
  have hF : ∀ p : ℕ × ℕ, Integrable (fun θ : ℝ =>
      a p.1 * (starRingEnd ℂ) (b p.2)
        * Complex.exp (2 * Real.pi * I
          * (((p.1 : ℤ) - p.2 - h : ℤ)) * θ))
      (volume.restrict (Ioc 0 1)) := by
    intro p
    refine Integrable.mono' (g := fun _ =>
      ‖a p.1 * (starRingEnd ℂ) (b p.2)‖)
      (integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    refine ae_of_all _ fun θ => ?_
    rw [norm_mul, norm_circle_char', mul_one]
  have hFnorm : ∀ p : ℕ × ℕ, (∫ θ in Ioc (0 : ℝ) 1,
      ‖a p.1 * (starRingEnd ℂ) (b p.2)
        * Complex.exp (2 * Real.pi * I
          * (((p.1 : ℤ) - p.2 - h : ℤ)) * θ)‖)
      = ‖a p.1‖ * ‖b p.2‖ := by
    intro p
    have h1 : ∀ θ : ℝ, ‖a p.1 * (starRingEnd ℂ) (b p.2)
        * Complex.exp (2 * Real.pi * I
          * (((p.1 : ℤ) - p.2 - h : ℤ)) * θ)‖
        = ‖a p.1‖ * ‖b p.2‖ := by
      intro θ
      rw [norm_mul, norm_circle_char', mul_one, norm_mul,
        RCLike.norm_conj]
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun θ _ => h1 θ), setIntegral_const,
      MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hsum : Summable (fun p : ℕ × ℕ => ∫ θ in Ioc (0 : ℝ) 1,
      ‖a p.1 * (starRingEnd ℂ) (b p.2)
        * Complex.exp (2 * Real.pi * I
          * (((p.1 : ℤ) - p.2 - h : ℤ)) * θ)‖) := by
    refine Summable.congr ?_ (fun p => (hFnorm p).symm)
    exact ha.mul_of_nonneg hb (fun n => norm_nonneg _)
      (fun n => norm_nonneg _)
  rw [← integral_tsum_of_summable_integral_norm hF hsum]
  have hval : ∀ p : ℕ × ℕ, (∫ θ in Ioc (0 : ℝ) 1,
      a p.1 * (starRingEnd ℂ) (b p.2)
        * Complex.exp (2 * Real.pi * I
          * (((p.1 : ℤ) - p.2 - h : ℤ)) * θ))
      = if (p.1 : ℤ) - p.2 - h = 0
        then a p.1 * (starRingEnd ℂ) (b p.2) else 0 := by
    intro p
    rw [MeasureTheory.integral_const_mul,
      integral_circle_char]
    by_cases hp : (p.1 : ℤ) - p.2 - h = 0
    · rw [if_pos hp, if_pos hp, mul_one]
    · rw [if_neg hp, if_neg hp, mul_zero]
  rw [tsum_congr hval]
  -- collapse to the diagonal `p = (n+h, n)`
  have hinj : Function.Injective
      (fun n : ℕ => ((n + h, n) : ℕ × ℕ)) := by
    intro m n hmn
    simpa using congrArg Prod.snd hmn
  rw [← Function.Injective.tsum_eq hinj ?_]
  · refine tsum_congr fun n => ?_
    rw [if_pos (by push_cast; ring)]
  · intro p hp
    rw [Function.mem_support] at hp
    by_cases hd : (p.1 : ℤ) - p.2 - h = 0
    · refine ⟨p.2, ?_⟩
      have h2 : p.1 = p.2 + h := by omega
      simp [h2.symm]
    · exact absurd (if_neg hd) hp

/-- `thm:arithmetic-grand-readouts`, boxed anomalous block:
Fourier orthogonality imposes `m + n = N`, collapsing to the
finite antidiagonal. -/
theorem grand_readout_anomalous (a b : ℕ → ℂ) (N : ℕ)
    (F : ℝ → ℂ)
    (ha : Summable fun n => ‖a n‖)
    (hb : Summable fun n => ‖b n‖)
    (hpt : ∀ θ ∈ Ioc (0 : ℝ) 1, F θ
      = ∑' p : ℕ × ℕ, a p.1 * b p.2
          * Complex.exp (2 * Real.pi * I
            * (((p.1 : ℤ) + p.2 - N : ℤ)) * θ)) :
    ∫ θ in Ioc (0 : ℝ) 1, F θ
      = ∑ m ∈ Finset.range (N + 1), a m * b (N - m) := by
  classical
  rw [setIntegral_congr_fun measurableSet_Ioc hpt]
  have hF : ∀ p : ℕ × ℕ, Integrable (fun θ : ℝ =>
      a p.1 * b p.2 * Complex.exp (2 * Real.pi * I
        * (((p.1 : ℤ) + p.2 - N : ℤ)) * θ))
      (volume.restrict (Ioc 0 1)) := by
    intro p
    refine Integrable.mono' (g := fun _ => ‖a p.1 * b p.2‖)
      (integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    refine ae_of_all _ fun θ => ?_
    rw [norm_mul, norm_circle_char', mul_one]
  have hFnorm : ∀ p : ℕ × ℕ, (∫ θ in Ioc (0 : ℝ) 1,
      ‖a p.1 * b p.2 * Complex.exp (2 * Real.pi * I
        * (((p.1 : ℤ) + p.2 - N : ℤ)) * θ)‖)
      = ‖a p.1‖ * ‖b p.2‖ := by
    intro p
    have h1 : ∀ θ : ℝ, ‖a p.1 * b p.2
        * Complex.exp (2 * Real.pi * I
          * (((p.1 : ℤ) + p.2 - N : ℤ)) * θ)‖
        = ‖a p.1‖ * ‖b p.2‖ := by
      intro θ
      rw [norm_mul, norm_circle_char', mul_one, norm_mul]
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun θ _ => h1 θ), setIntegral_const,
      MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hsum : Summable (fun p : ℕ × ℕ => ∫ θ in Ioc (0 : ℝ) 1,
      ‖a p.1 * b p.2 * Complex.exp (2 * Real.pi * I
        * (((p.1 : ℤ) + p.2 - N : ℤ)) * θ)‖) := by
    refine Summable.congr ?_ (fun p => (hFnorm p).symm)
    exact ha.mul_of_nonneg hb (fun n => norm_nonneg _)
      (fun n => norm_nonneg _)
  rw [← integral_tsum_of_summable_integral_norm hF hsum]
  have hval : ∀ p : ℕ × ℕ, (∫ θ in Ioc (0 : ℝ) 1,
      a p.1 * b p.2 * Complex.exp (2 * Real.pi * I
        * (((p.1 : ℤ) + p.2 - N : ℤ)) * θ))
      = if (p.1 : ℤ) + p.2 - N = 0
        then a p.1 * b p.2 else 0 := by
    intro p
    rw [MeasureTheory.integral_const_mul,
      integral_circle_char]
    by_cases hp : (p.1 : ℤ) + p.2 - N = 0
    · rw [if_pos hp, if_pos hp, mul_one]
    · rw [if_neg hp, if_neg hp, mul_zero]
  rw [tsum_congr hval]
  -- finite antidiagonal support
  rw [tsum_eq_sum (s := (Finset.range (N + 1)).image
    (fun m => ((m, N - m) : ℕ × ℕ))) ?_]
  · rw [Finset.sum_image ?_]
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hmN : m ≤ N := by
        have := Finset.mem_range.mp hm
        omega
      rw [if_pos (by push_cast [Nat.cast_sub hmN]; ring)]
    · intro m hm n hn hmn
      simpa using congrArg Prod.fst hmn
  · intro p hp
    by_cases hd : (p.1 : ℤ) + p.2 - N = 0
    · exfalso
      refine hp ?_
      refine Finset.mem_image.mpr ⟨p.1, ?_, ?_⟩
      · refine Finset.mem_range.mpr ?_
        omega
      · have h2 : p.2 = N - p.1 := by omega
        exact Prod.ext rfl h2.symm
    · exact if_neg hd

end NCG
