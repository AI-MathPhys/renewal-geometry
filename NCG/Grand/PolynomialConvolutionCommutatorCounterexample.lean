import NCG.Grand.CountableWeightedSchurKernel
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial convolution counterexample to finite-commutator locality

The scalar convolution kernel has every prescribed finite polynomial moment
in `ℓ¹(ℤ)`, but no positive exponential moment.  Together with the countable
Schur extension theorem this is the exact information boundary between a
finite commutator panel and exponential quasilocality.
-/

open Filter
open scoped Topology

namespace NCG
namespace PolynomialConvolutionCommutatorCounterexample

noncomputable section

/-- The manuscript's polynomial convolution coefficient, with the integer
exponent chosen uniformly as `N + 3 > N + 2`. -/
def polynomialKernel (N : ℕ) (z : ℤ) : ℝ :=
  1 / (1 + |(z : ℝ)|) ^ (N + 3)

/-- Absolute coefficient of the `j`th position commutator. -/
def polynomialMoment (N j : ℕ) (z : ℤ) : ℝ :=
  |(z : ℝ)| ^ j * polynomialKernel N z

private theorem summable_shifted_nat_pow_three :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by omega)
  have hs := h.comp_injective (i := fun n : ℕ => n + 1) (by
    intro a b hab
    exact Nat.add_right_cancel hab)
  change Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) at hs
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using hs

/-- The cubic tail on the integers is summable. -/
theorem summable_cubic_integer_tail :
    Summable (fun z : ℤ => 1 / (1 + |(z : ℝ)|) ^ 3) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [Int.cast_natCast, abs_of_nonneg, add_comm] using
      summable_shifted_nat_pow_three
  · simpa [abs_neg, Int.cast_neg, Int.cast_natCast, abs_of_nonneg, add_comm]
      using summable_shifted_nat_pow_three

private theorem moment_le_cubic_tail (N j : ℕ) (hj : j ≤ N) (z : ℤ) :
    polynomialMoment N j z ≤ 1 / (1 + |(z : ℝ)|) ^ 3 := by
  let a : ℝ := |(z : ℝ)|
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 < 1 + a := by positivity
  have hpow : a ^ j ≤ (1 + a) ^ j := by
    exact pow_le_pow_left₀ ha (by linarith) j
  have hj3 : j + 3 ≤ N + 3 := by omega
  calc
    polynomialMoment N j z = a ^ j / (1 + a) ^ (N + 3) := by
      simp [polynomialMoment, polynomialKernel, a, div_eq_mul_inv]
    _ ≤ (1 + a) ^ j / (1 + a) ^ (N + 3) := by
      exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ 1 / (1 + a) ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hb _) (pow_pos hb _)]
      calc
        (1 + a) ^ j * (1 + a) ^ 3 = (1 + a) ^ (j + 3) :=
          (pow_add _ _ _).symm
        _ ≤ (1 + a) ^ (N + 3) :=
          pow_le_pow_right₀ (by linarith) hj3
        _ = 1 * (1 + a) ^ (N + 3) := (one_mul _).symm
    _ = 1 / (1 + |(z : ℝ)|) ^ 3 := rfl

/-- Every commutator order through `N` has an absolutely summable convolution
kernel, hence a bounded `ℓ²(ℤ)` convolution operator by the Schur theorem. -/
theorem polynomialMoment_summable (N j : ℕ) (hj : j ≤ N) :
    Summable (polynomialMoment N j) := by
  apply summable_cubic_integer_tail.of_nonneg_of_le
  · intro z
    exact mul_nonneg (pow_nonneg (abs_nonneg _) _) (by
      unfold polynomialKernel
      positivity)
  · exact moment_le_cubic_tail N j hj

/-- Matrix kernel of the `j`th iterated position commutator. -/
def commutatorConvolutionKernel (N j : ℕ) (x y : ℤ) : ℂ :=
  (((x - y : ℤ) : ℝ) ^ j * polynomialKernel N (x - y) : ℝ)

theorem norm_commutatorConvolutionKernel (N j : ℕ) (x y : ℤ) :
    ‖commutatorConvolutionKernel N j x y‖ =
      polynomialMoment N j (x - y) := by
  have hk : 0 ≤ polynomialKernel N (x - y) := by
    unfold polynomialKernel
    positivity
  rw [commutatorConvolutionKernel, polynomialMoment, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hk]

/-- Every convolution row of a prescribed commutator order is summable. -/
theorem commutator_row_summable (N j : ℕ) (hj : j ≤ N) (x : ℤ) :
    Summable (fun y => ‖commutatorConvolutionKernel N j x y‖) := by
  have h := (Equiv.subLeft x).summable_iff.mpr
    (polynomialMoment_summable N j hj)
  change Summable (fun y : ℤ => polynomialMoment N j (x - y)) at h
  simpa only [norm_commutatorConvolutionKernel] using h

/-- Every convolution column of a prescribed commutator order is summable. -/
theorem commutator_column_summable (N j : ℕ) (hj : j ≤ N) (y : ℤ) :
    Summable (fun x => ‖commutatorConvolutionKernel N j x y‖) := by
  have h := (Equiv.subRight y).summable_iff.mpr
    (polynomialMoment_summable N j hj)
  change Summable (fun x : ℤ => polynomialMoment N j (x - y)) at h
  simpa only [norm_commutatorConvolutionKernel] using h

/-- The common absolute row/column sum. -/
noncomputable def commutatorSchurBound (N j : ℕ) : ℝ :=
  ∑' z : ℤ, polynomialMoment N j z

theorem commutatorSchurBound_nonneg (N j : ℕ) :
    0 ≤ commutatorSchurBound N j := by
  exact tsum_nonneg fun z => mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (by unfold polynomialKernel; positivity)

theorem commutator_row_tsum (N j : ℕ) (x : ℤ) :
    ∑' y, ‖commutatorConvolutionKernel N j x y‖ =
      commutatorSchurBound N j := by
  rw [commutatorSchurBound]
  simp only [norm_commutatorConvolutionKernel]
  exact (Equiv.subLeft x).tsum_eq (polynomialMoment N j)

theorem commutator_column_tsum (N j : ℕ) (y : ℤ) :
    ∑' x, ‖commutatorConvolutionKernel N j x y‖ =
      commutatorSchurBound N j := by
  rw [commutatorSchurBound]
  simp only [norm_commutatorConvolutionKernel]
  exact (Equiv.subRight y).tsum_eq (polynomialMoment N j)

/-- Countable Schur's test realizes every commutator order `j ≤ N` as a
bounded operator on `ℓ²(ℤ)`, with its exact common row/column moment as norm
bound. -/
noncomputable def boundedCommutatorOperator (N j : ℕ) (hj : j ≤ N) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  CountableWeightedSchurKernel.kernelOperator
    (commutatorConvolutionKernel N j) (commutatorSchurBound N j)
    (commutatorSchurBound_nonneg N j)
    (commutator_row_summable N j hj)
    (commutator_column_summable N j hj)
    (fun x => (commutator_row_tsum N j x).le)
    (fun y => (commutator_column_tsum N j y).le)

theorem boundedCommutatorOperator_norm_le (N j : ℕ) (hj : j ≤ N) :
    ‖boundedCommutatorOperator N j hj‖ ≤ commutatorSchurBound N j := by
  exact CountableWeightedSchurKernel.kernelOperator_norm_le
    (commutatorConvolutionKernel N j) (commutatorSchurBound N j)
    (commutatorSchurBound_nonneg N j)
    (commutator_row_summable N j hj)
    (commutator_column_summable N j hj)
    (fun x => (commutator_row_tsum N j x).le)
    (fun y => (commutator_column_tsum N j y).le)

private theorem weighted_nat_tail_tendsto_atTop (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun n : ℕ =>
      Real.exp (μ * (n : ℝ)) / (1 + (n : ℝ)) ^ (N + 3))
      atTop atTop := by
  have hbase := tendsto_exp_mul_div_rpow_atTop
    (N + 3 : ℝ) μ hμ
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hcomp := hbase.comp hshift
  have hscale : 0 < Real.exp (-μ) := Real.exp_pos _
  have hscaled := hcomp.const_mul_atTop hscale
  convert hscaled using 1
  funext n
  simp only [Function.comp_apply]
  rw [show (N : ℝ) + 3 = ((N + 3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  rw [show 1 + (n : ℝ) = (n : ℝ) + 1 by ring]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have he : Real.exp (μ * (n : ℝ)) =
      Real.exp (-μ) * Real.exp (μ * ((n : ℝ) + 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, mul_assoc]

/-- No positive exponential weighting is summable: already its restriction
to the nonnegative integers tends to `+∞`, rather than to zero. -/
theorem exponential_weight_not_summable (N : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ¬ Summable (fun z : ℤ =>
      Real.exp (μ * |(z : ℝ)|) * polynomialKernel N z) := by
  intro hs
  have hnat : Summable (fun n : ℕ =>
      Real.exp (μ * |((n : ℤ) : ℝ)|) * polynomialKernel N (n : ℤ)) :=
    hs.comp_injective Int.ofNat_injective
  have hzero := hnat.tendsto_atTop_zero
  have hinfty : Tendsto (fun n : ℕ =>
      Real.exp (μ * |((n : ℤ) : ℝ)|) * polynomialKernel N (n : ℤ))
      atTop atTop := by
    simpa [polynomialKernel, abs_of_nonneg, div_eq_mul_inv] using
      weighted_nat_tail_tendsto_atTop N hμ
  have hle : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤
      Real.exp (μ * |((n : ℤ) : ℝ)|) * polynomialKernel N (n : ℤ) :=
    hinfty.eventually (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.exp (μ * |((n : ℤ) : ℝ)|) * polynomialKernel N (n : ℤ) < 1 :=
    hzero.eventually (Iio_mem_nhds (by norm_num))
  rcases (hsmall.and hle).exists with ⟨n, hnlt, hnle⟩
  exact (not_lt_of_ge hnle) hnlt

/-- Scalar certificate for the full countertheorem: all prescribed finite
commutator moments are `ℓ¹`, while every exponential Schur moment diverges. -/
theorem finite_commutators_do_not_imply_exponential_locality (N : ℕ) :
    (∀ j, ∀ hj : j ≤ N,
      Summable (polynomialMoment N j) ∧
      ‖boundedCommutatorOperator N j hj‖ ≤
        commutatorSchurBound N j) ∧
      (∀ μ : ℝ, 0 < μ → ¬ Summable (fun z : ℤ =>
        Real.exp (μ * |(z : ℝ)|) * polynomialKernel N z)) := by
  exact ⟨fun j hj => ⟨polynomialMoment_summable N j hj,
      boundedCommutatorOperator_norm_le N j hj⟩,
    fun μ hμ => exponential_weight_not_summable N hμ⟩

end

end PolynomialConvolutionCommutatorCounterexample
end NCG
