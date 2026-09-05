/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FewOrbitJacobiBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fourier--Plancherel closure of the few-orbit Jacobi estimate

This module supplies the normalized theta-integral step in
`thm:ar-few-orbit`.  Quotient-complete endpoint coefficients are embedded as
finite Fourier banks with the Plancherel scale `sqrt Q`.  Unit-modulus phase
twists preserve every coefficient norm, the two bank scales contribute `Q`,
and the outer normalization `Q⁻¹` cancels it exactly.
-/

open scoped BigOperators
open intervalIntegral

namespace NCG
namespace FewOrbitFourierPlancherel

/-- The unit-modulus phase used by every residue--quotient Fourier label. -/
noncomputable def circlePhase (frequency theta : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * frequency * theta : ℝ) * Complex.I)

@[simp] theorem norm_circlePhase (frequency theta : ℝ) :
    ‖circlePhase frequency theta‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- A quotient-complete coefficient bank with Plancherel normalization
`sqrt Q`. -/
noncomputable def fourierBank {I : Type*}
    (Q : ℝ) (frequency : I → ℝ) (c : I → ℂ) (theta : ℝ) (i : I) : ℂ :=
  (Real.sqrt Q : ℂ) * circlePhase (frequency i) theta * c i

/-- Pointwise Plancherel identity for the normalized Fourier bank. -/
theorem fourierBank_norm_sq {I : Type*} [Fintype I]
    (Q : ℝ) (hQ : 0 ≤ Q) (frequency : I → ℝ) (c : I → ℂ)
    (theta : ℝ) :
    ∑ i, ‖fourierBank Q frequency c theta i‖ ^ 2 =
      Q * ∑ i, ‖c i‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fourierBank, norm_mul, norm_circlePhase, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg Q)]
  rw [mul_pow, Real.sq_sqrt hQ]

/-- Complex finite `l1` norm. -/
noncomputable def complexFiniteL1 {I : Type*} [Fintype I]
    (c : I → ℂ) : ℝ := ∑ i, ‖c i‖

/-- Complex finite squared `l2` norm. -/
noncomputable def complexFiniteL2Sq {I : Type*} [Fintype I]
    (c : I → ℂ) : ℝ := ∑ i, ‖c i‖ ^ 2

/-- Finite Cauchy--Schwarz for complex coefficient banks. -/
theorem complexFiniteL1_le_card_sqrt_mul_l2 {I : Type*} [Fintype I]
    (c : I → ℂ) :
    complexFiniteL1 c ≤
      Real.sqrt (Fintype.card I) * Real.sqrt (complexFiniteL2Sq c) := by
  unfold complexFiniteL1 complexFiniteL2Sq
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun _ : I => (1 : ℝ)) (fun i => ‖c i‖)
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- The phase-twisted finite Jacobi form.  All theta dependence has unit
modulus, including the outer carry phase. -/
noncomputable def fewOrbitForm
    {H L R : Type*} [Fintype H] [Fintype L] [Fintype R]
    (Q : ℝ) (leftFrequency : L → ℝ) (rightFrequency : R → ℝ)
    (kernelFrequency : H → L → R → ℝ)
    (w : H → ℂ) (K : H → L → R → ℂ)
    (cL : L → ℂ) (cR : R → ℂ) (theta : ℝ) : ℂ :=
  ∑ h, w h * ∑ i, ∑ j,
    star (fourierBank Q leftFrequency cL theta i) *
      (circlePhase (kernelFrequency h i j) theta * K h i j) *
        fourierBank Q rightFrequency cR theta j

/-- Entrywise Jacobi control and a lag `l1` bound give the complete
pointwise few-orbit estimate, including the exact Plancherel factor `Q`. -/
theorem norm_fewOrbitForm_le
    {H L R : Type*} [Fintype H] [Fintype L] [Fintype R]
    (Q eta W : ℝ) (hQ : 0 ≤ Q) (heta : 0 ≤ eta)
    (leftFrequency : L → ℝ) (rightFrequency : R → ℝ)
    (kernelFrequency : H → L → R → ℝ)
    (w : H → ℂ) (hw : complexFiniteL1 w ≤ W)
    (K : H → L → R → ℂ) (hK : ∀ h i j, ‖K h i j‖ ≤ eta)
    (cL : L → ℂ) (cR : R → ℂ) (theta : ℝ) :
    ‖fewOrbitForm Q leftFrequency rightFrequency kernelFrequency
        w K cL cR theta‖ ≤
      Q * W * eta * Real.sqrt (Fintype.card L * Fintype.card R) *
        Real.sqrt (complexFiniteL2Sq cL) *
          Real.sqrt (complexFiniteL2Sq cR) := by
  have hW : 0 ≤ W :=
    (Finset.sum_nonneg fun i _ => norm_nonneg (w i)).trans hw
  have hbankL : complexFiniteL1
      (fourierBank Q leftFrequency cL theta) ≤
      Real.sqrt Q * Real.sqrt (Fintype.card L) *
        Real.sqrt (complexFiniteL2Sq cL) := by
    calc
      complexFiniteL1 (fourierBank Q leftFrequency cL theta)
          = Real.sqrt Q * complexFiniteL1 cL := by
            unfold complexFiniteL1 fourierBank
            simp only [norm_mul, norm_circlePhase, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg Q)]
            rw [Finset.mul_sum]
      _ ≤ Real.sqrt Q *
          (Real.sqrt (Fintype.card L) * Real.sqrt (complexFiniteL2Sq cL)) :=
        mul_le_mul_of_nonneg_left (complexFiniteL1_le_card_sqrt_mul_l2 cL)
          (Real.sqrt_nonneg Q)
      _ = _ := by ring
  have hbankR : complexFiniteL1
      (fourierBank Q rightFrequency cR theta) ≤
      Real.sqrt Q * Real.sqrt (Fintype.card R) *
        Real.sqrt (complexFiniteL2Sq cR) := by
    calc
      complexFiniteL1 (fourierBank Q rightFrequency cR theta)
          = Real.sqrt Q * complexFiniteL1 cR := by
            unfold complexFiniteL1 fourierBank
            simp only [norm_mul, norm_circlePhase, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg Q)]
            rw [Finset.mul_sum]
      _ ≤ Real.sqrt Q *
          (Real.sqrt (Fintype.card R) * Real.sqrt (complexFiniteL2Sq cR)) :=
        mul_le_mul_of_nonneg_left (complexFiniteL1_le_card_sqrt_mul_l2 cR)
          (Real.sqrt_nonneg Q)
      _ = _ := by ring
  calc
    ‖fewOrbitForm Q leftFrequency rightFrequency kernelFrequency
        w K cL cR theta‖
        ≤ ∑ h, ‖w h‖ * ∑ i, ∑ j,
            ‖fourierBank Q leftFrequency cL theta i‖ * eta *
              ‖fourierBank Q rightFrequency cR theta j‖ := by
          unfold fewOrbitForm
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
          refine (norm_mul_le _ _).trans ?_
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          simp only [norm_mul, norm_star, norm_circlePhase, one_mul]
          gcongr
          exact hK h i j
    _ = complexFiniteL1 w *
          (complexFiniteL1 (fourierBank Q leftFrequency cL theta) *
            (eta * complexFiniteL1
              (fourierBank Q rightFrequency cR theta))) := by
          unfold complexFiniteL1
          calc
            (∑ h, ‖w h‖ * ∑ i, ∑ j,
                ‖fourierBank Q leftFrequency cL theta i‖ * eta *
                  ‖fourierBank Q rightFrequency cR theta j‖) =
              ∑ h, ‖w h‖ * ∑ i,
                ‖fourierBank Q leftFrequency cL theta i‖ *
                  (eta * ∑ j, ‖fourierBank Q rightFrequency cR theta j‖) := by
                apply Finset.sum_congr rfl
                intro h _
                congr 1
                apply Finset.sum_congr rfl
                intro i _
                calc
                  (∑ j, ‖fourierBank Q leftFrequency cL theta i‖ * eta *
                      ‖fourierBank Q rightFrequency cR theta j‖) =
                    (‖fourierBank Q leftFrequency cL theta i‖ * eta) *
                      ∑ j, ‖fourierBank Q rightFrequency cR theta j‖ := by
                        rw [Finset.mul_sum]
                  _ = _ := by ring
            _ = ∑ h, ‖w h‖ *
                ((∑ i, ‖fourierBank Q leftFrequency cL theta i‖) *
                  (eta * ∑ j, ‖fourierBank Q rightFrequency cR theta j‖)) := by
                apply Finset.sum_congr rfl
                intro h _
                congr 1
                exact (Finset.sum_mul _ _ _).symm
            _ = (∑ h, ‖w h‖) *
                ((∑ i, ‖fourierBank Q leftFrequency cL theta i‖) *
                  (eta * ∑ j, ‖fourierBank Q rightFrequency cR theta j‖)) := by
                exact (Finset.sum_mul _ _ _).symm
    _ = complexFiniteL1 w * eta *
          complexFiniteL1 (fourierBank Q leftFrequency cL theta) *
            complexFiniteL1 (fourierBank Q rightFrequency cR theta) := by ring
    _ ≤ W * eta *
          (Real.sqrt Q * Real.sqrt (Fintype.card L) *
            Real.sqrt (complexFiniteL2Sq cL)) *
          (Real.sqrt Q * Real.sqrt (Fintype.card R) *
            Real.sqrt (complexFiniteL2Sq cR)) := by
          have hL2L : 0 ≤ complexFiniteL2Sq cL := by
            exact Finset.sum_nonneg fun i _ => sq_nonneg ‖cL i‖
          have hL2R : 0 ≤ complexFiniteL2Sq cR := by
            exact Finset.sum_nonneg fun i _ => sq_nonneg ‖cR i‖
          have hL1L : 0 ≤ complexFiniteL1
              (fourierBank Q leftFrequency cL theta) := by
            exact Finset.sum_nonneg fun i _ => norm_nonneg _
          have hL1R : 0 ≤ complexFiniteL1
              (fourierBank Q rightFrequency cR theta) := by
            exact Finset.sum_nonneg fun i _ => norm_nonneg _
          gcongr
    _ = Q * W * eta * Real.sqrt (Fintype.card L * Fintype.card R) *
          Real.sqrt (complexFiniteL2Sq cL) *
            Real.sqrt (complexFiniteL2Sq cR) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card L))]
          push_cast
          calc
            W * eta * (√Q * √↑(Fintype.card L) * √(complexFiniteL2Sq cL)) *
                (√Q * √↑(Fintype.card R) * √(complexFiniteL2Sq cR)) =
              (√Q * √Q) * W * eta *
                (√↑(Fintype.card L) * √↑(Fintype.card R)) *
                √(complexFiniteL2Sq cL) * √(complexFiniteL2Sq cR) := by ring
            _ = _ := by rw [Real.mul_self_sqrt hQ]

/-- **Normalized residue--quotient Plancherel estimate.**  The theta integral
has length one, and the outer `Q⁻¹` cancels the two `sqrt Q` endpoint-bank
normalizations. -/
theorem normalized_fewOrbit_integral_le
    {H L R : Type*} [Fintype H] [Fintype L] [Fintype R]
    (Q eta W : ℝ) (hQ : 0 < Q) (heta : 0 ≤ eta)
    (leftFrequency : L → ℝ) (rightFrequency : R → ℝ)
    (kernelFrequency : H → L → R → ℝ)
    (w : H → ℂ) (hw : complexFiniteL1 w ≤ W)
    (K : H → L → R → ℂ) (hK : ∀ h i j, ‖K h i j‖ ≤ eta)
    (cL : L → ℂ) (cR : R → ℂ) :
    Q⁻¹ * (∫ theta in (0 : ℝ)..1,
      ‖fewOrbitForm Q leftFrequency rightFrequency kernelFrequency
        w K cL cR theta‖) ≤
      W * eta * Real.sqrt (Fintype.card L * Fintype.card R) *
        Real.sqrt (complexFiniteL2Sq cL) *
          Real.sqrt (complexFiniteL2Sq cR) := by
  let B := W * eta * Real.sqrt (Fintype.card L * Fintype.card R) *
    Real.sqrt (complexFiniteL2Sq cL) * Real.sqrt (complexFiniteL2Sq cR)
  have hpoint : ∀ theta : ℝ,
      ‖fewOrbitForm Q leftFrequency rightFrequency kernelFrequency
        w K cL cR theta‖ ≤ Q * B := by
    intro theta
    have h := norm_fewOrbitForm_le Q eta W hQ.le heta
      leftFrequency rightFrequency kernelFrequency w hw K hK cL cR theta
    dsimp only [B]
    convert h using 1 <;> ring
  have hcont : Continuous fun theta : ℝ =>
      ‖fewOrbitForm Q leftFrequency rightFrequency kernelFrequency
        w K cL cR theta‖ := by
    unfold fewOrbitForm fourierBank circlePhase
    fun_prop
  have hint :
      (∫ theta in (0 : ℝ)..1,
        ‖fewOrbitForm Q leftFrequency rightFrequency kernelFrequency
          w K cL cR theta‖) ≤ Q * B := by
    calc
      (∫ theta in (0 : ℝ)..1,
          ‖fewOrbitForm Q leftFrequency rightFrequency kernelFrequency
            w K cL cR theta‖)
          ≤ ∫ _theta in (0 : ℝ)..1, Q * B := by
            apply intervalIntegral.integral_mono_on zero_le_one
              hcont.continuousOn.intervalIntegrable
              continuous_const.continuousOn.intervalIntegrable
            intro theta _
            exact hpoint theta
      _ = Q * B := by simp
  calc
    Q⁻¹ * (∫ theta in (0 : ℝ)..1,
      ‖fewOrbitForm Q leftFrequency rightFrequency kernelFrequency
        w K cL cR theta‖)
        ≤ Q⁻¹ * (Q * B) := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hQ.le)
    _ = B := by field_simp
    _ = _ := rfl

end FewOrbitFourierPlancherel
end NCG
