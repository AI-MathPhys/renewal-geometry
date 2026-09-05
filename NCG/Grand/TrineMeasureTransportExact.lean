/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TrineTransportExtras
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Arbitrary-measure trine transport estimates

This is the `L¹`/total-variation layer of `thm:GT-trine-slack-transport`.
After transporting two trine packets to a common screen, dominate their six
positive measures by one reference measure.  The resulting densities satisfy
the exact carrier and complex-current bounds with constant one, the slack
bound with constant three, and total-variation duality for bounded payoffs.
-/

open Finset Filter Set
open scoped ENNReal MeasureTheory

namespace NCG
namespace TrineMeasureTransport

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Carrier density reconstructed from three positive outcome densities. -/
noncomputable def carrierDensity (r : Fin 3 → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ k, r k ω

/-- Complex-current density reconstructed with unit-modulus Fourier phases. -/
noncomputable def complexDensity (phase : Fin 3 → ℂ)
    (r : Fin 3 → Ω → ℝ) (ω : Ω) : ℂ :=
  ∑ k, phase k * (r k ω : ℂ)

/-- Scalar slack density on the common screen. -/
noncomputable def slackDensity (phase : Fin 3 → ℂ)
    (r : Fin 3 → Ω → ℝ) (ω : Ω) : ℝ :=
  carrierDensity r ω - 2 * ‖complexDensity phase r ω‖

/-- The manuscript's trine transport defect in dominated-density form. -/
noncomputable def trineTransportDefect
    (rX rY : Fin 3 → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∑ k, ∫ ω, |rX k ω - rY k ω| ∂μ

theorem carrierDensity_sub_abs_le
    (rX rY : Fin 3 → Ω → ℝ) (ω : Ω) :
    |carrierDensity rX ω - carrierDensity rY ω| ≤
      ∑ k, |rX k ω - rY k ω| := by
  simp only [carrierDensity, ← Finset.sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

theorem complexDensity_sub_norm_le
    (phase : Fin 3 → ℂ) (hphase : ∀ k, ‖phase k‖ = 1)
    (rX rY : Fin 3 → Ω → ℝ) (ω : Ω) :
    ‖complexDensity phase rX ω - complexDensity phase rY ω‖ ≤
      ∑ k, |rX k ω - rY k ω| := by
  simp only [complexDensity, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k, (phase k * (rX k ω : ℂ) - phase k * (rY k ω : ℂ))‖ ≤
        ∑ k, ‖phase k * (rX k ω : ℂ) - phase k * (rY k ω : ℂ)‖ :=
      norm_sum_le _ _
    _ = ∑ k, |rX k ω - rY k ω| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← mul_sub, norm_mul, hphase, one_mul, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]

theorem slackDensity_sub_abs_le_three
    (phase : Fin 3 → ℂ) (hphase : ∀ k, ‖phase k‖ = 1)
    (rX rY : Fin 3 → Ω → ℝ) (ω : Ω) :
    |slackDensity phase rX ω - slackDensity phase rY ω| ≤
      3 * ∑ k, |rX k ω - rY k ω| := by
  have hc := carrierDensity_sub_abs_le rX rY ω
  have hz := complexDensity_sub_norm_le phase hphase rX rY ω
  unfold slackDensity
  calc
    |(carrierDensity rX ω - 2 * ‖complexDensity phase rX ω‖) -
        (carrierDensity rY ω - 2 * ‖complexDensity phase rY ω‖)| ≤
      |carrierDensity rX ω - carrierDensity rY ω| +
        2 * ‖complexDensity phase rX ω - complexDensity phase rY ω‖ := by
      calc
        _ = |(carrierDensity rX ω - carrierDensity rY ω) -
            2 * (‖complexDensity phase rX ω‖ -
              ‖complexDensity phase rY ω‖)| := by ring
        _ ≤ |carrierDensity rX ω - carrierDensity rY ω| +
            |2 * (‖complexDensity phase rX ω‖ -
              ‖complexDensity phase rY ω‖)| := abs_sub _ _
        _ ≤ |carrierDensity rX ω - carrierDensity rY ω| +
            2 * ‖complexDensity phase rX ω - complexDensity phase rY ω‖ := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          gcongr
          exact abs_norm_sub_norm_le _ _
    _ ≤ 3 * ∑ k, |rX k ω - rY k ω| := by linarith

private theorem integrable_absDefect
    (rX rY : Fin 3 → Ω → ℝ)
    (hX : ∀ k, Integrable (rX k) μ) (hY : ∀ k, Integrable (rY k) μ) (k : Fin 3) :
    Integrable (fun ω => |rX k ω - rY k ω|) μ :=
  ((hX k).sub (hY k)).abs

private theorem integrable_defectSum
    (rX rY : Fin 3 → Ω → ℝ)
    (hX : ∀ k, Integrable (rX k) μ) (hY : ∀ k, Integrable (rY k) μ) :
    Integrable (fun ω => ∑ k, |rX k ω - rY k ω|) μ :=
  integrable_finset_sum _ fun k _ => integrable_absDefect rX rY hX hY k

private theorem integrable_carrierDensity
    (r : Fin 3 → Ω → ℝ) (hr : ∀ k, Integrable (r k) μ) :
    Integrable (carrierDensity r) μ := by
  unfold carrierDensity
  exact integrable_finset_sum _ fun k _ => hr k

private theorem integrable_complexDensity
    (phase : Fin 3 → ℂ) (r : Fin 3 → Ω → ℝ)
    (hr : ∀ k, Integrable (r k) μ) :
    Integrable (complexDensity phase r) μ := by
  unfold complexDensity
  exact integrable_finset_sum _ fun k _ => (hr k).ofReal.const_mul (phase k)

private theorem integrable_slackDensity
    (phase : Fin 3 → ℂ) (r : Fin 3 → Ω → ℝ)
    (hr : ∀ k, Integrable (r k) μ) :
    Integrable (slackDensity phase r) μ := by
  unfold slackDensity
  exact (integrable_carrierDensity r hr).sub
    ((integrable_complexDensity phase r hr).norm.const_mul 2)

/-- Total variation of the carrier difference is bounded by the sum of the
three outcome variations. -/
theorem integral_carrierDensity_sub_abs_le_defect
    (rX rY : Fin 3 → Ω → ℝ)
    (hX : ∀ k, Integrable (rX k) μ) (hY : ∀ k, Integrable (rY k) μ) :
    ∫ ω, |carrierDensity rX ω - carrierDensity rY ω| ∂μ ≤
      trineTransportDefect rX rY μ := by
  have hright := integrable_defectSum rX rY hX hY
  have hleft : Integrable
      (fun ω => |carrierDensity rX ω - carrierDensity rY ω|) μ :=
    ((integrable_carrierDensity rX hX).sub
      (integrable_carrierDensity rY hY)).abs
  calc
    ∫ ω, |carrierDensity rX ω - carrierDensity rY ω| ∂μ ≤
        ∫ ω, ∑ k, |rX k ω - rY k ω| ∂μ :=
      integral_mono_ae hleft hright
        (Filter.Eventually.of_forall fun ω => carrierDensity_sub_abs_le rX rY ω)
    _ = trineTransportDefect rX rY μ := by
      simp [trineTransportDefect, integral_finset_sum _
        (fun k _ => integrable_absDefect rX rY hX hY k)]

/-- Total variation of the complex-current difference obeys the same
constant-one trine bound. -/
theorem integral_complexDensity_sub_norm_le_defect
    (phase : Fin 3 → ℂ) (hphase : ∀ k, ‖phase k‖ = 1)
    (rX rY : Fin 3 → Ω → ℝ)
    (hX : ∀ k, Integrable (rX k) μ) (hY : ∀ k, Integrable (rY k) μ) :
    ∫ ω, ‖complexDensity phase rX ω - complexDensity phase rY ω‖ ∂μ ≤
      trineTransportDefect rX rY μ := by
  have hright := integrable_defectSum rX rY hX hY
  have hleft : Integrable
      (fun ω => ‖complexDensity phase rX ω - complexDensity phase rY ω‖) μ :=
    ((integrable_complexDensity phase rX hX).sub
      (integrable_complexDensity phase rY hY)).norm
  calc
    ∫ ω, ‖complexDensity phase rX ω - complexDensity phase rY ω‖ ∂μ ≤
        ∫ ω, ∑ k, |rX k ω - rY k ω| ∂μ :=
      integral_mono_ae hleft hright
        (Filter.Eventually.of_forall fun ω =>
          complexDensity_sub_norm_le phase hphase rX rY ω)
    _ = trineTransportDefect rX rY μ := by
      simp [trineTransportDefect, integral_finset_sum _
        (fun k _ => integrable_absDefect rX rY hX hY k)]

/-- The transported slack has the exact manuscript factor `3`. -/
theorem integral_slackDensity_sub_abs_le_three_defect
    (phase : Fin 3 → ℂ) (hphase : ∀ k, ‖phase k‖ = 1)
    (rX rY : Fin 3 → Ω → ℝ)
    (hX : ∀ k, Integrable (rX k) μ) (hY : ∀ k, Integrable (rY k) μ) :
    ∫ ω, |slackDensity phase rX ω - slackDensity phase rY ω| ∂μ ≤
      3 * trineTransportDefect rX rY μ := by
  have hright := (integrable_defectSum rX rY hX hY).const_mul 3
  have hleft : Integrable
      (fun ω => |slackDensity phase rX ω - slackDensity phase rY ω|) μ :=
    ((integrable_slackDensity phase rX hX).sub
      (integrable_slackDensity phase rY hY)).abs
  calc
    ∫ ω, |slackDensity phase rX ω - slackDensity phase rY ω| ∂μ ≤
        ∫ ω, 3 * ∑ k, |rX k ω - rY k ω| ∂μ :=
      integral_mono_ae hleft hright
        (Filter.Eventually.of_forall fun ω =>
          slackDensity_sub_abs_le_three phase hphase rX rY ω)
    _ = 3 * trineTransportDefect rX rY μ := by
      rw [integral_const_mul]
      simp [trineTransportDefect, integral_finset_sum _
        (fun k _ => integrable_absDefect rX rY hX hY k)]

/-- Total-variation duality for every bounded complex payoff. -/
theorem bounded_payoff_transport
    (phase : Fin 3 → ℂ) (hphase : ∀ k, ‖phase k‖ = 1)
    (rX rY : Fin 3 → Ω → ℝ)
    (hX : ∀ k, Integrable (rX k) μ) (hY : ∀ k, Integrable (rY k) μ)
    (A : Ω → ℂ) (hAmeas : AEStronglyMeasurable A μ)
    (M : ℝ) (hM : 0 ≤ M) (hA : ∀ ω, ‖A ω‖ ≤ M) :
    ‖∫ ω, (complexDensity phase rX ω - complexDensity phase rY ω) * A ω ∂μ‖ ≤
      M * trineTransportDefect rX rY μ := by
  have hdiff : Integrable
      (fun ω => complexDensity phase rX ω - complexDensity phase rY ω) μ :=
    (integrable_complexDensity phase rX hX).sub
      (integrable_complexDensity phase rY hY)
  have hprod : Integrable
      (fun ω => (complexDensity phase rX ω - complexDensity phase rY ω) * A ω) μ :=
    hdiff.mul_bdd hAmeas (Filter.Eventually.of_forall hA)
  have hbound : Integrable
      (fun ω => ‖complexDensity phase rX ω - complexDensity phase rY ω‖ * M) μ :=
    hdiff.norm.mul_const M
  calc
    ‖∫ ω, (complexDensity phase rX ω - complexDensity phase rY ω) * A ω ∂μ‖ ≤
        ∫ ω, ‖complexDensity phase rX ω - complexDensity phase rY ω‖ * M ∂μ := by
      calc
        _ ≤ ∫ ω, ‖(complexDensity phase rX ω - complexDensity phase rY ω) *
              A ω‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ ω, ‖complexDensity phase rX ω - complexDensity phase rY ω‖ * M ∂μ := by
          apply integral_mono_ae
          · exact hprod.norm
          · exact hbound
          · exact Filter.Eventually.of_forall fun ω => by
              change ‖(complexDensity phase rX ω - complexDensity phase rY ω) * A ω‖ ≤ _
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hA ω) (norm_nonneg _)
    _ = M * ∫ ω, ‖complexDensity phase rX ω - complexDensity phase rY ω‖ ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext ω
      ring
    _ ≤ M * trineTransportDefect rX rY μ :=
      mul_le_mul_of_nonneg_left
        (integral_complexDensity_sub_norm_le_defect phase hphase rX rY hX hY) hM

end TrineMeasureTransport
end NCG
