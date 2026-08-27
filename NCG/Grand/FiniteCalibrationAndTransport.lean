/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedWriterComparison
import NCG.Grand.CalibrationTransportAndPressureGauge
import NCG.Grand.TargetNativeCalibration

/-!
# Finite calibration, conditional means, and target transport

This file supplies the finite probability machinery used by the target-native
calibration layer.  In particular, orthogonality and the tower law are derived
from fibrewise conditional-mean balance; they are not theorem hypotheses.
-/

open Finset Filter Topology

namespace NCG
namespace FiniteCalibrationAndTransport

/-- Expectation against a finite real weight. -/
def expectation {Omega : Type*} [Fintype Omega]
    (mu f : Omega → ℝ) : ℝ :=
  ∑ omega, mu omega * f omega

/-- Squared residual of every declared multiplier-calibration equation. -/
def multiplierResidual {Omega H : Type*} [Fintype Omega] [Fintype H]
    (mu Y w : Omega → ℝ) (h : H → Omega → ℝ) : ℝ :=
  ∑ a, (expectation mu (fun omega ↦ h a omega * Y omega) -
    expectation mu (fun omega ↦ h a omega * w omega)) ^ 2

/-- The multiplier residual vanishes exactly when every calibration test
passes.  This is the non-tautological residual form of multiplier
calibration. -/
theorem multiplierResidual_eq_zero_iff {Omega H : Type*}
    [Fintype Omega] [Fintype H]
    (mu Y w : Omega → ℝ) (h : H → Omega → ℝ) :
    multiplierResidual mu Y w h = 0 ↔
      ∀ a, expectation mu (fun omega ↦ h a omega * Y omega) =
        expectation mu (fun omega ↦ h a omega * w omega) := by
  unfold multiplierResidual
  constructor
  · intro hzero a
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ ↦ sq_nonneg
        (expectation mu (fun omega ↦ h a omega * Y omega) -
          expectation mu (fun omega ↦ h a omega * w omega)))).mp hzero a
      (Finset.mem_univ a)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hterm)
  · intro hall
    apply Finset.sum_eq_zero
    intro a _
    rw [hall a, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
/-- Reweight a finite law by a multiplier. -/
noncomputable def reweightedLaw {Omega : Type*} [Fintype Omega]
    (mu h : Omega → ℝ) : Omega → ℝ :=
  fun omega ↦ mu omega * h omega / expectation mu h

/-- A nonnegative multiplier of positive mean defines a probability law. -/
theorem reweightedLaw_isProbability {Omega : Type*} [Fintype Omega]
    (mu h : Omega → ℝ)
    (hmu : ∀ omega, 0 ≤ mu omega) (hh : ∀ omega, 0 ≤ h omega)
    (hhmean : 0 < expectation mu h) :
    (∀ omega, 0 ≤ reweightedLaw mu h omega) ∧
      ∑ omega, reweightedLaw mu h omega = 1 := by
  constructor
  · intro omega
    exact div_nonneg (mul_nonneg (hmu omega) (hh omega)) hhmean.le
  · simp only [reweightedLaw, expectation]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hhmean)

/-- Multiplier calibration gives correctness under the normalized reweighted
law `d mu_h = h d mu / E_mu[h]`. -/
theorem calibrated_reweighted_expectation {Omega : Type*} [Fintype Omega]
    (mu h Y w : Omega → ℝ)
    (hcal : expectation mu (fun omega ↦ h omega * Y omega) =
      expectation mu (fun omega ↦ h omega * w omega)) :
    expectation (reweightedLaw mu h) Y =
      expectation (reweightedLaw mu h) w := by
  unfold expectation reweightedLaw at *
  calc
    ∑ omega, mu omega * h omega / (∑ omega, mu omega * h omega) * Y omega =
        (∑ omega, mu omega * h omega * Y omega) /
          (∑ omega, mu omega * h omega) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ = (∑ omega, mu omega * h omega * w omega) /
          (∑ omega, mu omega * h omega) := by
      congr 1
      simpa [mul_assoc] using hcal
    _ = ∑ omega, mu omega * h omega /
          (∑ omega, mu omega * h omega) * w omega := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro omega _
      ring

/-- A coarse function is a conditional mean when its residual has zero
weighted sum on every fibre of the retained record. -/
def IsConditionalMean {Omega B : Type*} [Fintype Omega] [Fintype B]
    [DecidableEq B] (C : Omega → B) (mu d : Omega → ℝ)
    (down : B → ℝ) : Prop :=
  ∀ b, ∑ omega ∈ Finset.univ.filter (fun omega ↦ C omega = b),
    mu omega * (d omega - down b) = 0

/-- Fibre balance implies the conditional-expectation tower identity. -/
theorem conditionalMean_tower {Omega B : Type*}
    [Fintype Omega] [Fintype B] [DecidableEq B]
    (C : Omega → B) (mu d : Omega → ℝ) (down : B → ℝ)
    (hdown : IsConditionalMean C mu d down) :
    expectation mu d = expectation mu (fun omega ↦ down (C omega)) := by
  have hres : expectation mu (fun omega ↦ d omega - down (C omega)) = 0 := by
    unfold expectation
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (g := C)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun omega ↦ mu omega * (d omega - down (C omega)))]
    apply Finset.sum_eq_zero
    intro b _
    calc
      ∑ omega ∈ Finset.univ.filter (fun omega ↦ C omega = b),
          mu omega * (d omega - down (C omega)) =
          ∑ omega ∈ Finset.univ.filter (fun omega ↦ C omega = b),
            mu omega * (d omega - down b) := by
        apply Finset.sum_congr rfl
        intro omega homega
        rw [(Finset.mem_filter.mp homega).2]
      _ = 0 := hdown b
  simp only [expectation, mul_sub, Finset.sum_sub_distrib] at hres
  exact sub_eq_zero.mp hres

/-- Fibre balance also implies orthogonality to every retained-record
function. -/
theorem conditionalMean_orthogonal {Omega B : Type*}
    [Fintype Omega] [Fintype B] [DecidableEq B]
    (C : Omega → B) (mu d : Omega → ℝ) (down phi : B → ℝ)
    (hdown : IsConditionalMean C mu d down) :
    expectation mu (fun omega ↦
      phi (C omega) * (d omega - down (C omega))) = 0 := by
  unfold expectation
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := C)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun omega ↦ mu omega *
      (phi (C omega) * (d omega - down (C omega))))]
  apply Finset.sum_eq_zero
  intro b _
  calc
    ∑ omega ∈ Finset.univ.filter (fun omega ↦ C omega = b),
        mu omega * (phi (C omega) * (d omega - down (C omega))) =
        phi b * ∑ omega ∈ Finset.univ.filter (fun omega ↦ C omega = b),
          mu omega * (d omega - down b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro omega homega
      rw [(Finset.mem_filter.mp homega).2]
      ring
    _ = 0 := by rw [hdown b, mul_zero]

/-- Conditional-expectation Pythagoras, derived from fibre balance. -/
theorem conditionalMean_pythagoras {Omega B : Type*}
    [Fintype Omega] [Fintype B] [DecidableEq B]
    (C : Omega → B) (mu d : Omega → ℝ) (down : B → ℝ)
    (hdown : IsConditionalMean C mu d down) :
    expectation mu (fun omega ↦ d omega ^ 2) =
      expectation mu (fun omega ↦ down (C omega) ^ 2) +
        expectation mu (fun omega ↦
          (d omega - down (C omega)) ^ 2) := by
  have horth := conditionalMean_orthogonal C mu d down down hdown
  simp only [expectation] at horth ⊢
  calc
    ∑ omega, mu omega * d omega ^ 2 =
        ∑ omega, (mu omega * down (C omega) ^ 2 +
          2 * (mu omega *
            (down (C omega) * (d omega - down (C omega)))) +
          mu omega * (d omega - down (C omega)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ = (∑ omega, mu omega * down (C omega) ^ 2) +
        ∑ omega, mu omega * (d omega - down (C omega)) ^ 2 := by
      simp only [Finset.sum_add_distrib]
      rw [show (∑ omega, 2 * (mu omega *
          (down (C omega) * (d omega - down (C omega))))) =
          2 * ∑ omega, mu omega *
            (down (C omega) * (d omega - down (C omega))) by
        rw [Finset.mul_sum]]
      rw [horth]
      ring

/-- Pushforward of a finite signed weight along a record map. -/
def pushforward {Omega B : Type*} [Fintype Omega] [DecidableEq B]
    (C : Omega → B) (mu : Omega → ℝ) (b : B) : ℝ :=
  ∑ omega ∈ Finset.univ.filter (fun omega ↦ C omega = b), mu omega

/-- Integration of a coarse function against a pushforward is integration of
its pullback against the original law. -/
theorem expectation_pushforward {Omega B : Type*}
    [Fintype Omega] [Fintype B] [DecidableEq B]
    (C : Omega → B) (mu : Omega → ℝ) (f : B → ℝ) :
    expectation (pushforward C mu) f =
      expectation mu (fun omega ↦ f (C omega)) := by
  unfold expectation pushforward
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := C)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun omega ↦ mu omega * f (C omega))]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega homega
  rw [(Finset.mem_filter.mp homega).2]

/-- The cutoff-law discrepancy is bounded by the sup norm times the exact
finite total variation of the pushforward signed law. -/
theorem pushforward_discrepancy_bound {Omega B : Type*}
    [Fintype Omega] [Fintype B] [DecidableEq B]
    (C : Omega → B) (mu : Omega → ℝ) (nu f : B → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hf : ∀ b, |f b| ≤ c) :
    |expectation mu (fun omega ↦ f (C omega)) - expectation nu f| ≤
      c * ∑ b, |pushforward C mu b - nu b| := by
  rw [← expectation_pushforward C mu f]
  have hid : expectation (pushforward C mu) f - expectation nu f =
      expectation (fun b ↦ pushforward C mu b - nu b) f := by
    simp [expectation, sub_mul, Finset.sum_sub_distrib]
  rw [hid]
  exact CalibrationTransportAndPressureGauge.expectation_abs_le_totalVariation
    (fun b ↦ pushforward C mu b - nu b) f c hc hf

/-- A conditional threshold probability satisfies the tower identity for the
joint law generated from the base law and the physical randomizer. -/
theorem threshold_probability_tower
    {Omega U : Type*} [Fintype Omega] [Fintype U]
    (mu : Omega → ℝ) (nu : Omega → U → ℝ)
    (ideal : Omega → U → ℝ) (thresholdMean : Omega → ℝ)
    (hthreshold : ∀ omega,
      thresholdMean omega = ∑ u, nu omega u * ideal omega u) :
    expectation mu thresholdMean =
      ∑ p : Omega × U, mu p.1 * nu p.1 p.2 * ideal p.1 p.2 := by
  unfold expectation
  calc
    ∑ omega, mu omega * thresholdMean omega =
        ∑ omega, ∑ u, mu omega * nu omega u * ideal omega u := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [hthreshold omega, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ p : Omega × U,
        mu p.1 * nu p.1 p.2 * ideal p.1 p.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product]

/-- Full comparator wrapper in which the tower equality is derived from the
conditional threshold probabilities. -/
theorem threshold_read_from_conditional_probability
    {Omega U : Type*} [Fintype Omega] [Fintype U]
    (mu : Omega → ℝ) (nu : Omega → U → ℝ)
    (q thresholdMean : Omega → ℝ) (kernel ideal : Omega → U → ℝ)
    (a b : ℝ)
    (hmu : ∀ omega, 0 ≤ mu omega)
    (hnu : ∀ omega u, 0 ≤ nu omega u)
    (hmass : ∑ omega, mu omega = 1)
    (hnuMass : ∀ omega, ∑ u, nu omega u = 1)
    (hthreshold : ∀ omega,
      thresholdMean omega = ∑ u, nu omega u * ideal omega u) :
    let joint : Omega × U → ℝ := fun p ↦ mu p.1 * nu p.1 p.2
    let EB := ∑ p : Omega × U, joint p * kernel p.1 p.2
    let Eq := expectation mu q
    let comparatorError := BoundedWriterComparison.weightedL2 joint
      (fun p ↦ kernel p.1 p.2 - ideal p.1 p.2)
    let thresholdError := BoundedWriterComparison.weightedL2 mu
      (fun omega ↦ thresholdMean omega - q omega)
    (EB - Eq =
        ∑ p : Omega × U, joint p *
          (kernel p.1 p.2 - ideal p.1 p.2) +
        expectation mu (fun omega ↦ thresholdMean omega - q omega)) ∧
      |a + (b - a) * EB -
        expectation mu (fun omega ↦ a + (b - a) * q omega)| ≤
        |b - a| * (comparatorError + thresholdError) := by
  dsimp only
  have hjointMass : ∑ p : Omega × U, mu p.1 * nu p.1 p.2 = 1 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    calc
      ∑ omega, ∑ u, mu omega * nu omega u =
          ∑ omega, mu omega * ∑ u, nu omega u := by
        apply Finset.sum_congr rfl
        intro omega _
        rw [Finset.mul_sum]
      _ = 1 := by simp [hnuMass, hmass]
  have htower := threshold_probability_tower mu nu ideal thresholdMean hthreshold
  exact BoundedWriterComparison.universal_bounded_writer_comparator
    mu (fun omega u ↦ mu omega * nu omega u) q thresholdMean kernel ideal a b
    hmu (fun omega u ↦ mul_nonneg (hmu omega) (hnu omega u)) hmass
    hjointMass (by
      simpa [expectation, BoundedWriterComparison.expectation] using htower)

/-- An affine conditional response with nonzero slope gives the displayed
writer-mean inversion. -/
theorem affine_mean_inversion (EY Ew alpha beta : ℝ) (hbeta : beta ≠ 0)
    (hresponse : EY = alpha + beta * Ew) :
    Ew = (EY - alpha) / beta := by
  apply (eq_div_iff hbeta).2
  linarith

/-- Any finite writer-value class strictly larger than its calibration bank
contains a held-out value. -/
theorem exists_heldOut_writerValue {W : Type*} [Fintype W]
    (anchors : Finset W) (hproper : anchors.card < Fintype.card W) :
    ∃ w, w ∉ anchors := by
  classical
  by_contra hnone
  push Not at hnone
  have hall : anchors = Finset.univ := Finset.eq_univ_of_forall hnone
  rw [hall, Finset.card_univ] at hproper
  omega

/-- Two distinct training anchors in a class with at least three writer values
leave an additional writer value as a held-out calibration row. -/
theorem two_anchors_leave_heldOut {W : Type*} [Fintype W] [DecidableEq W]
    (w0 w1 : W) (hne : w0 ≠ w1) (hthree : 2 < Fintype.card W) :
    ∃ w, w ∉ ({w0, w1} : Finset W) := by
  classical
  apply exists_heldOut_writerValue ({w0, w1} : Finset W)
  simpa [hne] using hthree
/-- If nested target intervals shrink to zero width and one endpoint is
Cauchy, then every selected scalar converges to their common endpoint limit. -/
theorem target_interval_converges
    (lower selected upper : ℕ → ℝ)
    (hsandwich : ∀ n, lower n ≤ selected n ∧ selected n ≤ upper n)
    (hwidth : Tendsto (fun n ↦ upper n - lower n) atTop (nhds 0))
    (hlower : CauchySeq lower) :
    ∃ L, Tendsto lower atTop (nhds L) ∧
      Tendsto selected atTop (nhds L) ∧ Tendsto upper atTop (nhds L) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hlower
  have hupper : Tendsto upper atTop (nhds L) := by
    have hsum := hL.add hwidth
    simpa [sub_add_cancel] using hsum
  refine ⟨L, hL, ?_, hupper⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hL hupper
    (fun n ↦ (hsandwich n).1) (fun n ↦ (hsandwich n).2)

end FiniteCalibrationAndTransport
end NCG
