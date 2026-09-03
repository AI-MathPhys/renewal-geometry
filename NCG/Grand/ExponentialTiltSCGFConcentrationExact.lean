/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExponentialTiltMeasureExact

/-!
# SCGF concentration for concrete exponentially tilted laws

This file identifies the moment ratio in the concrete Chernoff estimate with
the normalized-log-moment envelope used by the Gartner--Ellis argument.  It
then upgrades the abstract envelope convergence to concentration statements
for actual tilted masses of upper and lower half-lines.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.ExponentialTiltSCGFConcentration

open NCG.ExponentialTiltMeasure
open NCG.SCGFExponentialTiltConcentration

/-- At positive integer speed, the exponential-moment ratio is exactly the
SCGF Chernoff envelope. -/
theorem momentRatio_eq_tiltedChernoffEnvelope
    (Z : ℕ → ℝ → ℝ) (n : ℕ) (k q b : ℝ) (hn : 0 < n)
    (hk : 0 < Z n k) (hkq : 0 < Z n (k + q)) :
    Real.exp (-(n : ℝ) * q * b) * Z n (k + q) / Z n k =
      tiltedChernoffEnvelope Z k q b n := by
  rw [← Real.exp_log hkq, ← Real.exp_log hk]
  rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  unfold tiltedChernoffEnvelope normalizedLogMoment
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- The concrete upper tilted tail is bounded by the SCGF envelope. -/
theorem tiltedMass_Ici_le_envelope
    (mu : Measure ℝ) (n : ℕ) (k q b : ℝ) (hn : 0 < n) (hq : 0 ≤ q)
    (hk : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) mu)
    (hkq : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * (k + q) * x)) mu)
    (hpos : ∀ u : ℝ, 0 < exponentialMoment mu n u) :
    tiltedMass mu n k (Set.Ici b) ≤
      tiltedChernoffEnvelope (fun m u => exponentialMoment mu m u)
        k q b n := by
  rw [← momentRatio_eq_tiltedChernoffEnvelope
    (fun m u => exponentialMoment mu m u) n k q b hn (hpos k) (hpos (k + q))]
  exact tiltedMass_Ici_le mu n k q b hq hk hkq (hpos k)

/-- The concrete lower tilted tail is bounded by the SCGF envelope. -/
theorem tiltedMass_Iic_le_envelope
    (mu : Measure ℝ) (n : ℕ) (k q b : ℝ) (hn : 0 < n) (hq : q ≤ 0)
    (hk : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) mu)
    (hkq : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * (k + q) * x)) mu)
    (hpos : ∀ u : ℝ, 0 < exponentialMoment mu n u) :
    tiltedMass mu n k (Set.Iic b) ≤
      tiltedChernoffEnvelope (fun m u => exponentialMoment mu m u)
        k q b n := by
  rw [← momentRatio_eq_tiltedChernoffEnvelope
    (fun m u => exponentialMoment mu m u) n k q b hn (hpos k) (hpos (k + q))]
  exact tiltedMass_Iic_le mu n k q b hq hk hkq (hpos k)

/-- Differentiability of the SCGF yields concentration of a concrete tilted
law above the exposed value. -/
theorem exists_upper_tiltedMass_tendsto_zero
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (k a delta : ℝ)
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta)
    (hint : ∀ (n : ℕ) (q : ℝ), Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hpos : ∀ (n : ℕ) (q : ℝ), 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∃ q : ℝ, 0 < q ∧
      Tendsto (fun n => tiltedMass (mu n) n k (Set.Ici (a + delta)))
        atTop (𝓝 0) := by
  obtain ⟨q, hq, henv⟩ := exists_upper_tilt_with_concentration
    hderiv hdelta hlim
  refine ⟨q, hq, ?_⟩
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      tiltedMass_nonnegative (mu n) n k _ (hpos n k)
  · have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.2 ⟨1, fun n hn =>
        lt_of_lt_of_le Nat.zero_lt_one hn⟩
    filter_upwards [hnpos] with n hn
    exact tiltedMass_Ici_le_envelope (mu n) n k q (a + delta) hn hq.le
      (hint n k) (hint n (k + q)) (hpos n)
  · exact henv

/-- Differentiability of the SCGF yields concentration of a concrete tilted
law below the exposed value. -/
theorem exists_lower_tiltedMass_tendsto_zero
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (k a delta : ℝ)
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta)
    (hint : ∀ (n : ℕ) (q : ℝ), Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hpos : ∀ (n : ℕ) (q : ℝ), 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∃ q : ℝ, q < 0 ∧
      Tendsto (fun n => tiltedMass (mu n) n k (Set.Iic (a - delta)))
        atTop (𝓝 0) := by
  obtain ⟨q, hq, henv⟩ := exists_lower_tilt_with_concentration
    hderiv hdelta hlim
  refine ⟨q, hq, ?_⟩
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      tiltedMass_nonnegative (mu n) n k _ (hpos n k)
  · have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.2 ⟨1, fun n hn =>
        lt_of_lt_of_le Nat.zero_lt_one hn⟩
    filter_upwards [hnpos] with n hn
    exact tiltedMass_Iic_le_envelope (mu n) n k q (a - delta) hn hq.le
      (hint n k) (hint n (k + q)) (hpos n)
  · exact henv

end NCG.ExponentialTiltSCGFConcentration
