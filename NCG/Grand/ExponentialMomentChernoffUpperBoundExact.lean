/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExponentialTiltLocalLowerBoundExact

/-!
# Chernoff upper bounds from concrete exponential moments

This file proves exponential Markov bounds directly for real measures and
then inserts a normalized-log-moment limit.  It supplies both upper and lower
half-line estimates in the exact scaling used by the Gartner--Ellis theorem.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.ExponentialMomentChernoffUpperBound

open NCG.ExponentialTiltMeasure
open NCG.ExponentialTiltLocalLowerBound
open NCG.SCGFExponentialTiltConcentration

/-- Generic exponential Markov inequality on a measurable set. -/
theorem originalMass_set_le_exponentialMoment
    (mu : Measure ℝ) (n : ℕ) (q threshold : ℝ) (s : Set ℝ)
    (hs : MeasurableSet s)
    (hbound : ∀ x ∈ s, threshold ≤ q * x)
    (hq : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) mu)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu) :
    originalMass mu s ≤
      Real.exp (-(n : ℝ) * threshold) * exponentialMoment mu n q := by
  let c : ℝ := Real.exp (-(n : ℝ) * threshold)
  let f : ℝ → ℝ := fun x => Real.exp ((n : ℝ) * q * x)
  have hcf : IntegrableOn (fun x => c * f x) s mu :=
    (hq.const_mul c).integrableOn
  have hpoint : ∀ x ∈ s, (1 : ℝ) ≤ c * f x := by
    intro x hx
    rw [← Real.exp_zero, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hb := hbound x hx
    nlinarith
  have hset : originalMass mu s ≤ c * ∫ x in s, f x ∂mu := by
    unfold originalMass
    calc
      (∫ _ in s, (1 : ℝ) ∂mu) ≤ ∫ x in s, c * f x ∂mu :=
        MeasureTheory.setIntegral_mono_on hone.integrableOn hcf hs hpoint
      _ = c * ∫ x in s, f x ∂mu := by
        exact MeasureTheory.integral_const_mul _ _
  have hrestrict : (∫ x in s, f x ∂mu) ≤ ∫ x, f x ∂mu := by
    exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _) hq
  calc
    originalMass mu s ≤ c * ∫ x in s, f x ∂mu := hset
    _ ≤ c * ∫ x, f x ∂mu :=
      mul_le_mul_of_nonneg_left hrestrict (Real.exp_nonneg _)
    _ = Real.exp (-(n : ℝ) * threshold) *
        exponentialMoment mu n q := rfl

/-- Upper half-line Chernoff bound for a nonnegative tilt. -/
theorem originalMass_Ici_le
    (mu : Measure ℝ) (n : ℕ) (q b : ℝ) (hq0 : 0 ≤ q)
    (hq : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) mu)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu) :
    originalMass mu (Set.Ici b) ≤
      Real.exp (-(n : ℝ) * (q * b)) * exponentialMoment mu n q := by
  apply originalMass_set_le_exponentialMoment mu n q (q * b)
    (Set.Ici b) measurableSet_Ici _ hq hone
  intro x hx
  exact mul_le_mul_of_nonneg_left hx hq0

/-- Lower half-line Chernoff bound for a nonpositive tilt. -/
theorem originalMass_Iic_le
    (mu : Measure ℝ) (n : ℕ) (q b : ℝ) (hq0 : q ≤ 0)
    (hq : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) mu)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu) :
    originalMass mu (Set.Iic b) ≤
      Real.exp (-(n : ℝ) * (q * b)) * exponentialMoment mu n q := by
  apply originalMass_set_le_exponentialMoment mu n q (q * b)
    (Set.Iic b) measurableSet_Iic _ hq hone
  intro x hx
  exact mul_le_mul_of_nonpos_left hx hq0

/-- A normalized-log-moment limit converts the upper half-line Chernoff
estimate into its eventual exponential form. -/
theorem eventually_originalMass_Ici_le
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (q b epsilon : ℝ)
    (hq0 : 0 ≤ q) (hepsilon : 0 < epsilon)
    (hint : ∀ n : ℕ, Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ n : ℕ, 0 < exponentialMoment (mu n) n q)
    (hlim : Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∀ᶠ n : ℕ in atTop,
      originalMass (mu n) (Set.Ici b) ≤
        Real.exp (-(n : ℝ) * (q * b - psi q - epsilon)) := by
  have hnear : Set.Iio (psi q + epsilon) ∈ 𝓝 (psi q) :=
    Iio_mem_nhds (lt_add_of_pos_right _ hepsilon)
  have hlog := hlim.eventually hnear
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn =>
      lt_of_lt_of_le Nat.zero_lt_one hn⟩
  filter_upwards [hlog, hnpos] with n hlogn hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hZ : exponentialMoment (mu n) n q ≤
      Real.exp ((n : ℝ) * (psi q + epsilon)) := by
    have hmul : Real.log (exponentialMoment (mu n) n q) <
        (n : ℝ) * (psi q + epsilon) := by
      have := (div_lt_iff₀ hnreal).mp hlogn
      nlinarith
    have hexp := Real.exp_lt_exp.mpr hmul
    rw [Real.exp_log (hpos n)] at hexp
    exact le_of_lt hexp
  calc
    originalMass (mu n) (Set.Ici b) ≤
        Real.exp (-(n : ℝ) * (q * b)) *
          exponentialMoment (mu n) n q :=
      originalMass_Ici_le (mu n) n q b hq0 (hint n) (hone n)
    _ ≤ Real.exp (-(n : ℝ) * (q * b)) *
        Real.exp ((n : ℝ) * (psi q + epsilon)) :=
      mul_le_mul_of_nonneg_left hZ (Real.exp_nonneg _)
    _ = Real.exp (-(n : ℝ) * (q * b - psi q - epsilon)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The corresponding eventual lower half-line estimate for a nonpositive
tilt. -/
theorem eventually_originalMass_Iic_le
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (q b epsilon : ℝ)
    (hq0 : q ≤ 0) (hepsilon : 0 < epsilon)
    (hint : ∀ n : ℕ, Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ n : ℕ, 0 < exponentialMoment (mu n) n q)
    (hlim : Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∀ᶠ n : ℕ in atTop,
      originalMass (mu n) (Set.Iic b) ≤
        Real.exp (-(n : ℝ) * (q * b - psi q - epsilon)) := by
  have hnear : Set.Iio (psi q + epsilon) ∈ 𝓝 (psi q) :=
    Iio_mem_nhds (lt_add_of_pos_right _ hepsilon)
  have hlog := hlim.eventually hnear
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn =>
      lt_of_lt_of_le Nat.zero_lt_one hn⟩
  filter_upwards [hlog, hnpos] with n hlogn hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hZ : exponentialMoment (mu n) n q ≤
      Real.exp ((n : ℝ) * (psi q + epsilon)) := by
    have hmul : Real.log (exponentialMoment (mu n) n q) <
        (n : ℝ) * (psi q + epsilon) := by
      have := (div_lt_iff₀ hnreal).mp hlogn
      nlinarith
    have hexp := Real.exp_lt_exp.mpr hmul
    rw [Real.exp_log (hpos n)] at hexp
    exact le_of_lt hexp
  calc
    originalMass (mu n) (Set.Iic b) ≤
        Real.exp (-(n : ℝ) * (q * b)) *
          exponentialMoment (mu n) n q :=
      originalMass_Iic_le (mu n) n q b hq0 (hint n) (hone n)
    _ ≤ Real.exp (-(n : ℝ) * (q * b)) *
        Real.exp ((n : ℝ) * (psi q + epsilon)) :=
      mul_le_mul_of_nonneg_left hZ (Real.exp_nonneg _)
    _ = Real.exp (-(n : ℝ) * (q * b - psi q - epsilon)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end NCG.ExponentialMomentChernoffUpperBound
