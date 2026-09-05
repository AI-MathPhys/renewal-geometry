/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RealTimeTiltedConcentrationExact

/-!
# Local and open-set exponential lower bounds at all real horizons

Tilted-window concentration and the exact change-of-measure estimate give
the sharp local rate at every derivative slope. The proof uses arbitrary
real horizons and imposes integrability only at nonnegative times.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace NCG.RealTimeTiltedLowerBound

open RealTimeExponentialUpperBound RealTimeTiltedConcentration
open ExponentialTiltLocalLowerBound GartnerEllisOpenSetLowerBound

noncomputable section

/-- Real-time scalar change-of-measure compiler from a concentrated tilted mass. -/
theorem eventually_originalMass_lower_bound
    (mu : ℝ → Measure ℝ) (P Q : ℝ → ℝ) (psi : ℝ → ℝ) (k cost epsilon : ℝ)
    (hpos : ∀ t, 0 ≤ t → 0 < moment (mu t) t k)
    (hlim : Tendsto (fun t => logMoment mu t k) atTop (𝓝 (psi k)))
    (hQ : Tendsto Q atTop (𝓝 1))
    (hchange : ∀ t, 0 ≤ t → Real.exp (-t * cost) * moment (mu t) t k * Q t ≤ P t)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ t : ℝ in atTop, Real.exp (-t * (cost - psi k + epsilon)) ≤ P t := by
  have heps : 0 < epsilon / 2 := half_pos hepsilon
  have hlog := hlim.eventually (Ioi_mem_nhds (sub_lt_self (psi k) heps))
  have hZlower : ∀ᶠ t : ℝ in atTop,
      Real.exp (t * (psi k - epsilon / 2)) ≤ moment (mu t) t k := by
    filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with t hlogt ht1
    have ht : 0 < t := by linarith
    change psi k - epsilon / 2 < Real.log (moment (mu t) t k) / t at hlogt
    have hm : t * (psi k - epsilon / 2) < Real.log (moment (mu t) t k) := by
      simpa only [mul_comm] using (lt_div_iff₀ ht).mp hlogt
    have he := Real.exp_lt_exp.mpr hm
    rw [Real.exp_log (hpos t ht.le)] at he
    exact he.le
  have hdecay : Tendsto (fun t : ℝ => Real.exp (t * (-(epsilon / 2)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (neg_neg_of_pos heps))
  have hQhalf := hQ.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hdecayHalf := hdecay.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hZlower, hQhalf, hdecayHalf, eventually_ge_atTop (0 : ℝ)]
    with t hZt hQt hdt ht0
  have hQlower : Real.exp (t * (-(epsilon / 2))) ≤ Q t := (lt_trans hdt hQt).le
  calc
    Real.exp (-t * (cost - psi k + epsilon)) =
        Real.exp (-t * cost) * Real.exp (t * (psi k - epsilon / 2)) *
          Real.exp (t * (-(epsilon / 2))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-t * cost) * moment (mu t) t k * Real.exp (t * (-(epsilon / 2))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZt (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ ≤ Real.exp (-t * cost) * moment (mu t) t k * Q t :=
      mul_le_mul_of_nonneg_left hQlower (mul_nonneg (Real.exp_nonneg _) (hpos t ht0).le)
    _ ≤ P t := hchange t ht0

/-- The local lower estimate around every derivative slope, at all real horizons. -/
theorem eventually_mass_Ioo_lower_bound
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (k a delta epsilon : ℝ)
    (hd : HasDerivAt psi a k) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hint : ∀ t, 0 ≤ t → ∀ u, Integrable (fun x : ℝ => Real.exp (t * u * x)) (mu t))
    (hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ u, 0 < moment (mu t) t u)
    (hlim : ∀ u, Tendsto (fun t => logMoment mu t u) atTop (𝓝 (psi u))) :
    ∀ᶠ t : ℝ in atTop,
      Real.exp (-t * (k * a + |k| * delta - psi k + epsilon)) ≤
        originalMass (mu t) (Ioo (a - delta) (a + delta)) := by
  apply eventually_originalMass_lower_bound mu
    (fun t => originalMass (mu t) (Ioo (a - delta) (a + delta)))
    (fun t => tiltedMass (mu t) t k (Ioo (a - delta) (a + delta)))
    psi k (k * a + |k| * delta) epsilon
    (fun t ht => hpos t ht k) (hlim k)
    (tiltedWindow_tendsto_one mu psi k a delta hd hdelta hint hpos hlim) _ hepsilon
  intro t ht
  exact changeOfMeasure (mu t) t k (k * a + |k| * delta) ht
    (Ioo (a - delta) (a + delta)) measurableSet_Ioo
    (tilt_on_Ioo_le_center_add_abs_error k a delta)
    (hint t ht k) (hone t ht) (hpos t ht k)

/-- Open-set lower bound at a derivative slope for every sufficiently large real time. -/
theorem eventually_mass_open_lower_bound_at_derivative
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (G : Set ℝ) (k a epsilon : ℝ)
    (hG : IsOpen G) (ha : a ∈ G) (hd : HasDerivAt psi a k) (hepsilon : 0 < epsilon)
    (hint : ∀ t, 0 ≤ t → ∀ u, Integrable (fun x : ℝ => Real.exp (t * u * x)) (mu t))
    (hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ u, 0 < moment (mu t) t u)
    (hlim : ∀ u, Tendsto (fun t => logMoment mu t u) atTop (𝓝 (psi u))) :
    ∀ᶠ t : ℝ in atTop, Real.exp (-t * (k * a - psi k + epsilon)) ≤ originalMass (mu t) G := by
  obtain ⟨delta, hdelta, hsubset, herror⟩ :=
    exists_Ioo_subset_with_tilt_error G a k (epsilon / 2) hG ha (half_pos hepsilon)
  have hlocal := eventually_mass_Ioo_lower_bound mu psi k a delta (epsilon / 2)
    hd hdelta (half_pos hepsilon) hint hone hpos hlim
  filter_upwards [hlocal, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have hcost : k * a + |k| * delta - psi k + epsilon / 2 ≤ k * a - psi k + epsilon := by
    linarith
  calc
    Real.exp (-t * (k * a - psi k + epsilon)) ≤
        Real.exp (-t * (k * a + |k| * delta - psi k + epsilon / 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hcost (neg_nonpos.mpr ht0))
    _ ≤ originalMass (mu t) (Ioo (a - delta) (a + delta)) := ht
    _ ≤ originalMass (mu t) G :=
      SCGFExponentialTightness.originalMass_mono (mu t) _ _ hsubset (hone t ht0)

end

end NCG.RealTimeTiltedLowerBound
