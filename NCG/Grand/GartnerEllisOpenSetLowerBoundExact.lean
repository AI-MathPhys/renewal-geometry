/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SCGFExponentialTightnessExact

/-!
# Gartner--Ellis lower bounds on open sets

The exposed-point window estimate is upgraded to an arbitrary open set by
choosing a small interval around the exposed point.  The interval is chosen
small enough that the finite-window error is absorbed into the prescribed
asymptotic error.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.GartnerEllisOpenSetLowerBound

open NCG.ExponentialTiltMeasure
open NCG.ExponentialTiltLocalLowerBound
open NCG.SCGFExponentialTiltConcentration
open NCG.SCGFExponentialTightness

/-- Every point of a real open set contains a symmetric interval whose tilt
cost `|k| * delta` is less than any prescribed positive error. -/
theorem exists_Ioo_subset_with_tilt_error
    (G : Set ℝ) (a k epsilon : ℝ) (hG : IsOpen G) (ha : a ∈ G)
    (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ Set.Ioo (a - delta) (a + delta) ⊆ G ∧
      |k| * delta < epsilon := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hG a ha
  let d : ℝ := min (r / 2) (epsilon / (2 * (|k| + 1)))
  have hden : 0 < 2 * (|k| + 1) := by positivity
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min (half_pos hr) (div_pos hepsilon hden)
  have hd_r : d ≤ r / 2 := min_le_left _ _
  have hrhalf : r / 2 < r := by linarith
  have hsubset : Set.Ioo (a - d) (a + d) ⊆ G := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |x - a| < d := by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact (habs.trans_le hd_r).trans hrhalf
  have hd_eps : d ≤ epsilon / (2 * (|k| + 1)) := min_le_right _ _
  have hfactor : 0 < epsilon / (2 * (|k| + 1)) := div_pos hepsilon hden
  have htilt : |k| * d < epsilon := by
    calc
      |k| * d ≤ |k| * (epsilon / (2 * (|k| + 1))) :=
        mul_le_mul_of_nonneg_left hd_eps (abs_nonneg k)
      _ < (|k| + 1) * (epsilon / (2 * (|k| + 1))) :=
        mul_lt_mul_of_pos_right (lt_add_one _) hfactor
      _ = epsilon / 2 := by
        field_simp
      _ < epsilon := by linarith
  exact ⟨d, hd, hsubset, htilt⟩

/-- Concrete Gartner--Ellis lower bound on an arbitrary open set at each
exposed point contained in the set. -/
theorem eventually_originalMass_open_lower_bound_at_exposed
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (G : Set ℝ)
    (k a epsilon : ℝ)
    (hG : IsOpen G) (ha : a ∈ G)
    (hconv : ConvexOn ℝ Set.univ psi)
    (hderiv : HasDerivAt psi a k) (hepsilon : 0 < epsilon)
    (hint : ∀ (n : ℕ) (q : ℝ), Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ (n : ℕ) (q : ℝ), 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) * (NCG.rateFunction psi a + epsilon)) ≤
        originalMass (mu n) G := by
  obtain ⟨delta, hdelta, hwindow, htilt⟩ :=
    exists_Ioo_subset_with_tilt_error G a k (epsilon / 2)
      hG ha (half_pos hepsilon)
  have hlower := eventually_originalMass_Ioo_lower_bound_rateFunction
    mu psi k a delta (epsilon / 2) hconv hderiv hdelta
      (half_pos hepsilon) hint hone hpos hlim
  filter_upwards [hlower] with n hn
  have hcost : NCG.rateFunction psi a + |k| * delta + epsilon / 2 ≤
      NCG.rateFunction psi a + epsilon := by
    linarith
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    Real.exp (-(n : ℝ) * (NCG.rateFunction psi a + epsilon)) ≤
        Real.exp (-(n : ℝ) *
          (NCG.rateFunction psi a + |k| * delta + epsilon / 2)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hcost (neg_nonpos.mpr hnnonneg)
    _ ≤ originalMass (mu n) (Set.Ioo (a - delta) (a + delta)) := hn
    _ ≤ originalMass (mu n) G :=
      originalMass_mono (mu n) _ _ hwindow (hone n)

/-- Normalized-log form of the open-set lower bound at an exposed point. -/
theorem eventually_normalizedLog_originalMass_open_ge_at_exposed
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (G : Set ℝ)
    (k a epsilon : ℝ)
    (hG : IsOpen G) (ha : a ∈ G)
    (hconv : ConvexOn ℝ Set.univ psi)
    (hderiv : HasDerivAt psi a k) (hepsilon : 0 < epsilon)
    (hint : ∀ (n : ℕ) (q : ℝ), Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ (n : ℕ) (q : ℝ), 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∀ᶠ n : ℕ in atTop,
      -(NCG.rateFunction psi a + epsilon) ≤
        Real.log (originalMass (mu n) G) / n := by
  have hlower := eventually_originalMass_open_lower_bound_at_exposed
    mu psi G k a epsilon hG ha hconv hderiv hepsilon hint hone hpos hlim
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn =>
      lt_of_lt_of_le Nat.zero_lt_one hn⟩
  filter_upwards [hlower, hnpos] with n hlowern hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_le_log (Real.exp_pos _)
    hlowern
  rw [Real.log_exp] at hlog
  apply (le_div_iff₀ hnreal).2
  nlinarith

end NCG.GartnerEllisOpenSetLowerBound
