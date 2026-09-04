/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GartnerEllisCompactUpperBoundExact

/-!
# Real-time Chernoff bounds and finite-cover aggregation

The exponential scale is an arbitrary nonnegative real horizon. Only the
physical nonnegative-time laws need be finite or have exponential moments;
no conditions on an artificial negative-time process are imposed.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace NCG.RealTimeExponentialUpperBound

open ExponentialTiltLocalLowerBound ExponentialMomentChernoffUpperBound
open FiniteExponentialCoverUpperBound GartnerEllisCompactUpperBound

noncomputable section

/-- The actual exponential moment at real speed `t`. -/
def moment (mu : Measure ℝ) (t q : ℝ) : ℝ := ∫ x : ℝ, Real.exp (t * q * x) ∂mu

/-- Normalized log moment at an arbitrary real horizon. -/
def logMoment (mu : ℝ → Measure ℝ) (t q : ℝ) : ℝ := Real.log (moment (mu t) t q) / t

/-- Exponential Markov inequality at any nonnegative real speed. -/
theorem mass_set_le_moment (mu : Measure ℝ) (t q threshold : ℝ) (ht : 0 ≤ t)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hbound : ∀ x ∈ s, threshold ≤ q * x)
    (hint : Integrable (fun x : ℝ => Real.exp (t * q * x)) mu)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu) :
    originalMass mu s ≤ Real.exp (-t * threshold) * moment mu t q := by
  have hb : ∀ x ∈ s, t * threshold ≤ (t * q) * x := by
    intro x hx
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound x hx) ht
  have h := originalMass_set_le_exponentialMoment mu 1 (t * q) (t * threshold) s hs hb
    (by simpa only [Nat.cast_one, one_mul] using hint) hone
  simpa [moment, ExponentialTiltMeasure.exponentialMoment, neg_mul] using h

/-- Fixed finite prefactors are absorbed at every sufficiently large real horizon. -/
theorem eventually_card_le_exp (m : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ t : ℝ in atTop, (m : ℝ) ≤ Real.exp (t * epsilon) := by
  have htend : Tendsto (fun t : ℝ => Real.exp (t * epsilon)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hepsilon)
  exact htend.eventually (eventually_ge_atTop (m : ℝ))

/-- Simultaneous real-time local estimates yield the finite-cover bound. -/
theorem eventually_mass_subset_finiteCover_le {ι : Type*}
    (mu : ℝ → Measure ℝ) (hfinite : ∀ t, 0 ≤ t → IsFiniteMeasure (mu t))
    (K : Set ℝ) (cover : Finset ι) (U : ι → Set ℝ)
    (A epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hK : K ⊆ ⋃ i ∈ cover, U i) (hKmeas : MeasurableSet K)
    (hUmeas : ∀ i ∈ cover, MeasurableSet (U i))
    (hlocal : ∀ i ∈ cover, ∀ᶠ t : ℝ in atTop,
      originalMass (mu t) (U i) ≤ Real.exp (-t * (A + epsilon))) :
    ∀ᶠ t : ℝ in atTop, originalMass (mu t) K ≤ Real.exp (-t * A) := by
  have hall := eventually_finset_forall atTop cover
    (fun t i => originalMass (mu t) (U i) ≤ Real.exp (-t * (A + epsilon))) hlocal
  have hcard := eventually_card_le_exp cover.card epsilon hepsilon
  filter_upwards [hall, hcard, eventually_ge_atTop (0 : ℝ)] with t ht hct ht0
  letI := hfinite t ht0
  calc
    originalMass (mu t) K = (mu t).real K := originalMass_eq_measureReal (mu t) K hKmeas
    _ ≤ (mu t).real (⋃ i ∈ cover, U i) := measureReal_mono hK (measure_ne_top _ _)
    _ ≤ ∑ i ∈ cover, (mu t).real (U i) := measureReal_biUnion_finset_le cover U
    _ = ∑ i ∈ cover, originalMass (mu t) (U i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [originalMass_eq_measureReal (mu t) (U i) (hUmeas i hi)]
    _ ≤ ∑ _i ∈ cover, Real.exp (-t * (A + epsilon)) :=
      Finset.sum_le_sum fun i hi => ht i hi
    _ = (cover.card : ℝ) * Real.exp (-t * (A + epsilon)) := by simp
    _ ≤ Real.exp (t * epsilon) * Real.exp (-t * (A + epsilon)) :=
      mul_le_mul_of_nonneg_right hct (Real.exp_nonneg _)
    _ = Real.exp (-t * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- One affine Legendre-witness neighborhood obeys the real-time Chernoff bound. -/
theorem eventually_mass_affineTiltNeighborhood_le
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (q A epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hint : ∀ t, 0 ≤ t → Integrable (fun x : ℝ => Real.exp (t * q * x)) (mu t))
    (hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t))
    (hpos : ∀ t, 0 ≤ t → 0 < moment (mu t) t q)
    (hlim : Tendsto (fun t => logMoment mu t q) atTop (𝓝 (psi q))) :
    ∀ᶠ t : ℝ in atTop,
      originalMass (mu t) (affineTiltNeighborhood psi q (A + 2 * epsilon)) ≤
        Real.exp (-t * (A + epsilon)) := by
  have hlog := hlim.eventually (Iio_mem_nhds (lt_add_of_pos_right (psi q) hepsilon))
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with t hlogt ht1
  have ht : 0 < t := by linarith
  have hZ : moment (mu t) t q ≤ Real.exp (t * (psi q + epsilon)) := by
    change Real.log (moment (mu t) t q) / t < psi q + epsilon at hlogt
    have hm : Real.log (moment (mu t) t q) < t * (psi q + epsilon) := by
      simpa only [mul_comm] using (div_lt_iff₀ ht).mp hlogt
    have he := Real.exp_lt_exp.mpr hm
    rw [Real.exp_log (hpos t ht.le)] at he
    exact he.le
  calc
    originalMass (mu t) (affineTiltNeighborhood psi q (A + 2 * epsilon)) ≤
        Real.exp (-t * (psi q + (A + 2 * epsilon))) * moment (mu t) t q := by
      apply mass_set_le_moment (mu t) t q (psi q + (A + 2 * epsilon)) ht.le
        (affineTiltNeighborhood psi q (A + 2 * epsilon))
        (isOpen_affineTiltNeighborhood psi q (A + 2 * epsilon)).measurableSet
        (fun _ hx => hx.le) (hint t ht.le) (hone t ht.le)
    _ ≤ Real.exp (-t * (psi q + (A + 2 * epsilon))) *
        Real.exp (t * (psi q + epsilon)) :=
      mul_le_mul_of_nonneg_left hZ (Real.exp_nonneg _)
    _ = Real.exp (-t * (A + epsilon)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end

end NCG.RealTimeExponentialUpperBound
