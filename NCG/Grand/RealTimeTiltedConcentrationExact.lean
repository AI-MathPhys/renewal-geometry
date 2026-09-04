/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RealTimeExponentialUpperBoundExact

/-!
# Exponential-tilt concentration at arbitrary real horizons

The concrete tilted masses are ratios of integrals. Exact finite-measure
identities are reused at unit speed with tilt `t*k`; the limiting argument
is carried out at all real horizons. Differentiability of the limiting
pressure supplies the strict gaps needed for window concentration.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace NCG.RealTimeTiltedConcentration

open RealTimeExponentialUpperBound
open ExponentialTiltLocalLowerBound DifferentiableSCGFTiltGap

noncomputable section

/-- Actual exponentially tilted mass at real speed. -/
def tiltedMass (mu : Measure ℝ) (t k : ℝ) (s : Set ℝ) : ℝ :=
  (∫ x : ℝ in s, Real.exp (t * k * x) ∂mu) / moment mu t k

/-- Positivity of tilted masses from the genuine positive normalizer. -/
theorem tiltedMass_nonneg (mu : Measure ℝ) (t k : ℝ) (s : Set ℝ)
    (hpos : 0 < moment mu t k) : 0 ≤ tiltedMass mu t k s := by
  exact div_nonneg (integral_nonneg fun _ => Real.exp_nonneg _) hpos.le

/-- The Chernoff ratio bound at nonnegative real speed. -/
theorem tiltedMass_set_le_ratio
    (mu : Measure ℝ) (t k q b : ℝ) (ht : 0 ≤ t) (s : Set ℝ)
    (hs : MeasurableSet s) (hset : ∀ x ∈ s, 0 ≤ q * (x - b))
    (hk : Integrable (fun x : ℝ => Real.exp (t * k * x)) mu)
    (hkq : Integrable (fun x : ℝ => Real.exp (t * (k + q) * x)) mu)
    (hpos : 0 < moment mu t k) :
    tiltedMass mu t k s ≤ Real.exp (-t * q * b) * moment mu t (k + q) / moment mu t k := by
  have hsum : t * k + t * q = t * (k + q) := by ring
  have hb : ∀ x ∈ s, 0 ≤ (t * q) * (x - b) := by
    intro x hx
    simpa only [mul_assoc] using mul_nonneg ht (hset x hx)
  have h := ExponentialTiltMeasure.tiltedMass_set_le_moment_ratio
    mu 1 (t * k) (t * q) b s hs hb
    (by simpa only [Nat.cast_one, one_mul] using hk)
    (by simpa only [Nat.cast_one, one_mul, hsum] using hkq)
    (by simpa only [ExponentialTiltMeasure.exponentialMoment, Nat.cast_one, one_mul,
      moment] using hpos)
  simpa only [tiltedMass, moment, ExponentialTiltMeasure.tiltedMass,
    ExponentialTiltMeasure.exponentialMoment, Nat.cast_one, one_mul, neg_one_mul,
    hsum, neg_mul] using h

/-- Exact open-window decomposition under the real-speed tilted law. -/
theorem tiltedMass_Ioo_eq_one_sub_tails
    (mu : Measure ℝ) (t k lower upper : ℝ) (hlu : lower < upper)
    (hk : Integrable (fun x : ℝ => Real.exp (t * k * x)) mu)
    (hpos : 0 < moment mu t k) :
    tiltedMass mu t k (Ioo lower upper) =
      1 - tiltedMass mu t k (Iic lower) - tiltedMass mu t k (Ici upper) := by
  have h := ExponentialTiltWindowConcentration.tiltedMass_Ioo_eq_one_sub_tails
    mu 1 (t * k) lower upper hlu
    (by simpa only [Nat.cast_one, one_mul] using hk)
    (by simpa only [ExponentialTiltMeasure.exponentialMoment, Nat.cast_one, one_mul,
      moment] using hpos)
  simpa only [tiltedMass, moment, ExponentialTiltMeasure.tiltedMass,
    ExponentialTiltMeasure.exponentialMoment, Nat.cast_one, one_mul] using h

/-- The exact real-speed change-of-measure lower estimate. -/
theorem changeOfMeasure
    (mu : Measure ℝ) (t k cost : ℝ) (ht : 0 ≤ t) (s : Set ℝ)
    (hs : MeasurableSet s) (hbound : ∀ x ∈ s, k * x ≤ cost)
    (hk : Integrable (fun x : ℝ => Real.exp (t * k * x)) mu)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu)
    (hpos : 0 < moment mu t k) :
    Real.exp (-t * cost) * moment mu t k * tiltedMass mu t k s ≤ originalMass mu s := by
  have hb : ∀ x ∈ s, (t * k) * x ≤ t * cost := by
    intro x hx
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound x hx) ht
  have h := exponentialMoment_mul_tiltedMass_le_originalMass
    mu 1 (t * k) (t * cost) s hs hb
    (by simpa only [Nat.cast_one, one_mul] using hk) hone
    (by simpa only [ExponentialTiltMeasure.exponentialMoment, Nat.cast_one, one_mul,
      moment] using hpos)
  simpa only [tiltedMass, moment, ExponentialTiltMeasure.tiltedMass,
    ExponentialTiltMeasure.exponentialMoment, Nat.cast_one, one_mul, neg_one_mul,
    neg_mul] using h

/-- The real-time Chernoff envelope expressed through normalized log moments. -/
def envelope (mu : ℝ → Measure ℝ) (k q b t : ℝ) : ℝ :=
  Real.exp (t * (logMoment mu t (k + q) - logMoment mu t k - q * b))

theorem ratio_eq_envelope (mu : ℝ → Measure ℝ) (k q b t : ℝ) (ht : 0 < t)
    (hk : 0 < moment (mu t) t k) (hkq : 0 < moment (mu t) t (k + q)) :
    Real.exp (-t * q * b) * moment (mu t) t (k + q) / moment (mu t) t k =
      envelope mu k q b t := by
  rw [← Real.exp_log hkq, ← Real.exp_log hk]
  rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  unfold envelope logMoment
  congr 1
  field_simp
  <;> ring

/-- A negative limiting shifted exponent forces the real-time envelope to zero. -/
theorem envelope_tendsto_zero
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (k q b : ℝ)
    (hk : Tendsto (fun t => logMoment mu t k) atTop (𝓝 (psi k)))
    (hkq : Tendsto (fun t => logMoment mu t (k + q)) atTop (𝓝 (psi (k + q))))
    (hgap : psi (k + q) - psi k - q * b < 0) :
    Tendsto (envelope mu k q b) atTop (𝓝 0) := by
  let c := psi (k + q) - psi k - q * b
  have hc : c < c / 2 := by dsimp only [c]; linarith
  have hc2 : c / 2 < 0 := by dsimp only [c]; linarith
  have hnear := ((hkq.sub hk).sub_const (q * b)).eventually (Iio_mem_nhds hc)
  have hmajor : Tendsto (fun t : ℝ => Real.exp (t * (c / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hc2)
  apply squeeze_zero' (Eventually.of_forall fun _ => Real.exp_nonneg _) _ hmajor
  filter_upwards [hnear, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.le ht0)

/-- Any tilted tail with a strict shifted-SCGF gap vanishes at real horizons. -/
theorem tiltedMass_tendsto_zero_of_gap
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (k q b : ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (hset : ∀ x ∈ s, 0 ≤ q * (x - b))
    (hint : ∀ t, 0 ≤ t → ∀ u, Integrable (fun x : ℝ => Real.exp (t * u * x)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ u, 0 < moment (mu t) t u)
    (hlim : ∀ u, Tendsto (fun t => logMoment mu t u) atTop (𝓝 (psi u)))
    (hgap : psi (k + q) - psi k - q * b < 0) :
    Tendsto (fun t => tiltedMass (mu t) t k s) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (envelope_tendsto_zero mu psi k q b (hlim k) (hlim (k + q)) hgap)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact tiltedMass_nonneg (mu t) t k s (hpos t ht k)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht1
    have ht : 0 < t := by linarith
    calc
      tiltedMass (mu t) t k s ≤
          Real.exp (-t * q * b) * moment (mu t) t (k + q) / moment (mu t) t k :=
        tiltedMass_set_le_ratio (mu t) t k q b ht.le s hs hset
          (hint t ht.le k) (hint t ht.le (k + q)) (hpos t ht.le k)
      _ = envelope mu k q b t := ratio_eq_envelope mu k q b t ht
        (hpos t ht.le k) (hpos t ht.le (k + q))

/-- At every derivative slope the actual tilted window mass tends to one
as real time tends to infinity. -/
theorem tiltedWindow_tendsto_one
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (k a delta : ℝ)
    (hd : HasDerivAt psi a k) (hdelta : 0 < delta)
    (hint : ∀ t, 0 ≤ t → ∀ u, Integrable (fun x : ℝ => Real.exp (t * u * x)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ u, 0 < moment (mu t) t u)
    (hlim : ∀ u, Tendsto (fun t => logMoment mu t u) atTop (𝓝 (psi u))) :
    Tendsto (fun t => tiltedMass (mu t) t k (Ioo (a - delta) (a + delta))) atTop (𝓝 1) := by
  obtain ⟨qu, hqu, hgu⟩ := exists_positive_right_tilt_gap hd hdelta
  obtain ⟨ql, hql, hgl⟩ := exists_negative_left_tilt_gap hd hdelta
  have hu := tiltedMass_tendsto_zero_of_gap mu psi k qu (a + delta) (Ici (a + delta))
    measurableSet_Ici (fun x hx => mul_nonneg hqu.le (sub_nonneg.mpr hx)) hint hpos hlim hgu
  have hl := tiltedMass_tendsto_zero_of_gap mu psi k ql (a - delta) (Iic (a - delta))
    measurableSet_Iic (fun x hx => mul_nonneg_of_nonpos_of_nonpos hql.le (sub_nonpos.mpr hx))
    hint hpos hlim hgl
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h : Tendsto (fun t => 1 - tiltedMass (mu t) t k (Iic (a - delta)) -
      tiltedMass (mu t) t k (Ici (a + delta))) atTop (𝓝 1) := by
    simpa using (hc.sub hl).sub hu
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (tiltedMass_Ioo_eq_one_sub_tails (mu t) t k (a - delta) (a + delta)
    (by linarith) (hint t ht k) (hpos t ht k)).symm

end

end NCG.RealTimeTiltedConcentration
