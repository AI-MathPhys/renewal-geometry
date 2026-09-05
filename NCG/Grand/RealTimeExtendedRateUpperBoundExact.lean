/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RealTimeExponentialUpperBoundExact
import NCG.Grand.ExtendedLegendreRateExact
import NCG.Grand.GartnerEllisClosedSetUpperBoundExact

/-!
# All-real-time upper bounds with the extended Legendre rate

Compact covers and exponential tightness give a closed-set upper bound at
every sufficiently large real horizon, including infinite-rate points.
Only nonnegative-time laws are constrained by the moment hypotheses.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace NCG.RealTimeExtendedRateUpperBound

open ExponentialTiltLocalLowerBound GartnerEllisCompactUpperBound
open GartnerEllisClosedSetUpperBound SCGFExponentialTightness
open RealTimeExponentialUpperBound

noncomputable section

/-- Compact-set upper estimate at all sufficiently large real horizons. -/
theorem eventually_mass_compact_le
    (mu : ℝ → Measure ℝ) (hfinite : ∀ t, 0 ≤ t → IsFiniteMeasure (mu t))
    (psi : ℝ → ℝ) (K : Set ℝ) (A epsilon : ℝ)
    (hK : IsCompact K) (hepsilon : 0 < epsilon)
    (hgap : ∀ x ∈ K, ((A + 2 * epsilon : ℝ) : EReal) < ExtendedLegendreRate.rate psi x)
    (hint : ∀ t, 0 ≤ t → ∀ q, Integrable (fun x : ℝ => Real.exp (t * q * x)) (mu t))
    (hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ q, 0 < moment (mu t) t q)
    (hlim : ∀ q, Tendsto (fun t => logMoment mu t q) atTop (𝓝 (psi q))) :
    ∀ᶠ t : ℝ in atTop, originalMass (mu t) K ≤ Real.exp (-t * A) := by
  classical
  have hw : ∀ x : K, ∃ q : ℝ, x.1 ∈ affineTiltNeighborhood psi q (A + 2 * epsilon) := by
    intro x
    obtain ⟨q, hq⟩ := (ExtendedLegendreRate.coe_lt_rate_iff psi x.1 _).mp (hgap x.1 x.2)
    refine ⟨q, ?_⟩
    change psi q + (A + 2 * epsilon) < q * x.1
    linarith
  choose q hq using hw
  let U : K → Set ℝ := fun x => affineTiltNeighborhood psi (q x) (A + 2 * epsilon)
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hq ⟨x, hx⟩⟩
  obtain ⟨cover, hfiniteCover⟩ := hK.elim_finite_subcover U
    (fun x => isOpen_affineTiltNeighborhood psi (q x) (A + 2 * epsilon)) hcover
  apply eventually_mass_subset_finiteCover_le mu hfinite K cover U A epsilon
    hepsilon hfiniteCover hK.measurableSet
  · intro x _
    exact (isOpen_affineTiltNeighborhood psi (q x) (A + 2 * epsilon)).measurableSet
  · intro x _
    exact eventually_mass_affineTiltNeighborhood_le mu psi (q x) A epsilon hepsilon
      (fun t ht => hint t ht (q x)) hone (fun t ht => hpos t ht (q x)) (hlim (q x))

/-- Real-time exponential tightness derived from only the two unit tilts. -/
theorem exists_compact_exponential_tightness
    (mu : ℝ → Measure ℝ) (psi : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hint : ∀ t, 0 ≤ t → ∀ q, Integrable (fun x : ℝ => Real.exp (t * q * x)) (mu t))
    (hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ q, 0 < moment (mu t) t q)
    (hlim : ∀ q, Tendsto (fun t => logMoment mu t q) atTop (𝓝 (psi q))) :
    ∃ M : ℝ, 0 < M ∧ IsCompact (Icc (-M) M) ∧
      ∀ᶠ t : ℝ in atTop, originalMass (mu t) (Icc (-M) M)ᶜ ≤ Real.exp (-t * A) := by
  let M : ℝ := A + |psi 1| + |psi (-1)| + 3
  have hM : 0 < M := by dsimp only [M]; positivity
  have hright : Ici M ⊆ affineTiltNeighborhood psi 1 (A + 2 * 1) := by
    intro x hx
    change M ≤ x at hx
    change psi 1 + (A + 2 * 1) < 1 * x
    dsimp only [M] at hx
    have hp := le_abs_self (psi 1)
    have hn := abs_nonneg (psi (-1))
    linarith
  have hleft : Iic (-M) ⊆ affineTiltNeighborhood psi (-1) (A + 2 * 1) := by
    intro x hx
    change x ≤ -M at hx
    change psi (-1) + (A + 2 * 1) < (-1) * x
    dsimp only [M] at hx
    have hp := le_abs_self (psi (-1))
    have hn := abs_nonneg (psi 1)
    linarith
  have hu := eventually_mass_affineTiltNeighborhood_le mu psi 1 A 1 (by norm_num)
    (fun t ht => hint t ht 1) hone (fun t ht => hpos t ht 1) (hlim 1)
  have hl := eventually_mass_affineTiltNeighborhood_le mu psi (-1) A 1 (by norm_num)
    (fun t ht => hint t ht (-1)) hone (fun t ht => hpos t ht (-1)) (hlim (-1))
  have htwo := eventually_card_le_exp 2 1 (by norm_num)
  refine ⟨M, hM, isCompact_Icc, ?_⟩
  filter_upwards [hu, hl, htwo, eventually_ge_atTop (0 : ℝ)] with t hut hlt htwot ht0
  have hr := originalMass_mono (mu t) _ _ hright (hone t ht0)
  have hl' := originalMass_mono (mu t) _ _ hleft (hone t ht0)
  calc
    originalMass (mu t) (Icc (-M) M)ᶜ ≤
        originalMass (mu t) (Iic (-M)) + originalMass (mu t) (Ici M) :=
      originalMass_compl_Icc_le_closedTails (mu t) M hM (hone t ht0)
    _ ≤ 2 * Real.exp (-t * (A + 1)) := by linarith
    _ ≤ Real.exp (t * 1) * Real.exp (-t * (A + 1)) :=
      mul_le_mul_of_nonneg_right htwot (Real.exp_nonneg _)
    _ = Real.exp (-t * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Closed-set upper estimate for every sufficiently large real horizon,
with tightness derived internally and infinite-rate points retained. -/
theorem eventually_mass_closed_le
    (mu : ℝ → Measure ℝ) (hfinite : ∀ t, 0 ≤ t → IsFiniteMeasure (mu t))
    (psi : ℝ → ℝ) (F : Set ℝ) (A epsilon : ℝ)
    (hF : IsClosed F) (hepsilon : 0 < epsilon)
    (hgap : ∀ x ∈ F, ((A + 3 * epsilon : ℝ) : EReal) < ExtendedLegendreRate.rate psi x)
    (hint : ∀ t, 0 ≤ t → ∀ q, Integrable (fun x : ℝ => Real.exp (t * q * x)) (mu t))
    (hone : ∀ t, 0 ≤ t → Integrable (fun _ : ℝ => (1 : ℝ)) (mu t))
    (hpos : ∀ t, 0 ≤ t → ∀ q, 0 < moment (mu t) t q)
    (hlim : ∀ q, Tendsto (fun t => logMoment mu t q) atTop (𝓝 (psi q))) :
    ∀ᶠ t : ℝ in atTop, originalMass (mu t) F ≤ Real.exp (-t * A) := by
  obtain ⟨M, _, hK, htail⟩ := exists_compact_exponential_tightness
    mu psi (max 0 (A + epsilon)) (le_max_left _ _) hint hone hpos hlim
  let K : Set ℝ := Icc (-M) M
  have hc := eventually_mass_compact_le mu hfinite psi (F ∩ K) (A + epsilon) epsilon
    (hK.inter_left hF) hepsilon (fun x hx => by
      have heq : A + epsilon + 2 * epsilon = A + 3 * epsilon := by ring
      simpa only [heq] using hgap x hx.1) hint hone hpos hlim
  have htwo := eventually_card_le_exp 2 epsilon hepsilon
  filter_upwards [hc, htail, htwo, eventually_ge_atTop (0 : ℝ)] with t hct htt htwot ht0
  letI := hfinite t ht0
  have htt' : originalMass (mu t) Kᶜ ≤ Real.exp (-t * (A + epsilon)) := by
    apply htt.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (le_max_right _ _) (neg_nonpos.mpr ht0)
  calc
    originalMass (mu t) F ≤ originalMass (mu t) (F ∩ K) + originalMass (mu t) Kᶜ :=
      originalMass_closed_le_compactPart_add_tail (mu t) F K hF hK
    _ ≤ 2 * Real.exp (-t * (A + epsilon)) := by linarith
    _ ≤ Real.exp (t * epsilon) * Real.exp (-t * (A + epsilon)) :=
      mul_le_mul_of_nonneg_right htwot (Real.exp_nonneg _)
    _ = Real.exp (-t * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

end

end NCG.RealTimeExtendedRateUpperBound
