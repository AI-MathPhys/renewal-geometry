/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GartnerEllisCompactUpperBoundExact
import NCG.Grand.SCGFExponentialTightnessExact

/-!
# Closed-set Gartner--Ellis upper bound

The compact-set estimate is combined with exponential tightness.  Three
epsilon margins produce the local Legendre neighborhoods; a fourth absorbs
the two-term decomposition into the compact part and its tail.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.GartnerEllisClosedSetUpperBound

open NCG.ExponentialTiltLocalLowerBound
open NCG.ExponentialTiltMeasure
open NCG.SCGFExponentialTiltConcentration
open NCG.FiniteExponentialCoverUpperBound
open NCG.GartnerEllisCompactUpperBound

/-- Split the mass of a closed set into its part in a compact set and the
complementary tail. -/
theorem originalMass_closed_le_compactPart_add_tail
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (F K : Set ℝ) (hF : IsClosed F) (hK : IsCompact K) :
    originalMass mu F ≤
      originalMass mu (F ∩ K) + originalMass mu Kᶜ := by
  have hsubset : F ⊆ (F ∩ K) ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx, hxK⟩
    · exact Or.inr hxK
  calc
    originalMass mu F = mu.real F :=
      originalMass_eq_measureReal mu F hF.measurableSet
    _ ≤ mu.real ((F ∩ K) ∪ Kᶜ) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ mu.real (F ∩ K) + mu.real Kᶜ :=
      measureReal_union_le _ _
    _ = originalMass mu (F ∩ K) + originalMass mu Kᶜ := by
      rw [originalMass_eq_measureReal mu (F ∩ K)
        (hF.inter hK.isClosed).measurableSet,
        originalMass_eq_measureReal mu Kᶜ hK.isClosed.measurableSet.compl]

/-- A closed-set upper bound from concrete normalized log-moment limits and
one compact exponential-tightness witness at the requested rate. -/
theorem eventually_originalMass_closed_le
    (μ : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (μ n)]
    (ψ : ℝ → ℝ) (F K : Set ℝ) (A epsilon : ℝ)
    (hF : IsClosed F) (hK : IsCompact K) (hepsilon : 0 < epsilon)
    (hgap : ∀ x ∈ F, A + 3 * epsilon < rateFunction ψ x)
    (hint : ∀ n : ℕ, ∀ q : ℝ, Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (μ n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (μ n))
    (hpos : ∀ n : ℕ, ∀ q : ℝ, 0 < exponentialMoment (μ n) n q)
    (hlim : ∀ q : ℝ, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (μ m) m u) n q)
      atTop (nhds (ψ q)))
    (htail : ∀ᶠ n : ℕ in atTop,
      originalMass (μ n) Kᶜ ≤
        Real.exp (-(n : ℝ) * (A + epsilon))) :
    ∀ᶠ n : ℕ in atTop,
      originalMass (μ n) F ≤ Real.exp (-(n : ℝ) * A) := by
  have hcompact : IsCompact (F ∩ K) := hK.inter_left hF
  have hcompactBound : ∀ᶠ n : ℕ in atTop,
      originalMass (μ n) (F ∩ K) ≤
        Real.exp (-(n : ℝ) * (A + epsilon)) := by
    apply eventually_originalMass_compact_le
      μ ψ (F ∩ K) (A + epsilon) epsilon hcompact hepsilon
    · intro x hx
      have hxrate := hgap x hx.1
      convert hxrate using 1
      ring
    · exact hint
    · exact hone
    · exact hpos
    · exact hlim
  have htwo := eventually_natCard_le_exp_nat_mul 2 epsilon hepsilon
  filter_upwards [hcompactBound, htail, htwo] with n hcompn htailn htwon
  calc
    originalMass (μ n) F ≤
        originalMass (μ n) (F ∩ K) + originalMass (μ n) Kᶜ :=
      originalMass_closed_le_compactPart_add_tail (μ n) F K hF hK
    _ ≤ Real.exp (-(n : ℝ) * (A + epsilon)) +
        Real.exp (-(n : ℝ) * (A + epsilon)) :=
      add_le_add hcompn htailn
    _ = (2 : ℝ) * Real.exp (-(n : ℝ) * (A + epsilon)) := by ring
    _ ≤ Real.exp ((n : ℝ) * epsilon) *
        Real.exp (-(n : ℝ) * (A + epsilon)) :=
      mul_le_mul_of_nonneg_right htwon (Real.exp_nonneg _)
    _ = Real.exp (-(n : ℝ) * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

end NCG.GartnerEllisClosedSetUpperBound
