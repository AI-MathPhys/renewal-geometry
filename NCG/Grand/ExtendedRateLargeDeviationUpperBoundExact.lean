/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExtendedLegendreRateExact
import NCG.Grand.GartnerEllisClosedSetUpperBoundExact

/-!
# Large-deviation upper bounds with infinite-rate points

The concrete Chernoff and finite-cover estimates are assembled using the
extended Legendre rate. Infinite-rate points therefore admit arbitrarily
large finite exponential bounds. Exponential tightness is derived internally
from the moment limits. These statements use the existing natural-time
moment interface; no all-real-time LDP is claimed here.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace NCG.ExtendedRateLargeDeviationUpperBound

open ExponentialTiltLocalLowerBound ExponentialTiltMeasure
open SCGFExponentialTiltConcentration FiniteExponentialCoverUpperBound
open GartnerEllisCompactUpperBound GartnerEllisClosedSetUpperBound

noncomputable section

/-- An extended-rate gap supplies an affine Chernoff neighborhood even at an infinite-rate point. -/
theorem exists_affineTiltNeighborhood (psi : ℝ → ℝ) (A x : ℝ)
    (hA : (A : EReal) < ExtendedLegendreRate.rate psi x) :
    ∃ q : ℝ, x ∈ affineTiltNeighborhood psi q A := by
  obtain ⟨q, hq⟩ := (ExtendedLegendreRate.coe_lt_rate_iff psi x A).mp hA
  refine ⟨q, ?_⟩
  change psi q + A < q * x
  linarith

/-- Compact-set upper estimate using the full extended-valued Legendre rate. -/
theorem eventually_mass_compact_le
    (mu : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (mu n)]
    (psi : ℝ → ℝ) (K : Set ℝ) (A epsilon : ℝ)
    (hK : IsCompact K) (hepsilon : 0 < epsilon)
    (hgap : ∀ x ∈ K, ((A + 2 * epsilon : ℝ) : EReal) < ExtendedLegendreRate.rate psi x)
    (hint : ∀ n : ℕ, ∀ q : ℝ, Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ n : ℕ, ∀ q : ℝ, 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q : ℝ, Tendsto
      (fun n => normalizedLogMoment (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∀ᶠ n : ℕ in atTop, originalMass (mu n) K ≤ Real.exp (-(n : ℝ) * A) := by
  classical
  choose q hq using fun x : K =>
    exists_affineTiltNeighborhood psi (A + 2 * epsilon) x.1 (hgap x.1 x.2)
  let U : K → Set ℝ := fun x => affineTiltNeighborhood psi (q x) (A + 2 * epsilon)
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hq ⟨x, hx⟩⟩
  obtain ⟨cover, hfinite⟩ := hK.elim_finite_subcover U
    (fun x => isOpen_affineTiltNeighborhood psi (q x) (A + 2 * epsilon)) hcover
  apply eventually_originalMass_subset_finiteCover_le
    mu K cover U A epsilon hepsilon hfinite hK.measurableSet
  · intro x _
    exact (isOpen_affineTiltNeighborhood psi (q x) (A + 2 * epsilon)).measurableSet
  · intro x _
    exact eventually_originalMass_affineTiltNeighborhood_le
      mu psi (q x) A epsilon hepsilon (fun n => hint n (q x))
      hone (fun n => hpos n (q x)) (hlim (q x))

/-- Closed-set upper estimate, with exponential tightness derived rather
than supplied, valid also when every point of the set has infinite rate. -/
theorem eventually_mass_closed_le
    (mu : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (mu n)]
    (psi : ℝ → ℝ) (F : Set ℝ) (A epsilon : ℝ)
    (hF : IsClosed F) (hepsilon : 0 < epsilon)
    (hgap : ∀ x ∈ F, ((A + 3 * epsilon : ℝ) : EReal) < ExtendedLegendreRate.rate psi x)
    (hint : ∀ n : ℕ, ∀ q : ℝ, Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ n : ℕ, ∀ q : ℝ, 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q : ℝ, Tendsto
      (fun n => normalizedLogMoment (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∀ᶠ n : ℕ in atTop, originalMass (mu n) F ≤ Real.exp (-(n : ℝ) * A) := by
  obtain ⟨M, _, hK, htail⟩ :=
    SCGFExponentialTightness.exists_compactInterval_exponential_tightness
      mu psi (max 0 (A + epsilon)) (le_max_left _ _) hint hone hpos hlim
  let K : Set ℝ := Icc (-M) M
  have hcompact := eventually_mass_compact_le mu psi (F ∩ K)
    (A + epsilon) epsilon (hK.inter_left hF) hepsilon
    (fun x hx => by
      have heq : A + epsilon + 2 * epsilon = A + 3 * epsilon := by ring
      simpa only [heq] using hgap x hx.1) hint hone hpos hlim
  have htwo := eventually_natCard_le_exp_nat_mul 2 epsilon hepsilon
  filter_upwards [hcompact, htail, htwo] with n hcomp htailn htwon
  have htail' : originalMass (mu n) Kᶜ ≤ Real.exp (-(n : ℝ) * (A + epsilon)) := by
    apply htailn.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (le_max_right _ _) (neg_nonpos.mpr (Nat.cast_nonneg n))
  calc
    originalMass (mu n) F ≤ originalMass (mu n) (F ∩ K) + originalMass (mu n) Kᶜ :=
      originalMass_closed_le_compactPart_add_tail (mu n) F K hF hK
    _ ≤ 2 * Real.exp (-(n : ℝ) * (A + epsilon)) := by linarith
    _ ≤ Real.exp ((n : ℝ) * epsilon) * Real.exp (-(n : ℝ) * (A + epsilon)) :=
      mul_le_mul_of_nonneg_right htwon (Real.exp_nonneg _)
    _ = Real.exp (-(n : ℝ) * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

end

end NCG.ExtendedRateLargeDeviationUpperBound
