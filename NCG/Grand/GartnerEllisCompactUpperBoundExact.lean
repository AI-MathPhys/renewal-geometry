/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteExponentialCoverUpperBoundExact
import NCG.Grand.ExponentialMomentChernoffUpperBoundExact
import NCG.Gravity.RateFunction

/-!
# Compact-set Gartner--Ellis upper bound

This file converts pointwise Legendre witnesses into affine open
neighborhoods, extracts a finite subcover of a compact set, and aggregates
the resulting Chernoff estimates.  It is the compactness core of the
closed-set upper bound.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.GartnerEllisCompactUpperBound

open NCG.ExponentialTiltLocalLowerBound
open NCG.ExponentialTiltMeasure
open NCG.SCGFExponentialTiltConcentration
open NCG.ExponentialMomentChernoffUpperBound
open NCG.FiniteExponentialCoverUpperBound

/-- The open neighborhood on which one fixed tilt witnesses a prescribed
strict rate lower bound. -/
def affineTiltNeighborhood (ψ : ℝ → ℝ) (q R : ℝ) : Set ℝ :=
  {x | ψ q + R < q * x}

theorem isOpen_affineTiltNeighborhood
    (ψ : ℝ → ℝ) (q R : ℝ) :
    IsOpen (affineTiltNeighborhood ψ q R) := by
  exact isOpen_lt continuous_const (continuous_const.mul continuous_id)

/-- A strict lower bound on the Legendre transform supplies a concrete
tilt whose affine neighborhood contains the point. -/
theorem exists_mem_affineTiltNeighborhood_of_lt_rateFunction
    (ψ : ℝ → ℝ) (A x : ℝ)
    (hA : A < rateFunction ψ x) :
    ∃ q : ℝ, x ∈ affineTiltNeighborhood ψ q A := by
  have hsup : A < ⨆ q : ℝ, (q * x - ψ q) := by
    simpa only [rateFunction] using hA
  obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup hsup
  refine ⟨q, ?_⟩
  change ψ q + A < q * x
  linarith

/-- One affine Legendre-witness neighborhood satisfies the desired local
exponential estimate.  One epsilon is spent controlling the moment limit;
the other is retained for finite-cover aggregation. -/
theorem eventually_originalMass_affineTiltNeighborhood_le
    (μ : ℕ → Measure ℝ) (ψ : ℝ → ℝ) (q A epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hint : ∀ n : ℕ, Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (μ n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (μ n))
    (hpos : ∀ n : ℕ, 0 < exponentialMoment (μ n) n q)
    (hlim : Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (μ m) m u) n q)
      atTop (nhds (ψ q))) :
    ∀ᶠ n : ℕ in atTop,
      originalMass (μ n) (affineTiltNeighborhood ψ q (A + 2 * epsilon)) ≤
        Real.exp (-(n : ℝ) * (A + epsilon)) := by
  have hnear : Set.Iio (ψ q + epsilon) ∈ nhds (ψ q) :=
    Iio_mem_nhds (lt_add_of_pos_right _ hepsilon)
  have hlog := hlim.eventually hnear
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn =>
      lt_of_lt_of_le Nat.zero_lt_one hn⟩
  filter_upwards [hlog, hnpos] with n hlogn hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hZ : exponentialMoment (μ n) n q ≤
      Real.exp ((n : ℝ) * (ψ q + epsilon)) := by
    have hmul : Real.log (exponentialMoment (μ n) n q) <
        (n : ℝ) * (ψ q + epsilon) := by
      simpa only [mul_comm] using (div_lt_iff₀ hnreal).mp hlogn
    have hexp := Real.exp_lt_exp.mpr hmul
    rw [Real.exp_log (hpos n)] at hexp
    exact le_of_lt hexp
  calc
    originalMass (μ n) (affineTiltNeighborhood ψ q (A + 2 * epsilon)) ≤
        Real.exp (-(n : ℝ) * (ψ q + (A + 2 * epsilon))) *
          exponentialMoment (μ n) n q := by
      apply originalMass_set_le_exponentialMoment
        (μ n) n q (ψ q + (A + 2 * epsilon))
        (affineTiltNeighborhood ψ q (A + 2 * epsilon))
        (isOpen_affineTiltNeighborhood ψ q (A + 2 * epsilon)).measurableSet
        _ (hint n) (hone n)
      intro x hx
      exact le_of_lt hx
    _ ≤ Real.exp (-(n : ℝ) * (ψ q + (A + 2 * epsilon))) *
        Real.exp ((n : ℝ) * (ψ q + epsilon)) :=
      mul_le_mul_of_nonneg_left hZ (Real.exp_nonneg _)
    _ = Real.exp (-(n : ℝ) * (A + epsilon)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Compact-set Gartner--Ellis upper bound, in direct eventual-exponential
form.  It needs only the concrete normalized log-moment limits and the
strict separation of the compact set from the target rate level. -/
theorem eventually_originalMass_compact_le
    (μ : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (μ n)]
    (ψ : ℝ → ℝ) (K : Set ℝ) (A epsilon : ℝ)
    (hKcompact : IsCompact K) (hepsilon : 0 < epsilon)
    (hgap : ∀ x ∈ K, A + 2 * epsilon < rateFunction ψ x)
    (hint : ∀ n : ℕ, ∀ q : ℝ, Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (μ n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (μ n))
    (hpos : ∀ n : ℕ, ∀ q : ℝ, 0 < exponentialMoment (μ n) n q)
    (hlim : ∀ q : ℝ, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (μ m) m u) n q)
      atTop (nhds (ψ q))) :
    ∀ᶠ n : ℕ in atTop,
      originalMass (μ n) K ≤ Real.exp (-(n : ℝ) * A) := by
  classical
  choose q hq using fun x : K =>
    exists_mem_affineTiltNeighborhood_of_lt_rateFunction
      ψ (A + 2 * epsilon) x.1 (hgap x.1 x.2)
  let U : K → Set ℝ := fun x =>
    affineTiltNeighborhood ψ (q x) (A + 2 * epsilon)
  have hKU : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hq ⟨x, hx⟩⟩
  obtain ⟨cover, hcover⟩ := hKcompact.elim_finite_subcover U
    (fun x => isOpen_affineTiltNeighborhood ψ (q x) (A + 2 * epsilon)) hKU
  apply eventually_originalMass_subset_finiteCover_le
    μ K cover U A epsilon hepsilon hcover hKcompact.measurableSet
  · intro x hx
    exact (isOpen_affineTiltNeighborhood ψ (q x)
      (A + 2 * epsilon)).measurableSet
  · intro x hx
    exact eventually_originalMass_affineTiltNeighborhood_le
      μ ψ (q x) A epsilon hepsilon
      (fun n => hint n (q x)) hone (fun n => hpos n (q x)) (hlim (q x))

end NCG.GartnerEllisCompactUpperBound
