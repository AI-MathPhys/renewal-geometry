/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SixthOrderProfile

/-!
# Resolvent-limit closure of the sixth-order renewal profile

This module supplies the analytic bridge missing from `SixthOrderProfile`.
The coefficients of the seventh-and-higher tail are matrix coefficients of
powers of a uniformly contractive normalized cell insertion.  Their geometric
domination is therefore derived from operator norms.  The resulting estimates
are closed under subsequential limits, and the Stieltjes identity at zero
gives the sharp `2 E` memory-mass window for an arbitrary finite measure.
-/

namespace NCG

open MeasureTheory

/-- Matrix coefficients of powers of a norm-bounded insertion have the
geometric domination used in the normalized resolvent expansion. -/
theorem resolvent_power_coefficient_bound
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
    (T x : A) (observe : A →L[ℝ] ℝ) (D q : ℝ)
    (hq : 0 ≤ q) (hT : ‖T‖ ≤ q)
    (hD : ‖observe‖ * ‖x‖ ≤ D) (n : ℕ) :
    |observe (T ^ (n + 5) * x)| ≤ D * q ^ (n + 5) := by
  rw [← Real.norm_eq_abs]
  calc
    ‖observe (T ^ (n + 5) * x)‖
        ≤ ‖observe‖ * ‖T ^ (n + 5) * x‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖observe‖ * (‖T ^ (n + 5)‖ * ‖x‖) := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ ‖observe‖ * (‖T‖ ^ (n + 5) * ‖x‖) := by
          gcongr
          exact norm_pow_le _ _
    _ = (‖observe‖ * ‖x‖) * ‖T‖ ^ (n + 5) := by ring
    _ ≤ D * q ^ (n + 5) := by
          exact mul_le_mul hD
            (pow_le_pow_left₀ (norm_nonneg T) hT _)
            (pow_nonneg (norm_nonneg T) _) (le_trans
              (mul_nonneg (norm_nonneg observe) (norm_nonneg x)) hD)

/-- The exact normalized resolvent tail has the manuscript's boxed
seventh-order bound.  Unlike the older scalar tail lemma, the coefficient
bound is discharged here from the cell insertion, source, and observation
norms. -/
theorem normalized_resolvent_seventh_order_bound
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
    (T x : A) (observe : A →L[ℝ] ℝ) (D q θ : ℝ)
    (hq : 0 ≤ q) (hT : ‖T‖ ≤ q)
    (hD : ‖observe‖ * ‖x‖ ≤ D)
    (hsmall : q * |θ| < 1) :
    |∑' n : ℕ, observe (T ^ (n + 5) * x) * θ ^ (n + 7)|
      ≤ D * q ^ 5 * |θ| ^ 7 / (1 - q * |θ|) := by
  exact geometric_remainder_bound
    (fun n => observe (T ^ (n + 5) * x)) D q θ
    (le_trans (mul_nonneg (norm_nonneg observe) (norm_nonneg x)) hD)
    hq hsmall (resolvent_power_coefficient_bound T x observe D q hq hT hD)

/-- A closed real inequality passes to every subsequential continuum limit.
This is the precise compactness step used twice in the cell-profile theorem,
once at finite spectral parameter and once for the instantaneous part. -/
theorem abs_sub_le_of_tendsto
    (u : ℕ → ℝ) (a P E : ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds a))
    (hbound : ∀ n, |u n - P| ≤ E) :
    |a - P| ≤ E := by
  have hlim : Filter.Tendsto (fun n => |u n - P|)
      Filter.atTop (nhds |a - P|) := (hu.sub_const P).abs
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

/-- The Stieltjes identity at `z = 0` converts the two jet estimates into the
sharp memory-mass interval for an arbitrary finite positive measure. -/
theorem stieltjes_measure_mass_bound
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν]
    (m0 d P E : ℝ)
    (hstieltjes : m0 = d + (ν Set.univ).toReal)
    (hm : |m0 - P| ≤ E) (hd : |d - P| ≤ E) :
    0 ≤ (ν Set.univ).toReal ∧ (ν Set.univ).toReal ≤ 2 * E := by
  have hnonneg : 0 ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
  have h1 := abs_le.mp hm
  have h2 := abs_le.mp hd
  refine ⟨hnonneg, ?_⟩
  linarith

/-- Full continuum closure from normalized finite-cell resolvents.

For each cutoff and spectral parameter, `hfinite` identifies the difference
from the displayed sixth-order jet with the genuine tail of a normalized
resolvent.  Thus its bound is proved from `‖T‖ ≤ q`; it is not an assumed
profile estimate.  `hprofileLimit` and `hinstantLimit` are exactly the data of
a chosen continuum subsequential Stieltjes profile. -/
theorem renewal_sixth_order_profile_from_resolvent_limits
    {A X : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
    [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν]
    (T : ℕ → ℝ → A) (x : ℕ → ℝ → A)
    (observe : ℕ → ℝ → A →L[ℝ] ℝ)
    (instantT : ℕ → A) (instantX : ℕ → A)
    (instantObserve : ℕ → A →L[ℝ] ℝ)
    (finiteProfile : ℕ → ℝ → ℝ) (finiteInstant : ℕ → ℝ)
    (profile : ℝ → ℝ) (d P D q θ : ℝ)
    (hq : 0 ≤ q) (hsmall : q * |θ| < 1)
    (hT : ∀ n z, 0 ≤ z → ‖T n z‖ ≤ q)
    (hsource : ∀ n z, 0 ≤ z →
      ‖observe n z‖ * ‖x n z‖ ≤ D)
    (hfinite : ∀ n z, 0 ≤ z →
      finiteProfile n z - P =
        ∑' j : ℕ, observe n z (T n z ^ (j + 5) * x n z)
          * θ ^ (j + 7))
    (hinstantT : ∀ n, ‖instantT n‖ ≤ q)
    (hinstantSource : ∀ n,
      ‖instantObserve n‖ * ‖instantX n‖ ≤ D)
    (hfiniteInstant : ∀ n,
      finiteInstant n - P =
        ∑' j : ℕ,
          instantObserve n (instantT n ^ (j + 5) * instantX n)
            * θ ^ (j + 7))
    (hprofileLimit : ∀ z, 0 ≤ z →
      Filter.Tendsto (fun n => finiteProfile n z)
        Filter.atTop (nhds (profile z)))
    (hinstantLimit : Filter.Tendsto finiteInstant Filter.atTop (nhds d))
    (hstieltjes : profile 0 = d + (ν Set.univ).toReal) :
    (∀ z, 0 ≤ z →
        |profile z - P| ≤ D * q ^ 5 * |θ| ^ 7 /
          (1 - q * |θ|))
      ∧ |d - P| ≤ D * q ^ 5 * |θ| ^ 7 /
          (1 - q * |θ|)
      ∧ 0 ≤ (ν Set.univ).toReal
      ∧ (ν Set.univ).toReal ≤ 2 * (D * q ^ 5 * |θ| ^ 7 /
          (1 - q * |θ|)) := by
  let E := D * q ^ 5 * |θ| ^ 7 / (1 - q * |θ|)
  have hfiniteBound : ∀ n z, 0 ≤ z → |finiteProfile n z - P| ≤ E := by
    intro n z hz
    rw [hfinite n z hz]
    exact normalized_resolvent_seventh_order_bound
      (T n z) (x n z) (observe n z) D q θ hq
      (hT n z hz) (hsource n z hz) hsmall
  have hinstantBound : ∀ n, |finiteInstant n - P| ≤ E := by
    intro n
    rw [hfiniteInstant n]
    exact normalized_resolvent_seventh_order_bound
      (instantT n) (instantX n) (instantObserve n) D q θ hq
      (hinstantT n) (hinstantSource n) hsmall
  have hprofileBound : ∀ z, 0 ≤ z → |profile z - P| ≤ E := by
    intro z hz
    exact abs_sub_le_of_tendsto (fun n => finiteProfile n z)
      (profile z) P E (hprofileLimit z hz) (fun n => hfiniteBound n z hz)
  have hd : |d - P| ≤ E :=
    abs_sub_le_of_tendsto finiteInstant d P E hinstantLimit hinstantBound
  have hmass := stieltjes_measure_mass_bound ν (profile 0) d P E
    hstieltjes (hprofileBound 0 (by positivity)) hd
  exact ⟨hprofileBound, hd, hmass⟩

end NCG
