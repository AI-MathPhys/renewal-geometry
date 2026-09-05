/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The spectral one-crossing theorem (GR_emergence, Phase 2)

`thm:fractional-one-crossing` and
`cor:fit-free-crossing-direction`: a derivative with a
single-crossover spectrum — positive (exchange-dominated) modes with
rates strictly above `r*` and negative (restoring) modes with rates
at most `r*` — has at most one zero, and any crossing is necessarily
`+ → -`.  No amplitudes or cosmological fit parameters enter.

Mechanism: the tilted function `e^{r*t}·Ḃ(t)` is strictly
antitone — the tilted positive part strictly decays, the tilted
negative part weakly grows — so it crosses zero at most once, from
above.

* `singleCrossover` — the mode-resolved derivative
  `Ḃ(t) = Σ aᵢe^{-rᵢt} - Σ bⱼe^{-sⱼt}`;
* `tilted_strictAnti` — strict antitonicity of the tilted function;
* `fractional_one_crossing` — at most one zero;
* `crossing_direction` — positive before, negative after: the
  crossing direction is `w_rec < -1 → w_rec > -1` via the sign
  dictionary `NCG.phantom_sign_dictionary`.

This is the finite-mode (atomic-measure) form of the manuscript's
spectral class; general Borel mode measures replace the sums by
integrals with the same monotonicity argument.
-/

namespace NCG

open Real Finset

/-- The mode-resolved single-crossover derivative
`Ḃ(t) = Σ aᵢ e^{-rᵢ t} - Σ bⱼ e^{-sⱼ t}`. -/
noncomputable def singleCrossover {k l : ℕ} (a : Fin k → ℝ)
    (r : Fin k → ℝ) (b : Fin l → ℝ) (s : Fin l → ℝ) (t : ℝ) : ℝ :=
  ∑ i, a i * Real.exp (-(r i * t)) - ∑ j, b j * Real.exp (-(s j * t))

/-- The tilted function `e^{r*t}·Ḃ(t)` in mode-resolved form. -/
theorem tilted_eq {k l : ℕ} (a : Fin k → ℝ) (r : Fin k → ℝ)
    (b : Fin l → ℝ) (s : Fin l → ℝ) (rstar t : ℝ) :
    Real.exp (rstar * t) * singleCrossover a r b s t
      = ∑ i, a i * Real.exp ((rstar - r i) * t)
        - ∑ j, b j * Real.exp ((rstar - s j) * t) := by
  unfold singleCrossover
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, mul_comm (Real.exp (rstar * t)) (a i), mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, mul_comm (Real.exp (rstar * t)) (b j), mul_assoc,
      ← Real.exp_add]
    congr 2
    ring

/-- The tilted single-crossover function is strictly antitone: the
positive modes strictly decay after tilting, the restoring modes
weakly grow. -/
theorem tilted_strictAnti {k l : ℕ} (a : Fin (k + 1) → ℝ)
    (r : Fin (k + 1) → ℝ) (b : Fin l → ℝ) (s : Fin l → ℝ) (rstar : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 ≤ b j)
    (hr : ∀ i, rstar < r i) (hs : ∀ j, s j ≤ rstar) :
    StrictAnti (fun t => ∑ i, a i * Real.exp ((rstar - r i) * t)
      - ∑ j, b j * Real.exp ((rstar - s j) * t)) := by
  intro t1 t2 h12
  have hpos : ∀ i : Fin (k + 1),
      a i * Real.exp ((rstar - r i) * t2)
        < a i * Real.exp ((rstar - r i) * t1) := by
    intro i
    apply mul_lt_mul_of_pos_left _ (ha i)
    apply Real.exp_lt_exp.mpr
    have hc : rstar - r i < 0 := by linarith [hr i]
    nlinarith
  have hneg : ∀ j : Fin l,
      b j * Real.exp ((rstar - s j) * t1)
        ≤ b j * Real.exp ((rstar - s j) * t2) := by
    intro j
    apply mul_le_mul_of_nonneg_left _ (hb j)
    apply Real.exp_le_exp.mpr
    have hc : 0 ≤ rstar - s j := by linarith [hs j]
    nlinarith
  have h1 : ∑ i, a i * Real.exp ((rstar - r i) * t2)
      < ∑ i, a i * Real.exp ((rstar - r i) * t1) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      fun i _ => hpos i
  have h2 : ∑ j, b j * Real.exp ((rstar - s j) * t1)
      ≤ ∑ j, b j * Real.exp ((rstar - s j) * t2) :=
    Finset.sum_le_sum fun j _ => hneg j
  linarith

/-- `thm:fractional-one-crossing`: a single-crossover derivative has
at most one zero on the whole line — oscillatory sequences of
crossings are excluded within the spectral class, with no amplitude
or fit parameter entering. -/
theorem fractional_one_crossing {k l : ℕ} (a : Fin (k + 1) → ℝ)
    (r : Fin (k + 1) → ℝ) (b : Fin l → ℝ) (s : Fin l → ℝ) (rstar : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 ≤ b j)
    (hr : ∀ i, rstar < r i) (hs : ∀ j, s j ≤ rstar) :
    ∀ t1 t2, singleCrossover a r b s t1 = 0
      → singleCrossover a r b s t2 = 0 → t1 = t2 := by
  intro t1 t2 h1 h2
  have hF := tilted_strictAnti a r b s rstar ha hb hr hs
  have hz : ∀ t, singleCrossover a r b s t = 0 →
      (∑ i, a i * Real.exp ((rstar - r i) * t)
        - ∑ j, b j * Real.exp ((rstar - s j) * t)) = 0 := by
    intro t ht
    rw [← tilted_eq, ht, mul_zero]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h3 : (∑ i, a i * Real.exp ((rstar - r i) * t2)
        - ∑ j, b j * Real.exp ((rstar - s j) * t2))
        < (∑ i, a i * Real.exp ((rstar - r i) * t1)
        - ∑ j, b j * Real.exp ((rstar - s j) * t1)) := hF h
    rw [hz t1 h1, hz t2 h2] at h3
    exact lt_irrefl 0 h3
  · have h3 : (∑ i, a i * Real.exp ((rstar - r i) * t1)
        - ∑ j, b j * Real.exp ((rstar - s j) * t1))
        < (∑ i, a i * Real.exp ((rstar - r i) * t2)
        - ∑ j, b j * Real.exp ((rstar - s j) * t2)) := hF h
    rw [hz t1 h1, hz t2 h2] at h3
    exact lt_irrefl 0 h3

/-- `cor:fit-free-crossing-direction` (direction): around any zero
the single-crossover derivative is positive before and negative
after — with the sign dictionary `NCG.phantom_sign_dictionary` the
unique crossing is necessarily `w_rec < -1 → w_rec > -1`; the
reverse crossing and oscillations are excluded. -/
theorem crossing_direction {k l : ℕ} (a : Fin (k + 1) → ℝ)
    (r : Fin (k + 1) → ℝ) (b : Fin l → ℝ) (s : Fin l → ℝ) (rstar : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 ≤ b j)
    (hr : ∀ i, rstar < r i) (hs : ∀ j, s j ≤ rstar)
    {t0 : ℝ} (h0 : singleCrossover a r b s t0 = 0) :
    (∀ t, t < t0 → 0 < singleCrossover a r b s t) ∧
    (∀ t, t0 < t → singleCrossover a r b s t < 0) := by
  have hF := tilted_strictAnti a r b s rstar ha hb hr hs
  have hz0 : (∑ i, a i * Real.exp ((rstar - r i) * t0)
      - ∑ j, b j * Real.exp ((rstar - s j) * t0)) = 0 := by
    rw [← tilted_eq, h0, mul_zero]
  have hsign : ∀ t, Real.exp (rstar * t) * singleCrossover a r b s t
      = ∑ i, a i * Real.exp ((rstar - r i) * t)
        - ∑ j, b j * Real.exp ((rstar - s j) * t) := fun t =>
    tilted_eq a r b s rstar t
  constructor
  · intro t ht
    have h1 : (0:ℝ) < ∑ i, a i * Real.exp ((rstar - r i) * t)
        - ∑ j, b j * Real.exp ((rstar - s j) * t) := by
      have h4 : (∑ i, a i * Real.exp ((rstar - r i) * t0)
          - ∑ j, b j * Real.exp ((rstar - s j) * t0))
          < (∑ i, a i * Real.exp ((rstar - r i) * t)
          - ∑ j, b j * Real.exp ((rstar - s j) * t)) := hF ht
      rw [hz0] at h4
      linarith
    rw [← hsign t] at h1
    have hexp : (0:ℝ) < Real.exp (rstar * t) := Real.exp_pos _
    by_contra hc
    push Not at hc
    have h2 : Real.exp (rstar * t) * singleCrossover a r b s t ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inl ⟨hexp.le, hc⟩)
    linarith
  · intro t ht
    have h1 : (∑ i, a i * Real.exp ((rstar - r i) * t)
        - ∑ j, b j * Real.exp ((rstar - s j) * t)) < 0 := by
      have h4 : (∑ i, a i * Real.exp ((rstar - r i) * t)
          - ∑ j, b j * Real.exp ((rstar - s j) * t))
          < (∑ i, a i * Real.exp ((rstar - r i) * t0)
          - ∑ j, b j * Real.exp ((rstar - s j) * t0)) := hF ht
      rw [hz0] at h4
      linarith
    rw [← hsign t] at h1
    have hexp : (0:ℝ) < Real.exp (rstar * t) := Real.exp_pos _
    by_contra hc
    push Not at hc
    have h2 : 0 ≤ Real.exp (rstar * t) * singleCrossover a r b s t :=
      mul_nonneg hexp.le hc
    linarith

end NCG
