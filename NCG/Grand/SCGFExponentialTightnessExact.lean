/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExponentialMomentChernoffUpperBoundExact

/-!
# Exponential tightness from two finite SCGF values

A normalized log-moment limit at `+1` and `-1` gives exponentially small
mass outside a sufficiently large compact interval.  This is the concrete
one-dimensional exponential-tightness step in the Gartner--Ellis argument.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.SCGFExponentialTightness

open NCG.ExponentialTiltMeasure
open NCG.ExponentialTiltLocalLowerBound
open NCG.ExponentialMomentChernoffUpperBound
open NCG.SCGFExponentialTiltConcentration

/-- Original real masses are monotone under inclusion. -/
theorem originalMass_mono
    (mu : Measure ℝ) (s t : Set ℝ) (hst : s ⊆ t)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu) :
    originalMass mu s ≤ originalMass mu t := by
  unfold originalMass
  exact MeasureTheory.integral_mono_measure
    (Measure.restrict_mono_set mu hst)
    (Filter.Eventually.of_forall fun _ => by norm_num) hone.integrableOn

/-- The complement of a closed interval is dominated by the two closed
half-line tails. -/
theorem originalMass_compl_Icc_le_closedTails
    (mu : Measure ℝ) (M : ℝ) (hM : 0 < M)
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu) :
    originalMass mu (Set.Icc (-M) M)ᶜ ≤
      originalMass mu (Set.Iic (-M)) + originalMass mu (Set.Ici M) := by
  have hsubset : (Set.Icc (-M) M)ᶜ ⊆
      Set.Iic (-M) ∪ Set.Ici M := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union,
      Set.mem_Iic, Set.mem_Ici] at hx ⊢
    by_cases hxl : x ≤ -M
    · exact Or.inl hxl
    · right
      apply le_of_not_gt
      intro hxu
      exact hx ⟨lt_of_not_ge hxl |>.le, hxu.le⟩
  calc
    originalMass mu (Set.Icc (-M) M)ᶜ ≤
        originalMass mu (Set.Iic (-M) ∪ Set.Ici M) :=
      originalMass_mono mu _ _ hsubset hone
    _ = originalMass mu (Set.Iic (-M)) +
        originalMass mu (Set.Ici M) := by
      unfold originalMass
      have hdisj : Disjoint (Set.Iic (-M)) (Set.Ici M) := by
        rw [Set.disjoint_left]
        intro x hxl hxu
        change x ≤ -M at hxl
        change M ≤ x at hxu
        linarith
      exact MeasureTheory.setIntegral_union hdisj measurableSet_Ici
        hone.integrableOn hone.integrableOn

/-- Every prescribed exponential speed is achieved outside some compact
interval, using only the SCGF limits at `+1` and `-1`. -/
theorem exists_compactInterval_exponential_tightness
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hint : ∀ (n : ℕ) (q : ℝ), Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hone : ∀ n : ℕ, Integrable (fun _ : ℝ => (1 : ℝ)) (mu n))
    (hpos : ∀ (n : ℕ) (q : ℝ), 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    ∃ M : ℝ, 0 < M ∧ IsCompact (Set.Icc (-M) M) ∧
      ∀ᶠ n : ℕ in atTop,
        originalMass (mu n) (Set.Icc (-M) M)ᶜ ≤
          Real.exp (-(n : ℝ) * A) := by
  let M : ℝ := A + |psi 1| + |psi (-1)| + 3
  have hM : 0 < M := by
    dsimp only [M]
    positivity
  have hupper := eventually_originalMass_Ici_le mu psi 1 M 1
    (by norm_num) (by norm_num) (fun n => hint n 1) hone
    (fun n => hpos n 1) (hlim 1)
  have hlower := eventually_originalMass_Iic_le mu psi (-1) (-M) 1
    (by norm_num) (by norm_num) (fun n => hint n (-1)) hone
    (fun n => hpos n (-1)) (hlim (-1))
  have hnpos : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
    Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩
  refine ⟨M, hM, isCompact_Icc, ?_⟩
  filter_upwards [hupper, hlower, hnpos] with n hu hl hn
  have hrateUpper : A + 1 ≤ 1 * M - psi 1 - 1 := by
    dsimp only [M]
    have hpsi : psi 1 ≤ |psi 1| := le_abs_self _
    have hnonneg : 0 ≤ |psi (-1)| := abs_nonneg _
    linarith
  have hrateLower : A + 1 ≤ (-1) * (-M) - psi (-1) - 1 := by
    dsimp only [M]
    have hpsi : psi (-1) ≤ |psi (-1)| := le_abs_self _
    have hnonneg : 0 ≤ |psi 1| := abs_nonneg _
    linarith
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hu' : originalMass (mu n) (Set.Ici M) ≤
      Real.exp (-(n : ℝ) * (A + 1)) :=
    hu.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hrateUpper (neg_nonpos.mpr hnreal)))
  have hl' : originalMass (mu n) (Set.Iic (-M)) ≤
      Real.exp (-(n : ℝ) * (A + 1)) :=
    hl.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hrateLower (neg_nonpos.mpr hnreal)))
  calc
    originalMass (mu n) (Set.Icc (-M) M)ᶜ ≤
        originalMass (mu n) (Set.Iic (-M)) +
          originalMass (mu n) (Set.Ici M) :=
      originalMass_compl_Icc_le_closedTails (mu n) M hM (hone n)
    _ ≤ 2 * Real.exp (-(n : ℝ) * (A + 1)) := by
      nlinarith
    _ ≤ Real.exp ((n : ℝ)) * Real.exp (-(n : ℝ) * (A + 1)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      have hnrealOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have htwo : (2 : ℝ) ≤ 1 + (n : ℝ) := by linarith
      exact htwo.trans (by simpa [add_comm] using Real.add_one_le_exp (n : ℝ))
    _ = Real.exp (-(n : ℝ) * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

end NCG.SCGFExponentialTightness
