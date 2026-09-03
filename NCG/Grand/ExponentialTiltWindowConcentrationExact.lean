/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExponentialTiltSCGFConcentrationExact

/-!
# Window concentration for concrete exponentially tilted laws

The complement of an open interval is the disjoint union of its two closed
tails.  This file turns the two tilted Chernoff tail limits into convergence
of the actual tilted window mass to one.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace NCG.ExponentialTiltWindowConcentration

open NCG.ExponentialTiltMeasure
open NCG.ExponentialTiltSCGFConcentration
open NCG.SCGFExponentialTiltConcentration

/-- Exact decomposition of a concrete tilted open-window mass into one minus
the two complementary tail masses. -/
theorem tiltedMass_Ioo_eq_one_sub_tails
    (mu : Measure ℝ) (n : ℕ) (k lower upper : ℝ) (hlu : lower < upper)
    (hk : Integrable (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) mu)
    (hpos : 0 < exponentialMoment mu n k) :
    tiltedMass mu n k (Set.Ioo lower upper) =
      1 - tiltedMass mu n k (Set.Iic lower) -
        tiltedMass mu n k (Set.Ici upper) := by
  let f : ℝ → ℝ := fun x => Real.exp ((n : ℝ) * k * x)
  have hcomp : (Set.Ioo lower upper)ᶜ =
      Set.Iic lower ∪ Set.Ici upper := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ioo, Set.mem_union,
      Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro hx
      by_cases hxl : x ≤ lower
      · exact Or.inl hxl
      · right
        apply le_of_not_gt
        intro hxu
        exact hx ⟨lt_of_not_ge hxl, hxu⟩
    · intro hx hwindow
      rcases hx with hxl | hxu
      · exact (not_lt_of_ge hxl) hwindow.1
      · exact (not_lt_of_ge hxu) hwindow.2
  have hdisj : Disjoint (Set.Iic lower) (Set.Ici upper) := by
    rw [Set.disjoint_left]
    intro x hxl hxu
    exact (not_le_of_gt hlu) (hxu.trans hxl)
  have htails :
      (∫ x in (Set.Ioo lower upper)ᶜ, f x ∂mu) =
        (∫ x in Set.Iic lower, f x ∂mu) +
          ∫ x in Set.Ici upper, f x ∂mu := by
    rw [hcomp]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ici
      hk.integrableOn hk.integrableOn
  have hpartition :
      (∫ x in Set.Ioo lower upper, f x ∂mu) +
          ∫ x in (Set.Ioo lower upper)ᶜ, f x ∂mu = ∫ x, f x ∂mu :=
    MeasureTheory.integral_add_compl
      (μ := mu) (f := f) (s := Set.Ioo lower upper) measurableSet_Ioo hk
  rw [htails] at hpartition
  unfold tiltedMass exponentialMoment
  change (∫ x in Set.Ioo lower upper, f x ∂mu) / (∫ x, f x ∂mu) = _
  have hden : (∫ x, f x ∂mu) ≠ 0 := by
    change exponentialMoment mu n k ≠ 0
    exact hpos.ne'
  dsimp only [f] at hpartition hden ⊢
  field_simp [hden]
  linarith

/-- Vanishing lower and upper tilted tails imply that the mass of the open
window between them converges to one. -/
theorem tiltedMass_Ioo_tendsto_one_of_tails
    (mu : ℕ → Measure ℝ) (k lower upper : ℝ) (hlu : lower < upper)
    (hint : ∀ n : ℕ, Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * k * x)) (mu n))
    (hpos : ∀ n : ℕ, 0 < exponentialMoment (mu n) n k)
    (hlower : Tendsto
      (fun n => tiltedMass (mu n) n k (Set.Iic lower)) atTop (𝓝 0))
    (hupper : Tendsto
      (fun n => tiltedMass (mu n) n k (Set.Ici upper)) atTop (𝓝 0)) :
    Tendsto (fun n => tiltedMass (mu n) n k (Set.Ioo lower upper))
      atTop (𝓝 1) := by
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have h : Tendsto
      (fun n => 1 - tiltedMass (mu n) n k (Set.Iic lower) -
        tiltedMass (mu n) n k (Set.Ici upper)) atTop (𝓝 1) := by
    simpa using (hconst.sub hlower).sub hupper
  convert h using 1
  funext n
  exact tiltedMass_Ioo_eq_one_sub_tails (mu n) n k lower upper hlu
    (hint n) (hpos n)

/-- At every exposed value `a = psi'(k)`, the concrete law tilted by `k`
concentrates in each nontrivial open window around `a`. -/
theorem exposed_tiltedWindow_tendsto_one
    (mu : ℕ → Measure ℝ) (psi : ℝ → ℝ) (k a delta : ℝ)
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta)
    (hint : ∀ (n : ℕ) (q : ℝ), Integrable
      (fun x : ℝ => Real.exp ((n : ℝ) * q * x)) (mu n))
    (hpos : ∀ (n : ℕ) (q : ℝ), 0 < exponentialMoment (mu n) n q)
    (hlim : ∀ q, Tendsto
      (fun n => normalizedLogMoment
        (fun m u => exponentialMoment (mu m) m u) n q)
      atTop (𝓝 (psi q))) :
    Tendsto (fun n =>
      tiltedMass (mu n) n k (Set.Ioo (a - delta) (a + delta)))
      atTop (𝓝 1) := by
  obtain ⟨qUpper, hqUpper, hupper⟩ :=
    exists_upper_tiltedMass_tendsto_zero mu psi k a delta
      hderiv hdelta hint hpos hlim
  obtain ⟨qLower, hqLower, hlower⟩ :=
    exists_lower_tiltedMass_tendsto_zero mu psi k a delta
      hderiv hdelta hint hpos hlim
  exact tiltedMass_Ioo_tendsto_one_of_tails mu k (a - delta) (a + delta)
    (by linarith) (fun n => hint n k) (fun n => hpos n k) hlower hupper

end NCG.ExponentialTiltWindowConcentration
