/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteZeroTomographyExact

/-!
# Finite-height zero tomography: complete assembly

This file closes the assembly gap in `thm:GRH-finite-zero-tomography`.
`FiniteZeroTomographyExact` proves the Prony uniqueness, strip anti-aliasing,
unimodularity criterion, exact block-Hankel factorization, and the singular
floor separately.  The theorem below presents GRH.19--GRH.22 in one record,
with the row-subtracted output identity retained as the physical input stated
in the manuscript.
-/

open Polynomial Finset

namespace NCG
namespace FiniteHeightZeroTomography

open ZeroTomography

variable {H : Type*} [NormedAddCommGroup H] [Module ℂ H]

/-- Complete finite-height tomography packet (GRH.19--GRH.22).

The hypotheses `hY`, `hB`, `hD`, and `hA` are precisely the manuscript's
row-subtraction identity and the three least-singular-value bounds defining
`σ_Pr`, `m_vis`, and `σ_min(V_ζ)`.  Everything after those physical data is
derived: anti-aliasing makes the nodes distinct, Prony gives the unique monic
recurrence, node modulus detects the critical line, and exact Hankel
factorization multiplies the three floors. -/
theorem finite_height_zero_tomography
    {M : ℕ} {τ T : ℝ} (hτ : 0 < τ) (hτT : τ * T < Real.pi)
    (ρnode : Fin M → ℂ) (hdist : Function.Injective ρnode)
    (him : ∀ j, |(ρnode j).im| ≤ T)
    (v : Fin M → H) (hv : ∀ j, v j ≠ 0)
    (ζ : Fin M → ℂ)
    (hζdef : ∀ j,
      ζ j = Complex.exp ((τ : ℂ) * (ρnode j - ((1 : ℝ) / 2 : ℝ))))
    (Y : ℕ → H) (hY : ∀ k, Y k = signal ζ v k)
    {σV mvis : ℝ} (hσ : 0 ≤ σV) (hm : 0 ≤ mvis)
    (hB : ∀ c : Fin M → ℂ, σV * ‖c‖ ≤ ‖vandApply ζ c‖)
    (hD : ∀ u : Fin M → ℂ, mvis * ‖u‖ ≤ ‖diagApply v u‖)
    (hA : ∀ w : Fin M → H, σV * ‖w‖ ≤ ‖synthApply ζ w‖) :
    (∀ k, Y k = ∑ j, ζ j ^ k • v j) ∧
    (∀ P : Polynomial ℂ, P.Monic → P.natDegree = M →
      (∀ k : Fin M,
        ∑ i ∈ Finset.range (M + 1), P.coeff i • Y ((k : ℕ) + i) = 0) →
      P = ∏ j, (Polynomial.X - Polynomial.C (ζ j))) ∧
    ((∀ j, (ρnode j).re = 1 / 2) ↔ (∀ j, ‖ζ j‖ = 1)) ∧
    (∀ c : Fin M → ℂ,
      mvis * σV ^ 2 * ‖c‖ ≤
        ‖fun k : Fin M =>
          ∑ i : Fin M, c i • Y ((k : ℕ) + (i : ℕ))‖) := by
  obtain ⟨hSignal, hProny, hCritical⟩ :=
    grh_finite_zero_tomography hτ hτT ρnode hdist him v hv ζ hζdef Y hY
  refine ⟨hSignal, hProny, hCritical, fun c => ?_⟩
  simpa only [hY] using
    (hankel_sigma_lower ζ v hσ hm hB hD hA c)

end FiniteHeightZeroTomography
end NCG
