/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteLineValuedEinstein

/-!
# Line-valued Einstein response on a finite phase cohomology complex

The phase line is represented by its protected finite cochain complex.  A
connection one-cochain need not be globally exact; curvature is its
two-coboundary, and the nontrivial degree-one class is precisely the holonomy
obstruction to an ordinary scalar action.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Pointwise polar decomposition of an entire nowhere-zero amplitude
section, with a unit phase section and real action coordinate. -/
theorem finite_amplitude_section_polar
    {X : Type*} (z : X → ℂ) (hz : ∀ x, z x ≠ 0) :
    ∃ S : X → ℝ, ∃ s : X → ℂ,
      (∀ x, ‖s x‖ = 1) ∧
      (∀ x, z x = Real.exp (-S x) • s x) ∧
      (∀ x, S x = -Real.log ‖z x‖) := by
  classical
  choose S s hs hpolar hS using fun x => amplitude_polar (z x) (hz x)
  exact ⟨S, s, hs, hpolar, hS⟩

/-- Complete finite line-valued Einstein packet.  The phase cochain is allowed
to carry a nonzero degree-one cohomology class; a global scalar gauge exists
exactly when curvature vanishes and that holonomy class is trivial. -/
theorem line_valued_Einstein_phase_cohomology_exact
    {X v e f n : Type*}
    [Fintype v] [Fintype e] [Fintype n] [DecidableEq n]
    (z dz : X → ℂ) (hz : ∀ x, z x ≠ 0)
    (d0 : Matrix e v ℂ) (d1 : Matrix f e ℂ)
    (hd : d1 * d0 = 0)
    (S : v → ℂ) (alpha : e → ℂ)
    (G : Matrix n n ℂ) (hG : G.PosDef) (E t : n → ℂ) :
    (∃ Sreal : X → ℝ, ∃ phase : X → ℂ,
      (∀ x, ‖phase x‖ = 1) ∧
      (∀ x, z x = Real.exp (-Sreal x) • phase x) ∧
      (∀ x, Sreal x = -Real.log ‖z x‖))
    ∧ ((∃! Xi : X → ℂ, ∀ x, dz x = Xi x * z x)
      ∧ (-finitePhaseLogResponse d0 S alpha =
        d0 *ᵥ S - Complex.I • alpha)
      ∧ (d1 *ᵥ finitePhaseLogResponse d0 S alpha =
        Complex.I • finitePhaseCurvature d1 alpha)
      ∧ (GlobalScalarPhaseGauge d0 S alpha ↔
        finitePhaseCurvature d1 alpha = 0 ∧
          FinitePhaseHolonomyTrivial d0 alpha)
      ∧ (((star E ⬝ᵥ G⁻¹.mulVec E).re +
        (star t ⬝ᵥ G⁻¹.mulVec t).re = 0) ↔ E = 0 ∧ t = 0)) := by
  exact ⟨finite_amplitude_section_polar z hz,
    finite_line_valued_Einstein z dz hz d0 d1 hd S alpha G hG E t⟩

/-- On an exact protected phase complex, flatness alone is equivalent to
trivial holonomy and hence to existence of the ordinary scalar phase gauge. -/
theorem scalar_action_iff_flat_on_exact_phase_complex
    {v e f : Type*} [Fintype v] [Fintype e]
    (d0 : Matrix e v ℂ) (d1 : Matrix f e ℂ)
    (hd : d1 * d0 = 0)
    (hexact : ExactAtFinitePhaseOne d0 d1)
    (S : v → ℂ) (alpha : e → ℂ) :
    GlobalScalarPhaseGauge d0 S alpha ↔
      finitePhaseCurvature d1 alpha = 0 := by
  rw [globalScalarPhaseGauge_iff_flat_trivialHolonomy d0 d1 hd S alpha]
  constructor
  · exact fun h => h.1
  · intro hflat
    exact ⟨hflat, (curvature_zero_iff_trivialHolonomy
      d0 d1 hd hexact alpha).mp hflat⟩

end NCG
