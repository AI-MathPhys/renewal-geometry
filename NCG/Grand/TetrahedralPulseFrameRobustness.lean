/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TetrahedralOddPulseFrame
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Robustness of the tetrahedral two-pulse synthesis

The exact pulses have orthogonal squared norm two.  This file proves the
operator-level perturbation statement: an operator-norm perturbation by
`ε < √2` retains lower synthesis bound `(√2-ε)²`.  This is the
quadratic-form content of `cor:SM-tetrahedral-frame-robustness`, not merely its
scalar triangle-inequality shadow.
-/

open scoped InnerProductSpace

namespace NCG

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Perturbing a `√2`-tight synthesis by at most `ε` preserves the
adjoint lower frame bound `√2-ε`, and hence its squared quadratic-form
bound. -/
theorem perturbedSynthesis_frameLowerBound
    (S measured : E →L[ℝ] F) (ε : ℝ)
    (hframe : ∀ y : F, ‖S.adjoint y‖ = Real.sqrt 2 * ‖y‖)
    (hperturb : ‖measured - S‖ ≤ ε)
    (hε : ε < Real.sqrt 2) :
    (0 < Real.sqrt 2 - ε) ∧
      (∀ y : F, (Real.sqrt 2 - ε) * ‖y‖ ≤ ‖measured.adjoint y‖) ∧
      (∀ y : F,
        (Real.sqrt 2 - ε) ^ 2 * ‖y‖ ^ 2 ≤
          ‖measured.adjoint y‖ ^ 2) := by
  have hmargin : 0 < Real.sqrt 2 - ε := sub_pos.mpr hε
  have hadjoint : ‖measured.adjoint - S.adjoint‖ ≤ ε := by
    calc
      ‖measured.adjoint - S.adjoint‖ = ‖(measured - S).adjoint‖ := by
        rw [map_sub]
      _ = ‖measured - S‖ :=
        (ContinuousLinearMap.adjoint.norm_map (measured - S))
      _ ≤ ε := hperturb
  have hlower : ∀ y : F,
      (Real.sqrt 2 - ε) * ‖y‖ ≤ ‖measured.adjoint y‖ := by
    intro y
    have happly : ‖(measured.adjoint - S.adjoint) y‖ ≤ ε * ‖y‖ := by
      calc
        ‖(measured.adjoint - S.adjoint) y‖ ≤
            ‖measured.adjoint - S.adjoint‖ * ‖y‖ :=
          (measured.adjoint - S.adjoint).le_opNorm y
        _ ≤ ε * ‖y‖ :=
          mul_le_mul_of_nonneg_right hadjoint (norm_nonneg y)
    have htriangle : ‖S.adjoint y‖ ≤
        ‖measured.adjoint y‖ +
          ‖(measured.adjoint - S.adjoint) y‖ := by
      calc
        ‖S.adjoint y‖ =
            ‖measured.adjoint y -
              (measured.adjoint - S.adjoint) y‖ := by
                congr 1
                simp
        _ ≤ ‖measured.adjoint y‖ +
            ‖(measured.adjoint - S.adjoint) y‖ := norm_sub_le _ _
    rw [hframe y] at htriangle
    linarith
  refine ⟨hmargin, hlower, ?_⟩
  intro y
  have hleft : 0 ≤ (Real.sqrt 2 - ε) * ‖y‖ :=
    mul_nonneg hmargin.le (norm_nonneg y)
  have hright : 0 ≤ ‖measured.adjoint y‖ := norm_nonneg _
  nlinarith [hlower y]

/-- The coordinate synthesis of the exact two-pulse frame: after identifying
the two-dimensional relation space with its normalized pulse basis, synthesis
is `√2` times the identity. -/
noncomputable def exactTwoPulseCoordinateSynthesis :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Real.sqrt 2 • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))

/-- The exact coordinate synthesis has the required `√2` adjoint norm. -/
theorem exactTwoPulseCoordinateSynthesis_adjoint_norm
    (y : EuclideanSpace ℝ (Fin 2)) :
    ‖exactTwoPulseCoordinateSynthesis.adjoint y‖ = Real.sqrt 2 * ‖y‖ := by
  rw [exactTwoPulseCoordinateSynthesis, map_smul]
  rw [ContinuousLinearMap.adjoint_id]
  change ‖Real.sqrt 2 • y‖ = Real.sqrt 2 * ‖y‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- `cor:SM-tetrahedral-frame-robustness` in the normalized coordinates
certified by the explicit pulse-frame identities. -/
theorem tetrahedralTwoPulse_frameRobustness
    (measured : EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2)) (ε : ℝ)
    (hperturb : ‖measured - exactTwoPulseCoordinateSynthesis‖ ≤ ε)
    (hε : ε < Real.sqrt 2) :
    ∀ y : EuclideanSpace ℝ (Fin 2),
      (Real.sqrt 2 - ε) ^ 2 * ‖y‖ ^ 2 ≤
        ‖measured.adjoint y‖ ^ 2 := by
  exact (perturbedSynthesis_frameLowerBound
    exactTwoPulseCoordinateSynthesis measured ε
    exactTwoPulseCoordinateSynthesis_adjoint_norm hperturb hε).2.2

end NCG
