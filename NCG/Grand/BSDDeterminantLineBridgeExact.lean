/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.BSDBridge
import NCG.Grand.AnalyticJetPseudodeterminant

/-!
# Conditional analytic--Selmer determinant-line bridge

The full unitary chain comparison identifies the degree-zero cohomology
dimensions.  The independently normalized kernel-complement differential is
compared with the canonical reduced analytic-jet block; conjugation preserves
its determinant, hence its determinant-line magnitude.
-/

open Matrix

noncomputable section

namespace NCG.BSDDeterminantLine

/-- Magnitude of the determinant line of an invertible reduced differential. -/
def reducedDeterminantMagnitude {d : ℕ}
    (D : Matrix (Fin d) (Fin d) ℂ) : ℝ := ‖D.det‖

/-- Similar reduced differentials have exactly the same determinant-line
magnitude.  Unitarity is stronger than the invertibility used here. -/
theorem reducedDeterminantMagnitude_conj {d : ℕ}
    (D U : Matrix (Fin d) (Fin d) ℂ) (hU : IsUnit U.det) :
    reducedDeterminantMagnitude (U * D * U⁻¹) =
      reducedDeterminantMagnitude D := by
  rw [reducedDeterminantMagnitude, reducedDeterminantMagnitude,
    Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det U).2 hU)]

/-- **Conditional analytic--Selmer determinant-line bridge.**  B1 is
`halg`; B2 is the pair of conjugation identities for the full and reduced
differentials; B3 identifies the reduced arithmetic determinant with the
independently normalized arithmetic line. -/
theorem bsd_determinant_line_bridge
    (F : ℕ → ℂ) {m r ralg : ℕ}
    (hrm : r < m) (hlow : ∀ q, q < r → F q = 0) (hne : F r ≠ 0)
    (Jsel Ufull : Matrix (Fin m) (Fin m) ℂ)
    (hUfull : IsUnit Ufull.det)
    (halg : Module.finrank ℂ (LinearMap.ker Jsel.mulVecLin) = ralg)
    (hfull : Ufull * Jsel * Ufull⁻¹ = NCG.jetMatrix F m)
    (JselReduced Ured : Matrix (Fin (m - r)) (Fin (m - r)) ℂ)
    (hUred : IsUnit Ured.det)
    (hreduced : JselReduced =
      Ured * NCG.jetReducedMatrix F m r * Ured⁻¹) :
    r = ralg ∧
      reducedDeterminantMagnitude JselReduced =
        NCG.analyticJetNonzeroSingularProduct F m r := by
  have hker := NCG.kernel_dim_conjugation Jsel Ufull hUfull
  rw [hfull, halg] at hker
  have han := NCG.analytic_jet_rank_and_leading_magnitude F hrm hlow hne
  have hrank : r = ralg := by
    rw [han.1] at hker
    exact hker
  constructor
  · exact hrank
  · rw [hreduced, reducedDeterminantMagnitude_conj _ _ hUred,
      reducedDeterminantMagnitude, NCG.jetReducedMatrix_det,
      norm_pow, NCG.analyticJetNonzeroSingularProduct_eq]

end NCG.BSDDeterminantLine
