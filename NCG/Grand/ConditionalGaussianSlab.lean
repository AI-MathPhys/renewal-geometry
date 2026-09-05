import NCG.Grand.FiniteGrassmannWickExteriorExact
import NCG.Grand.ExteriorReflectionPositivityCriterionExact
import NCG.Grand.ExteriorSecondQuantizationDressingExact
import NCG.Grand.FiniteGaussianOccurrenceResidualExact
import NCG.Grand.FinitePositiveBosonicGaussianMixtureExact

/-!
# Conditional Gaussian slab theorem

On one fixed finite bosonic history, the Grassmann Wick functional equals
pairing against fermionic exterior second quantization.  Positivity of the
complete reflected hierarchy is exactly scalar-line positivity together with
one-particle positivity; dressing, held-out occurrence tests, and positive
bosonic mixing are supplied by companion exact modules.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace NCG
namespace ConditionalGaussianSlab

open FiniteGrassmannWickExterior
open FiniteCompoundMatrixExteriorPower
open ExteriorReflectionPositivityCriterion
open ExteriorSecondQuantizationDressing

/-- The direct conditional Wick functional, exterior realization, complete
positivity criterion, and dressed Gram realization on one finite slab. -/
theorem conditional_gaussian_slab
    {d : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
    (q : ℝ) (P : Matrix (Fin d) (Fin d) ℂ)
    (hq : 0 ≤ q) (hP : P.PosSemidef) :
    (∀ X Y : FockVector d,
      (q : ℂ) * reflectedGaussianPairing P X Y =
        (q : ℂ) * secondQuantizationPairing P X Y) ∧
    ScalarExteriorPositive q P ∧
    (∀ r : ℕ, ∀ W : Matrix (GradeIdx r d) F ℂ,
      (dressedExteriorKernel q P r W).PosSemidef ∧
      dressedExteriorKernel q P r W =
        (dressedExteriorSynthesis q P r W)ᴴ *
          dressedExteriorSynthesis q P r W) := by
  have hwick := reflectedGaussianPairing_eq_secondQuantization P
  have hscalar : ScalarExteriorPositive q P := by
    apply (scalarExteriorPositive_iff q P).2
    rcases hq.eq_or_lt with hq0 | hqpos
    · exact Or.inl hq0.symm
    · exact Or.inr ⟨hqpos, hP⟩
  refine ⟨?_, hscalar, ?_⟩
  · intro X Y
    rw [hwick X Y]
  · intro r W
    exact ⟨dressedExteriorKernel_posSemidef hq hP r W,
      dressedExteriorKernel_eq_synthesisGram hq hP r W⟩

/-- Conversely, positivity of every reflected scalar exterior grade detects
the scalar branch and one-particle positivity already at the vacuum and
grade-one words. -/
theorem conditional_gaussian_positivity_iff
    {d : ℕ} (q : ℝ) (P : Matrix (Fin d) (Fin d) ℂ) :
    ScalarExteriorPositive q P ↔
      q = 0 ∨ (0 < q ∧ P.PosSemidef) :=
  scalarExteriorPositive_iff q P

end ConditionalGaussianSlab
end NCG

