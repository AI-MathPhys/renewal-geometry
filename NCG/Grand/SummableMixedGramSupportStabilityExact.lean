/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SummablePositiveMixedGramCorrection
import NCG.Grand.GRHRestoringShortExact

/-!
# Support stability from the corrected Gram spectral floor

This removes the tautological support hypothesis from the final clause of
`thm:summable-mixed-Gram-correction`.  Membership in the faithful spectral window with
positive floor is proved to make the corrected Gram positive definite; its CFC support
projection is therefore derived to be the identity.  Support stability for two cutoffs
then follows without assuming either projection in advance.
-/

namespace NCG
namespace SummableMixedGramSupportStability

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- A corrected Gram in a positive spectral window has full support. -/
theorem supportProjection_eq_one_of_spectralFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {A : Matrix ι ι ℂ}
    (hA : A ∈ faithfulGramSpectralSlice (ι := ι) μ M) :
    SourceCoercivityInfluence.supportProj
      (faithfulGramSpectralSlice_isStrictlyPositive hμ hA).posDef.1 = 1 :=
  GRHRestoringShort.supportProj_eq_one
    (faithfulGramSpectralSlice_isStrictlyPositive hμ hA).posDef

/-- Support projections of any two corrected Grams in the same positive-floor window are
exactly equal, with the equality derived from the floor rather than supplied as input. -/
theorem corrected_supportProjections_stable
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {A B : Matrix ι ι ℂ}
    (hA : A ∈ faithfulGramSpectralSlice (ι := ι) μ M)
    (hB : B ∈ faithfulGramSpectralSlice (ι := ι) μ M) :
    SourceCoercivityInfluence.supportProj
        (faithfulGramSpectralSlice_isStrictlyPositive hμ hA).posDef.1 =
      SourceCoercivityInfluence.supportProj
        (faithfulGramSpectralSlice_isStrictlyPositive hμ hB).posDef.1 := by
  rw [supportProjection_eq_one_of_spectralFloor hμ hA,
    supportProjection_eq_one_of_spectralFloor hμ hB]

/-- The complete spectral-window conclusion used by the summable mixed-Gram theorem:
strict positivity and exact support stability are simultaneous consequences of one common
positive lower floor. -/
theorem spectralFloor_gives_strictPositivity_and_supportStability
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {A B : Matrix ι ι ℂ}
    (hA : A ∈ faithfulGramSpectralSlice (ι := ι) μ M)
    (hB : B ∈ faithfulGramSpectralSlice (ι := ι) μ M) :
    IsStrictlyPositive A ∧ IsStrictlyPositive B ∧
      SourceCoercivityInfluence.supportProj
          (faithfulGramSpectralSlice_isStrictlyPositive hμ hA).posDef.1 =
        SourceCoercivityInfluence.supportProj
          (faithfulGramSpectralSlice_isStrictlyPositive hμ hB).posDef.1 :=
  ⟨faithfulGramSpectralSlice_isStrictlyPositive hμ hA,
    faithfulGramSpectralSlice_isStrictlyPositive hμ hB,
    corrected_supportProjections_stable hμ hA hB⟩

end SummableMixedGramSupportStability
end NCG
