import NCG.Grand.FiniteLoadedEuclideanLandingNonemptyExact
import NCG.Grand.PhysicalSourceMinimality

/-!
# Finite common-history Euclidean/OS spectral landing

The five finite landing panels imply exterior reflection positivity, the exact
source-minimal exterior rank and dimension, and descent of the represented
algebraic data through the covariance null.  Source-minimality supplies the
usual uniqueness of any source-fixing intertwiner.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace NCG
namespace FiniteCommonHistoryEuclideanLanding

open FiniteLoadedEuclideanLanding
open ExteriorReflectionPositivityCriterion
open ExteriorSecondQuantizationRank

/-- The exact finite Euclidean/OS landing consequences of panels L1--L5. -/
theorem finite_common_history_Euclidean_landing {d : ℕ}
    (p : Packet d) (hp : IsLoadedLanding p) :
    ScalarExteriorPositive p.lineWeight p.covariance ∧
    (∀ n, p.wordKernel n =
      (p.lineWeight : ℂ) •
        FiniteCompoundMatrixExteriorPower.cmpd n p.covariance) ∧
    exteriorGammaRank p.covariance = 2 ^ p.covariance.rank ∧
    Fintype.card (SourceMinimalCarrier p.covariance) =
      2 ^ p.covariance.rank ∧
    (∀ a, p.representation a =
      a • (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
    p.coefficient.IsHermitian ∧
    p.grading.IsHermitian ∧
    p.grading * p.grading = 1 ∧
    p.coefficient * p.grading + p.grading * p.coefficient = 0 ∧
    p.realStructure * p.realStructure = 1 ∧
    (∀ (a : ℂ) (v : Fin d → ℂ),
      p.covariance.mulVec v = 0 →
      p.covariance.mulVec ((p.representation a).mulVec v) = 0) ∧
    0 < p.lineModulus ∧ p.lineSection ≠ 0 ∧
    p.zeroModeInsertion ≠ 0 := by
  rcases hp with ⟨hcyl, ⟨hq, hP⟩, ⟨hword, hheld⟩,
    ⟨hrep, hcoef, hgrade, hgradeSq, hodd, hrealSq, hnull⟩,
    hline, hmod, hsection, hzero⟩
  have hscalar : ScalarExteriorPositive p.lineWeight p.covariance := by
    apply (scalarExteriorPositive_iff p.lineWeight p.covariance).2
    rcases hq.eq_or_lt with hq0 | hqpos
    · exact Or.inl hq0.symm
    · exact Or.inr ⟨hqpos, hP⟩
  have hrank := smqg_exterior_rank p.covariance hP.1
  exact ⟨hscalar, hword, hrank.2.1, hrank.2.2, hrep, hcoef,
    hgrade, hgradeSq, hodd, hrealSq, hnull, hline, hsection, hzero⟩

/-- The source-minimal exterior fermion carrier has the displayed dimension
including its vacuum grade. -/
theorem sourceMinimal_fermion_dimension {d : ℕ}
    (p : Packet d) (hp : IsLoadedLanding p) :
    Fintype.card (SourceMinimalCarrier p.covariance) =
      2 ^ p.covariance.rank := by
  exact (finite_common_history_Euclidean_landing p hp).2.2.2.1

end FiniteCommonHistoryEuclideanLanding
end NCG

