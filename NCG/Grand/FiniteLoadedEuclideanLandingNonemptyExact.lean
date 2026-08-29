/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExteriorReflectionPositivityCriterionExact
import NCG.Grand.ExteriorSecondQuantizationRankExact

/-!
# A nonempty finite loaded Euclidean/OS landing

This is the explicit finite witness required by
`cor:GT-NCG-finite-landing-nonempty`.  It keeps every component on one
two-dimensional cylinder, uses the positive reflected covariance `P = 1`,
the exact exterior kernels `⋀ⁿP`, a nontrivial odd Dirac coefficient, scalar
represented operations, and a populated positive local line.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace NCG
namespace FiniteLoadedEuclideanLanding

open FiniteCompoundMatrixExteriorPower
open ExteriorReflectionPositivityCriterion
open ExteriorSecondQuantizationRank

/-- A finite loaded packet with all displayed data sharing one carrier. -/
structure Packet (d : ℕ) where
  cylinder : ℂ
  coefficient : Matrix (Fin d) (Fin d) ℂ
  reflection : Matrix (Fin d) (Fin d) ℂ
  covariance : Matrix (Fin d) (Fin d) ℂ
  lineWeight : ℝ
  representation : ℂ → Matrix (Fin d) (Fin d) ℂ
  realStructure : Matrix (Fin d) (Fin d) ℂ
  grading : Matrix (Fin d) (Fin d) ℂ
  wordKernel : (n : ℕ) → Matrix (GradeIdx n d) (GradeIdx n d) ℂ
  heldOutTwoWord : Matrix (GradeIdx 2 d) (GradeIdx 2 d) ℂ
  lineSection : ℂ
  lineModulus : ℝ
  divisorOrder : ℕ
  zeroModeInsertion : ℂ

/-- The five finite landing panels L1--L5, specialized only by replacing the
abstract OS-null quotient with its literal covariance kernel. -/
def IsLoadedLanding {d : ℕ} (p : Packet d) : Prop :=
  p.cylinder ≠ 0 ∧
  (0 ≤ p.lineWeight ∧ p.covariance.PosSemidef) ∧
  ((∀ n, p.wordKernel n = (p.lineWeight : ℂ) • cmpd n p.covariance) ∧
    p.heldOutTwoWord - (p.lineWeight : ℂ) • cmpd 2 p.covariance = 0) ∧
  ((∀ a, p.representation a = a • (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
    p.coefficient.IsHermitian ∧ p.grading.IsHermitian ∧
    p.grading * p.grading = 1 ∧
    p.coefficient * p.grading + p.grading * p.coefficient = 0 ∧
    p.realStructure * p.realStructure = 1 ∧
    (∀ (a : ℂ) (v : Fin d → ℂ), p.covariance.mulVec v = 0 →
      p.covariance.mulVec ((p.representation a).mulVec v) = 0)) ∧
  (0 < p.lineModulus ∧ p.lineModulus = ‖p.lineSection‖ ∧
    p.lineSection ≠ 0 ∧ p.zeroModeInsertion ≠ 0)

/-- The odd two-point coefficient. -/
def dirac2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The grading on the two-point packet. -/
def grading2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- One explicit loaded finite cylinder. -/
def basicPacket : Packet 2 where
  cylinder := 1
  coefficient := dirac2
  reflection := 1
  covariance := 1
  lineWeight := 1
  representation := fun a => a • 1
  realStructure := 1
  grading := grading2
  wordKernel := fun n => cmpd n 1
  heldOutTwoWord := cmpd 2 1
  lineSection := 1
  lineModulus := 1
  divisorOrder := 0
  zeroModeInsertion := 1

theorem dirac2_isHermitian : dirac2.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dirac2, Matrix.conjTranspose_apply]

theorem grading2_isHermitian : grading2.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading2, Matrix.conjTranspose_apply]

theorem grading2_sq : grading2 * grading2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading2, Matrix.mul_apply, Fin.sum_univ_two]

theorem dirac2_odd : dirac2 * grading2 + grading2 * dirac2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dirac2, grading2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The explicit packet passes all five finite landing panels. -/
theorem basicPacket_isLoadedLanding : IsLoadedLanding basicPacket := by
  have hP : basicPacket.covariance.PosSemidef := by
    change (1 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef
    exact Matrix.PosSemidef.one
  refine ⟨by norm_num [basicPacket], ?_, ?_, ?_, ?_⟩
  · exact ⟨by norm_num [basicPacket], hP⟩
  · constructor
    · intro n
      simp [basicPacket]
    · simp [basicPacket]
  · refine ⟨fun a => rfl, dirac2_isHermitian, grading2_isHermitian,
      grading2_sq, dirac2_odd, ?_, ?_⟩
    · simp [basicPacket]
    · intro a v hv
      have hv0 : v = 0 := by simpa [basicPacket] using hv
      subst v
      simp [basicPacket]
  · norm_num [basicPacket]

/-- The reflected exterior kernels are positive on every grade. -/
theorem basicPacket_exteriorPositive :
    ExteriorPositive basicPacket.covariance := by
  apply (exteriorPositive_iff basicPacket.covariance).2
  change (1 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef
  exact Matrix.PosSemidef.one

/-- The source-minimal fermion carrier of the explicit packet has dimension
`2^rank(P)=4`, including the vacuum grade. -/
theorem basicPacket_fermionCarrier_card :
    exteriorGammaRank basicPacket.covariance = 4 ∧
      Fintype.card (SourceMinimalCarrier basicPacket.covariance) = 4 := by
  have h := smqg_exterior_rank basicPacket.covariance Matrix.isHermitian_one
  have hrank : basicPacket.covariance.rank = 2 := by
    simp [basicPacket, Matrix.rank_one]
  rw [h.2.1, h.2.2, hrank]
  norm_num

/-- **`cor:GT-NCG-finite-landing-nonempty`.**  A nonempty cutoff-indexed
family of finite loaded Euclidean/OS packets, with exact exterior positivity
and its source-minimal fermion dimension. -/
theorem finite_loaded_spectral_branch_nonempty :
    ∃ family : ℕ → Packet 2, ∀ X,
      IsLoadedLanding (family X) ∧
      ExteriorPositive (family X).covariance ∧
      exteriorGammaRank (family X).covariance = 4 ∧
      Fintype.card (SourceMinimalCarrier (family X).covariance) = 4 := by
  refine ⟨fun _ => basicPacket, fun X => ?_⟩
  exact ⟨basicPacket_isLoadedLanding, basicPacket_exteriorPositive,
    basicPacket_fermionCarrier_card.1, basicPacket_fermionCarrier_card.2⟩

end FiniteLoadedEuclideanLanding
end NCG
