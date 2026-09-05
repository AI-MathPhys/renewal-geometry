/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PrivateMultiplicityMoorePenroseExport
import NCG.Grand.LockedIncidenceOrbitPolytope

/-!
# Explicit locked private-provenance compiler

The four terminal cells contribute twenty-four real statistics.  This module
turns those statistics into the two standard-multiplicity frames and proves
the weighted Gram, rank, singular Schur, Moore--Penrose propagation, and
homogeneous-tail formulas used by the manuscript's private compiler.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace LockedPrivateProvenanceCompiler

noncomputable section

abbrev Cell := Fin 4
abbrev StandardAxis := Fin 2

/-- The twenty-four accepted locked-cylinder statistics: six real numbers in
each of the four terminal cells. -/
structure AcceptedLockedStatistics where
  terminalMass : Cell → ℝ
  tailMass : Cell → ℝ
  aggregateE : Cell → ℝ
  aggregateA : Cell → ℝ
  tailE : Cell → ℝ
  tailA : Cell → ℝ
  terminalMass_nonneg : ∀ c, 0 ≤ terminalMass c
  zeroMass_zeroMoments : ∀ c, terminalMass c = 0 →
    aggregateE c = 0 ∧ aggregateA c = 0 ∧ tailE c = 0 ∧ tailA c = 0

/-- Moore--Penrose reciprocal of a nonnegative cell mass. -/
def massReciprocal (τ : ℝ) : ℝ := if τ = 0 then 0 else τ⁻¹

/-- The aggregate standard-coordinate row
`(E_c/√3,A_c/√6)`. -/
def AcceptedLockedStatistics.aggregateFrame
    (S : AcceptedLockedStatistics) : Matrix Cell StandardAxis ℂ :=
  fun c j => if j = 0 then S.aggregateE c / Real.sqrt 3
    else S.aggregateA c / Real.sqrt 6

/-- The binary-tail standard-coordinate row
`(E_c^(1)/√3,A_c^(1)/√6)`. -/
def AcceptedLockedStatistics.tailFrame
    (S : AcceptedLockedStatistics) : Matrix Cell StandardAxis ℂ :=
  fun c j => if j = 0 then S.tailE c / Real.sqrt 3
    else S.tailA c / Real.sqrt 6

/-- Terminal standard multiplicity metric. -/
def AcceptedLockedStatistics.terminalMetric
    (S : AcceptedLockedStatistics) : Matrix Cell Cell ℂ :=
  Matrix.diagonal fun c => S.terminalMass c

/-- The diagonal reciprocal-mass weight `W`. -/
def AcceptedLockedStatistics.weight
    (S : AcceptedLockedStatistics) : Matrix Cell Cell ℂ :=
  Matrix.diagonal fun c => massReciprocal (S.terminalMass c)

/-- Positive diagonal square root of `W`. -/
def AcceptedLockedStatistics.weightRoot
    (S : AcceptedLockedStatistics) : Matrix Cell Cell ℂ :=
  Matrix.diagonal fun c => Real.sqrt (massReciprocal (S.terminalMass c))

theorem massReciprocal_nonneg (τ : ℝ) (hτ : 0 ≤ τ) :
    0 ≤ massReciprocal τ := by
  by_cases hzero : τ = 0
  · simp [massReciprocal, hzero]
  · simp [massReciprocal, hzero, inv_nonneg.mpr hτ]

theorem weightRoot_conjTranspose_mul_self (S : AcceptedLockedStatistics) :
    S.weightRootᴴ * S.weightRoot = S.weight := by
  have hself : S.weightRootᴴ = S.weightRoot := by
    ext c d
    by_cases hcd : c = d
    · subst d
      simp [AcceptedLockedStatistics.weightRoot, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply]
    · simp [AcceptedLockedStatistics.weightRoot, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, hcd, Ne.symm hcd]
  rw [hself]
  simp only [AcceptedLockedStatistics.weightRoot,
    AcceptedLockedStatistics.weight, Matrix.diagonal_mul_diagonal]
  congr 1
  funext c
  norm_cast
  simpa [pow_two] using
    Real.sq_sqrt (massReciprocal_nonneg _ (S.terminalMass_nonneg c))

/-- Weighted aggregate and tail source frames. -/
def AcceptedLockedStatistics.weightedAggregate
    (S : AcceptedLockedStatistics) : Matrix Cell StandardAxis ℂ :=
  S.weightRoot * S.aggregateFrame

def AcceptedLockedStatistics.weightedTail
    (S : AcceptedLockedStatistics) : Matrix Cell StandardAxis ℂ :=
  S.weightRoot * S.tailFrame

/-- Aggregate, cross, and tail Grams. -/
def AcceptedLockedStatistics.aggregateGram
    (S : AcceptedLockedStatistics) : Matrix StandardAxis StandardAxis ℂ :=
  S.aggregateFrameᴴ * S.weight * S.aggregateFrame

def AcceptedLockedStatistics.crossGram
    (S : AcceptedLockedStatistics) : Matrix StandardAxis StandardAxis ℂ :=
  S.aggregateFrameᴴ * S.weight * S.tailFrame

def AcceptedLockedStatistics.tailGram
    (S : AcceptedLockedStatistics) : Matrix StandardAxis StandardAxis ℂ :=
  S.tailFrameᴴ * S.weight * S.tailFrame

theorem zeroMass_zeroRows (S : AcceptedLockedStatistics) (c : Cell)
    (hc : S.terminalMass c = 0) :
    S.aggregateFrame c = 0 ∧ S.tailFrame c = 0 := by
  obtain ⟨hE, hA, hE1, hA1⟩ := S.zeroMass_zeroMoments c hc
  constructor <;> funext j <;> fin_cases j <;>
    simp [AcceptedLockedStatistics.aggregateFrame,
      AcceptedLockedStatistics.tailFrame, hE, hA, hE1, hA1]

theorem weightedGram_formulas (S : AcceptedLockedStatistics) :
    S.aggregateGram = S.weightedAggregateᴴ * S.weightedAggregate ∧
    S.crossGram = S.weightedAggregateᴴ * S.weightedTail ∧
    S.tailGram = S.weightedTailᴴ * S.weightedTail := by
  have hroot := weightRoot_conjTranspose_mul_self S
  constructor
  · rw [AcceptedLockedStatistics.aggregateGram,
      AcceptedLockedStatistics.weightedAggregate,
      Matrix.conjTranspose_mul, ← hroot]
    simp only [Matrix.mul_assoc]
  constructor
  · rw [AcceptedLockedStatistics.crossGram,
      AcceptedLockedStatistics.weightedAggregate,
      AcceptedLockedStatistics.weightedTail,
      Matrix.conjTranspose_mul, ← hroot]
    simp only [Matrix.mul_assoc]
  · rw [AcceptedLockedStatistics.tailGram,
      AcceptedLockedStatistics.weightedTail,
      Matrix.conjTranspose_mul, ← hroot]
    simp only [Matrix.mul_assoc]

/-- Determinant of two standard-coordinate rows. -/
def rowDet (A : Matrix Cell StandardAxis ℂ) (c d : Cell) : ℂ :=
  A c 0 * A d 1 - A c 1 * A d 0

set_option maxRecDepth 10000 in
/-- Four-cell `2×2` Cauchy--Binet identity. -/
theorem fourCell_weightedGram_determinant
    (A : Matrix Cell StandardAxis ℂ) (w : Cell → ℝ) :
    (Aᴴ * Matrix.diagonal (fun c => (w c : ℂ)) * A).det =
      (w 0 * w 1 : ℂ) * star (rowDet A 0 1) * rowDet A 0 1 +
      (w 0 * w 2 : ℂ) * star (rowDet A 0 2) * rowDet A 0 2 +
      (w 0 * w 3 : ℂ) * star (rowDet A 0 3) * rowDet A 0 3 +
      (w 1 * w 2 : ℂ) * star (rowDet A 1 2) * rowDet A 1 2 +
      (w 1 * w 3 : ℂ) * star (rowDet A 1 3) * rowDet A 1 3 +
      (w 2 * w 3 : ℂ) * star (rowDet A 2 3) * rowDet A 2 3 := by
  simp [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_four,
    rowDet, Matrix.diagonal_apply]
  ring

theorem aggregateGram_determinant (S : AcceptedLockedStatistics) :
    S.aggregateGram.det =
      let A := S.aggregateFrame
      let w := fun c => massReciprocal (S.terminalMass c)
      (w 0 * w 1 : ℂ) * star (rowDet A 0 1) * rowDet A 0 1 +
      (w 0 * w 2 : ℂ) * star (rowDet A 0 2) * rowDet A 0 2 +
      (w 0 * w 3 : ℂ) * star (rowDet A 0 3) * rowDet A 0 3 +
      (w 1 * w 2 : ℂ) * star (rowDet A 1 2) * rowDet A 1 2 +
      (w 1 * w 3 : ℂ) * star (rowDet A 1 3) * rowDet A 1 3 +
      (w 2 * w 3 : ℂ) * star (rowDet A 2 3) * rowDet A 2 3 := by
  simpa [AcceptedLockedStatistics.aggregateGram,
    AcceptedLockedStatistics.weight] using
    (fourCell_weightedGram_determinant S.aggregateFrame
      (fun c => massReciprocal (S.terminalMass c)))

theorem readableProvenanceRank_atMostTwo (S : AcceptedLockedStatistics) :
    S.weightedAggregate.rank ≤ 2 := by
  exact Matrix.rank_le_width S.weightedAggregate

/-! ## Singular Moore--Penrose compiler -/

/-- Support of the readable aggregate Gram. -/
def AcceptedLockedStatistics.readableSupport
    (S : AcceptedLockedStatistics) : Matrix StandardAxis StandardAxis ℂ :=
  sourceGramPseudoinverse S.weightedAggregate *
    (S.weightedAggregateᴴ * S.weightedAggregate)

/-- Canonical dressed private propagator `G_A† C_AT`. -/
def AcceptedLockedStatistics.privatePropagator
    (S : AcceptedLockedStatistics) : Matrix StandardAxis StandardAxis ℂ :=
  sourceGramPseudoinverse S.weightedAggregate *
    (S.weightedAggregateᴴ * S.weightedTail)

/-- Exact range Schur residual. -/
def AcceptedLockedStatistics.rangeResidual
    (S : AcceptedLockedStatistics) : Matrix StandardAxis StandardAxis ℂ :=
  sourceSchurResidual S.weightedAggregate S.weightedTail

/-- Exact null-support residual, written as its weighted Gram. -/
def AcceptedLockedStatistics.nullResidual
    (S : AcceptedLockedStatistics) : Matrix StandardAxis StandardAxis ℂ :=
  let R := S.weightedTail * (1 - S.readableSupport)
  Rᴴ * R

theorem readableSupport_properties (S : AcceptedLockedStatistics) :
    S.readableSupportᴴ = S.readableSupport ∧
      S.readableSupport * S.readableSupport = S.readableSupport ∧
      S.weightedAggregate * S.readableSupport = S.weightedAggregate := by
  exact NCG.sourceCoefficientSupport_properties S.weightedAggregate

theorem privatePropagator_leftSupported (S : AcceptedLockedStatistics) :
    S.readableSupport * S.privatePropagator = S.privatePropagator := by
  let A := S.weightedAggregate
  let X := Aᴴ * A
  let J := sourceGramPseudoinverse A
  have hJXJ := (sourceGramPseudoinverse_projection A).2.2.1
  change (J * X) * (J * (Aᴴ * S.weightedTail)) =
    J * (Aᴴ * S.weightedTail)
  calc
    (J * X) * (J * (Aᴴ * S.weightedTail)) =
        (J * X * J) * (Aᴴ * S.weightedTail) := by
      simp only [Matrix.mul_assoc]
    _ = J * (Aᴴ * S.weightedTail) := by rw [hJXJ]

theorem nullResidual_eq_projectedTailGram (S : AcceptedLockedStatistics) :
    S.nullResidual =
      (1 - S.readableSupport) *
        (S.weightedTailᴴ * S.weightedTail) *
          (1 - S.readableSupport) := by
  have hQH := (readableSupport_properties S).1
  rw [AcceptedLockedStatistics.nullResidual]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hQH]
  simp only [Matrix.mul_assoc]

theorem rangeResidual_eq_weightedLeastSquares
    (S : AcceptedLockedStatistics) :
    S.rangeResidual =
      (S.weightedTail - S.weightedAggregate * S.privatePropagator)ᴴ *
        (S.weightedTail - S.weightedAggregate * S.privatePropagator) := by
  let A := S.weightedAggregate
  let T := S.weightedTail
  let P := sourceRangeProjection A
  obtain ⟨hPH, hP2, -⟩ :=
    (sourceGramPseudoinverse_projection A).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  have hcomplement2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hdiff : T - A *
      (sourceGramPseudoinverse A * (Aᴴ * T)) = (1 - P) * T := by
    dsimp only [P, sourceRangeProjection]
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
  rw [AcceptedLockedStatistics.rangeResidual,
    sourceSchurResidual_eq_orthogonalResidual]
  change Tᴴ * (1 - P) * T = _
  change Tᴴ * (1 - P) * T =
    (T - A * (sourceGramPseudoinverse A * (Aᴴ * T)))ᴴ *
      (T - A * (sourceGramPseudoinverse A * (Aᴴ * T)))
  rw [hdiff]
  symm
  calc
    ((1 - P) * T)ᴴ * ((1 - P) * T) =
        Tᴴ * ((1 - P) * (1 - P)) * T := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, hPH]
      simp only [Matrix.mul_assoc]
    _ = Tᴴ * (1 - P) * T := by
      rw [hcomplement2]

theorem rangeResidual_zero_implies_canonicalFactorization
    (S : AcceptedLockedStatistics) (hzero : S.rangeResidual = 0) :
    S.weightedTail = S.weightedAggregate * S.privatePropagator := by
  let R := S.weightedTail - S.weightedAggregate * S.privatePropagator
  have hgram : Rᴴ * R = 0 := by
    rw [← rangeResidual_eq_weightedLeastSquares S, hzero]
  have hR : R = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hgram
  exact sub_eq_zero.mp hR

theorem nullResidual_eq_zero_iff (S : AcceptedLockedStatistics) :
    S.nullResidual = 0 ↔
      S.weightedTail * (1 - S.readableSupport) = 0 := by
  unfold AcceptedLockedStatistics.nullResidual
  exact Matrix.conjTranspose_mul_self_eq_zero

/-- Joint vanishing gives the unique dressed propagator on the faithful
readable quotient, including both support equations. -/
theorem jointResidual_zero_branch (S : AcceptedLockedStatistics) :
    (S.rangeResidual = 0 ∧ S.nullResidual = 0) ↔
      S.weightedTail = S.weightedAggregate * S.privatePropagator ∧
        S.privatePropagator =
          S.readableSupport * S.privatePropagator * S.readableSupport := by
  constructor
  · rintro ⟨hrange, hnull⟩
    have hfactor := rangeResidual_zero_implies_canonicalFactorization S hrange
    have htailQ : S.weightedTail * S.readableSupport = S.weightedTail := by
      have h := (nullResidual_eq_zero_iff S).mp hnull
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
      exact h.symm
    have hleft := privatePropagator_leftSupported S
    have hright : S.privatePropagator * S.readableSupport =
        S.privatePropagator := by
      rw [AcceptedLockedStatistics.privatePropagator]
      simp only [Matrix.mul_assoc]
      rw [htailQ]
    refine ⟨hfactor, ?_⟩
    calc
      S.privatePropagator =
          S.privatePropagator * S.readableSupport := hright.symm
      _ = (S.readableSupport * S.privatePropagator) *
          S.readableSupport := by rw [hleft]
  · rintro ⟨hfactor, hsupp⟩
    constructor
    · exact (sourceSchurResidual_eq_zero_iff_rangeIncluded
        S.weightedAggregate S.weightedTail).mpr
          ⟨S.privatePropagator, hfactor⟩
    · rw [nullResidual_eq_zero_iff S]
      rw [hfactor]
      have hPQ : S.privatePropagator * S.readableSupport =
          S.privatePropagator := by
        calc
          S.privatePropagator * S.readableSupport =
              (S.readableSupport * S.privatePropagator *
                S.readableSupport) * S.readableSupport := by rw [← hsupp]
          _ = S.readableSupport * S.privatePropagator *
              (S.readableSupport * S.readableSupport) := by
            simp only [Matrix.mul_assoc]
          _ = S.privatePropagator := by
            rw [(readableSupport_properties S).2.1, ← hsupp]
      calc
        S.weightedAggregate * S.privatePropagator *
            (1 - S.readableSupport) =
          S.weightedAggregate *
            (S.privatePropagator * (1 - S.readableSupport)) := by
              simp only [Matrix.mul_assoc]
        _ = 0 := by
          rw [Matrix.mul_sub, Matrix.mul_one, hPQ, sub_self,
            Matrix.mul_zero]

/-- Homogeneous survival removes exactly one scalar factor. -/
theorem homogeneousTail_undressedPropagator
    (S : AcceptedLockedStatistics)
    (Mprivate : Matrix StandardAxis StandardAxis ℂ)
    (s : ℝ) (hs : s ≠ 0)
    (hhom : S.privatePropagator = (s : ℂ) • Mprivate) :
    Mprivate = ((s : ℂ)⁻¹) • S.privatePropagator :=
  homogeneousPrivateTail_export S.privatePropagator Mprivate s hs hhom

/-- The metric inequality used for physical contractivity after homogeneous
survival. -/
def MetricContractiveAtSurvival
    (G P : Matrix StandardAxis StandardAxis ℂ) (s : ℝ) : Prop :=
  Pᴴ * G * P ≤ (s ^ 2 : ℝ) • G

theorem metricContractivity_rescale
    (G M : Matrix StandardAxis StandardAxis ℂ) (s : ℝ) (hs : 0 < s) :
    Mᴴ * G * M ≤ G ↔
      ((s : ℝ) • M)ᴴ * G * ((s : ℝ) • M) ≤
        (s ^ 2 : ℝ) • G := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, star_trivial]
  rw [show s * s = s ^ 2 by ring]
  exact (smul_le_smul_iff_of_pos_left hs2).symm

/-- On a one-dimensional readable quotient the metric condition is exactly
the scalar survival bound. -/
theorem rankOne_metricContractivity (g p s : ℝ)
    (hg : 0 < g) (hs : 0 ≤ s) :
    g * p ^ 2 ≤ s ^ 2 * g ↔ |p| ≤ s := by
  constructor
  · intro h
    have hp2 : p ^ 2 ≤ s ^ 2 := by nlinarith
    nlinarith [sq_abs p]
  · intro h
    have hprod : 0 ≤ (s - |p|) * (s + |p|) :=
      mul_nonneg (sub_nonneg.mpr h) (add_nonneg hs (abs_nonneg p))
    have hp2 : p ^ 2 ≤ s ^ 2 := by nlinarith [sq_abs p]
    nlinarith

/-- A Hermitian `2×2` matrix is positive semidefinite exactly when its trace
and determinant are nonnegative. -/
theorem finTwo_posSemidef_iff_trace_det_nonneg
    (D : Matrix StandardAxis StandardAxis ℂ) (hD : Dᴴ = D) :
    D.PosSemidef ↔ (0 : ℂ) ≤ D.trace ∧ (0 : ℂ) ≤ D.det := by
  let hHerm : D.IsHermitian := hD
  constructor
  · intro hpos
    exact ⟨hpos.trace_nonneg, hpos.det_nonneg⟩
  · rintro ⟨htrace, hdet⟩
    rw [hHerm.posSemidef_iff_eigenvalues_nonneg]
    have htrace' := htrace
    rw [hHerm.trace_eq_sum_eigenvalues] at htrace'
    simp only [Fin.sum_univ_two] at htrace'
    have hdet' := hdet
    rw [hHerm.det_eq_prod_eigenvalues] at hdet'
    simp only [Fin.prod_univ_two] at hdet'
    have htraceR : 0 ≤ hHerm.eigenvalues 0 + hHerm.eigenvalues 1 :=
      Complex.zero_le_real.mp (by simpa using htrace')
    have hdetR : 0 ≤ hHerm.eigenvalues 0 * hHerm.eigenvalues 1 :=
      Complex.zero_le_real.mp (by simpa using hdet')
    intro i
    fin_cases i
    · by_contra hneg
      push Not at hneg
      change hHerm.eigenvalues 0 < 0 at hneg
      nlinarith
    · by_contra hneg
      push Not at hneg
      change hHerm.eigenvalues 1 < 0 at hneg
      nlinarith

/-- Rank-two contractivity is therefore exactly the manuscript's two scalar
tests for `D_s = s²G_A - P_privᴴ G_A P_priv`. -/
theorem rankTwo_metricContractivity_trace_det
    (G P : Matrix StandardAxis StandardAxis ℂ) (s : ℝ)
    (hG : Gᴴ = G) :
    let D := (s ^ 2 : ℝ) • G - Pᴴ * G * P
    D.PosSemidef ↔ (0 : ℂ) ≤ D.trace ∧ (0 : ℂ) ≤ D.det := by
  dsimp
  apply finTwo_posSemidef_iff_trace_det_nonneg
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hG]
  simp only [star_trivial, Matrix.mul_assoc]

/-- The six statistic fields on four cells determine the complete compiler
input; all displayed matrices and residuals above are functions of this
record. -/
theorem twentyFourStatistics_determine_panel
    (S S' : AcceptedLockedStatistics)
    (hτ : S.terminalMass = S'.terminalMass)
    (hσ : S.tailMass = S'.tailMass)
    (hE : S.aggregateE = S'.aggregateE)
    (hA : S.aggregateA = S'.aggregateA)
    (hE1 : S.tailE = S'.tailE)
    (hA1 : S.tailA = S'.tailA) :
    S = S' := by
  cases S
  cases S'
  simp_all

end
end LockedPrivateProvenanceCompiler
end NCG
