/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MatchingAxis

/-!
# Matching-axis half-edge decomposition

This file gives the exact finite linear-algebra package behind
thm:matching-axis-half-edge in the Gran-Tensor manuscript.  The twelve
matching-labelled half-edges are kept as a concrete finite type.  Rational
source matrices prove the two standard-copy Gram identities without numerical
approximation.  Five mutually orthogonal, permutation-equivariant projectors
realize the decomposition

[4] ⊕ [31]entry ⊕ [31]axis ⊕ [22] ⊕ [211]

with dimensions 1, 3, 3, 2, 3.  Finally an explicit eight-column basis
identifies the conditional point-Read innovation and its eigenvalue 1/12.
-/

open Matrix

namespace NCG
namespace MatchingAxisHalfEdgeDecomposition

noncomputable section

abbrev Vertex := Fin 4
abbrev Matching := Fin 3
abbrev MatchingHalfEdge := Vertex × Matching
abbrev InnovationCoordinate := Vertex × Fin 2

/-- The matching containing the unordered pair of distinct vertices.  Values
on the diagonal are irrelevant. -/
def matchingIndex : Vertex → Vertex → Matching :=
  ![![0, 0, 1, 2],
    ![0, 0, 2, 1],
    ![1, 2, 0, 0],
    ![2, 1, 0, 0]]

@[simp] theorem matchingIndex_partner (i : Vertex) (m : Matching) :
    matchingIndex i (matchPartner m i) = m := by
  fin_cases i <;> fin_cases m <;> decide

/-- The induced action of a vertex permutation on the three matchings. -/
def permuteMatching (σ : Equiv.Perm Vertex) (m : Matching) : Matching :=
  matchingIndex (σ 0) (σ (matchPartner m 0))

theorem permuteMatching_partner :
    ∀ (σ : Equiv.Perm Vertex) (m : Matching) (i : Vertex),
      matchPartner (permuteMatching σ m) (σ i) = σ (matchPartner m i) := by
  native_decide

theorem permuteMatching_bijective :
    ∀ σ : Equiv.Perm Vertex, Function.Bijective (permuteMatching σ) := by
  native_decide

/-- Diagonal S₄ action on matching-labelled half-edges. -/
noncomputable def permuteHalfEdge (σ : Equiv.Perm Vertex) :
    Equiv.Perm MatchingHalfEdge :=
  Equiv.prodCongr σ (Equiv.ofBijective (permuteMatching σ)
    (permuteMatching_bijective σ))

/-- Permutation matrix of the diagonal S₄ action. -/
def halfEdgeAction (σ : Equiv.Perm Vertex) :
    Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  fun p q =>
    if p = (σ q.1, permuteMatching σ q.2) then 1 else 0

/-- Entry source x ↦ ((i,m) ↦ xᵢ). -/
def entrySourceMatrix : Matrix MatchingHalfEdge Vertex ℚ :=
  fun p i => if p.1 = i then 1 else 0

/-- Locked-edge source x ↦ ((i,m) ↦ xᵢ + xⱼ). -/
def lockedSourceMatrix : Matrix MatchingHalfEdge Vertex ℚ :=
  fun p i => if p.1 = i ∨ matchPartner p.2 p.1 = i then 1 else 0

/-- Conditional matching-axis source S_lock - (2/3) S_ent. -/
def axisSourceMatrix : Matrix MatchingHalfEdge Vertex ℚ :=
  lockedSourceMatrix - (2 / 3 : ℚ) • entrySourceMatrix

/-- Uniform twelve-point Gram matrix of two source matrices. -/
def uniformGram (A B : Matrix MatchingHalfEdge Vertex ℚ) :
    Matrix Vertex Vertex ℚ :=
  (1 / 12 : ℚ) • (A.transpose * B)

def vertexOnes : Matrix Vertex Vertex ℚ := fun _ _ => 1

theorem entrySource_uniformGram :
    uniformGram entrySourceMatrix entrySourceMatrix = (1 / 4 : ℚ) • 1 := by
  native_decide

theorem lockedSource_uniformGram :
    uniformGram lockedSourceMatrix lockedSourceMatrix =
      (1 / 3 : ℚ) • 1 + (1 / 6 : ℚ) • vertexOnes := by
  native_decide

theorem entryLocked_uniformGram :
    uniformGram entrySourceMatrix lockedSourceMatrix =
      (1 / 6 : ℚ) • 1 + (1 / 12 : ℚ) • vertexOnes := by
  native_decide

theorem entryAxis_uniformGram :
    uniformGram entrySourceMatrix axisSourceMatrix =
      (1 / 12 : ℚ) • vertexOnes := by
  native_decide

theorem axisSource_uniformGram :
    uniformGram axisSourceMatrix axisSourceMatrix =
      (2 / 9 : ℚ) • 1 + (1 / 18 : ℚ) • vertexOnes := by
  native_decide

/-- Standard coefficient vectors have zero coordinate sum. -/
def IsStandard (x : Vertex → ℚ) : Prop := ∑ i, x i = 0

theorem vertexOnes_mulVec_of_standard {x : Vertex → ℚ}
    (hx : IsStandard x) :
    vertexOnes *ᵥ x = 0 := by
  ext i
  change ∑ j, x j = 0 at hx
  simpa only [Matrix.mulVec, dotProduct, vertexOnes, one_mul,
    Pi.zero_apply] using hx

theorem matchingAxis_standard_gram {x : Vertex → ℚ}
    (hx : IsStandard x) :
    uniformGram entrySourceMatrix entrySourceMatrix *ᵥ x = (1 / 4 : ℚ) • x ∧
    uniformGram lockedSourceMatrix lockedSourceMatrix *ᵥ x = (1 / 3 : ℚ) • x ∧
    uniformGram entrySourceMatrix lockedSourceMatrix *ᵥ x = (1 / 6 : ℚ) • x ∧
    uniformGram entrySourceMatrix axisSourceMatrix *ᵥ x = 0 ∧
    uniformGram axisSourceMatrix axisSourceMatrix *ᵥ x = (2 / 9 : ℚ) • x := by
  have hJ := vertexOnes_mulVec_of_standard hx
  rw [entrySource_uniformGram, lockedSource_uniformGram,
    entryLocked_uniformGram, entryAxis_uniformGram, axisSource_uniformGram]
  simp [hJ, Matrix.add_mulVec, Matrix.smul_mulVec]

/-! ## Manuscript normalization -/

/-- Real entry source used in the normalized two-standard plane. -/
def entrySourceReal : Matrix MatchingHalfEdge Vertex ℝ :=
  fun p i => if p.1 = i then 1 else 0

/-- Real locked-edge source. -/
def lockedSourceReal : Matrix MatchingHalfEdge Vertex ℝ :=
  fun p i => if p.1 = i ∨ matchPartner p.2 p.1 = i then 1 else 0

/-- Real conditional matching-axis source. -/
def axisSourceReal : Matrix MatchingHalfEdge Vertex ℝ :=
  lockedSourceReal - (2 / 3 : ℝ) • entrySourceReal

def normalizedEntrySource :
    Matrix MatchingHalfEdge Vertex ℝ :=
  (2 : ℝ) • entrySourceReal

def normalizedAxisSource :
    Matrix MatchingHalfEdge Vertex ℝ :=
  (3 / Real.sqrt 2 : ℝ) • axisSourceReal

def normalizedLockedSource :
    Matrix MatchingHalfEdge Vertex ℝ :=
  Real.sqrt 3 • lockedSourceReal

/-- The locked source is the fixed combination of the two normalized standard
copies appearing in the manuscript. -/
theorem normalizedLockedSource_decomposition :
    normalizedLockedSource =
      (1 / Real.sqrt 3 : ℝ) • normalizedEntrySource +
        Real.sqrt (2 / 3 : ℝ) • normalizedAxisSource := by
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by norm_num
  have h3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := by norm_num
  have hsqrtDiv :
      Real.sqrt (2 / 3 : ℝ) = Real.sqrt 2 / Real.sqrt 3 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  have hlocked :
      Real.sqrt (2 / 3 : ℝ) * (3 / Real.sqrt 2) = Real.sqrt 3 := by
    rw [hsqrtDiv]
    field_simp [ne_of_gt h2pos, ne_of_gt h3pos]
    nlinarith
  have hentry :
      (1 / Real.sqrt 3 : ℝ) * 2 =
        (Real.sqrt (2 / 3 : ℝ) * (3 / Real.sqrt 2)) * (2 / 3) := by
    rw [hlocked]
    field_simp [ne_of_gt h3pos]
    nlinarith
  have hentry' :
      (1 / Real.sqrt 3 : ℝ) * 2 = Real.sqrt 3 * (2 / 3) := by
    rw [hentry, hlocked]
  ext p i
  simp only [normalizedLockedSource, normalizedEntrySource,
    normalizedAxisSource, axisSourceReal, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  rw [← mul_assoc (Real.sqrt (2 / 3 : ℝ))]
  rw [hlocked]
  rw [← mul_assoc (1 / Real.sqrt 3 : ℝ) 2]
  rw [hentry']
  ring

/-! ## Equivariant isotypic projectors -/

def constantProjector : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  fun _ _ => 1 / 12

def entryFibreProjector : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  fun p q => if p.1 = q.1 then 1 / 3 else 0

def matchingFibreProjector : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  fun p q => if p.2 = q.2 then 1 / 4 else 0

def entryStandardProjector : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  entryFibreProjector - constantProjector

def matchingStandardProjector : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  matchingFibreProjector - constantProjector

def vertexStandardProjector : Matrix Vertex Vertex ℚ :=
  1 - (1 / 4 : ℚ) • vertexOnes

def axisStandardProjector : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  (3 / 8 : ℚ) •
    (axisSourceMatrix * vertexStandardProjector * axisSourceMatrix.transpose)

def residualThreeProjector : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  1 - constantProjector - entryStandardProjector -
    matchingStandardProjector - axisStandardProjector

theorem matchingAxis_projector_sum :
    constantProjector + entryStandardProjector + axisStandardProjector +
      matchingStandardProjector + residualThreeProjector = 1 := by
  native_decide

theorem matchingAxis_projectors_idempotent :
    constantProjector * constantProjector = constantProjector ∧
    entryStandardProjector * entryStandardProjector = entryStandardProjector ∧
    axisStandardProjector * axisStandardProjector = axisStandardProjector ∧
    matchingStandardProjector * matchingStandardProjector =
      matchingStandardProjector ∧
    residualThreeProjector * residualThreeProjector =
      residualThreeProjector := by
  native_decide

theorem matchingAxis_projectors_pairwiseOrthogonal :
    constantProjector * entryStandardProjector = 0 ∧
    constantProjector * axisStandardProjector = 0 ∧
    constantProjector * matchingStandardProjector = 0 ∧
    constantProjector * residualThreeProjector = 0 ∧
    entryStandardProjector * axisStandardProjector = 0 ∧
    entryStandardProjector * matchingStandardProjector = 0 ∧
    entryStandardProjector * residualThreeProjector = 0 ∧
    axisStandardProjector * matchingStandardProjector = 0 ∧
    axisStandardProjector * residualThreeProjector = 0 ∧
    matchingStandardProjector * residualThreeProjector = 0 := by
  native_decide

theorem matchingAxis_projector_traces :
    Matrix.trace constantProjector = 1 ∧
    Matrix.trace entryStandardProjector = 3 ∧
    Matrix.trace axisStandardProjector = 3 ∧
    Matrix.trace matchingStandardProjector = 2 ∧
    Matrix.trace residualThreeProjector = 3 := by
  native_decide

theorem matchingAxis_projectors_equivariant :
    ∀ σ : Equiv.Perm Vertex,
      halfEdgeAction σ * constantProjector =
          constantProjector * halfEdgeAction σ ∧
      halfEdgeAction σ * entryStandardProjector =
          entryStandardProjector * halfEdgeAction σ ∧
      halfEdgeAction σ * axisStandardProjector =
          axisStandardProjector * halfEdgeAction σ ∧
      halfEdgeAction σ * matchingStandardProjector =
          matchingStandardProjector * halfEdgeAction σ ∧
      halfEdgeAction σ * residualThreeProjector =
          residualThreeProjector * halfEdgeAction σ := by
  native_decide

/-- Exact projector form of [4] ⊕ 2[31] ⊕ [22] ⊕ [211]. -/
theorem matchingAxis_isotypic_decomposition :
    constantProjector + entryStandardProjector + axisStandardProjector +
        matchingStandardProjector + residualThreeProjector = 1 ∧
    (Matrix.trace constantProjector,
      Matrix.trace entryStandardProjector,
      Matrix.trace axisStandardProjector,
      Matrix.trace matchingStandardProjector,
      Matrix.trace residualThreeProjector) = (1, 3, 3, 2, 3) ∧
    (∀ σ : Equiv.Perm Vertex,
      halfEdgeAction σ * constantProjector =
          constantProjector * halfEdgeAction σ ∧
      halfEdgeAction σ * entryStandardProjector =
          entryStandardProjector * halfEdgeAction σ ∧
      halfEdgeAction σ * axisStandardProjector =
          axisStandardProjector * halfEdgeAction σ ∧
      halfEdgeAction σ * matchingStandardProjector =
          matchingStandardProjector * halfEdgeAction σ ∧
      halfEdgeAction σ * residualThreeProjector =
          residualThreeProjector * halfEdgeAction σ) := by
  refine ⟨matchingAxis_projector_sum, ?_, matchingAxis_projectors_equivariant⟩
  rcases matchingAxis_projector_traces with ⟨h0, h1, h2, h3, h4⟩
  simp [h0, h1, h2, h3, h4]

/-! ## Rank-eight conditional innovation -/

/-- Fibrewise centered point-Read projector. -/
def innovationProjector : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  1 - entryFibreProjector

/-- Conditional point-Read covariance. -/
def innovationCovariance : Matrix MatchingHalfEdge MatchingHalfEdge ℚ :=
  (1 / 12 : ℚ) • innovationProjector

/-- Two centered coordinates in each of the four three-point fibres. -/
def innovationBasisMatrix :
    Matrix MatchingHalfEdge InnovationCoordinate ℚ :=
  fun p q =>
    if p = (q.1, Fin.castSucc q.2) then 1
    else if p = (q.1, 2) then -1 else 0

/-- Coordinates obtained from the first two entries of each centered fibre. -/
def innovationCoordinateMatrix :
    Matrix InnovationCoordinate MatchingHalfEdge ℚ :=
  fun q p => innovationProjector (q.1, Fin.castSucc q.2) p

theorem innovationProjector_factorization :
    innovationProjector =
      innovationBasisMatrix * innovationCoordinateMatrix := by
  native_decide

theorem innovationProjector_fixes_basis :
    innovationProjector * innovationBasisMatrix = innovationBasisMatrix := by
  native_decide

theorem innovationBasisMatrix_injective :
    Function.Injective innovationBasisMatrix.mulVec := by
  intro x y hxy
  funext q
  have hq := congrFun hxy (q.1, Fin.castSucc q.2)
  have hlast : Fin.castSucc q.2 ≠ (2 : Fin 3) := by
    simpa using q.2.castSucc_ne_last
  have hrow (z : InnovationCoordinate → ℚ) :
      innovationBasisMatrix.mulVec z (q.1, Fin.castSucc q.2) = z q := by
    classical
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single q]
    · simp [innovationBasisMatrix]
    · intro b _ hb
      have hpair :
          (q.1, Fin.castSucc q.2) ≠ (b.1, Fin.castSucc b.2) := by
        intro hp
        apply hb
        apply Prod.ext
        · exact (congrArg Prod.fst hp).symm
        · apply Fin.castSucc_injective
          exact (congrArg Prod.snd hp).symm
      simp [innovationBasisMatrix, hpair, hlast]
    · simp
  rw [hrow x, hrow y] at hq
  exact hq

theorem innovationProjector_range_eq_basisRange :
    LinearMap.range innovationProjector.mulVecLin =
      LinearMap.range innovationBasisMatrix.mulVecLin := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨innovationCoordinateMatrix *ᵥ x, ?_⟩
    change innovationBasisMatrix *ᵥ
      (innovationCoordinateMatrix *ᵥ x) = innovationProjector *ᵥ x
    rw [Matrix.mulVec_mulVec, ← innovationProjector_factorization]
  · rintro y ⟨x, rfl⟩
    refine ⟨innovationBasisMatrix *ᵥ x, ?_⟩
    change innovationProjector *ᵥ
      (innovationBasisMatrix *ᵥ x) = innovationBasisMatrix *ᵥ x
    rw [Matrix.mulVec_mulVec, innovationProjector_fixes_basis]

theorem conditionalPointReadInnovation_finrank :
    Module.finrank ℚ (LinearMap.range innovationCovariance.mulVecLin) = 8 := by
  have hrangeScalar :
      LinearMap.range innovationCovariance.mulVecLin =
        LinearMap.range innovationProjector.mulVecLin := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      refine ⟨(1 / 12 : ℚ) • x, ?_⟩
      ext p
      simp [innovationCovariance, Matrix.mulVecLin]
    · rintro y ⟨x, rfl⟩
      refine ⟨(12 : ℚ) • x, ?_⟩
      ext p
      simp [innovationCovariance, Matrix.mulVecLin]
  rw [hrangeScalar, innovationProjector_range_eq_basisRange,
    LinearMap.finrank_range_of_inj innovationBasisMatrix_injective]
  simp

theorem conditionalPointReadInnovation_spectrum :
    innovationCovariance * innovationCovariance =
        (1 / 12 : ℚ) • innovationCovariance ∧
    innovationCovariance * innovationBasisMatrix =
        (1 / 12 : ℚ) • innovationBasisMatrix ∧
    Module.finrank ℚ (LinearMap.range innovationCovariance.mulVecLin) = 8 := by
  refine ⟨?_, ?_, conditionalPointReadInnovation_finrank⟩
  · native_decide
  · native_decide

end
end MatchingAxisHalfEdgeDecomposition
end NCG
