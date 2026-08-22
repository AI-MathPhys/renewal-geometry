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

All finite identities are certified by the kernel (`decide +kernel`) on an
**integer computational layer**: every rational source matrix and projector
is an explicit rational multiple of the cast of an integer matrix, the
identities are decided over `ℤ`, and cast back.  No `native_decide` is used.
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
  decide +kernel

theorem permuteMatching_bijective :
    ∀ σ : Equiv.Perm Vertex, Function.Bijective (permuteMatching σ) := by
  decide +kernel

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

/-! ## The integer computational layer -/

/-- Cast an integer matrix to a rational one. -/
def castQ {m n : Type} (M : Matrix m n ℤ) : Matrix m n ℚ :=
  M.map (Int.castRingHom ℚ)

theorem castQ_apply {m n : Type} (M : Matrix m n ℤ) (i : m) (j : n) :
    castQ M i j = (M i j : ℚ) := rfl

theorem castQ_mul {m n o : Type} [Fintype n] (A : Matrix m n ℤ)
    (B : Matrix n o ℤ) : castQ (A * B) = castQ A * castQ B :=
  Matrix.map_mul

theorem castQ_transpose {m n : Type} (A : Matrix m n ℤ) :
    castQ A.transpose = (castQ A).transpose :=
  Matrix.transpose_map

theorem castQ_add {m n : Type} (A B : Matrix m n ℤ) :
    castQ (A + B) = castQ A + castQ B :=
  Matrix.map_add _ (fun _ _ => by simp) A B

theorem castQ_sub {m n : Type} (A B : Matrix m n ℤ) :
    castQ (A - B) = castQ A - castQ B :=
  Matrix.map_sub _ (fun _ _ => by simp) A B

theorem castQ_zsmul {m n : Type} (k : ℤ) (A : Matrix m n ℤ) :
    castQ (k • A) = (k : ℚ) • castQ A := by
  ext i j
  simp [castQ_apply, Matrix.smul_apply]

theorem castQ_one {n : Type} [DecidableEq n] :
    castQ (1 : Matrix n n ℤ) = 1 :=
  Matrix.map_one _ (by simp) (by simp)

theorem castQ_zero {m n : Type} :
    castQ (0 : Matrix m n ℤ) = 0 := by
  ext i j
  simp [castQ_apply]

theorem castQ_trace {n : Type} [Fintype n] (A : Matrix n n ℤ) :
    Matrix.trace (castQ A) = ((Matrix.trace A : ℤ) : ℚ) := by
  simp [Matrix.trace, Matrix.diag, castQ_apply]

/-- Integer entry source. -/
def entryZ : Matrix MatchingHalfEdge Vertex ℤ :=
  fun p i => if p.1 = i then 1 else 0

/-- Integer locked source. -/
def lockedZ : Matrix MatchingHalfEdge Vertex ℤ :=
  fun p i => if p.1 = i ∨ matchPartner p.2 p.1 = i then 1 else 0

/-- Three times the axis source: `3·S_lock - 2·S_ent`. -/
def axisZ : Matrix MatchingHalfEdge Vertex ℤ :=
  (3 : ℤ) • lockedZ - (2 : ℤ) • entryZ

/-- Integer all-ones matrices. -/
def onesZ4 : Matrix Vertex Vertex ℤ := fun _ _ => 1
def onesZ12 : Matrix MatchingHalfEdge MatchingHalfEdge ℤ := fun _ _ => 1

theorem entrySource_eq_cast : entrySourceMatrix = castQ entryZ := by
  ext p i
  simp only [entrySourceMatrix, entryZ, castQ_apply]
  split_ifs <;> simp

theorem lockedSource_eq_cast : lockedSourceMatrix = castQ lockedZ := by
  ext p i
  simp only [lockedSourceMatrix, lockedZ, castQ_apply]
  split_ifs <;> simp

theorem vertexOnes_eq_cast : vertexOnes = castQ onesZ4 := by
  ext i j
  simp [vertexOnes, onesZ4, castQ_apply]

theorem axisSource_eq_cast :
    axisSourceMatrix = (1 / 3 : ℚ) • castQ axisZ := by
  rw [axisSourceMatrix, entrySource_eq_cast, lockedSource_eq_cast, axisZ,
    castQ_sub, castQ_zsmul, castQ_zsmul]
  ext p i
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-! ## Gram identities (decided over `ℤ`) -/

theorem entryZ_gram : entryZ.transpose * entryZ = (3 : ℤ) • 1 := by
  decide +kernel

theorem lockedZ_gram :
    lockedZ.transpose * lockedZ = (4 : ℤ) • 1 + (2 : ℤ) • onesZ4 := by
  decide +kernel

theorem entryLockedZ_gram :
    entryZ.transpose * lockedZ = (2 : ℤ) • 1 + onesZ4 := by
  decide +kernel

theorem entryAxisZ_gram :
    entryZ.transpose * axisZ = (3 : ℤ) • onesZ4 := by
  decide +kernel

theorem axisZ_gram :
    axisZ.transpose * axisZ = (24 : ℤ) • 1 + (6 : ℤ) • onesZ4 := by
  decide +kernel

theorem entrySource_uniformGram :
    uniformGram entrySourceMatrix entrySourceMatrix = (1 / 4 : ℚ) • 1 := by
  rw [uniformGram, entrySource_eq_cast, ← castQ_transpose, ← castQ_mul,
    entryZ_gram, castQ_zsmul, castQ_one, smul_smul]
  norm_num

theorem lockedSource_uniformGram :
    uniformGram lockedSourceMatrix lockedSourceMatrix =
      (1 / 3 : ℚ) • 1 + (1 / 6 : ℚ) • vertexOnes := by
  rw [uniformGram, lockedSource_eq_cast, ← castQ_transpose, ← castQ_mul,
    lockedZ_gram, castQ_add, castQ_zsmul, castQ_zsmul, castQ_one,
    vertexOnes_eq_cast, smul_add, smul_smul, smul_smul]
  norm_num

theorem entryLocked_uniformGram :
    uniformGram entrySourceMatrix lockedSourceMatrix =
      (1 / 6 : ℚ) • 1 + (1 / 12 : ℚ) • vertexOnes := by
  rw [uniformGram, entrySource_eq_cast, lockedSource_eq_cast,
    ← castQ_transpose, ← castQ_mul, entryLockedZ_gram, castQ_add,
    castQ_zsmul, castQ_one, vertexOnes_eq_cast, smul_add, smul_smul]
  norm_num

theorem entryAxis_uniformGram :
    uniformGram entrySourceMatrix axisSourceMatrix =
      (1 / 12 : ℚ) • vertexOnes := by
  rw [uniformGram, entrySource_eq_cast, axisSource_eq_cast,
    ← castQ_transpose, Matrix.mul_smul, ← castQ_mul, entryAxisZ_gram,
    castQ_zsmul, vertexOnes_eq_cast, smul_smul, smul_smul]
  norm_num

theorem axisSource_uniformGram :
    uniformGram axisSourceMatrix axisSourceMatrix =
      (2 / 9 : ℚ) • 1 + (1 / 18 : ℚ) • vertexOnes := by
  rw [uniformGram, axisSource_eq_cast, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, ← castQ_transpose, ← castQ_mul,
    axisZ_gram, castQ_add, castQ_zsmul, castQ_zsmul, castQ_one,
    vertexOnes_eq_cast]
  simp only [smul_add, smul_smul]
  norm_num

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

/-! ### Integer numerators with common scale `96` -/

/-- Entry-fibre indicator. -/
def fibreEZ : Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  fun p q => if p.1 = q.1 then 1 else 0

/-- Matching-fibre indicator. -/
def fibreMZ : Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  fun p q => if p.2 = q.2 then 1 else 0

def constantZ : Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  (8 : ℤ) • onesZ12

def entryStandardZ : Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  (32 : ℤ) • fibreEZ - (8 : ℤ) • onesZ12

def matchingStandardZ : Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  (24 : ℤ) • fibreMZ - (8 : ℤ) • onesZ12

/-- `4·P_std` on vertices. -/
def vertexStandardZ : Matrix Vertex Vertex ℤ :=
  (4 : ℤ) • 1 - onesZ4

def axisStandardZ : Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  axisZ * vertexStandardZ * axisZ.transpose

def residualThreeZ : Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  (96 : ℤ) • 1 - constantZ - entryStandardZ - matchingStandardZ
    - axisStandardZ

theorem constantProjector_eq_cast :
    constantProjector = (1 / 96 : ℚ) • castQ constantZ := by
  ext p q
  simp only [constantProjector, constantZ, onesZ12, castQ_apply,
    Matrix.smul_apply, smul_eq_mul]
  push_cast
  norm_num

theorem entryStandardProjector_eq_cast :
    entryStandardProjector = (1 / 96 : ℚ) • castQ entryStandardZ := by
  ext p q
  simp only [entryStandardProjector, entryFibreProjector, constantProjector,
    entryStandardZ, fibreEZ, onesZ12, castQ_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> norm_num

theorem matchingStandardProjector_eq_cast :
    matchingStandardProjector = (1 / 96 : ℚ) • castQ matchingStandardZ := by
  ext p q
  simp only [matchingStandardProjector, matchingFibreProjector,
    constantProjector, matchingStandardZ, fibreMZ, onesZ12, castQ_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> norm_num

theorem vertexStandardProjector_eq_cast :
    vertexStandardProjector = (1 / 4 : ℚ) • castQ vertexStandardZ := by
  rw [vertexStandardProjector, vertexStandardZ, castQ_sub, castQ_zsmul,
    castQ_one, vertexOnes_eq_cast, smul_sub, smul_smul]
  norm_num

theorem axisStandardProjector_eq_cast :
    axisStandardProjector = (1 / 96 : ℚ) • castQ axisStandardZ := by
  rw [axisStandardProjector, axisSource_eq_cast,
    vertexStandardProjector_eq_cast, axisStandardZ, castQ_mul, castQ_mul,
    castQ_transpose, Matrix.transpose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

theorem residualThreeProjector_eq_cast :
    residualThreeProjector = (1 / 96 : ℚ) • castQ residualThreeZ := by
  rw [residualThreeProjector, residualThreeZ, constantProjector_eq_cast,
    entryStandardProjector_eq_cast, matchingStandardProjector_eq_cast,
    axisStandardProjector_eq_cast, castQ_sub, castQ_sub, castQ_sub,
    castQ_sub, castQ_zsmul, castQ_one, smul_sub, smul_sub, smul_sub,
    smul_sub, smul_smul]
  norm_num

/-- The permutation matrix over `ℤ`. -/
def halfEdgeActionZ (σ : Equiv.Perm Vertex) :
    Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  fun p q => if p = (σ q.1, permuteMatching σ q.2) then 1 else 0

theorem halfEdgeAction_eq_cast (σ : Equiv.Perm Vertex) :
    halfEdgeAction σ = castQ (halfEdgeActionZ σ) := by
  ext p q
  simp only [halfEdgeAction, halfEdgeActionZ, castQ_apply]
  split_ifs <;> simp

/-! ### Decided integer identities -/

theorem projectorZ_sum :
    constantZ + entryStandardZ + axisStandardZ + matchingStandardZ
      + residualThreeZ = (96 : ℤ) • 1 := by
  decide +kernel

theorem projectorZ_idempotent :
    constantZ * constantZ = (96 : ℤ) • constantZ ∧
    entryStandardZ * entryStandardZ = (96 : ℤ) • entryStandardZ ∧
    axisStandardZ * axisStandardZ = (96 : ℤ) • axisStandardZ ∧
    matchingStandardZ * matchingStandardZ = (96 : ℤ) • matchingStandardZ ∧
    residualThreeZ * residualThreeZ = (96 : ℤ) • residualThreeZ := by
  decide +kernel

theorem projectorZ_pairwiseOrthogonal :
    constantZ * entryStandardZ = 0 ∧
    constantZ * axisStandardZ = 0 ∧
    constantZ * matchingStandardZ = 0 ∧
    constantZ * residualThreeZ = 0 ∧
    entryStandardZ * axisStandardZ = 0 ∧
    entryStandardZ * matchingStandardZ = 0 ∧
    entryStandardZ * residualThreeZ = 0 ∧
    axisStandardZ * matchingStandardZ = 0 ∧
    axisStandardZ * residualThreeZ = 0 ∧
    matchingStandardZ * residualThreeZ = 0 := by
  decide +kernel

theorem projectorZ_traces :
    Matrix.trace constantZ = 96 ∧
    Matrix.trace entryStandardZ = 288 ∧
    Matrix.trace axisStandardZ = 288 ∧
    Matrix.trace matchingStandardZ = 192 ∧
    Matrix.trace residualThreeZ = 288 := by
  decide +kernel

theorem projectorZ_equivariant :
    ∀ σ : Equiv.Perm Vertex,
      halfEdgeActionZ σ * constantZ = constantZ * halfEdgeActionZ σ ∧
      halfEdgeActionZ σ * entryStandardZ =
          entryStandardZ * halfEdgeActionZ σ ∧
      halfEdgeActionZ σ * axisStandardZ =
          axisStandardZ * halfEdgeActionZ σ ∧
      halfEdgeActionZ σ * matchingStandardZ =
          matchingStandardZ * halfEdgeActionZ σ ∧
      halfEdgeActionZ σ * residualThreeZ =
          residualThreeZ * halfEdgeActionZ σ := by
  decide +kernel

/-! ### Transfer to the rational projectors -/

/-- Idempotence transfers through the scaling `P = (1/96)·cast Pz`. -/
theorem idempotent_of_Z
    (P : Matrix MatchingHalfEdge MatchingHalfEdge ℚ)
    (Pz : Matrix MatchingHalfEdge MatchingHalfEdge ℤ)
    (hP : P = (1 / 96 : ℚ) • castQ Pz)
    (hz : Pz * Pz = (96 : ℤ) • Pz) : P * P = P := by
  rw [hP, Matrix.smul_mul, Matrix.mul_smul, ← castQ_mul, hz, castQ_zsmul,
    smul_smul, smul_smul]
  norm_num

theorem orthogonal_of_Z
    (P Q : Matrix MatchingHalfEdge MatchingHalfEdge ℚ)
    (Pz Qz : Matrix MatchingHalfEdge MatchingHalfEdge ℤ)
    (hP : P = (1 / 96 : ℚ) • castQ Pz)
    (hQ : Q = (1 / 96 : ℚ) • castQ Qz)
    (hz : Pz * Qz = 0) : P * Q = 0 := by
  rw [hP, hQ, Matrix.smul_mul, Matrix.mul_smul, ← castQ_mul, hz, castQ_zero,
    smul_zero, smul_zero]

theorem commute_of_Z (σ : Equiv.Perm Vertex)
    (P : Matrix MatchingHalfEdge MatchingHalfEdge ℚ)
    (Pz : Matrix MatchingHalfEdge MatchingHalfEdge ℤ)
    (hP : P = (1 / 96 : ℚ) • castQ Pz)
    (hz : halfEdgeActionZ σ * Pz = Pz * halfEdgeActionZ σ) :
    halfEdgeAction σ * P = P * halfEdgeAction σ := by
  rw [hP, halfEdgeAction_eq_cast, Matrix.mul_smul, Matrix.smul_mul,
    ← castQ_mul, ← castQ_mul, hz]

theorem matchingAxis_projector_sum :
    constantProjector + entryStandardProjector + axisStandardProjector +
      matchingStandardProjector + residualThreeProjector = 1 := by
  rw [constantProjector_eq_cast, entryStandardProjector_eq_cast,
    axisStandardProjector_eq_cast, matchingStandardProjector_eq_cast,
    residualThreeProjector_eq_cast, ← smul_add, ← smul_add, ← smul_add,
    ← smul_add, ← castQ_add, ← castQ_add, ← castQ_add, ← castQ_add,
    projectorZ_sum, castQ_zsmul, castQ_one, smul_smul]
  norm_num

theorem matchingAxis_projectors_idempotent :
    constantProjector * constantProjector = constantProjector ∧
    entryStandardProjector * entryStandardProjector = entryStandardProjector ∧
    axisStandardProjector * axisStandardProjector = axisStandardProjector ∧
    matchingStandardProjector * matchingStandardProjector =
      matchingStandardProjector ∧
    residualThreeProjector * residualThreeProjector =
      residualThreeProjector := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := projectorZ_idempotent
  exact ⟨idempotent_of_Z _ _ constantProjector_eq_cast h0,
    idempotent_of_Z _ _ entryStandardProjector_eq_cast h1,
    idempotent_of_Z _ _ axisStandardProjector_eq_cast h2,
    idempotent_of_Z _ _ matchingStandardProjector_eq_cast h3,
    idempotent_of_Z _ _ residualThreeProjector_eq_cast h4⟩

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
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    projectorZ_pairwiseOrthogonal
  exact ⟨orthogonal_of_Z _ _ _ _ constantProjector_eq_cast
      entryStandardProjector_eq_cast h1,
    orthogonal_of_Z _ _ _ _ constantProjector_eq_cast
      axisStandardProjector_eq_cast h2,
    orthogonal_of_Z _ _ _ _ constantProjector_eq_cast
      matchingStandardProjector_eq_cast h3,
    orthogonal_of_Z _ _ _ _ constantProjector_eq_cast
      residualThreeProjector_eq_cast h4,
    orthogonal_of_Z _ _ _ _ entryStandardProjector_eq_cast
      axisStandardProjector_eq_cast h5,
    orthogonal_of_Z _ _ _ _ entryStandardProjector_eq_cast
      matchingStandardProjector_eq_cast h6,
    orthogonal_of_Z _ _ _ _ entryStandardProjector_eq_cast
      residualThreeProjector_eq_cast h7,
    orthogonal_of_Z _ _ _ _ axisStandardProjector_eq_cast
      matchingStandardProjector_eq_cast h8,
    orthogonal_of_Z _ _ _ _ axisStandardProjector_eq_cast
      residualThreeProjector_eq_cast h9,
    orthogonal_of_Z _ _ _ _ matchingStandardProjector_eq_cast
      residualThreeProjector_eq_cast h10⟩

theorem matchingAxis_projector_traces :
    Matrix.trace constantProjector = 1 ∧
    Matrix.trace entryStandardProjector = 3 ∧
    Matrix.trace axisStandardProjector = 3 ∧
    Matrix.trace matchingStandardProjector = 2 ∧
    Matrix.trace residualThreeProjector = 3 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := projectorZ_traces
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [constantProjector_eq_cast, Matrix.trace_smul, castQ_trace, h0]
    norm_num
  · rw [entryStandardProjector_eq_cast, Matrix.trace_smul, castQ_trace, h1]
    norm_num
  · rw [axisStandardProjector_eq_cast, Matrix.trace_smul, castQ_trace, h2]
    norm_num
  · rw [matchingStandardProjector_eq_cast, Matrix.trace_smul, castQ_trace,
      h3]
    norm_num
  · rw [residualThreeProjector_eq_cast, Matrix.trace_smul, castQ_trace, h4]
    norm_num

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
  intro σ
  obtain ⟨h0, h1, h2, h3, h4⟩ := projectorZ_equivariant σ
  exact ⟨commute_of_Z σ _ _ constantProjector_eq_cast h0,
    commute_of_Z σ _ _ entryStandardProjector_eq_cast h1,
    commute_of_Z σ _ _ axisStandardProjector_eq_cast h2,
    commute_of_Z σ _ _ matchingStandardProjector_eq_cast h3,
    commute_of_Z σ _ _ residualThreeProjector_eq_cast h4⟩

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

/-- `3·P_innov` over the integers. -/
def innovationZ : Matrix MatchingHalfEdge MatchingHalfEdge ℤ :=
  (3 : ℤ) • 1 - fibreEZ

def innovationBasisZ : Matrix MatchingHalfEdge InnovationCoordinate ℤ :=
  fun p q =>
    if p = (q.1, Fin.castSucc q.2) then 1
    else if p = (q.1, 2) then -1 else 0

def innovationCoordinateZ : Matrix InnovationCoordinate MatchingHalfEdge ℤ :=
  fun q p => innovationZ (q.1, Fin.castSucc q.2) p

theorem innovationProjector_eq_cast :
    innovationProjector = (1 / 3 : ℚ) • castQ innovationZ := by
  ext p q
  simp only [innovationProjector, entryFibreProjector, innovationZ, fibreEZ,
    castQ_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> push_cast <;> norm_num

theorem innovationBasisMatrix_eq_cast :
    innovationBasisMatrix = castQ innovationBasisZ := by
  ext p q
  simp only [innovationBasisMatrix, innovationBasisZ, castQ_apply]
  split_ifs <;> simp

theorem innovationCoordinateMatrix_eq_cast :
    innovationCoordinateMatrix = (1 / 3 : ℚ) • castQ innovationCoordinateZ := by
  ext q p
  simp only [innovationCoordinateMatrix, innovationCoordinateZ,
    innovationProjector_eq_cast, castQ_apply, Matrix.smul_apply]

theorem innovationZ_factorization :
    innovationZ = innovationBasisZ * innovationCoordinateZ := by
  decide +kernel

theorem innovationZ_fixes_basis :
    innovationZ * innovationBasisZ = (3 : ℤ) • innovationBasisZ := by
  decide +kernel

theorem innovationZ_idempotent :
    innovationZ * innovationZ = (3 : ℤ) • innovationZ := by
  decide +kernel

theorem innovationProjector_factorization :
    innovationProjector =
      innovationBasisMatrix * innovationCoordinateMatrix := by
  rw [innovationProjector_eq_cast, innovationBasisMatrix_eq_cast,
    innovationCoordinateMatrix_eq_cast, Matrix.mul_smul, ← castQ_mul,
    ← innovationZ_factorization]

theorem innovationProjector_fixes_basis :
    innovationProjector * innovationBasisMatrix = innovationBasisMatrix := by
  rw [innovationProjector_eq_cast, innovationBasisMatrix_eq_cast,
    Matrix.smul_mul, ← castQ_mul, innovationZ_fixes_basis, castQ_zsmul,
    smul_smul]
  norm_num

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
  · rw [innovationCovariance, innovationProjector_eq_cast, smul_smul,
      Matrix.smul_mul, Matrix.mul_smul, ← castQ_mul, innovationZ_idempotent,
      castQ_zsmul]
    simp only [smul_smul]
    norm_num
  · rw [innovationCovariance, innovationProjector_eq_cast,
      innovationBasisMatrix_eq_cast, smul_smul, Matrix.smul_mul,
      ← castQ_mul, innovationZ_fixes_basis, castQ_zsmul, smul_smul]
    norm_num

end
end MatchingAxisHalfEdgeDecomposition
end NCG
