/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.PositiveStencilDecompositionExact

/-!
# Positive local stencil: normalization and finite good cover

Paper `predictive_spectral_geometry`, label `lem:positive-stencil-main`.

The algebraic core (`lem:supp-positive-decomposition`) is
`RenewalGeometry.positive_stencil_decomposition`.  This file adds the two
remaining clauses of `lem:positive-stencil-main`:

* **Near-identity clause.**  Every symmetric matrix entrywise within `η` of
  the identity, with `d η ≤ 1`, lies in the stencil window
  `eq:supp-stencil-window` and therefore admits the positive
  `d²`-direction decomposition `eq:positive-stencil-main`
  (`positive_stencil_of_nearOne`).
* **Linear normalization.**  Every positive definite real matrix `P` admits an
  invertible `S` with `S P Sᵀ = 1` (`exists_normalization`), via the spectral
  theorem.
* **Finite good cover.**  For a continuous field `x ↦ g x` of positive
  definite matrices on a compact space (the inverse metric of a closed
  Riemannian manifold in the paper), there is a finite family of open sets
  covering the space, each with a linear normalization `S`, such that on every
  member the normalized field `S g(x) Sᵀ` stays in the stencil window and has
  a strictly positive stencil decomposition
  (`exists_finite_positive_stencil_cover`).

The manifold is abstracted to a compact topological space carrying a
continuous positive definite matrix field; no Riemannian-manifold structure is
formalized, which is the only gap between the paper's wording and the Lean
statement.
-/

open Matrix Finset Topology

namespace RenewalGeometry
namespace PositiveStencilCover

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The stencil window `eq:supp-stencil-window`: off-diagonal entries below
`η` in absolute value and diagonal entries above `(d-1) η`. -/
def InStencilWindow (A : Matrix ι ι ℝ) (η : ℝ) : Prop :=
  (∀ i j, i ≠ j → |A i j| < η) ∧ ∀ i, ((Fintype.card ι : ℝ) - 1) * η < A i i

/-- Entrywise closeness to the identity: `|A i j - δ i j| < η`. -/
def NearOne (A : Matrix ι ι ℝ) (η : ℝ) : Prop :=
  ∀ i j, |A i j - (1 : Matrix ι ι ℝ) i j| < η

omit [Fintype ι] in
/-- The identity is near itself for every positive tolerance. -/
theorem nearOne_one {η : ℝ} (hη : 0 < η) : NearOne (1 : Matrix ι ι ℝ) η := by
  intro i j
  simpa using hη

/-- A matrix entrywise within `η ≤ 1/d` of the identity lies in the stencil
window `eq:supp-stencil-window`. -/
theorem inStencilWindow_of_nearOne {A : Matrix ι ι ℝ} {η : ℝ}
    (hηd : (Fintype.card ι : ℝ) * η ≤ 1) (h : NearOne A η) : InStencilWindow A η := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := h i j
    rwa [Matrix.one_apply_ne hij, sub_zero] at this
  · have := h i i
    rw [Matrix.one_apply_eq] at this
    have h1 := (abs_lt.mp this).1
    have hexp : ((Fintype.card ι : ℝ) - 1) * η = (Fintype.card ι : ℝ) * η - η := by ring
    rw [hexp]
    linarith

/-- **Near-identity clause of `lem:positive-stencil-main`.**  Every symmetric
matrix entrywise within `η ≤ 1/d` of the identity admits the positive
`d²`-direction decomposition `eq:positive-stencil-main` with the explicit
strictly positive weights of `eq:supp-stencil-weights`. -/
theorem positive_stencil_of_nearOne (A : Matrix ι ι ℝ) (η : ℝ) (hA : A.IsSymm)
    (hη : 0 < η) (hηd : (Fintype.card ι : ℝ) * η ≤ 1) (h : NearOne A η) :
    (∀ i, 0 < stencilDiagonalWeight A η i) ∧
      (∀ i j, i ≠ j → 0 < stencilPlusWeight A η i j) ∧
      (∀ i j, i ≠ j → 0 < stencilMinusWeight A η i j) ∧
      A = ∑ i, stencilDiagonalWeight A η i • vecMulVec (stencilUnit i) (stencilUnit i)
        + ∑ i, ∑ j, stencilPairTerm A η i j := by
  classical
  have hw := inStencilWindow_of_nearOne hηd h
  exact positive_stencil_decomposition A η hA hη hw.1 hw.2

omit [Fintype ι] [LinearOrder ι] in
/-- Over `ℝ`, positive definite matrices are symmetric. -/
theorem isSymm_of_posDef {P : Matrix ι ι ℝ} (hP : P.PosDef) : P.IsSymm := by
  have h := hP.1
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- **Linear normalization at a point.**  Every positive definite real matrix
`P` admits an invertible `S` with `S P Sᵀ = 1`; the paper's choice is
`S = P^{-1/2}`, here realised through the spectral theorem. -/
theorem exists_normalization {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    ∃ S : Matrix ι ι ℝ, IsUnit S ∧ S * P * Sᵀ = 1 := by
  have hH : P.IsHermitian := hP.1
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hH.eigenvectorUnitary
  have hspec : P = U * diagonal hH.eigenvalues * star U := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hUdef] using h
  have hpos : ∀ i, 0 < hH.eigenvalues i := hP.eigenvalues_pos
  set r : ι → ℝ := fun i => (Real.sqrt (hH.eigenvalues i))⁻¹ with hr
  set S : Matrix ι ι ℝ := diagonal r * star U with hS
  have hcancel : ∀ X : Matrix ι ι ℝ, star U * (U * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hSt : Sᵀ = U * diagonal r := by
    rw [hS, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  have hsqrt : ∀ i, r i * (hH.eigenvalues i * r i) = 1 := by
    intro i
    set s : ℝ := Real.sqrt (hH.eigenvalues i) with hsdef
    have hs : 0 < s := Real.sqrt_pos.mpr (hpos i)
    have hss : s * s = hH.eigenvalues i := Real.mul_self_sqrt (hpos i).le
    have hri : r i = s⁻¹ := rfl
    rw [hri]
    calc s⁻¹ * (hH.eigenvalues i * s⁻¹) = s⁻¹ * ((s * s) * s⁻¹) := by rw [hss]
      _ = (s⁻¹ * s) * (s * s⁻¹) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_mul]
  refine ⟨S, ?_, ?_⟩
  · -- `S * (U * diagonal (sqrt λ)) = 1`
    set T : Matrix ι ι ℝ := U * diagonal (fun i => Real.sqrt (hH.eigenvalues i)) with hT
    have hST : S * T = 1 := by
      rw [hS, hT, Matrix.mul_assoc, hcancel, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      have hs : 0 < Real.sqrt (hH.eigenvalues i) := Real.sqrt_pos.mpr (hpos i)
      exact inv_mul_cancel₀ hs.ne'
    have hTS : T * S = 1 := mul_eq_one_comm.mp hST
    exact ⟨⟨S, T, hST, hTS⟩, rfl⟩
  · rw [hSt, hspec, hS]
    simp only [Matrix.mul_assoc]
    rw [hcancel, hcancel, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hsqrt i

section Cover

variable {K : Type*} [TopologicalSpace K]

/-- The normalized field `x ↦ S g(x) Sᵀ`. -/
def normalizedField (S : Matrix ι ι ℝ) (g : K → Matrix ι ι ℝ) (x : K) : Matrix ι ι ℝ :=
  S * g x * Sᵀ

omit [LinearOrder ι] [TopologicalSpace K] in
theorem normalizedField_isSymm (S : Matrix ι ι ℝ) (g : K → Matrix ι ι ℝ) (x : K)
    (hg : (g x).IsSymm) : (normalizedField S g x).IsSymm := by
  unfold Matrix.IsSymm normalizedField
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hg.eq,
    Matrix.mul_assoc]

omit [LinearOrder ι] in
theorem continuous_normalizedField (S : Matrix ι ι ℝ) {g : K → Matrix ι ι ℝ}
    (hg : Continuous g) : Continuous (normalizedField S g) :=
  (continuous_const.matrix_mul hg).matrix_mul continuous_const

/-- The chart on which the normalized field stays entrywise within `η` of the
identity is open. -/
theorem isOpen_nearOne_chart (S : Matrix ι ι ℝ) {g : K → Matrix ι ι ℝ}
    (hg : Continuous g) (η : ℝ) :
    IsOpen {x : K | NearOne (normalizedField S g x) η} := by
  have hcont := continuous_normalizedField S hg
  have hset : {x : K | NearOne (normalizedField S g x) η} =
      ⋂ i, ⋂ j, {x : K | |normalizedField S g x i j - (1 : Matrix ι ι ℝ) i j| < η} := by
    ext x
    simp [NearOne]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_lt (((hcont.matrix_elem i j).sub continuous_const).abs) continuous_const

/-- **Lemma `lem:positive-stencil-main` (good-cover clause).**  Let `g` be a
continuous field of positive definite matrices on a compact space (the inverse
metric of a closed Riemannian manifold).  Then there are finitely many points
`x₀ ∈ t`, each with a linear normalization `S x₀` (`S x₀ * g x₀ * (S x₀)ᵀ = 1`)
and an open chart `U x₀ ∋ x₀`, covering the space, such that on every chart the
normalized inverse metric `S x₀ * g x * (S x₀)ᵀ` lies in the stencil window
`eq:supp-stencil-window` and admits the strictly positive `d²`-direction
decomposition `eq:positive-stencil-main`. -/
theorem exists_finite_positive_stencil_cover [CompactSpace K]
    (g : K → Matrix ι ι ℝ) (hg : Continuous g) (hpos : ∀ x, (g x).PosDef)
    {η : ℝ} (hη : 0 < η) (hηd : (Fintype.card ι : ℝ) * η ≤ 1) :
    ∃ (t : Finset K) (S : K → Matrix ι ι ℝ) (U : K → Set K),
      (∀ x₀, IsUnit (S x₀)) ∧
      (∀ x₀, S x₀ * g x₀ * (S x₀)ᵀ = 1) ∧
      (∀ x₀, IsOpen (U x₀)) ∧
      (∀ x₀, x₀ ∈ U x₀) ∧
      (∀ x, ∃ x₀ ∈ t, x ∈ U x₀) ∧
      ∀ x₀, ∀ x ∈ U x₀,
        InStencilWindow (normalizedField (S x₀) g x) η ∧
        (∀ i, 0 < stencilDiagonalWeight (normalizedField (S x₀) g x) η i) ∧
        (∀ i j, i ≠ j → 0 < stencilPlusWeight (normalizedField (S x₀) g x) η i j) ∧
        (∀ i j, i ≠ j → 0 < stencilMinusWeight (normalizedField (S x₀) g x) η i j) ∧
        normalizedField (S x₀) g x =
          ∑ i, stencilDiagonalWeight (normalizedField (S x₀) g x) η i •
              vecMulVec (stencilUnit i) (stencilUnit i)
            + ∑ i, ∑ j, stencilPairTerm (normalizedField (S x₀) g x) η i j := by
  classical
  have hex : ∀ x₀, ∃ S : Matrix ι ι ℝ, IsUnit S ∧ S * g x₀ * Sᵀ = 1 :=
    fun x₀ => exists_normalization (hpos x₀)
  choose S hS using hex
  let U : K → Set K := fun x₀ => {x : K | NearOne (normalizedField (S x₀) g x) η}
  have hopen : ∀ x₀, IsOpen (U x₀) := fun x₀ => isOpen_nearOne_chart (S x₀) hg η
  have hmem : ∀ x₀, x₀ ∈ U x₀ := by
    intro x₀
    show NearOne (normalizedField (S x₀) g x₀) η
    unfold normalizedField
    rw [(hS x₀).2]
    exact nearOne_one hη
  have hcover : (Set.univ : Set K) ⊆ ⋃ x₀, U x₀ := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨t, S, U, fun x₀ => (hS x₀).1, fun x₀ => (hS x₀).2, hopen, hmem, ?_, ?_⟩
  · intro x
    have hx := ht (Set.mem_univ x)
    simpa [Set.mem_iUnion] using hx
  · intro x₀ x hx
    have hnear : NearOne (normalizedField (S x₀) g x) η := hx
    have hsymm : (normalizedField (S x₀) g x).IsSymm :=
      normalizedField_isSymm (S x₀) g x (isSymm_of_posDef (hpos x))
    exact ⟨inStencilWindow_of_nearOne hηd hnear,
      positive_stencil_of_nearOne _ η hsymm hη hηd hnear⟩

end Cover

end PositiveStencilCover
end RenewalGeometry
