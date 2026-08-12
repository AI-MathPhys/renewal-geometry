/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Analysis.FiniteGramLeastSquares
import NCG.Grand.ChannelNativeReversibleTangent
import NCG.Grand.InnerDerivationConditioning

/-!
# Finite Hamiltonian-tangent certificate

This file realizes a matrix superoperator as its finite array of matrix-unit
output coefficients.  The resulting real Euclidean norm is exactly the
superoperator Hilbert--Schmidt norm used in the manuscript.  Applying the
finite Gram projection theorem to sampled Hamiltonian derivations produces
the canonical traceless Hermitian minimizer and the normalized positive
residual obstruction.
-/

open Matrix Finset

namespace NCG

variable {d I : Type*} [Fintype d] [DecidableEq d]
  [Nonempty d] [Fintype I] [DecidableEq I]

/-- Finite coordinate Hilbert space for maps `M_d → M_d`: the first matrix
index labels the input matrix unit and the second labels an output entry. -/
abbrev SuperoperatorHSSpace (d : Type*) [Fintype d] :=
  EuclideanSpace ℂ ((d × d) × (d × d))

/-- All matrix-unit output coordinates of a complex-linear map. -/
noncomputable def superoperatorHSSample
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) : SuperoperatorHSSpace d :=
  WithLp.toLp 2 fun p =>
    L (Matrix.single p.1.1 p.1.2 1) p.2.1 p.2.2

/-- The sampled `-i[H,-]` direction, as a real-linear function of `H`. -/
noncomputable def hamiltonianSampleLinear :
    Matrix d d ℂ →ₗ[ℝ] SuperoperatorHSSpace d where
  toFun H := superoperatorHSSample (hamiltonianDerivation H)
  map_add' H K := by
    ext p
    simp [superoperatorHSSample, hamiltonianDerivation_apply,
      Matrix.add_mul, Matrix.mul_add]
    ring
  map_smul' r H := by
    ext p
    simp [superoperatorHSSample, hamiltonianDerivation_apply,
      Matrix.smul_mul, Matrix.mul_smul, smul_eq_mul]
    ring

@[simp]
theorem hamiltonianSampleLinear_apply (H : Matrix d d ℂ) :
    hamiltonianSampleLinear H =
      superoperatorHSSample (hamiltonianDerivation H) := rfl

/-- The Euclidean sample norm is the squared superoperator HS norm from the
manuscript. -/
theorem superoperatorHSSample_norm_sq
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    ‖superoperatorHSSample L‖ ^ 2 = tangentSuperHSSq L := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ p : ((d × d) × (d × d)),
      ‖L (Matrix.single p.1.1 p.1.2 1) p.2.1 p.2.2‖ ^ 2)
    = tangentSuperHSSq L
  unfold tangentSuperHSSq hsFrobSq
  simp only [Fintype.sum_prod_type, Complex.sq_norm]

/-- A finite real basis presentation of the traceless Hermitian matrices.
The existence and uniqueness of coordinates is the exact content needed from
the manuscript's chosen orthonormal basis `(T_α)`. -/
structure TracelessHermitianBasisData (d I : Type*)
    [Fintype d] [DecidableEq d] [Fintype I] where
  basisMatrix : I → Matrix d d ℂ
  hermitian : ∀ i, (basisMatrix i)ᴴ = basisMatrix i
  trace_zero : ∀ i, Matrix.trace (basisMatrix i) = 0
  coordinates : ∀ H : Matrix d d ℂ, Hᴴ = H → Matrix.trace H = 0 →
    ∃! c : I → ℝ, H = ∑ i, c i • basisMatrix i

/-- Sampled Hamiltonian directions associated with the chosen basis. -/
noncomputable def TracelessHermitianBasisData.direction
    (B : TracelessHermitianBasisData d I) : I → SuperoperatorHSSpace d :=
  fun i => hamiltonianSampleLinear (B.basisMatrix i)

/-- The Gram-formula Hamiltonian `H_L`. -/
noncomputable def canonicalHamiltonian
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ i, (finiteGramCoefficients B.direction (superoperatorHSSample L) i : ℂ) •
    B.basisMatrix i

/-- The squared distance from `L` to its canonical Hamiltonian direction. -/
noncomputable def hamiltonianTangentDefect
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) : ℝ :=
  ‖superoperatorHSSample L - hamiltonianSampleLinear (canonicalHamiltonian B L)‖ ^ 2

/-- The least-squares functional appearing in the manuscript.  Since
`hamiltonianDerivation H = -i ad_H`, this is
`‖L + i ad_H‖²_sup,HS`. -/
noncomputable def hamiltonianFitObjective
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) (H : Matrix d d ℂ) : ℝ :=
  ‖superoperatorHSSample L - hamiltonianSampleLinear H‖ ^ 2

theorem superoperatorHSSample_injective :
    Function.Injective
      (superoperatorHSSample :
        (Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) → SuperoperatorHSSpace d) := by
  intro L K hLK
  have hunit : ∀ a b, L (Matrix.single a b 1) =
      K (Matrix.single a b 1) := by
    intro a b
    ext i j
    exact congrArg (fun z => z ((a, b), (i, j))) hLK
  apply LinearMap.ext
  intro X
  rw [Matrix.matrix_eq_sum_single X, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show Matrix.single a b (X a b) =
      X a b • Matrix.single a b (1 : ℂ) by
        rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, map_smul, hunit]

theorem canonicalHamiltonian_sample
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    hamiltonianSampleLinear (canonicalHamiltonian B L) =
      finiteGramProjection B.direction (superoperatorHSSample L) := by
  change hamiltonianSampleLinear
      (∑ i, finiteGramCoefficients B.direction (superoperatorHSSample L) i •
        B.basisMatrix i) = _
  simp [finiteGramProjection, TracelessHermitianBasisData.direction]

theorem canonicalHamiltonian_hermitian
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    (canonicalHamiltonian B L)ᴴ = canonicalHamiltonian B L := by
  rw [canonicalHamiltonian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.conjTranspose_smul, B.hermitian]
  simp

theorem canonicalHamiltonian_trace_zero
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    Matrix.trace (canonicalHamiltonian B L) = 0 := by
  rw [canonicalHamiltonian, Matrix.trace_sum]
  simp [Matrix.trace_smul, B.trace_zero]

theorem hamiltonianSample_mem_span
    (B : TracelessHermitianBasisData d I) (H : Matrix d d ℂ)
    (hH : Hᴴ = H) (htr : Matrix.trace H = 0) :
    hamiltonianSampleLinear H ∈
      Submodule.span ℝ (Set.range B.direction) := by
  rcases B.coordinates H hH htr with ⟨c, hc, hunique⟩
  rw [hc, map_sum]
  exact Submodule.sum_mem _ fun i hi => by
    rw [map_smul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)

theorem hamiltonianSample_injective_on_traceless
    (H K : Matrix d d ℂ) (hH : Hᴴ = H) (hK : Kᴴ = K)
    (htrH : Matrix.trace H = 0) (htrK : Matrix.trace K = 0)
    (hsample : hamiltonianSampleLinear H = hamiltonianSampleLinear K) :
    H = K := by
  have hderiv : hamiltonianDerivation H = hamiltonianDerivation K :=
    superoperatorHSSample_injective hsample
  apply inner_derivation_injective_on_traceless H K hH hK htrH htrK
  intro a b
  have h := congrArg
    (fun F : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ =>
      F (Matrix.single a b 1)) hderiv
  have hscaled := congrArg (fun X : Matrix d d ℂ => Complex.I • X) h
  simpa [hamiltonianDerivation_apply, smul_smul] using hscaled

theorem basisRealCombination_hermitian
    (B : TracelessHermitianBasisData d I) (c : I → ℝ) :
    (∑ i, (c i : ℂ) • B.basisMatrix i)ᴴ =
      ∑ i, (c i : ℂ) • B.basisMatrix i := by
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.conjTranspose_smul, B.hermitian]
  simp

theorem basisRealCombination_trace_zero
    (B : TracelessHermitianBasisData d I) (c : I → ℝ) :
    Matrix.trace (∑ i, (c i : ℂ) • B.basisMatrix i) = 0 := by
  rw [Matrix.trace_sum]
  simp [Matrix.trace_smul, B.trace_zero]

theorem basisMatrix_linearIndependent
    (B : TracelessHermitianBasisData d I) :
    LinearIndependent ℝ B.basisMatrix := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rcases B.coordinates 0 (by simp) (by simp) with ⟨c₀, hc₀, huniq⟩
  have hc_eq : c = c₀ := huniq c hc.symm
  have hzero_eq : (0 : I → ℝ) = c₀ := huniq 0 (by simp)
  intro i
  exact congrFun (hc_eq.trans hzero_eq.symm) i

theorem hamiltonianDirection_linearIndependent
    (B : TracelessHermitianBasisData d I) :
    LinearIndependent ℝ B.direction := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let H : Matrix d d ℂ := ∑ i, (c i : ℂ) • B.basisMatrix i
  have hH : Hᴴ = H := basisRealCombination_hermitian B c
  have htr : Matrix.trace H = 0 := basisRealCombination_trace_zero B c
  have hsamp : hamiltonianSampleLinear H = hamiltonianSampleLinear 0 := by
    change hamiltonianSampleLinear
      (∑ i, c i • B.basisMatrix i) = hamiltonianSampleLinear 0
    rw [map_sum, map_zero]
    simpa [TracelessHermitianBasisData.direction] using hc
  have hH0 : H = 0 := hamiltonianSample_injective_on_traceless H 0
    hH (by simp) htr (by simp) hsamp
  exact (Fintype.linearIndependent_iff.mp
    (basisMatrix_linearIndependent B)) c hH0

/-- The Hamiltonian Gram matrix is automatically invertible: basis
independence and exact inner-derivation injectivity make its sampled
directions linearly independent. -/
noncomputable def hamiltonianGramInvertible
    (B : TracelessHermitianBasisData d I) :
    Invertible (finiteGramMatrix B.direction) := by
  have hdet : (finiteGramMatrix B.direction).det ≠ 0 := by
    change (Matrix.gram ℝ B.direction).det ≠ 0
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
      (hamiltonianDirection_linearIndependent B)
  exact Matrix.invertibleOfIsUnitDet (finiteGramMatrix B.direction)
    (isUnit_iff_ne_zero.mpr hdet)

theorem superoperatorHSSample_sub
    (L K : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    superoperatorHSSample (L - K) =
      superoperatorHSSample L - superoperatorHSSample K := by
  ext p
  simp [superoperatorHSSample]

theorem hamiltonianFitObjective_eq_superoperatorHSSq
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) (H : Matrix d d ℂ) :
    hamiltonianFitObjective L H =
      tangentSuperHSSq (L - hamiltonianDerivation H) := by
  change ‖superoperatorHSSample L -
    superoperatorHSSample (hamiltonianDerivation H)‖ ^ 2 = _
  rw [← superoperatorHSSample_sub,
    superoperatorHSSample_norm_sq]

theorem canonicalHamiltonian_minimizes
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (H : Matrix d d ℂ) (hH : Hᴴ = H) (htr : Matrix.trace H = 0) :
    hamiltonianFitObjective L (canonicalHamiltonian B L) ≤
      hamiltonianFitObjective L H := by
  letI := hamiltonianGramInvertible B
  have hmin := (finiteGram_unique_minimizer B.direction
    (superoperatorHSSample L)).2.1
    (hamiltonianSampleLinear H)
    (hamiltonianSample_mem_span B H hH htr)
  rw [hamiltonianFitObjective, hamiltonianFitObjective,
    canonicalHamiltonian_sample]
  exact hmin

theorem canonicalHamiltonian_unique_minimizer
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (H : Matrix d d ℂ) (hH : Hᴴ = H) (htr : Matrix.trace H = 0)
    (heq : hamiltonianFitObjective L H =
      hamiltonianFitObjective L (canonicalHamiltonian B L)) :
    H = canonicalHamiltonian B L := by
  letI := hamiltonianGramInvertible B
  have heq' :
      ‖superoperatorHSSample L - hamiltonianSampleLinear H‖ ^ 2 =
        ‖superoperatorHSSample L -
          finiteGramProjection B.direction (superoperatorHSSample L)‖ ^ 2 := by
    unfold hamiltonianFitObjective at heq
    rw [canonicalHamiltonian_sample] at heq
    exact heq
  have hsample := (finiteGram_unique_minimizer B.direction
    (superoperatorHSSample L)).2.2
    (hamiltonianSampleLinear H)
    (hamiltonianSample_mem_span B H hH htr) heq'
  apply hamiltonianSample_injective_on_traceless H
    (canonicalHamiltonian B L) hH
    (canonicalHamiltonian_hermitian B L) htr
    (canonicalHamiltonian_trace_zero B L)
  exact hsample.trans (canonicalHamiltonian_sample B L).symm

theorem hamiltonianTangentDefect_eq_zero_iff
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    hamiltonianTangentDefect B L = 0 ↔
      L = hamiltonianDerivation (canonicalHamiltonian B L) := by
  rw [hamiltonianTangentDefect, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]
  change superoperatorHSSample L =
      superoperatorHSSample
        (hamiltonianDerivation (canonicalHamiltonian B L)) ↔ _
  constructor
  · intro h
    exact (superoperatorHSSample_injective (d := d)) h
  · intro h
    exact congrArg superoperatorHSSample h

/-- The explicit normalized residual coordinate vector from the positive
branch of the manuscript theorem. -/
noncomputable def normalizedHamiltonianResidualSample
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) : SuperoperatorHSSpace d :=
  (Real.sqrt (hamiltonianTangentDefect B L))⁻¹ •
    (superoperatorHSSample L -
      hamiltonianSampleLinear (canonicalHamiltonian B L))

theorem normalizedHamiltonianResidualSample_not_mem
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hpos : 0 < hamiltonianTangentDefect B L) :
    normalizedHamiltonianResidualSample B L ∉
      Submodule.span ℝ (Set.range B.direction) := by
  letI := hamiltonianGramInvertible B
  have h := finiteGram_normalized_residual_not_mem B.direction
    (superoperatorHSSample L)
  rw [← canonicalHamiltonian_sample B L] at h
  exact h hpos

/-- **Finite Hamiltonian-tangent certificate.**  The Gram-formula operator is
the unique traceless Hermitian minimizer; its defect vanishes exactly for the
canonical Hamiltonian derivation; and a positive normalized residual is not a
Hamiltonian direction. -/
theorem finite_hamiltonian_tangent_certificate
    (B : TracelessHermitianBasisData d I)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) :
    (canonicalHamiltonian B L)ᴴ = canonicalHamiltonian B L
      ∧ Matrix.trace (canonicalHamiltonian B L) = 0
      ∧ (∀ H : Matrix d d ℂ, Hᴴ = H → Matrix.trace H = 0 →
          hamiltonianFitObjective L (canonicalHamiltonian B L) ≤
            hamiltonianFitObjective L H)
      ∧ (∀ H : Matrix d d ℂ, Hᴴ = H → Matrix.trace H = 0 →
          hamiltonianFitObjective L H =
              hamiltonianFitObjective L (canonicalHamiltonian B L) →
            H = canonicalHamiltonian B L)
      ∧ (hamiltonianTangentDefect B L = 0 ↔
          L = hamiltonianDerivation (canonicalHamiltonian B L))
      ∧ (0 < hamiltonianTangentDefect B L →
          normalizedHamiltonianResidualSample B L ∉
            Submodule.span ℝ (Set.range B.direction)) := by
  exact ⟨canonicalHamiltonian_hermitian B L,
    canonicalHamiltonian_trace_zero B L,
    fun H hH htr => canonicalHamiltonian_minimizes B L H hH htr,
    fun H hH htr heq =>
      canonicalHamiltonian_unique_minimizer B L H hH htr heq,
    hamiltonianTangentDefect_eq_zero_iff B L,
    fun hpos => normalizedHamiltonianResidualSample_not_mem B L hpos⟩

end NCG
