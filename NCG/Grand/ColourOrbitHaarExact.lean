/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactHaarRankOneAverage
import NCG.Grand.ColourOrbitAssemblyExact

/-!
# Exact SU(4) Haar colour orbit

This file removes the abstract covariance hypotheses from the colour-orbit
assembly by constructing the normalized `SU(4)` Haar average itself.
-/

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace NCG
namespace ColourOrbitHaarExact

open CompactHaarRankOneAverage

noncomputable local instance colourSU4TopologicalSpace : TopologicalSpace SU4 :=
  CompactHaarRankOneAverage.su4TopologicalSpace

abbrev M4 := Matrix (Fin 4) (Fin 4) ℂ

/-- Euclidean realization of Hilbert--Schmidt four-by-four matrices. -/
abbrev H4 := EuclideanSpace ℂ (Fin 4 × Fin 4)

/-- Forget the Euclidean wrapper and reshape a vector as a matrix. -/
def toMatrix (x : H4) : M4 := fun i j => x (i, j)

/-- Flatten a matrix into the Euclidean Hilbert--Schmidt carrier. -/
def ofMatrix (A : M4) : H4 := WithLp.toLp 2 fun p => A p.1 p.2

@[simp] theorem toMatrix_add (x y : H4) : toMatrix (x + y) = toMatrix x + toMatrix y := by
  rfl

@[simp] theorem toMatrix_smul (c : ℂ) (x : H4) : toMatrix (c • x) = c • toMatrix x := by
  rfl

@[simp] theorem toMatrix_ofMatrix (A : M4) : toMatrix (ofMatrix A) = A := by
  ext i j
  rfl

@[simp] theorem ofMatrix_toMatrix (x : H4) : ofMatrix (toMatrix x) = x := by
  apply WithLp.ofLp_injective 2
  rfl

/-- Linear equivalence between matrices and their Euclidean Hilbert--Schmidt model. -/
def matrixEuclideanEquiv : M4 ≃ₗ[ℂ] H4 where
  toFun := ofMatrix
  invFun := toMatrix
  left_inv := toMatrix_ofMatrix
  right_inv := ofMatrix_toMatrix
  map_add' A B := by
    apply WithLp.ofLp_injective 2
    rfl
  map_smul' c A := by
    apply WithLp.ofLp_injective 2
    rfl

/-- Hilbert--Schmidt inner product in trace form. -/
theorem inner_eq_trace (x y : H4) :
    ⟪x, y⟫_ℂ = Matrix.trace (star (toMatrix x) * toMatrix y) := by
  simp [PiLp.inner_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, toMatrix,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Finset.sum_product]
  simp_rw [mul_comm]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]

/-- Special-unitary conjugation on the Euclidean Hilbert--Schmidt carrier. -/
def conjugationLinear (U : SU4) : H4 →ₗ[ℂ] H4 where
  toFun x := ofMatrix (U.1 * toMatrix x * star U.1)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    funext p
    simp [ofMatrix, toMatrix, Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    funext p
    simp [ofMatrix, toMatrix, Matrix.mul_smul, Matrix.smul_mul]

/-- Special-unitary conjugation as a continuous linear map. -/
noncomputable def conjugation (U : SU4) : H4 →L[ℂ] H4 :=
  (conjugationLinear U).toContinuousLinearMap

@[simp] theorem toMatrix_conjugation (U : SU4) (x : H4) :
    toMatrix (conjugation U x) = U.1 * toMatrix x * star U.1 := by
  rw [conjugation]
  exact toMatrix_ofMatrix _

/-- The defining conjugation representation of `SU(4)` on Hilbert--Schmidt matrices. -/
noncomputable def conjugationAction :
    ContinuousUnitaryAction (G := SU4) (E := H4) where
  act := conjugation
  continuous_act := by
    letI : TopologicalSpace SU4 :=
      CompactHaarRankOneAverage.su4TopologicalSpace
    have hval : Continuous (fun U : SU4 => (U.1 : M4)) :=
      continuous_induced_dom
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro p
    simp only [conjugation, conjugationLinear, LinearMap.coe_toContinuousLinearMap',
      Function.comp_apply, ofMatrix, toMatrix, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    apply continuous_finsetSum
    intro k _hk
    apply Continuous.mul
    · apply continuous_finsetSum
      intro l _hl
      apply Continuous.mul
      · exact ((continuous_apply l).comp ((continuous_apply p.1).comp
          (hval.comp continuous_fst)))
      · exact (PiLp.continuous_apply (p := 2) (fun _ : Fin 4 × Fin 4 => ℂ) (l, k)).comp
          continuous_snd
    · exact Continuous.star ((continuous_apply k).comp ((continuous_apply p.2).comp
        (hval.comp continuous_fst)))
  one_act := by
    apply ContinuousLinearMap.ext
    intro x
    apply WithLp.ofLp_injective 2
    funext p
    simp [conjugation, conjugationLinear, ofMatrix, toMatrix]
  mul_act := by
    intro U V
    apply ContinuousLinearMap.ext
    intro x
    change ofMatrix ((U * V).1 * toMatrix x * star (U * V).1) =
      ofMatrix (U.1 * (V.1 * toMatrix x * star V.1) * star U.1)
    congr 1
    simp only [Submonoid.coe_mul, star_mul]
    noncomm_ring
  inner_map := by
    intro U x y
    rw [inner_eq_trace, inner_eq_trace, toMatrix_conjugation, toMatrix_conjugation]
    simp only [star_mul, star_star]
    rw [show U.1 * (star (toMatrix x) * star U.1) * (U.1 * toMatrix y * star U.1) =
        U.1 * (star (toMatrix x) * (star U.1 * U.1) * toMatrix y) * star U.1 by
      noncomm_ring]
    rw [U.2.1.1, Matrix.mul_one]
    rw [Matrix.trace_mul_cycle]
    simp [U.2.1.1, Matrix.mul_assoc]

/-- Every unitary conjugation of four-by-four matrices is already represented
by a special-unitary conjugation: a scalar fourth root corrects the determinant
without changing conjugation. -/
theorem unitary_conjugation_represented_in_SU4
    (U : M4) (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ V : SU4, ∀ A : M4, V.1 * A * star V.1 = U * A * star U := by
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (Matrix.det U)⁻¹ (by norm_num : 0 < 4)
  have hdetnorm : ‖Matrix.det U‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  have hznormpow : ‖z‖ ^ 4 = 1 := by
    have h := congrArg norm hz
    simpa [norm_pow, norm_inv, hdetnorm] using h
  have hznorm : ‖z‖ = 1 := by
    nlinarith [norm_nonneg z, sq_nonneg (‖z‖ ^ 2 - 1)]
  have hstarz : (starRingEnd ℂ) z * z = 1 := by
    rw [Complex.conj_mul', hznorm]
    norm_num
  have hscaledU : z • U ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hstarz] using Matrix.mem_unitaryGroup_iff.mp hU
  have hdetne : Matrix.det U ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hdetnorm
    norm_num at hdetnorm
  have hscaledDet : Matrix.det (z • U) = 1 := by
    rw [Matrix.det_smul]
    norm_num [hz]
    exact inv_mul_cancel₀ hdetne
  let V : SU4 :=
    ⟨z • U, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hscaledU, hscaledDet⟩⟩
  refine ⟨V, fun A => ?_⟩
  change (z • U) * A * star (z • U) = U * A * star U
  simp [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hstarz]

/-- The colour seed in the Euclidean Hilbert--Schmidt carrier. -/
def colourSeed : H4 := ofMatrix NCG.colourR

@[simp] theorem toMatrix_colourSeed : toMatrix colourSeed = NCG.colourR :=
  toMatrix_ofMatrix _

/-- The diagonal colour seed is self-adjoint. -/
@[simp] theorem star_colourR : star NCG.colourR = NCG.colourR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NCG.colourR, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]

/-- The normalized Haar barycenter of the colour orbit. -/
noncomputable def colourOrbitMean : H4 :=
  CompactHaarRankOneAverage.orbitMean conjugationAction colourSeed

/-- The colour-orbit barycenter transported back to matrices. -/
noncomputable def colourOrbitMeanMatrix : M4 := toMatrix colourOrbitMean

/-- Matrix trace as a continuous functional on the Euclidean Hilbert--Schmidt
carrier. -/
noncomputable def matrixTraceContinuous : H4 →L[ℂ] ℂ :=
  ((Matrix.traceLinearMap (Fin 4) ℂ ℂ).comp
    matrixEuclideanEquiv.symm.toLinearMap).toContinuousLinearMap

@[simp] theorem matrixTraceContinuous_apply (x : H4) :
    matrixTraceContinuous x = Matrix.trace (toMatrix x) := rfl

/-- Trace is constant along the concrete colour orbit. -/
theorem trace_colour_orbit (V : SU4) :
    Matrix.trace (V.1 * NCG.colourR * star V.1) = -2 := by
  rw [Matrix.trace_mul_cycle, Matrix.mem_unitaryGroup_iff'.mp V.2.1,
    Matrix.one_mul, NCG.colourR_trace]

/-- The colour-orbit barycenter is fixed by special-unitary conjugation. -/
theorem colourOrbitMeanMatrix_invariant_SU (V : SU4) :
    V.1 * colourOrbitMeanMatrix * star V.1 = colourOrbitMeanMatrix := by
  have h := CompactHaarRankOneAverage.orbitMean_invariant
    conjugationAction V colourSeed
  change conjugation V colourOrbitMean = colourOrbitMean at h
  exact congrArg toMatrix h

/-- The colour-orbit barycenter is fixed by every unitary conjugation. -/
theorem colourOrbitMeanMatrix_invariant
    (U : M4) (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    U * colourOrbitMeanMatrix * star U = colourOrbitMeanMatrix := by
  obtain ⟨V, hV⟩ := unitary_conjugation_represented_in_SU4 U hU
  rw [← hV colourOrbitMeanMatrix]
  exact colourOrbitMeanMatrix_invariant_SU V

/-- The orbit barycenter has the seed trace, namely `-2`. -/
theorem colourOrbitMeanMatrix_trace :
    Matrix.trace colourOrbitMeanMatrix = -2 := by
  rw [colourOrbitMeanMatrix, ← matrixTraceContinuous_apply]
  change matrixTraceContinuous colourOrbitMean = -2
  rw [colourOrbitMean,
    CompactHaarRankOneAverage.map_orbitMean conjugationAction]
  change (∫ V : SU4, Matrix.trace
    (V.1 * NCG.colourR * star V.1) ∂normalizedHaar SU4) = -2
  simp_rw [trace_colour_orbit]
  simp

/-- The commutant calculation fixes the orbit barycenter exactly. -/
theorem colourOrbitMeanMatrix_eq :
    colourOrbitMeanMatrix = (-1 / 2 : ℂ) • (1 : M4) := by
  obtain ⟨c, hc⟩ := SchurCovariant.central_of_unitary_comm
    (B := colourOrbitMeanMatrix) (fun U hU => by
      have hinv := colourOrbitMeanMatrix_invariant U hU
      calc
        U * colourOrbitMeanMatrix =
            (U * colourOrbitMeanMatrix * star U) * U := by
              rw [Matrix.mul_assoc,
                Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.mul_one]
        _ = colourOrbitMeanMatrix * U := by rw [hinv])
  have htrace := congrArg Matrix.trace hc
  rw [colourOrbitMeanMatrix_trace, Matrix.trace_smul, Matrix.trace_one] at htrace
  norm_num at htrace
  have hcval : c = (-1 / 2 : ℂ) := by
    linear_combination -htrace / 4
  rw [hc, hcval]

/-- The actual normalized `SU(4)` Haar integral of colour-orbit rank-one operators. -/
noncomputable def colourHaarAverage : H4 →L[ℂ] H4 :=
  CompactHaarRankOneAverage.average conjugationAction colourSeed

/-- Pointwise Bochner-integral formula for the colour Haar covariance. -/
theorem colourHaarAverage_apply (x : H4) :
    colourHaarAverage x =
      ∫ U : SU4, ⟪conjugation U colourSeed, x⟫_ℂ • conjugation U colourSeed
        ∂normalizedHaar SU4 := by
  exact CompactHaarRankOneAverage.average_apply conjugationAction colourSeed x

/-- The seed has Hilbert--Schmidt squared norm four. -/
theorem colourSeed_inner_self : ⟪colourSeed, colourSeed⟫_ℂ = 4 := by
  rw [inner_eq_trace, toMatrix_colourSeed, star_colourR,
    NCG.colourR_involution]
  norm_num [Matrix.trace_one]

/-- Every orbit vector pairs with the identity by the constant seed trace. -/
theorem colourOrbit_inner_one (V : SU4) :
    ⟪conjugation V colourSeed, ofMatrix (1 : M4)⟫_ℂ = -2 := by
  rw [inner_eq_trace, toMatrix_conjugation, toMatrix_colourSeed,
    toMatrix_ofMatrix, star_mul, star_mul, star_star, star_colourR,
    Matrix.mul_one, ← Matrix.mul_assoc, trace_colour_orbit]

/-- The concrete Haar covariance fixes the identity matrix. -/
theorem colourHaarAverage_one :
    colourHaarAverage (ofMatrix (1 : M4)) = ofMatrix (1 : M4) := by
  have h := CompactHaarRankOneAverage.average_apply_of_inner_eq
    conjugationAction colourSeed (ofMatrix (1 : M4)) (-2) colourOrbit_inner_one
  change colourHaarAverage (ofMatrix (1 : M4)) = (-2 : ℂ) • colourOrbitMean at h
  rw [h]
  rw [show colourOrbitMean = ofMatrix colourOrbitMeanMatrix by
    rw [colourOrbitMeanMatrix, ofMatrix_toMatrix], colourOrbitMeanMatrix_eq]
  change (-2 : ℂ) • matrixEuclideanEquiv ((-1 / 2 : ℂ) • (1 : M4)) =
    matrixEuclideanEquiv (1 : M4)
  rw [map_smul, smul_smul]
  norm_num

/-- The operator trace of the actual Haar covariance is four. -/
theorem colourHaarAverage_trace :
    colourHaarAverage.toLinearMap.trace ℂ H4 = 4 := by
  rw [colourHaarAverage, CompactHaarRankOneAverage.average_trace,
    colourSeed_inner_self]

/-- The actual Haar covariance transported back to the manuscript's matrix carrier. -/
noncomputable def colourHaarMatrix : M4 →ₗ[ℂ] M4 :=
  matrixEuclideanEquiv.symm.toLinearMap.comp
    (colourHaarAverage.toLinearMap.comp matrixEuclideanEquiv.toLinearMap)

@[simp] theorem colourHaarMatrix_apply (A : M4) :
    colourHaarMatrix A = toMatrix (colourHaarAverage (ofMatrix A)) := rfl

/-- Hilbert--Schmidt pairing with the identity is the matrix trace. -/
theorem inner_one_eq_trace (A : M4) :
    ⟪ofMatrix (1 : M4), ofMatrix A⟫_ℂ = Matrix.trace A := by
  rw [inner_eq_trace, toMatrix_ofMatrix, toMatrix_ofMatrix]
  simp

/-- The transported Haar covariance fixes the identity matrix. -/
theorem colourHaarMatrix_one : colourHaarMatrix (1 : M4) = 1 := by
  rw [colourHaarMatrix_apply, colourHaarAverage_one, toMatrix_ofMatrix]

/-- Self-adjointness and identity normalization imply preservation of the
traceless matrix sector. -/
theorem colourHaarMatrix_preserves_trace_zero
    (A : M4) (hA : Matrix.trace A = 0) :
    Matrix.trace (colourHaarMatrix A) = 0 := by
  rw [← inner_one_eq_trace, colourHaarMatrix_apply, ofMatrix_toMatrix]
  have hs := CompactHaarRankOneAverage.average_inner_symmetric
    conjugationAction colourSeed (ofMatrix (1 : M4)) (ofMatrix A)
  change ⟪ofMatrix (1 : M4), colourHaarAverage (ofMatrix A)⟫_ℂ =
    ⟪colourHaarAverage (ofMatrix (1 : M4)), ofMatrix A⟫_ℂ at hs
  rw [hs, colourHaarAverage_one, inner_one_eq_trace, hA]

/-- Operator trace is invariant under transport through the matrix--Euclidean
linear equivalence. -/
theorem colourHaarMatrix_trace :
    LinearMap.trace ℂ M4 colourHaarMatrix = 4 := by
  have h := LinearMap.trace_conj' colourHaarAverage.toLinearMap
    matrixEuclideanEquiv.symm
  change LinearMap.trace ℂ M4 colourHaarMatrix =
    LinearMap.trace ℂ H4 colourHaarAverage.toLinearMap at h
  rw [h, colourHaarAverage_trace]

/-- The concrete Haar covariance intertwines special-unitary conjugation. -/
theorem colourHaarMatrix_covariant_SU (V : SU4) (A : M4) :
    colourHaarMatrix (V.1 * A * star V.1) =
      V.1 * colourHaarMatrix A * star V.1 := by
  have h := CompactHaarRankOneAverage.average_equivariant
    conjugationAction V colourSeed (ofMatrix A)
  change colourHaarAverage (conjugation V (ofMatrix A)) =
    conjugation V (colourHaarAverage (ofMatrix A)) at h
  rw [colourHaarMatrix_apply, colourHaarMatrix_apply,
    show ofMatrix (V.1 * A * star V.1) = conjugation V (ofMatrix A) by rfl,
    ← toMatrix_conjugation]
  exact congrArg toMatrix h

/-- The concrete Haar covariance intertwines every unitary conjugation. -/
theorem colourHaarMatrix_covariant
    (U : M4) (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (A : M4) :
    colourHaarMatrix (U * A * star U) =
      U * colourHaarMatrix A * star U := by
  obtain ⟨V, hV⟩ := unitary_conjugation_represented_in_SU4 U hU
  rw [← hV A, colourHaarMatrix_covariant_SU, hV (colourHaarMatrix A)]

/-- **Exact colour Haar covariance**: the actual normalized `SU(4)` Haar
integral is the scalar projector plus one fifth of the traceless projector. -/
theorem colourHaarMatrix_exact (A : M4) :
    colourHaarMatrix A = (Matrix.trace A / 4) • 1
      + (5⁻¹ : ℂ) • (A - (Matrix.trace A / 4) • 1) := by
  exact ColourOrbitAssembly.colour_covariance_forced colourHaarMatrix
    (fun U hU A => colourHaarMatrix_covariant U hU A)
    colourHaarMatrix_preserves_trace_zero colourHaarMatrix_one
    colourHaarMatrix_trace A

/-- The manuscript's score-square normalization halves the exact Haar
coefficients to `1/2` and `1/10`. -/
theorem colourHaarScore_exact (A : M4) :
    ((2⁻¹ : ℂ) • colourHaarMatrix) A =
      (2⁻¹ * (Matrix.trace A / 4)) • 1
        + (10⁻¹ : ℂ) • (A - (Matrix.trace A / 4) • 1) := by
  exact ColourOrbitAssembly.colour_score_bridge_forced colourHaarMatrix
    (fun U hU A => colourHaarMatrix_covariant U hU A)
    colourHaarMatrix_preserves_trace_zero colourHaarMatrix_one
    colourHaarMatrix_trace A

/-- The exact scalar and adjoint Haar coefficients are strictly positive. -/
theorem colourHaar_coefficients_positive :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 5⁻¹ := by
  norm_num

end ColourOrbitHaarExact
end NCG
