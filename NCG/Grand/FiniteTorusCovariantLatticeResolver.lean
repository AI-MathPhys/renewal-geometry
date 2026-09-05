/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteFiberFourierInterpolationCoefficients
import NCG.Grand.FiniteTorusCovariantContinuumResolvent
import NCG.Grand.FiniteTorusNormalizedFourierEquiv

/-!
# Finite-lattice realization of covariant resolvents

The zero-extended coefficient resolver preserves the finite centered Fourier
subspace.  Pulling it back through the centered coefficient embedding defines
the literal finite-lattice resolver, and interpolation intertwines this
finite operator exactly with the embedded continuum-torus resolver.
-/

open scoped InnerProduct lp

noncomputable section

local instance finiteTorusCovariantLatticeResolverMeasureSpace :
    MeasureTheory.MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance finiteTorusCovariantLatticeResolverIsAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance finiteTorusCovariantLatticeResolverIsProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {r : Type} [Fintype r] [Nonempty r]

/-- Fourier transform after interpolation is definitionally the centered
coefficient embedding. -/
@[simp]
theorem finiteFiberTorusFourierEquiv_apply_interpolation
    (N : ℕ)
    (Phi : FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r)) :
    finiteFiberTorusFourierEquiv
        (finiteFiberFourierInterpolationCLM Phi) =
      finiteFiberCenteredCoefficientEmbedding Phi := rfl

/-- Applying the finite-stage coefficient resolver to an interpolated vector
again produces centered coefficient data coming from a finite lattice
vector. -/
theorem exists_finiteFiberLattice_preimage_coefficientResolver
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam)
    (g : ℓ²(d → ℤ, EuclideanSpace ℂ r)) :
    ∃ Psi : FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r),
      finiteFiberCenteredCoefficientEmbedding Psi =
        finiteTorusCovariantCoefficientResolver N B lam hlam g := by
  classical
  let f := finiteTorusCovariantCoefficientResolver N B lam hlam
    g
  let data : r → EuclideanSpace ℂ (d → ZMod (N + 1)) :=
    fun a ↦ WithLp.toLp 2 fun q ↦
      f (finiteTorusCenteredFrequency q) a
  choose psi hpsi using fun a ↦
    exists_finiteTorus_function_with_normalizedFourier (data a)
  let Psi : FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r) :=
    WithLp.toLp 2 fun a ↦ psi a
  refine ⟨Psi, ?_⟩
  apply lp.ext
  funext k
  by_cases hk : k ∈ Set.range
      (finiteTorusCenteredFrequency (N := N + 1) (d := d))
  · obtain ⟨q, rfl⟩ := hk
    apply WithLp.ofLp_injective
    funext a
    simpa only [
      finiteFiberCenteredCoefficientEmbedding_apply_centered,
      Psi, WithLp.ofLp_toLp, data] using hpsi a q
  · rw [finiteFiberCenteredCoefficientEmbedding_apply_eq_zero_of_not_mem_range
      Psi k hk]
    have hwindow :
        k ∉ finiteTorusCenteredFrequencyWindow (d := d) N := by
      intro hmem
      obtain ⟨q, hq⟩ :=
        (mem_finiteTorusCenteredFrequencyWindow_iff (d := d) N k).1 hmem
      exact hk ⟨q, hq⟩
    change 0 = finiteTorusCovariantResolverBlock N B lam hlam k
      (g k)
    rw [finiteTorusCovariantResolverBlock, if_neg hwindow]
    rfl

/-- The zero-extended finite-stage coefficient resolver is symmetric. -/
theorem finiteTorusCovariantCoefficientResolver_isSymmetric
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    LinearMap.IsSymmetric
      (finiteTorusCovariantCoefficientResolver N B lam hlam).toLinearMap := by
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  change inner ℂ
      (finiteTorusCovariantResolverBlock N B lam hlam k (f k)) (g k) =
    inner ℂ (f k)
      (finiteTorusCovariantResolverBlock N B lam hlam k (g k))
  by_cases hk : k ∈ finiteTorusCenteredFrequencyWindow (d := d) N
  · rw [finiteTorusCovariantResolverBlock, if_pos hk]
    exact VaryingHilbert.boundedOperatorNormalResolvent_isSymmetric
      (meshCovariantFourierOperatorStack (finiteTorusCutoffMesh N) k B)
      lam hlam (f k) (g k)
  · rw [finiteTorusCovariantResolverBlock, if_neg hk]
    simp

/-- The zero-extended coefficient resolver equals its Hilbert adjoint. -/
theorem finiteTorusCovariantCoefficientResolver_adjoint
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    (finiteTorusCovariantCoefficientResolver N B lam hlam).adjoint =
      finiteTorusCovariantCoefficientResolver N B lam hlam :=
  (finiteTorusCovariantCoefficientResolver_isSymmetric N B lam hlam).clm_adjoint_eq

/-- Projection onto centered coefficient data acts identically after the
finite-stage resolver. -/
theorem centeredCoefficientProjection_comp_coefficientResolver
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    (finiteFiberCenteredCoefficientEmbeddingCLM
      (N := N + 1) (d := d) (r := r)).comp
        ((finiteFiberCenteredCoefficientExtractionCLM
          (N := N + 1) (d := d) (r := r)).comp
          (finiteTorusCovariantCoefficientResolver N B lam hlam)) =
      finiteTorusCovariantCoefficientResolver N B lam hlam := by
  apply ContinuousLinearMap.ext
  intro g
  obtain ⟨Psi, hPsi⟩ :=
    exists_finiteFiberLattice_preimage_coefficientResolver
      N B lam hlam g
  change (finiteFiberCenteredCoefficientEmbeddingCLM
      (N := N + 1) (d := d) (r := r))
      ((finiteFiberCenteredCoefficientExtractionCLM
        (N := N + 1) (d := d) (r := r))
        (finiteTorusCovariantCoefficientResolver N B lam hlam g)) = _
  rw [← hPsi]
  change (finiteFiberCenteredCoefficientEmbeddingCLM
      (N := N + 1) (d := d) (r := r))
      ((finiteFiberCenteredCoefficientExtractionCLM
        (N := N + 1) (d := d) (r := r))
        ((finiteFiberCenteredCoefficientEmbeddingCLM
          (N := N + 1) (d := d) (r := r)) Psi)) = _
  rw [finiteFiberCenteredCoefficientExtraction_apply_embedding]
  rfl

/-- The finite-stage resolver also depends only on centered coefficient
data. -/
theorem coefficientResolver_comp_centeredCoefficientProjection
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    (finiteTorusCovariantCoefficientResolver N B lam hlam).comp
        ((finiteFiberCenteredCoefficientEmbeddingCLM
          (N := N + 1) (d := d) (r := r)).comp
          (finiteFiberCenteredCoefficientExtractionCLM
            (N := N + 1) (d := d) (r := r))) =
      finiteTorusCovariantCoefficientResolver N B lam hlam := by
  rw [← ContinuousLinearMap.comp_assoc]
  have h := congrArg ContinuousLinearMap.adjoint
    (centeredCoefficientProjection_comp_coefficientResolver
      N B lam hlam)
  simpa only [ContinuousLinearMap.adjoint_comp,
    finiteFiberCenteredCoefficientExtractionCLM,
    ContinuousLinearMap.adjoint_adjoint,
    finiteTorusCovariantCoefficientResolver_adjoint] using h

/-- The finite-lattice covariant resolver, obtained by pulling the exact
finite-stage coefficient multiplier back through normalized finite Fourier
interpolation. -/
def finiteTorusCovariantLatticeResolver
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r) →L[ℂ]
      FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r) :=
  finiteFiberCenteredCoefficientExtractionCLM.comp
    ((finiteTorusCovariantCoefficientResolver N B lam hlam).comp
      finiteFiberCenteredCoefficientEmbeddingCLM)

/-- Exact intertwining of the finite-lattice resolver with its centered
coefficient multiplier. -/
theorem finiteFiberCenteredCoefficientEmbedding_intertwines_latticeResolver
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam)
    (Phi : FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r)) :
    finiteFiberCenteredCoefficientEmbedding
        (finiteTorusCovariantLatticeResolver N B lam hlam Phi) =
      finiteTorusCovariantCoefficientResolver N B lam hlam
        (finiteFiberCenteredCoefficientEmbedding Phi) := by
  obtain ⟨Psi, hPsi⟩ :=
    exists_finiteFiberLattice_preimage_coefficientResolver
      N B lam hlam (finiteFiberCenteredCoefficientEmbedding Phi)
  change finiteFiberCenteredCoefficientEmbedding
      (finiteFiberCenteredCoefficientExtractionCLM
        (finiteTorusCovariantCoefficientResolver N B lam hlam
          (finiteFiberCenteredCoefficientEmbedding Phi))) = _
  rw [← hPsi]
  change (finiteFiberCenteredCoefficientEmbeddingCLM
      (N := N + 1) (d := d) (r := r))
      ((finiteFiberCenteredCoefficientExtractionCLM
        (N := N + 1) (d := d) (r := r))
        ((finiteFiberCenteredCoefficientEmbeddingCLM
          (N := N + 1) (d := d) (r := r)) Psi)) = _
  rw [finiteFiberCenteredCoefficientExtraction_apply_embedding]
  rfl

/-- Literal continuum interpolation exactly intertwines the finite-lattice
resolver with the embedded continuum-torus resolver. -/
theorem finiteFiberFourierInterpolation_intertwines_covariantLatticeResolver
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam)
    (Phi : FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r)) :
    finiteFiberFourierInterpolationCLM
        (finiteTorusCovariantLatticeResolver N B lam hlam Phi) =
      finiteTorusCovariantEmbeddedResolver N B lam hlam
        (finiteFiberFourierInterpolationCLM Phi) := by
  apply finiteFiberTorusFourierEquiv.injective
  rw [finiteFiberTorusFourierEquiv_apply_interpolation,
    finiteFiberCenteredCoefficientEmbedding_intertwines_latticeResolver]
  change finiteTorusCovariantCoefficientResolver N B lam hlam
      (finiteFiberCenteredCoefficientEmbedding Phi) =
    finiteFiberTorusFourierEquiv
      (finiteFiberTorusFourierEquiv.symm
        (finiteTorusCovariantCoefficientResolver N B lam hlam
          (finiteFiberTorusFourierEquiv
            (finiteFiberFourierInterpolationCLM Phi))))
  rw [finiteFiberTorusFourierEquiv_apply_interpolation,
    LinearIsometryEquiv.apply_symm_apply]
/-- Extraction after the continuum Fourier unitary is exactly the adjoint of
literal Fourier interpolation. -/
@[simp]
theorem finiteFiberCenteredCoefficientExtraction_apply_torusFourierEquiv
    (N : ℕ)
    (f : FiniteFiberContinuumTorusL2 (d := d) (r := r)) :
    (finiteFiberCenteredCoefficientExtractionCLM
      (N := N + 1) (d := d) (r := r))
        (finiteFiberTorusFourierEquiv f) =
      finiteFiberFourierInterpolationAdjoint
        (N := N + 1) (d := d) (r := r) f := by
  unfold finiteFiberCenteredCoefficientExtractionCLM
  change ContinuousLinearMap.adjoint
      (finiteFiberTorusFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (finiteFiberFourierInterpolationCLM
          (N := N + 1) (d := d) (r := r)))
      (finiteFiberTorusFourierEquiv f) = _
  rw [ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm]
  change finiteFiberFourierInterpolationAdjoint
      (finiteFiberTorusFourierEquiv.symm
        (finiteFiberTorusFourierEquiv f)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- The manuscript-shaped embedded finite resolver: interpolate the finite
lattice resolver after applying the interpolation adjoint. -/
def finiteTorusCovariantInterpolatedResolver
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  (finiteFiberFourierInterpolationCLM
    (N := N + 1) (d := d) (r := r)).comp
      ((finiteTorusCovariantLatticeResolver N B lam hlam).comp
        (finiteFiberFourierInterpolationAdjoint
          (N := N + 1) (d := d) (r := r)))

/-- The interpolation-adjoint formula is exactly the zero-extended physical
resolver, as an equality of bounded operators on continuum torus `L²`. -/
theorem finiteTorusCovariantInterpolatedResolver_eq_embeddedResolver
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    finiteTorusCovariantInterpolatedResolver N B lam hlam =
      finiteTorusCovariantEmbeddedResolver N B lam hlam := by
  apply ContinuousLinearMap.ext
  intro f
  change (finiteFiberFourierInterpolationCLM
      (N := N + 1) (d := d) (r := r))
      (finiteTorusCovariantLatticeResolver N B lam hlam
        ((finiteFiberFourierInterpolationAdjoint
          (N := N + 1) (d := d) (r := r)) f)) = _
  rw [finiteFiberFourierInterpolation_intertwines_covariantLatticeResolver]
  apply finiteFiberTorusFourierEquiv.injective
  simp [finiteTorusCovariantEmbeddedResolver,
    conjugateByFiniteFiberTorusFourierEquiv]
  rw [← finiteFiberCenteredCoefficientExtraction_apply_torusFourierEquiv]
  have h := congrArg (fun T :
      ℓ²(d → ℤ, EuclideanSpace ℂ r) →L[ℂ]
        ℓ²(d → ℤ, EuclideanSpace ℂ r) ↦
      T (finiteFiberTorusFourierEquiv f))
    (coefficientResolver_comp_centeredCoefficientProjection
      N B lam hlam)
  simpa [finiteFiberCenteredCoefficientEmbeddingCLM] using h

/-- Operator-norm convergence in the literal manuscript form
`I_N R_N I_N† → R`. -/
theorem finiteTorusCovariantInterpolatedResolver_tendsto
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    Filter.Tendsto
      (fun N ↦ finiteTorusCovariantInterpolatedResolver N B lam hlam)
      Filter.atTop
      (nhds (continuumTorusCovariantResolver B lam hlam)) := by
  simpa only [finiteTorusCovariantInterpolatedResolver_eq_embeddedResolver]
    using finiteTorusCovariantEmbeddedResolver_tendsto B lam hlam


end NCG
