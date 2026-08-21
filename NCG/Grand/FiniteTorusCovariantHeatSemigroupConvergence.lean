/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusCovariantRieszConvergence
import NCG.Grand.L2BlockDiagonalPositivity
import NCG.Grand.OperatorGraphResolventHeatFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Heat-semigroup convergence for periodic covariant resolvents

Finite and continuum covariant resolvents are positive self-adjoint
contractions at scale `1 / λ`.  Their spectra therefore lie in the common
compact interval `[0, λ⁻¹]`.  Continuity of the real functional calculus
then upgrades norm-resolvent convergence to operator-norm convergence of the
canonical positive-time heat semigroups.
-/

open Filter Set Topology
open scoped InnerProduct lp

noncomputable section

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {r : Type} [Fintype r] [Nonempty r]

/-- Every finite-stage coefficient resolver block is positive. -/
theorem finiteTorusCovariantResolverBlock_isPositive
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) (k : d → ℤ) :
    (finiteTorusCovariantResolverBlock N B lam hlam k).IsPositive := by
  by_cases hk : k ∈ finiteTorusCenteredFrequencyWindow (d := d) N
  · rw [finiteTorusCovariantResolverBlock, if_pos hk]
    exact VaryingHilbert.boundedOperatorNormalResolvent_isPositive _ lam hlam
  · rw [finiteTorusCovariantResolverBlock, if_neg hk]
    exact ContinuousLinearMap.isPositive_zero

/-- Every continuum coefficient resolver block is positive. -/
theorem continuumCovariantResolverBlock_isPositive
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) (k : d → ℤ) :
    (continuumCovariantResolverBlock B lam hlam k).IsPositive :=
  VaryingHilbert.boundedOperatorNormalResolvent_isPositive _ lam hlam

/-- The finite coefficient resolver is positive. -/
theorem finiteTorusCovariantCoefficientResolver_isPositive
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    (finiteTorusCovariantCoefficientResolver N B lam hlam).IsPositive :=
  l2BlockDiagonal_isPositive
    (finiteTorusCovariantResolverBlock N B lam hlam)
    (1 / lam) (by positivity)
    (finiteTorusCovariantResolverBlock_norm_apply_le_inv N B lam hlam)
    (finiteTorusCovariantResolverBlock_isPositive N B lam hlam)

/-- The continuum coefficient resolver is positive. -/
theorem continuumCovariantCoefficientResolver_isPositive
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    (continuumCovariantCoefficientResolver B lam hlam).IsPositive :=
  l2BlockDiagonal_isPositive
    (continuumCovariantResolverBlock B lam hlam)
    (1 / lam) (by positivity)
    (continuumCovariantResolverBlock_norm_apply_le_inv B lam hlam)
    (continuumCovariantResolverBlock_isPositive B lam hlam)

/-- Unitary finite-fibre Fourier conjugation preserves positivity. -/
theorem conjugateByFiniteFiberTorusFourierEquiv_isPositive
    (T : ℓ²(d → ℤ, EuclideanSpace ℂ r) →L[ℂ]
      ℓ²(d → ℤ, EuclideanSpace ℂ r))
    (hT : T.IsPositive) :
    (conjugateByFiniteFiberTorusFourierEquiv T).IsPositive := by
  have h := hT.conj_adjoint
    finiteFiberTorusFourierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  simpa only [conjugateByFiniteFiberTorusFourierEquiv,
    ContinuousLinearMap.comp_assoc,
    LinearIsometryEquiv.adjoint_eq_symm] using h

/-- Every literal interpolated finite resolver is positive. -/
theorem finiteTorusCovariantInterpolatedResolver_isPositive
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    (finiteTorusCovariantInterpolatedResolver N B lam hlam).IsPositive := by
  rw [finiteTorusCovariantInterpolatedResolver_eq_embeddedResolver]
  exact conjugateByFiniteFiberTorusFourierEquiv_isPositive _
    (finiteTorusCovariantCoefficientResolver_isPositive N B lam hlam)

/-- The literal continuum torus resolver is positive. -/
theorem continuumTorusCovariantResolver_isPositive
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    (continuumTorusCovariantResolver B lam hlam).IsPositive :=
  conjugateByFiniteFiberTorusFourierEquiv_isPositive _
    (continuumCovariantCoefficientResolver_isPositive B lam hlam)

/-- The finite coefficient resolver has the sharp shift bound. -/
theorem finiteTorusCovariantCoefficientResolver_opNorm_le_inv
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    ‖finiteTorusCovariantCoefficientResolver N B lam hlam‖ ≤ 1 / lam :=
  l2BlockDiagonal_opNorm_le _ (1 / lam) (by positivity)
    (finiteTorusCovariantResolverBlock_norm_apply_le_inv N B lam hlam)

/-- The continuum coefficient resolver has the sharp shift bound. -/
theorem continuumCovariantCoefficientResolver_opNorm_le_inv
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    ‖continuumCovariantCoefficientResolver B lam hlam‖ ≤ 1 / lam :=
  l2BlockDiagonal_opNorm_le _ (1 / lam) (by positivity)
    (continuumCovariantResolverBlock_norm_apply_le_inv B lam hlam)

/-- Unitary finite-fibre Fourier conjugation preserves any operator-norm
upper bound. -/
theorem conjugateByFiniteFiberTorusFourierEquiv_opNorm_le
    (T : ℓ²(d → ℤ, EuclideanSpace ℂ r) →L[ℂ]
      ℓ²(d → ℤ, EuclideanSpace ℂ r))
    (C : ℝ) (hC : 0 ≤ C) (hT : ‖T‖ ≤ C) :
    ‖conjugateByFiniteFiberTorusFourierEquiv T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  simp only [conjugateByFiniteFiberTorusFourierEquiv,
    ContinuousLinearMap.comp_apply]
  rw [LinearIsometryEquiv.norm_map]
  calc
    ‖T (finiteFiberTorusFourierEquiv f)‖ ≤
        ‖T‖ * ‖finiteFiberTorusFourierEquiv f‖ :=
      T.le_opNorm _
    _ ≤ C * ‖finiteFiberTorusFourierEquiv f‖ :=
      mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ = C * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]

/-- Every literal interpolated finite resolver has norm at most `1 / λ`. -/
theorem finiteTorusCovariantInterpolatedResolver_opNorm_le_inv
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    ‖finiteTorusCovariantInterpolatedResolver N B lam hlam‖ ≤ 1 / lam := by
  rw [finiteTorusCovariantInterpolatedResolver_eq_embeddedResolver]
  exact conjugateByFiniteFiberTorusFourierEquiv_opNorm_le _
    (1 / lam) (by positivity)
    (finiteTorusCovariantCoefficientResolver_opNorm_le_inv N B lam hlam)

/-- The literal continuum resolver has norm at most `1 / λ`. -/
theorem continuumTorusCovariantResolver_opNorm_le_inv
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    ‖continuumTorusCovariantResolver B lam hlam‖ ≤ 1 / lam :=
  conjugateByFiniteFiberTorusFourierEquiv_opNorm_le _
    (1 / lam) (by positivity)
    (continuumCovariantCoefficientResolver_opNorm_le_inv B lam hlam)

/-- A positive resolver with the shift bound has real spectrum in the
canonical interval. -/
theorem realSpectrum_subset_Icc_of_isPositive_of_opNorm_le_inv
    (T : FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r))
    (lam : ℝ) (hpositive : T.IsPositive) (hnorm : ‖T‖ ≤ 1 / lam) :
    spectrum ℝ T ⊆ Icc 0 lam⁻¹ := by
  intro x hx
  constructor
  · exact spectrum_nonneg_of_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive) hx
  · exact (Real.le_norm_self x).trans
      ((spectrum.norm_le_norm_of_mem hx).trans (by simpa [one_div] using hnorm))

/-- The heat operator reconstructed from the finite interpolated resolver. -/
def finiteTorusCovariantInterpolatedHeat
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam t : ℝ) (hlam : 0 < lam) :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  VaryingHilbert.operatorGraphResolventHeat
    (finiteTorusCovariantInterpolatedResolver N B lam hlam) lam t

/-- The heat operator reconstructed from the continuum torus resolver. -/
def continuumTorusCovariantHeat
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam t : ℝ) (hlam : 0 < lam) :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  VaryingHilbert.operatorGraphResolventHeat
    (continuumTorusCovariantResolver B lam hlam) lam t

/-- Positive-time heat semigroups converge in operator norm, hence in
particular strongly. -/
theorem finiteTorusCovariantInterpolatedHeat_tendsto
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Tendsto
      (fun N ↦ finiteTorusCovariantInterpolatedHeat N B lam t hlam)
      atTop
      (𝓝 (continuumTorusCovariantHeat B lam t hlam)) := by
  have hconv :=
    finiteTorusCovariantInterpolatedResolver_tendsto B lam hlam
  have hspecStage : ∀ N,
      spectrum ℝ (finiteTorusCovariantInterpolatedResolver N B lam hlam) ⊆
        Icc 0 lam⁻¹ := fun N ↦
    realSpectrum_subset_Icc_of_isPositive_of_opNorm_le_inv
      _ lam
      (finiteTorusCovariantInterpolatedResolver_isPositive N B lam hlam)
      (finiteTorusCovariantInterpolatedResolver_opNorm_le_inv N B lam hlam)
  have hspecLim :
      spectrum ℝ (continuumTorusCovariantResolver B lam hlam) ⊆
        Icc 0 lam⁻¹ :=
    realSpectrum_subset_Icc_of_isPositive_of_opNorm_le_inv
      _ lam (continuumTorusCovariantResolver_isPositive B lam hlam)
      (continuumTorusCovariantResolver_opNorm_le_inv B lam hlam)
  have hcfc := hconv.cfc
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) lam⁻¹))
    (ImplicitEuler.resolventHeatMultiplier lam t)
    (Eventually.of_forall hspecStage)
    (Eventually.of_forall fun N ↦
      (finiteTorusCovariantInterpolatedResolver_isPositive
        N B lam hlam).isSelfAdjoint)
    hspecLim
    (continuumTorusCovariantResolver_isPositive B lam hlam).isSelfAdjoint
    (ImplicitEuler.continuousOn_resolventHeatMultiplier lam t hlam ht)
  simpa only [finiteTorusCovariantInterpolatedHeat,
    continuumTorusCovariantHeat,
    VaryingHilbert.operatorGraphResolventHeat] using hcfc

end NCG
