/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusCovariantContinuumResolvent
import NCG.Grand.L2BlockDiagonalCompactness

/-!
# Compactness of the continuum covariant resolver

The quadratic Fourier tail makes the continuum coefficient resolver a norm
limit of finite coordinate compressions.  Finite-dimensional fibres therefore
make this resolver compact.  Unitary Fourier conjugation transfers compactness
to the literal continuum-torus carrier.
-/

open scoped InnerProduct lp

noncomputable section

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Nontrivial E] [FiniteDimensional ℂ E]

/-- The continuum covariant coefficient resolver is compact for a
finite-dimensional fibre. -/
theorem continuumCovariantCoefficientResolver_isCompactOperator
    (B : d → E →L[ℂ] E) (lam : ℝ) (hlam : 0 < lam) :
    IsCompactOperator
      ((continuumCovariantCoefficientResolver B lam hlam :
          ℓ²(d → ℤ, E) →L[ℂ] ℓ²(d → ℤ, E)) :
        ℓ²(d → ℤ, E) → ℓ²(d → ℤ, E)) := by
  apply isCompactOperator_of_finsetScreen_compression_approx_arbitrarily
  intro ε hε
  obtain ⟨R, _, hthreshold, hsmall⟩ :=
    exists_covariantResolverTailRadius
      lam (finiteConnectionNormEnvelope B) ε hlam hε
  refine ⟨integerFourierBox (d := d) R, ?_⟩
  have htail :
      ‖continuumCovariantCoefficientResolver B lam hlam -
          screenCompression
            (l2FinsetScreen (E := E) (integerFourierBox (d := d) R))
            (continuumCovariantCoefficientResolver B lam hlam)‖ ≤
        1 / (lam + integerFourierCoercivityFloor R) := by
    apply (continuumCovariantCoefficientResolver_isL2BlockDiagonal
      (B := B) (lam := lam) hlam).norm_sub_screenCompression_le_of_outside
      (integerFourierBox (d := d) R)
      (1 / (lam + integerFourierCoercivityFloor R))
      (one_div_nonneg.mpr
        (add_nonneg hlam.le (integerFourierCoercivityFloor_nonneg R))) ?_
    intro k hk x
    have hblock :=
      continuumCovariantFourierOperatorStack_resolvent_opNorm_le
        R (finiteConnectionNormEnvelope B) k B lam hk hlam
        (norm_le_finiteConnectionNormEnvelope B) hthreshold
    exact (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right hblock (norm_nonneg x))
  exact htail.trans_lt hsmall

variable {r : Type} [Fintype r] [Nonempty r]

/-- The continuum covariant resolver on literal torus `L²` is compact. -/
theorem continuumTorusCovariantResolver_isCompactOperator
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    IsCompactOperator
      ((continuumTorusCovariantResolver B lam hlam :
          FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
            FiniteFiberContinuumTorusL2 (d := d) (r := r)) :
        FiniteFiberContinuumTorusL2 (d := d) (r := r) →
          FiniteFiberContinuumTorusL2 (d := d) (r := r)) := by
  have hcoeff :=
    continuumCovariantCoefficientResolver_isCompactOperator B lam hlam
  exact (hcoeff.comp_clm
    finiteFiberTorusFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      finiteFiberTorusFourierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap

end NCG
