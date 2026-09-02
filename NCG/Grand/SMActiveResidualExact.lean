/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMActiveResidual
import NCG.Grand.ActiveResidualAlgebra
import NCG.Grand.DimensionLockedK4DecompositionExact

/-!
# Exact active geometry short and residual census

This completes `thm:SM-active-residual-short` by pairing the general positive
Schur-short theorem with the concrete ordered-root carrier census.  The five
central orthogonal projectors have dimensions `1,2,3,3,3`; the first three
are reversal-even and the last two reversal-odd.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace NCG
namespace SMActiveResidual

/-- On the conservative active product carrier the mixed block is zero, so
shorting leaves the scalar twelve-dimensional internal Gram unchanged. -/
theorem active_product_short_eq
    {k d : Type*} [Fintype k] [Fintype d]
    [DecidableEq k] [DecidableEq d]
    (θ : ℝ) (D : Matrix d d ℂ) :
    (θ : ℂ) • (1 : Matrix k k ℂ) -
        (0 : Matrix d k ℂ)ᴴ * D⁻¹ * (0 : Matrix d k ℂ) =
      (θ : ℂ) • (1 : Matrix k k ℂ) := by
  simp

/-- Concrete multiplicity-free residual census
`ℂ_type⁺ ⊕ W₊ ⊕ (V₂)₊ ⊕ W₋ ⊕ (W⊗sgn)₋`. -/
theorem active_residual_census_exact :
    ActiveResidual.Qtype + ActiveResidual.QW2 + ActiveResidual.QC +
        ActiveResidual.QG + ActiveResidual.QP = 1
    ∧ ActiveResidual.Qtype.trace = 1
    ∧ ActiveResidual.QW2.trace = 2
    ∧ ActiveResidual.QC.trace = 3
    ∧ ActiveResidual.QG.trace = 3
    ∧ ActiveResidual.QP.trace = 3
    ∧ ActiveResidual.Qtype + ActiveResidual.QW2 + ActiveResidual.QC =
        (2 : ℂ)⁻¹ • (1 + ActiveResidual.Rm)
    ∧ ActiveResidual.Qtype * ActiveResidual.Qtype = ActiveResidual.Qtype
    ∧ ActiveResidual.QW2 * ActiveResidual.QW2 = ActiveResidual.QW2
    ∧ ActiveResidual.QC * ActiveResidual.QC = ActiveResidual.QC
    ∧ ActiveResidual.QG * ActiveResidual.QG = ActiveResidual.QG
    ∧ ActiveResidual.QP * ActiveResidual.QP = ActiveResidual.QP
    ∧ ActiveResidual.Qtypeᴴ = ActiveResidual.Qtype
    ∧ ActiveResidual.QW2ᴴ = ActiveResidual.QW2
    ∧ ActiveResidual.QCᴴ = ActiveResidual.QC
    ∧ ActiveResidual.QGᴴ = ActiveResidual.QG
    ∧ ActiveResidual.QPᴴ = ActiveResidual.QP
    ∧ ActiveResidual.Qtype * ActiveResidual.QW2 = 0
    ∧ ActiveResidual.Qtype * ActiveResidual.QC = 0
    ∧ ActiveResidual.Qtype * ActiveResidual.QG = 0
    ∧ ActiveResidual.Qtype * ActiveResidual.QP = 0
    ∧ ActiveResidual.QW2 * ActiveResidual.QC = 0
    ∧ ActiveResidual.QW2 * ActiveResidual.QG = 0
    ∧ ActiveResidual.QW2 * ActiveResidual.QP = 0
    ∧ ActiveResidual.QC * ActiveResidual.QG = 0
    ∧ ActiveResidual.QC * ActiveResidual.QP = 0
    ∧ ActiveResidual.QG * ActiveResidual.QP = 0 := by
  exact ⟨ActiveResidual.Qsum,
    ActiveResidual.Qtype_trace,
    ActiveResidual.QW2_trace,
    ActiveResidual.QC_trace,
    ActiveResidual.QG_trace,
    ActiveResidual.QP_trace,
    ActiveResidual.even_corner,
    ActiveResidual.Qtype_idem,
    ActiveResidual.QW2_idem,
    ActiveResidual.QC_idem,
    ActiveResidual.QG_idem,
    ActiveResidual.QP_idem,
    ActiveResidual.Qtype_herm,
    ActiveResidual.QW2_herm,
    ActiveResidual.QC_herm,
    ActiveResidual.QG_herm,
    ActiveResidual.QP_herm,
    ActiveResidual.Qtype_QW2,
    ActiveResidual.Qtype_QC,
    ActiveResidual.Qtype_QG,
    ActiveResidual.Qtype_QP,
    ActiveResidual.QW2_QC,
    ActiveResidual.QW2_QG,
    ActiveResidual.QW2_QP,
    ActiveResidual.QC_QG,
    ActiveResidual.QC_QP,
    ActiveResidual.QG_QP⟩

end SMActiveResidual
end NCG
