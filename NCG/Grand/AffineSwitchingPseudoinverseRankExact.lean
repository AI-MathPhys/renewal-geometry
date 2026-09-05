/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineSwitching
import NCG.Grand.ExactSourceSchurResidual

/-!
# Pseudoinverse and rank form of affine switching incidence

The switching bank may be rank deficient: its Moore--Penrose source-range
projection defines the innovation, whose rank is exactly the missing block-Gram
rank increment.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace AffineSwitchingPseudoinverseRankExact


/-- Complete AFF.1 with the genuine Moore--Penrose projector and its missing
source-dimension rank formula, followed by the one-line parity statement. -/
theorem affine_switching_incidence_pseudoinverse_rank
    {h e₁ e₂ : ℕ}
    (Ssw : Matrix (Fin h) (Fin e₁) ℂ)
    (Npar : Matrix (Fin h) (Fin e₂) ℂ)
    (q : ℝ → ℝ) (hq : ∀ c x : ℝ, q (c * x) = c ^ 2 * q x) :
    (sourceSchurResidual Ssw Npar =
      Nparᴴ * (1 - sourceRangeProjection Ssw) * Npar) ∧
    (sourceSchurResidual Ssw Npar).PosSemidef ∧
    (sourceSchurResidual Ssw Npar = 0 ↔ SourceRangeIncluded Npar Ssw) ∧
    ((Matrix.fromBlocks (Sswᴴ * Ssw) (Sswᴴ * Npar)
        ((Sswᴴ * Npar)ᴴ) (Nparᴴ * Npar)).rank - (Sswᴴ * Ssw).rank =
      (sourceSchurResidual Ssw Npar).rank) ∧
    (∀ x : ℝ, q x = q 1 * x ^ 2) := by
  exact ⟨sourceSchurResidual_eq_orthogonalResidual Ssw Npar,
    sourceSchurResidual_posSemidef Ssw Npar,
    sourceSchurResidual_eq_zero_iff_rangeIncluded Ssw Npar,
    sourceSchurResidual_rank_increment Ssw Npar,
    affine_parity_line_scalar q hq⟩

end AffineSwitchingPseudoinverseRankExact
end NCG
