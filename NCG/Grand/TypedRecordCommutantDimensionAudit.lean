/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.MinimalNaturality

/-!
# Typed record commutant dimension audit

The former displayed algebra in `thm:SM-typed-occurrence-RN` contained a full
`M₂(ℂ)` neutral block, while its subsequent parameter count treats that block
as though its commutant were all Hermitian `2 × 2` matrices.  These two claims
cannot simultaneously hold in the natural representation. This file records
the precise finite-dimensional obstruction that motivated the corrected
scalar algebra acting with multiplicity two.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- The commutant of the displayed full neutral `M₂(ℂ)` block is scalar. -/
theorem typedNeutralFullMatrixBlock_commutant_scalar
    (K : Matrix (Fin 2) (Fin 2) ℂ)
    (hK : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A * K = K * A) :
    ∃ k : ℂ, K = k • 1 :=
  full_commutant_scalar K hK

/-- A concrete non-scalar Hermitian effect on the neutral doublet fails the
nondemolition commutation condition for the full `M₂(ℂ)` record block. -/
theorem neutralRankOneEffect_not_in_fullMatrixBlock_commutant :
    ¬ (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      A * (Matrix.diagonal ![1, 0]) =
        (Matrix.diagonal ![1, 0]) * A) := by
  intro h
  have hs := h (Matrix.single 0 1 1)
  have hij := congrFun (congrFun hs 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hij

/-- Consequently, arbitrary `2 × 2` neutral effects are incompatible with
the commutant of the displayed full matrix record block. -/
theorem arbitraryNeutralEffects_incompatible_with_fullMatrixRecord :
    ∃ K : Matrix (Fin 2) (Fin 2) ℂ,
      K.IsHermitian ∧ K.PosSemidef ∧
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - K).PosSemidef ∧
      ¬ (∀ A : Matrix (Fin 2) (Fin 2) ℂ, A * K = K * A) := by
  have hK : (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  have hcomp : ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
      Matrix.diagonal ![1, 0]).PosSemidef := by
    have heq : (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        Matrix.diagonal ![1, 0] = Matrix.diagonal ![0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [heq, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  exact ⟨Matrix.diagonal ![1, 0], hK.isHermitian, hK, hcomp,
    neutralRankOneEffect_not_in_fullMatrixBlock_commutant⟩

end NCG
