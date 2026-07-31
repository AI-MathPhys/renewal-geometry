/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Shared-source scalar cycles and the mixed Wick obstruction
  (`thm:shared-source-block-cycle-main`,
   `thm:mixed-wick-polarisation-main`,
   `cor:no-inherited-common-history-mass-main`, SM_emergence)

* `offdiag_block_trace_fourth` — for the doubled off-diagonal block
  `X = [[0, Yᴴ], [Y, 0]]`, `Tr X⁴ = 2·Tr((YᴴY)²)`;
* `shared_source_block_cycle` — stacking two Dirac blocks with a
  common right endpoint, `Y = [O; C]`, gives the boxed identity
  `Tr X(O,C)⁴ = 2Tr A² + 2Tr B² + 4Tr(AB)` with `A = OᴴO`,
  `B = CᴴC` — the forced mixed four-cycle;
* `mixed_wick_polarisation` — under the unit Gaussian contraction
  `𝔼R = M·1`, the traceless-adjoint polarisation vanishes and the
  trace-singlet polarisation is `M·Tr S`;
* `no_inherited_common_history_mass` — hence a centred
  traceless-adjoint history exchange contributes no
  representation-blind remnant mass.

The Gaussian moment `𝔼[XᴴX] = M·1` is the declared probabilistic
input of the Wick theorem.
-/

namespace NCG

open Matrix

variable {k m n p : Type*} [Fintype k] [Fintype m] [Fintype n]
  [Fintype p]

/-- For the doubled off-diagonal block, `Tr X⁴ = 2·Tr((YᴴY)²)`. -/
theorem offdiag_block_trace_fourth (Y : Matrix p k ℂ) :
    Matrix.trace ((Matrix.fromBlocks 0 Yᴴ Y 0)
        * Matrix.fromBlocks 0 Yᴴ Y 0
        * (Matrix.fromBlocks 0 Yᴴ Y 0
          * Matrix.fromBlocks 0 Yᴴ Y 0))
      = 2 * Matrix.trace ((Yᴴ * Y) * (Yᴴ * Y)) := by
  have hsq : (Matrix.fromBlocks 0 Yᴴ Y 0)
      * Matrix.fromBlocks 0 Yᴴ Y 0
      = Matrix.fromBlocks (Yᴴ * Y) 0 0 (Y * Yᴴ) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1 <;> simp
  have htrb : ∀ (A : Matrix k k ℂ) (D : Matrix p p ℂ),
      Matrix.trace (Matrix.fromBlocks A 0 0 D)
        = Matrix.trace A + Matrix.trace D := by
    intro A D
    simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  rw [hsq, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [htrb]
  have hcyc : Matrix.trace (Y * Yᴴ * (Y * Yᴴ))
      = Matrix.trace (Yᴴ * Y * (Yᴴ * Y)) := by
    rw [show Y * Yᴴ * (Y * Yᴴ) = Y * (Yᴴ * (Y * Yᴴ)) from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hcyc]
  ring

/-- `thm:shared-source-block-cycle-main`: two primitive Dirac blocks
with a common right endpoint force the boxed mixed four-cycle
`Tr X⁴ = 2Tr A² + 2Tr B² + 4Tr(AB)`, `A = OᴴO`, `B = CᴴC`. -/
theorem shared_source_block_cycle (O : Matrix m k ℂ)
    (C : Matrix n k ℂ) :
    Matrix.trace ((Matrix.fromBlocks 0 (Matrix.fromRows O C)ᴴ
          (Matrix.fromRows O C) 0)
        * Matrix.fromBlocks 0 (Matrix.fromRows O C)ᴴ
          (Matrix.fromRows O C) 0
        * (Matrix.fromBlocks 0 (Matrix.fromRows O C)ᴴ
            (Matrix.fromRows O C) 0
          * Matrix.fromBlocks 0 (Matrix.fromRows O C)ᴴ
            (Matrix.fromRows O C) 0))
      = 2 * Matrix.trace (Oᴴ * O * (Oᴴ * O))
        + 2 * Matrix.trace (Cᴴ * C * (Cᴴ * C))
        + 4 * Matrix.trace (Oᴴ * O * (Cᴴ * C)) := by
  rw [offdiag_block_trace_fourth]
  have hgram : (Matrix.fromRows O C)ᴴ * Matrix.fromRows O C
      = Oᴴ * O + Cᴴ * C := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  rw [hgram]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  have hBA : Matrix.trace (Cᴴ * C * (Oᴴ * O))
      = Matrix.trace (Oᴴ * O * (Cᴴ * C)) :=
    Matrix.trace_mul_comm _ _
  rw [hBA]
  ring

/-- `thm:mixed-wick-polarisation-main`: under the unit Gaussian
contraction `𝔼R = M·1`, the traceless-adjoint polarisation
vanishes and the trace-singlet polarisation equals `M·Tr S`. -/
theorem mixed_wick_polarisation {N : ℕ} (hN : 0 < N)
    (ER S : Matrix (Fin N) (Fin N) ℂ) (M : ℂ)
    (hER : ER = M • (1 : Matrix (Fin N) (Fin N) ℂ)) :
    Matrix.trace (ER * S)
        - (1 / (N : ℂ)) * Matrix.trace ER * Matrix.trace S = 0
      ∧ (1 / (N : ℂ)) * Matrix.trace ER * Matrix.trace S
        = M * Matrix.trace S := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have htr1 : Matrix.trace (1 : Matrix (Fin N) (Fin N) ℂ) = N := by
    rw [Matrix.trace_one]
    simp
  have h1 : Matrix.trace (ER * S) = M * Matrix.trace S := by
    rw [hER, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      smul_eq_mul]
  have h2 : Matrix.trace ER = M * N := by
    rw [hER, Matrix.trace_smul, htr1, smul_eq_mul]
  constructor
  · rw [h1, h2]
    field_simp
    ring
  · rw [h2]
    field_simp

/-- `cor:no-inherited-common-history-mass-main`: a remnant mass
sourced only through the centred traceless-adjoint polarisation
vanishes. -/
theorem no_inherited_common_history_mass {N : ℕ} (hN : 0 < N)
    (ER S : Matrix (Fin N) (Fin N) ℂ) (M kappa : ℂ)
    (hER : ER = M • (1 : Matrix (Fin N) (Fin N) ℂ))
    {dm : ℂ}
    (hdm : dm = kappa * (Matrix.trace (ER * S)
      - (1 / (N : ℂ)) * Matrix.trace ER * Matrix.trace S)) :
    dm = 0 := by
  rw [hdm, (mixed_wick_polarisation hN ER S M hER).1, mul_zero]

end NCG
