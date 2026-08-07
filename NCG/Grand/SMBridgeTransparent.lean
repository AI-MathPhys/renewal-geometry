/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Universal grading-bridge transparency
  (`thm:SM-bridge-transparent`, Gran-Tensor manuscript)

* `sm_bridge_transparent`: for the edge coefficient
  `Y_e = D_e ⊗ F_e` with polar factor `F_e = U_e P_e`
  (`U_e` an isometry, `P_e` Hermitian) and carrier squares
  `D_e^*D_e = c_e p_e`, `D_eD_e^* = c_e q_e`, the boxed squares
  are `Y^*Y = c(p ⊗ P²)` and `YY^* = c(q ⊗ U P² U^*)`; and an
  internal-carrier commutant element `1 ⊗ R'` (target) /
  `1 ⊗ R` (source) commutes through `Y_e` exactly when
  `R' F = F R` — so all generation/flavour data are independent
  of every nonzero carrier factor.

Rendering disclosed: the multi-sector direct sum
`⊕_λ I ⊗ R_λ` reduces to the displayed single-edge cancellation
sector by sector; independence of "the score-square bridge and
its scalar rate" is the visible fact that the cancellation
hypothesis only requires the carrier factor `D_e` to be nonzero.
-/

open Matrix Kronecker

namespace NCG

/-- `thm:SM-bridge-transparent`: the boxed edge squares and the
carrier-transparent commutant cancellation. -/
theorem sm_bridge_transparent {v w a : Type*} [Fintype v]
    [Fintype w] [Fintype a] [DecidableEq v] [DecidableEq w]
    [DecidableEq a]
    (D : Matrix v w ℂ) (U P : Matrix a a ℂ) (c : ℂ)
    (p : Matrix w w ℂ) (q : Matrix v v ℂ)
    (hDl : Dᴴ * D = c • p) (hDr : D * Dᴴ = c • q)
    (hU : Uᴴ * U = 1) (hP : Pᴴ = P) :
    ((D ⊗ₖ (U * P))ᴴ * (D ⊗ₖ (U * P))
        = c • (p ⊗ₖ (P * P)))
    ∧ ((D ⊗ₖ (U * P)) * (D ⊗ₖ (U * P))ᴴ
        = c • (q ⊗ₖ (U * (P * P) * Uᴴ)))
    ∧ (∀ (R R' : Matrix a a ℂ),
        (∃ i j, D i j ≠ 0) →
        (((1 : Matrix v v ℂ) ⊗ₖ R') * (D ⊗ₖ (U * P))
            = (D ⊗ₖ (U * P)) * ((1 : Matrix w w ℂ) ⊗ₖ R)
          ↔ R' * (U * P) = (U * P) * R)) := by
  have hFsq : (U * P)ᴴ * (U * P) = P * P := by
    rw [Matrix.conjTranspose_mul]
    calc Pᴴ * Uᴴ * (U * P) = Pᴴ * (Uᴴ * U) * P := by
          simp only [Matrix.mul_assoc]
      _ = P * P := by
          rw [hU, Matrix.mul_one, hP]
  have hFFh : (U * P) * (U * P)ᴴ = U * (P * P) * Uᴴ := by
    rw [Matrix.conjTranspose_mul, hP]
    simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, hDl, hFsq,
      Matrix.smul_kronecker]
  · rw [Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, hDr, hFFh,
      Matrix.smul_kronecker]
  · intro R R' hD
    constructor
    · intro hcomm
      obtain ⟨i, j, hij⟩ := hD
      rw [← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Matrix.mul_one] at hcomm
      ext x y
      have h := congrArg (fun M => M (i, x) (j, y)) hcomm
      simp only [Matrix.kroneckerMap_apply] at h
      exact mul_left_cancel₀ hij h
    · intro hcomm
      rw [← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Matrix.mul_one, hcomm]

end NCG
