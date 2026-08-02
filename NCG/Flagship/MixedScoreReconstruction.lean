/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.StoreFrequencyPencil

/-!
# Finite mixed Store–score reconstruction
  (`thm:mixed-score-reconstruction-master`, flagship manuscript)

With `V_{rj} = λ_jʳ` (`0 ≤ r ≤ s-1`) and the mixed moments
`m_{r,n} = Σ_j λ_jʳ p_{j,n}` of the per-block score successes
`p_{j,n}` at any fixed score depth `n`, the boxed reconstruction

  `(m_{0,n},…,m_{s-1,n})ᵀ = V(p_{1,n},…,p_{s,n})ᵀ`,
  `(p_{j,n})_j = V⁻¹(m_{r,n})_r`

holds (`mixed_score_reconstruction`): finitely many mixed
histories reconstruct the semantic success sequence loaded by
every Store-frequency source without a sharp central-frequency
Read.  The score depth enters only through the vector `p`
(disclosed interface: the `p_{j,n}` are the per-block scores at
the fixed depth).
-/

open Matrix

namespace NCG

variable {s : ℕ} (lam : Fin s → ℝ) (p : Fin s → ℝ)

/-- `thm:mixed-score-reconstruction-master`, boxed reconstruction:
the mixed moments are the Vandermonde image of the per-block score
vector, and the score vector is recovered by the inverse. -/
theorem mixed_score_reconstruction (hinj : Function.Injective lam) :
    ((Matrix.vandermonde lam)ᵀ *ᵥ p
      = fun r : Fin s => ∑ j, lam j ^ (r : ℕ) * p j)
    ∧ (((Matrix.vandermonde lam)ᵀ)⁻¹ *ᵥ
        (fun r : Fin s => ∑ j, lam j ^ (r : ℕ) * p j) = p) := by
  have h1 : (Matrix.vandermonde lam)ᵀ *ᵥ p
      = fun r : Fin s => ∑ j, lam j ^ (r : ℕ) * p j := by
    funext r
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde_apply]
  refine ⟨h1, ?_⟩
  rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul,
    Matrix.one_mulVec]
  rw [Matrix.det_transpose]
  exact (vandermonde_det_ne_zero lam hinj).isUnit

end NCG
