/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.StoreFrequencyPencil

/-!
# Centrally unmarked semantic alternative
  (`thm:no-unmarked-semantic-split-master`, flagship manuscript)

With source-rank-one blocks `A(q)z_j = a_j(q)z_j` on loaded
Store-frequency sources separated by the mixed window (distinct
loaded values `λ_j`, nonzero weights `w_j`), the one-step mixed
moments `m_r = Σ_j λ_jʳ a_j w_j` separate the blockwise values:
the mixed-moment map is injective by Vandermonde nondegeneracy.
Central unmarkedness — the response is not future consequential —
enters as the hypothesis that the mixed moments agree with those
of a scalar label `c`; the boxed conclusion `a_1 = ⋯ = a_s (= c)`
follows (`no_unmarked_semantic_split`).  The contrapositive is
the manuscript's argument: unequal `a_j` make
`C(q) = Σ a_j e_j` a mixed-moment-detectable, hence
future-consequential, central label (disclosed rendering).
-/

open Matrix Finset

namespace NCG

variable {s : ℕ}

/-- `thm:no-unmarked-semantic-split-master`, boxed alternative:
if the mixed one-step moments of the blockwise response agree
with those of a scalar label, every loaded block carries that
scalar value. -/
theorem no_unmarked_semantic_split (lam a w : Fin s → ℝ)
    (hw : ∀ j, w j ≠ 0) (hinj : Function.Injective lam) (c : ℝ)
    (hmom : ∀ r : Fin s,
      ∑ j, lam j ^ (r : ℕ) * (a j * w j)
        = ∑ j, lam j ^ (r : ℕ) * (c * w j)) :
    ∀ j, a j = c := by
  have hdet : IsUnit ((Matrix.vandermonde lam)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact (vandermonde_det_ne_zero lam hinj).isUnit
  have hvec : (Matrix.vandermonde lam)ᵀ *ᵥ (fun j => a j * w j)
      = (Matrix.vandermonde lam)ᵀ *ᵥ (fun j => c * w j) := by
    funext r
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde_apply]
    exact hmom r
  have hcancel : (fun j => a j * w j) = fun j => c * w j := by
    have h1 := congrArg
      (fun v => ((Matrix.vandermonde lam)ᵀ)⁻¹ *ᵥ v) hvec
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec] using h1
  intro j
  have h2 := congrFun hcancel j
  exact mul_right_cancel₀ (hw j) h2

end NCG
