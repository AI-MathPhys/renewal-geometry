/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ReturnedFeedbackHankelRankExact

/-!
# Matrix form of returned-feedback Hankel saturation

This identifies the factorized finite panel with the literal matrix
`[B D^(i+j) C]` and transfers the exact rank formula to that matrix.
-/

open Matrix Finset

namespace NCG

variable {l e : Type*} [Fintype l] [Fintype e]
  [DecidableEq l] [DecidableEq e]

theorem returnedFeedbackHankelPanel_mulVecLin
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (p q : ℕ) :
    (returnedFeedbackHankelPanel B C D p q).mulVecLin =
      (returnedFeedbackRowPanel B C D p).comp
        (returnedFeedbackColumnPanel B C D q) := by
  apply LinearMap.ext
  intro x
  funext ia
  change (∑ jb : Fin q × l,
      (B * D ^ ((ia.1 : ℕ) + (jb.1 : ℕ)) * C) ia.2 jb.2 * x jb) =
    returnedFeedbackOutput B C D
      (((returnedFeedbackTransition B C D) ^ (ia.1 : ℕ))
        (∑ j : Fin q,
          ((returnedFeedbackTransition B C D) ^ (j : ℕ))
            (returnedFeedbackSource B C D (fun a => x (j, a))))) ia.2
  rw [map_sum]
  simp_rw [← Module.End.mul_apply, ← pow_add]
  rw [map_sum, Fintype.sum_prod_type]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrFun (returnedFeedback_realizes_kernel B C D
    ((ia.1 : ℕ) + (j : ℕ)) (fun a => x (j, a))) ia.2
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h.symm

/-- Clause (v) of `thm:canonical-pre-renewal-decomposition`: every block
Hankel panel at depths at least the returned-feedback dimension has rank
exactly that dimension. -/
theorem returnedFeedbackHankelPanel_rank
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (p q : ℕ)
    (hp : Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ p)
    (hq : Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ q) :
    (returnedFeedbackHankelPanel B C D p q).rank =
      Module.finrank ℂ (ReturnedFeedbackSpace B C D) := by
  rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_mulVecLin,
    returnedFeedbackHankelPanel_mulVecLin]
  exact returnedFeedback_finiteHankelPanel_rank B C D p q hp hq

end NCG
