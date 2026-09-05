/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Complete-multiplet invisibility and mass-hierarchy nonselection
  (`prop:complete-multiplet`, `prop:mass-hierarchy-not-mixing`,
  SM manuscript)

* `complete_multiplet_invisibility` — at one loop,
  `α_i⁻¹(μ) = α_i⁻¹(M) + b_i/(2π)·log(M/μ)`; a threshold shifting
  all three coefficients by the same amount leaves every pairwise
  inverse-coupling difference unchanged, so it cannot repair a
  weak-mixing mismatch at one loop (prose).

* `mass_hierarchy_not_mixing` — for any prescribed singular values
  and any unitary `V`, there are Yukawa matrices with exactly those
  singular values whose relative left singular frame is exactly
  `V`: a hierarchical charged-lepton spectrum alone imposes no
  hierarchy on the PMNS matrix (prose).
-/

open Matrix

namespace NCG

/-- One-loop running of the inverse coupling. -/
noncomputable def oneLoopInv (αM b L : ℝ) : ℝ :=
  αM + b / (2 * Real.pi) * L

/-- `prop:complete-multiplet`: a common shift of the one-loop
coefficients cancels from every pairwise inverse-coupling
difference. -/
theorem complete_multiplet_invisibility (αMi αMj bi bj δ L : ℝ) :
    oneLoopInv αMi (bi + δ) L - oneLoopInv αMj (bj + δ) L
      = oneLoopInv αMi bi L - oneLoopInv αMj bj L := by
  rw [oneLoopInv, oneLoopInv, oneLoopInv, oneLoopInv]
  ring

/-- `prop:mass-hierarchy-not-mixing`: for any prescribed singular
values `s_e, s_ν` and any unitary `V`, there are Yukawa matrices
with singular value decompositions carrying exactly those values
whose relative left frame `U_e*U_ν` is exactly `V`. -/
theorem mass_hierarchy_not_mixing (se sν : Fin 3 → ℝ)
    (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : Vᴴ * V = 1) :
    ∃ (Ye Yν Ue Uν We Wν : Matrix (Fin 3) (Fin 3) ℂ),
      -- the four frames are unitary
      (Ueᴴ * Ue = 1) ∧ (Uνᴴ * Uν = 1) ∧ (Weᴴ * We = 1)
        ∧ (Wνᴴ * Wν = 1) ∧
      -- singular value decompositions with the prescribed values
      (Ye = Ue * Matrix.diagonal (fun i => (se i : ℂ)) * Weᴴ) ∧
      (Yν = Uν * Matrix.diagonal (fun i => (sν i : ℂ)) * Wνᴴ) ∧
      -- the relative left frame is exactly `V`
      Ueᴴ * Uν = V := by
    refine ⟨Matrix.diagonal (fun i => (se i : ℂ)),
      V * Matrix.diagonal (fun i => (sν i : ℂ)), 1, V, 1, 1,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · exact hV
    · simp
    · simp
    · simp
    · simp
    · simp

end NCG
