/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EdgeCommutantDimensionExact

/-!
# The degree-one edge commutant has dimension exactly seven

Fourth machinery layer for `thm:SM-active-residual-algebra`: the seven relation
matrices are conjugation-invariant members of the commutant (`relMatrix_mem`, via
the `decide`-certified relabeling invariance `rel_act`), evaluation at the seven
representatives sends them to the standard basis (`rel_rep`), so together with the
upper bound of `EdgeCommutantDimensionExact` the degree-one commutant has dimension
**exactly seven** (`commutant_finrank_eq_seven`) — the numerical content of
`C₁ ≅ ℂ ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`.
-/

open Finset Matrix NCG.ActiveResidual NCG.EdgeCommutant

namespace NCG
namespace EdgeCommutantBasis

/-- The seven relation matrices. -/
def relMatrix (t : Fin 7) : Matrix E E ℂ :=
  fun e f => if rel e f = t then 1 else 0

set_option maxHeartbeats 4000000 in
/-- Relabeling invariance of the relation type. -/
theorem rel_act : ∀ (σ : Equiv.Perm V) (e f : E),
    rel (act σ e) (act σ f) = rel e f := by
  decide

set_option maxHeartbeats 400000 in
/-- The representatives realize their own types. -/
theorem rel_rep : ∀ t : Fin 7, rel (rep t).1 (rep t).2 = t := by
  decide

/-- The relation matrices lie in the commutant. -/
theorem relMatrix_mem (t : Fin 7) : relMatrix t ∈ commutantSubmodule := by
  intro σ
  ext e f
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ m, relMatrix t e m * Pm σ m f = relMatrix t e (act σ f) := by
    have hm : ∀ m : E, relMatrix t e m * Pm σ m f
        = if m = act σ f then relMatrix t e m else 0 := by
      intro m
      rw [Pm_apply]
      by_cases hmf : m = act σ f
      · rw [if_pos hmf, if_pos hmf, mul_one]
      · rw [if_neg hmf, if_neg hmf, mul_zero]
    rw [Finset.sum_congr rfl fun m _ => hm m,
      Finset.sum_ite_eq' Finset.univ (act σ f) fun m => relMatrix t e m,
      if_pos (Finset.mem_univ _)]
  have hR : ∑ m, Pm σ e m * relMatrix t m f = relMatrix t (act σ⁻¹ e) f := by
    have hm : ∀ m : E, Pm σ e m * relMatrix t m f
        = if e = act σ m then relMatrix t m f else 0 := by
      intro m
      rw [Pm_apply]
      by_cases hme : e = act σ m
      · rw [if_pos hme, if_pos hme, one_mul]
      · rw [if_neg hme, if_neg hme, zero_mul]
    have hiff : ∀ m : E, (e = act σ m) ↔ (m = act σ⁻¹ e) := by
      intro m
      constructor
      · intro h1
        rw [h1, ← act_mul, inv_mul_cancel, act_one]
      · intro h1
        rw [h1, ← act_mul, mul_inv_cancel, act_one]
    rw [Finset.sum_congr rfl fun m _ => by
      rw [hm m, if_congr (hiff m) rfl rfl]]
    rw [Finset.sum_ite_eq' Finset.univ (act σ⁻¹ e) fun m => relMatrix t m f,
      if_pos (Finset.mem_univ _)]
  rw [hL, hR]
  -- rel e (act σ f) = rel (act σ⁻¹ e) f, from relabeling invariance
  have hinv : rel e (act σ f) = rel (act σ⁻¹ e) f := by
    have h := rel_act σ (act σ⁻¹ e) f
    rw [← act_mul, mul_inv_cancel, act_one] at h
    exact h
  rw [relMatrix, relMatrix]
  rw [if_congr (by rw [hinv]) rfl rfl]

/-- Evaluation sends the relation matrices to the standard basis vectors. -/
theorem evalRep_relMatrix (t s : Fin 7) :
    evalRep ⟨relMatrix t, relMatrix_mem t⟩ s = if s = t then 1 else 0 := by
  have h : evalRep ⟨relMatrix t, relMatrix_mem t⟩ s
      = relMatrix t (rep s).1 (rep s).2 := rfl
  rw [h, relMatrix, rel_rep s]

/-- **The degree-one commutant has dimension exactly seven** — the numerical
content of `C₁ ≅ ℂ ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`. -/
theorem commutant_finrank_eq_seven :
    Module.finrank ℂ commutantSubmodule = 7 := by
  refine le_antisymm commutant_finrank_le_seven ?_
  -- the family of relation matrices is linearly independent via evaluation
  have hli : LinearIndependent ℂ
      (fun t : Fin 7 => (⟨relMatrix t, relMatrix_mem t⟩ : commutantSubmodule)) := by
    have hev : LinearIndependent ℂ
        (fun t : Fin 7 => evalRep ⟨relMatrix t, relMatrix_mem t⟩) := by
      have heq : (fun t : Fin 7 => evalRep ⟨relMatrix t, relMatrix_mem t⟩)
          = fun t : Fin 7 => (Pi.single t 1 : Fin 7 → ℂ) := by
        funext t
        funext s
        rw [evalRep_relMatrix t s, Pi.single_apply]
      rw [heq]
      convert (Pi.basisFun ℂ (Fin 7)).linearIndependent using 1
      funext t
      simp [Pi.basisFun_apply]
    exact hev.of_comp evalRep
  have h := hli.fintype_card_le_finrank
  simpa using h

end EdgeCommutantBasis
end NCG
