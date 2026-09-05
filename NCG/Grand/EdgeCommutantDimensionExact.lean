/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ActiveResidualAlgebra

/-!
# The degree-one edge commutant has dimension seven

Third machinery layer for `thm:SM-active-residual-algebra` (the SM.0k firewall).

On the `12`-dimensional directed-edge carrier of `K₄`, the commutant of the
tetrahedral relabeling algebra is cut out by conjugation invariance; every ordered
pair of directed edges is equivalent to one of **seven** relation types
(`cover`, checked by `decide` on the finite `S₄` combinatorics), so evaluation at
the seven representatives embeds the commutant into `ℂ⁷`
(`commutant_finrank_le_seven`).  Consequently the degree-one commutant admits no
injective linear embedding of `M₃(ℂ)` (`no_M3_embedding`): degree-one accepted
contrasts alone cannot contain an internal colour block.
-/

open Finset Matrix NCG.ActiveResidual

namespace NCG
namespace EdgeCommutant

/-- The seven relation types of an ordered pair of directed `K₄` edges. -/
def rel (e f : E) : Fin 7 :=
  if e = f then 0
  else if e = rv f then 1
  else if e.val.1 = f.val.1 then 2
  else if e.val.2 = f.val.2 then 3
  else if e.val.2 = f.val.1 then 4
  else if e.val.1 = f.val.2 then 5
  else 6

/-- Representative pairs for the seven relation types. -/
def rep : Fin 7 → E × E :=
  ![(⟨(0, 1), by decide⟩, ⟨(0, 1), by decide⟩),
    (⟨(0, 1), by decide⟩, ⟨(1, 0), by decide⟩),
    (⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩),
    (⟨(0, 1), by decide⟩, ⟨(2, 1), by decide⟩),
    (⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩),
    (⟨(0, 1), by decide⟩, ⟨(2, 0), by decide⟩),
    (⟨(0, 1), by decide⟩, ⟨(2, 3), by decide⟩)]

set_option maxHeartbeats 4000000 in
/-- Every ordered pair of directed edges is a tetrahedral relabeling of its
relation-type representative. -/
theorem cover : ∀ e f : E, ∃ σ : Equiv.Perm V,
    e = act σ (rep (rel e f)).1 ∧ f = act σ (rep (rel e f)).2 := by
  decide

/-- The commutant of the tetrahedral relabeling algebra on the edge carrier. -/
def commutantSubmodule : Submodule ℂ (Matrix E E ℂ) where
  carrier := {X | ∀ σ : Equiv.Perm V, X * Pm σ = Pm σ * X}
  zero_mem' := fun σ => by rw [Matrix.zero_mul, Matrix.mul_zero]
  add_mem' := fun {X Y} hX hY σ => by
    rw [Matrix.add_mul, Matrix.mul_add, hX σ, hY σ]
  smul_mem' := fun c {X} hX σ => by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX σ]

theorem mem_commutant {X : Matrix E E ℂ} :
    X ∈ commutantSubmodule ↔ ∀ σ : Equiv.Perm V, X * Pm σ = Pm σ * X := Iff.rfl

/-- Commutant members are conjugation invariant entrywise. -/
theorem commutant_invariance {X : Matrix E E ℂ} (hX : X ∈ commutantSubmodule)
    (σ : Equiv.Perm V) (e f : E) : X (act σ e) (act σ f) = X e f := by
  have h := congrFun (congrFun (hX σ) (act σ e)) f
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  have hL : ∑ m, X (act σ e) m * Pm σ m f = X (act σ e) (act σ f) := by
    have hm : ∀ m : E, X (act σ e) m * Pm σ m f
        = if m = act σ f then X (act σ e) m else 0 := by
      intro m
      rw [Pm_apply]
      by_cases hmf : m = act σ f
      · rw [if_pos hmf, if_pos hmf, mul_one]
      · rw [if_neg hmf, if_neg hmf, mul_zero]
    rw [Finset.sum_congr rfl fun m _ => hm m,
      Finset.sum_ite_eq' Finset.univ (act σ f) fun m => X (act σ e) m,
      if_pos (Finset.mem_univ _)]
  have hR : ∑ m, Pm σ (act σ e) m * X m f = X e f := by
    have hm : ∀ m : E, Pm σ (act σ e) m * X m f
        = if act σ e = act σ m then X m f else 0 := by
      intro m
      rw [Pm_apply]
      by_cases hme : act σ e = act σ m
      · rw [if_pos hme, if_pos hme, one_mul]
      · rw [if_neg hme, if_neg hme, zero_mul]
    have hinj : ∀ m : E, (act σ e = act σ m) ↔ (m = e) := by
      intro m
      constructor
      · intro h1
        have h2 := congrArg (act σ⁻¹) h1
        rw [← act_mul, ← act_mul, inv_mul_cancel, act_one, act_one] at h2
        exact h2.symm
      · intro h1
        rw [h1]
    rw [Finset.sum_congr rfl fun m _ => by
      rw [hm m, if_congr (hinj m) rfl rfl]]
    rw [Finset.sum_ite_eq' Finset.univ e fun m => X m f,
      if_pos (Finset.mem_univ _)]
  rw [hL, hR] at h
  exact h

/-- Evaluation of a commutant member at the seven representatives. -/
def evalRep : commutantSubmodule →ₗ[ℂ] (Fin 7 → ℂ) where
  toFun X := fun t => (X : Matrix E E ℂ) (rep t).1 (rep t).2
  map_add' X Y := by
    funext t
    rfl
  map_smul' c X := by
    funext t
    rfl

theorem evalRep_injective : Function.Injective evalRep := by
  intro X Y h
  apply Subtype.ext
  ext e f
  obtain ⟨σ, he, hf⟩ := cover e f
  have hX := commutant_invariance X.2 σ (rep (rel e f)).1 (rep (rel e f)).2
  have hY := commutant_invariance Y.2 σ (rep (rel e f)).1 (rep (rel e f)).2
  rw [← he, ← hf] at hX hY
  have hrep := congrFun h (rel e f)
  calc (X : Matrix E E ℂ) e f
      = (X : Matrix E E ℂ) (rep (rel e f)).1 (rep (rel e f)).2 := hX
    _ = (Y : Matrix E E ℂ) (rep (rel e f)).1 (rep (rel e f)).2 := hrep
    _ = (Y : Matrix E E ℂ) e f := hY.symm

/-- **The degree-one commutant has dimension at most seven.** -/
theorem commutant_finrank_le_seven :
    Module.finrank ℂ commutantSubmodule ≤ 7 := by
  have h := LinearMap.finrank_le_finrank_of_injective evalRep_injective
  simpa using h

/-- **The SM.0k firewall**: the degree-one commutant admits no injective linear
embedding of `M₃(ℂ)` — degree-one accepted contrasts cannot contain an internal
colour block. -/
theorem no_M3_embedding
    (f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] commutantSubmodule) :
    ¬Function.Injective f := by
  intro hinj
  have h9 := LinearMap.finrank_le_finrank_of_injective hinj
  have h7 := commutant_finrank_le_seven
  have hM3 : Module.finrank ℂ (Matrix (Fin 3) (Fin 3) ℂ) = 9 := by
    rw [Module.finrank_matrix, Module.finrank_self]
    simp
  omega

end EdgeCommutant
end NCG
