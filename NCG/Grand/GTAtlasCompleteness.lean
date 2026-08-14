/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Atlas-relative source completeness
  (`thm:GT-atlas-completeness`, Gran-Tensor manuscript)

* `gt_idempotent_rank_compl`: rank additivity
  `rank P + rank(1-P) = n` for an idempotent — the
  dimension bookkeeping behind the boxed SA.3.

* `gt_atlas_completeness`: for the completeness kernel
  `ℂ_{U|𝒦} = U*(1-P)U` of a writer atlas `U` against the
  reached-sector projection `P`,
  (i) the boxed SA.4 — `ℂ_{U|𝒦} = 0` exactly when
      `(1-P)U = 0` (the atlas reaches nothing outside
      `𝒦`);
  (ii) the boxed SA.3 — for a surjective (complete) atlas,
      `rank ℂ_{U|𝒦} + dim 𝒦 = dim ℋ_phys`;
  (iii) the boxed SA.5 value identity — an unreached
      direction certifies the kernel exactly:
      `Ux = v, Pv = 0 ⟹ x*ℂx = ‖v‖²` (with the atlas
      floor `m_U‖x‖² ≤ ‖v‖²` this gives the boxed
      `‖ℂ_{U|𝒦}‖ ≥ m_U`).

The source-minimal missing bank
`J^miss = (1-P)U ℂ^{†/2}` (SA.6) is the manuscript's
half-power construction on top of (i)–(iii).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Rank additivity for an idempotent:
`rank P + rank(1-P) = n`. -/
theorem gt_idempotent_rank_compl {n : Type} [Fintype n]
    [DecidableEq n] (P : Matrix n n ℂ)
    (hPP : P * P = P) :
    P.rank + (1 - P).rank = Fintype.card n := by
  have h1 : LinearMap.range P.mulVecLin
      ⊔ LinearMap.range (1 - P).mulVecLin = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = P *ᵥ v + (1 - P) *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [hv]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have hP1P : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have h2 : LinearMap.range P.mulVecLin
      ⊓ LinearMap.range (1 - P).mulVecLin = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hPv : P *ᵥ v = v := by
      have hx' : P *ᵥ x = v := hx
      rw [← hx', Matrix.mulVec_mulVec, hPP]
    have hP0 : P *ᵥ v = 0 := by
      have hy' : (1 - P) *ᵥ y = v := hy
      rw [← hy', Matrix.mulVec_mulVec, hP1P,
        Matrix.zero_mulVec]
    rw [← hPv, hP0]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range P.mulVecLin)
    (LinearMap.range (1 - P).mulVecLin)
  rw [h1, h2, finrank_bot, finrank_top] at hsum
  have hcard : Module.finrank ℂ (n → ℂ)
      = Fintype.card n := Module.finrank_pi ℂ
  unfold Matrix.rank
  omega

/-- `thm:GT-atlas-completeness` (SA.3–SA.5). -/
theorem gt_atlas_completeness {n e : Type} [Fintype n]
    [Fintype e] [DecidableEq n]
    (P : Matrix n n ℂ) (hPP : P * P = P) (hPH : Pᴴ = P)
    (U : Matrix n e ℂ) :
    -- (i) the boxed SA.4 vanishing criterion
    (Uᴴ * (1 - P) * U = 0 ↔ (1 - P) * U = 0)
    -- (ii) the boxed SA.3 rank formula for a complete
    -- atlas
    ∧ (Function.Surjective U.mulVecLin →
        (Uᴴ * (1 - P) * U).rank + P.rank
          = Fintype.card n)
    -- (iii) the boxed SA.5 value identity
    ∧ (∀ (x : e → ℂ) (v : n → ℂ),
        U *ᵥ x = v → P *ᵥ v = 0 →
        star x ⬝ᵥ ((Uᴴ * (1 - P) * U) *ᵥ x)
          = star v ⬝ᵥ v) := by
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  have h1PH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPH]
  have hidem : (1 - P) * ((1 - P) * U) = (1 - P) * U := by
    rw [← Matrix.mul_assoc, h1P]
  have hfact : Uᴴ * (1 - P) * U
      = ((1 - P) * U)ᴴ * ((1 - P) * U) := by
    rw [Matrix.conjTranspose_mul, h1PH,
      Matrix.mul_assoc Uᴴ (1 - P) U, ← hidem,
      ← Matrix.mul_assoc, hidem]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfact]
    exact Matrix.conjTranspose_mul_self_eq_zero
  · intro hsurj
    have hrankC : (Uᴴ * (1 - P) * U).rank
        = ((1 - P) * U).rank := by
      rw [hfact, Matrix.rank_conjTranspose_mul_self]
    have hrangeeq : LinearMap.range
        ((1 - P) * U).mulVecLin
        = LinearMap.range (1 - P).mulVecLin := by
      rw [Matrix.mulVecLin_mul, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr hsurj,
        Submodule.map_top]
    have hrankPU : ((1 - P) * U).rank
        = (1 - P).rank := by
      unfold Matrix.rank
      rw [hrangeeq]
    have hadd := gt_idempotent_rank_compl P hPP
    rw [hrankC, hrankPU]
    omega
  · intro x v hx hv
    have hXx : ((1 - P) * U) *ᵥ x = v := by
      rw [← Matrix.mulVec_mulVec, hx,
        Matrix.sub_mulVec, Matrix.one_mulVec, hv,
        sub_zero]
    calc star x ⬝ᵥ ((Uᴴ * (1 - P) * U) *ᵥ x)
        = star x ⬝ᵥ ((((1 - P) * U)ᴴ
            * ((1 - P) * U)) *ᵥ x) := by rw [hfact]
      _ = star x ⬝ᵥ (((1 - P) * U)ᴴ
            *ᵥ (((1 - P) * U) *ᵥ x)) := by
          rw [Matrix.mulVec_mulVec]
      _ = (star x ᵥ* ((1 - P) * U)ᴴ)
            ⬝ᵥ (((1 - P) * U) *ᵥ x) := by
          rw [Matrix.dotProduct_mulVec]
      _ = star (((1 - P) * U) *ᵥ x)
            ⬝ᵥ (((1 - P) * U) *ᵥ x) := by
          rw [← Matrix.star_mulVec]
      _ = star v ⬝ᵥ v := by rw [hXx]

end NCG
