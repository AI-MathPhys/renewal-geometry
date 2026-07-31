/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Electroweak Hessian rank theorems
  (`thm:untyped-ew-hessian-nogo`, `thm:typed-rank-two-higgs`,
   SM_emergence)

The scalar carrier is `𝒱_EW ≅ ℝ³` (spanned by `H_u, H̃_d, χ̃`):

* `untyped_hessian_no_go` — a copy-blind (single-row) predictive
  penalty has Gram matrix of rank at most one, hence kernel of
  dimension at least two: it cannot select one light doublet;
* `cross_row_orthogonal` — the cross product annihilates both
  continuation rows;
* `typed_rank_two_higgs` — with the closed/open typed rows
  nonproportional (`r_cl ∧ r_op ≠ 0`) and any positive weight `W`,
  the typed Gram Hessian `G = CᵀWC` has kernel exactly the line
  spanned by the boxed cross product `n_h = r_cl × r_op`, and
  `rank G = 2`.

The inheritance of the closed/open projectors by the bosonic second
variation (`op:bosonic-mark-inheritance`) is the manuscript's
declared open functorial step; the rank statements themselves are
unconditional.
-/

namespace NCG

open Matrix Module

/-- `thm:untyped-ew-hessian-nogo`: a single defect row on the
three-dimensional scalar carrier has Gram rank at most one and
kernel dimension at least two. -/
theorem untyped_hessian_no_go (r : Fin 3 → ℝ) :
    (Matrix.vecMulVec r r).rank ≤ 1
      ∧ 2 ≤ finrank ℝ
          (LinearMap.ker (Matrix.vecMulVec r r).mulVecLin) := by
  have h1 := Matrix.rank_vecMulVec_le (R := ℝ) r r
  refine ⟨h1, ?_⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker
    (Matrix.vecMulVec r r).mulVecLin
  have h3 : finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  rw [h3] at h2
  have h4 : (Matrix.vecMulVec r r).rank
      = finrank ℝ (LinearMap.range (Matrix.vecMulVec r r).mulVecLin) :=
    rfl
  omega

/-- The two-row continuation matrix. -/
def ewRows (rcl rop : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of ![rcl, rop]

/-- The boxed Higgs direction: the cross product of the typed
rows. -/
def higgsDirection (rcl rop : Fin 3 → ℝ) : Fin 3 → ℝ :=
  crossProduct rcl rop

/-- `thm:typed-rank-two-higgs` (orthogonality): the cross product
annihilates both continuation rows. -/
theorem cross_row_orthogonal (rcl rop : Fin 3 → ℝ) :
    rcl ⬝ᵥ higgsDirection rcl rop = 0
      ∧ rop ⬝ᵥ higgsDirection rcl rop = 0 :=
  ⟨dot_self_cross rcl rop, dot_cross_self rcl rop⟩

/-- `thm:typed-rank-two-higgs` (kernel and rank): with
nonproportional typed rows and any positive-definite weight, the
typed Gram Hessian `G = CᵀWC` has kernel exactly the Higgs line
`span{r_cl × r_op}` and rank two. -/
theorem typed_rank_two_higgs (rcl rop : Fin 3 → ℝ)
    (hn : higgsDirection rcl rop ≠ 0)
    (W : Matrix (Fin 2) (Fin 2) ℝ) (hW : W.PosDef) :
    LinearMap.ker ((ewRows rcl rop)ᵀ * W
        * ewRows rcl rop).mulVecLin
      = Submodule.span ℝ {higgsDirection rcl rop}
    ∧ ((ewRows rcl rop)ᵀ * W * ewRows rcl rop).rank = 2 := by
  classical
  set C : Matrix (Fin 2) (Fin 3) ℝ := ewRows rcl rop with hC
  set n : Fin 3 → ℝ := higgsDirection rcl rop with hndef
  -- the quadratic form factors through `C`
  have hquad : ∀ x : Fin 3 → ℝ,
      x ⬝ᵥ (Cᵀ * W * C).mulVec x
        = (C.mulVec x) ⬝ᵥ W.mulVec (C.mulVec x) := by
    intro x
    rw [show Cᵀ * W * C = Cᵀ * (W * C) from by
      rw [Matrix.mul_assoc]]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
  -- kernel of the Gram form = kernel of C
  have hker : ∀ x : Fin 3 → ℝ,
      (Cᵀ * W * C).mulVec x = 0 ↔ C.mulVec x = 0 := by
    intro x
    constructor
    · intro h
      by_contra hCx
      have hCx' : C.mulVec x ≠ 0 := hCx
      have hpos := hW.dotProduct_mulVec_pos hCx'
      have hzero : (C.mulVec x) ⬝ᵥ W.mulVec (C.mulVec x) = 0 := by
        rw [← hquad x, h]
        simp
      have hstar : star (C.mulVec x) = C.mulVec x := by
        funext i
        simp
      rw [hstar] at hpos
      rw [hzero] at hpos
      exact lt_irrefl 0 hpos
    · intro h
      rw [show Cᵀ * W * C = Cᵀ * (W * C) from by
        rw [Matrix.mul_assoc], ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, h]
      simp
  -- kernel of C = the Higgs line
  have hCn : C.mulVec n = 0 := by
    funext i
    fin_cases i
    · change rcl ⬝ᵥ n = 0
      exact (cross_row_orthogonal rcl rop).1
    · change rop ⬝ᵥ n = 0
      exact (cross_row_orthogonal rcl rop).2
  have hkerC : ∀ x : Fin 3 → ℝ, C.mulVec x = 0 →
      x ∈ Submodule.span ℝ {n} := by
    intro x hx
    have h1 : rcl ⬝ᵥ x = 0 := congrFun hx 0
    have h2 : rop ⬝ᵥ x = 0 := congrFun hx 1
    -- (r_cl × r_op) × x = (r_cl·x)·r_op - (r_op·x)·r_cl = 0
    have hcross : crossProduct n x = 0 := by
      rw [hndef]
      change crossProduct (crossProduct rcl rop) x = 0
      rw [cross_cross_eq_smul_sub_smul]
      rw [h1, h2]
      simp
    -- collinearity from vanishing cross product
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    · have hdep : ¬ LinearIndependent ℝ ![n, x] := by
        rw [← crossProduct_ne_zero_iff_linearIndependent]
        simpa using hcross
      rw [LinearIndependent.pair_iff] at hdep
      push Not at hdep
      obtain ⟨s, t, hst, hne⟩ := hdep
      by_cases ht : t = 0
      · exfalso
        rw [ht, zero_smul, add_zero] at hst
        rcases smul_eq_zero.mp hst with hs | hn0
        · exact hne hs ht
        · exact hn hn0
      · have hts : t • x = (-s) • n := by
          linear_combination (norm := module) hst
        have hx' : x = (-s / t) • n := by
          have h := congrArg (fun v => t⁻¹ • v) hts
          simp only [smul_smul] at h
          rw [inv_mul_cancel₀ ht, one_smul] at h
          rw [h]
          congr 1
          field_simp
        rw [hx']
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self n)
  -- assemble the kernel identity
  have hkereq : LinearMap.ker (Cᵀ * W * C).mulVecLin
      = Submodule.span ℝ {n} := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
      exact hkerC x ((hker x).mp hx)
    · rw [Submodule.span_le]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv, SetLike.mem_coe, LinearMap.mem_ker,
        Matrix.mulVecLin_apply]
      exact (hker n).mpr hCn
  refine ⟨hkereq, ?_⟩
  -- rank–nullity
  have h2 := LinearMap.finrank_range_add_finrank_ker
    (Cᵀ * W * C).mulVecLin
  have h3 : finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  rw [h3, hkereq, finrank_span_singleton hn] at h2
  have h4 : (Cᵀ * W * C).rank
      = finrank ℝ (LinearMap.range (Cᵀ * W * C).mulVecLin) := rfl
  omega

end NCG
