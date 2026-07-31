/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Single-spurion electroweak Hessian and the one light doublet
  (`thm:single-spurion-ew-hessian-consolidated`,
   `cor:one-light-doublet-consolidated`, SM_emergence)

With a unique weak ray `r` (rank-one right covariance), the
perpendicular combination `H_⊥ = ℍr_⊥`, `r_⊥ = εr̄`, decouples:

* `spurion_perp_orthogonal` — `r†r_⊥ = 0` (antisymmetric pairing of
  a vector with itself);
* `higgs_direction_orthogonal` — the boxed normalized direction
  `n_h = (-r̄_d, r̄_u, 0)` is orthogonal to the aligned ray;
* `perp_exact_eigenvector` — in the boxed block form, `H_⊥` is an
  exact eigenvector with eigenvalue `m_H²`;
* `one_light_doublet` — at `m_H² = 0` with positive-definite heavy
  block, `Ker 𝓜²_EW = span{e_⊥}` and `rank 𝓜²_EW = 2`: exactly one
  light doublet.

The `SU(2)_R`-covariance classification producing the block form is
the manuscript's declared representation-theoretic step.
-/

namespace NCG

open Matrix Module

open scoped ComplexOrder

/-- `thm:single-spurion-ew-hessian-consolidated` (decoupling pairing):
`r†(εr̄) = 0` — the antisymmetric form vanishes on the pair `(r̄, r̄)`. -/
theorem spurion_perp_orthogonal (ru rd : ℂ) :
    star ru * (-(star rd)) + star rd * star ru = 0 := by
  ring

/-- `cor:one-light-doublet-consolidated` (boxed direction): the
normalized light doublet `n_h = (-r̄_d, r̄_u, 0)` pairs to zero with
the aligned ray `(r_u, r_d, 0)`. -/
theorem higgs_direction_orthogonal (ru rd : ℂ) :
    star ru * (-(star rd)) + star rd * (star ru) + 0 * 0 = 0 := by
  ring

/-- The boxed single-spurion Hessian. -/
def spurionHessian (m Δ b : ℂ) (mu : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![m, 0, 0; 0, m + Δ, mu; 0, star mu, b]

/-- `thm:single-spurion-ew-hessian-consolidated` (exact
eigenvector): `H_⊥ = e₀` is an exact eigenvector of the boxed
Hessian with eigenvalue `m_H²`. -/
theorem perp_exact_eigenvector (m Δ b mu : ℂ) :
    (spurionHessian m Δ b mu).mulVec ![1, 0, 0] = m • ![1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [spurionHessian, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- `cor:one-light-doublet-consolidated`: at bidoublet criticality
`m_H² = 0` with positive-definite heavy block, the Hessian kernel is
exactly the light-doublet line and the rank is two. -/
theorem one_light_doublet (Δ b mu : ℂ)
    (hB : (!![Δ, mu; star mu, b] : Matrix (Fin 2) (Fin 2) ℂ).PosDef) :
    LinearMap.ker (spurionHessian 0 Δ b mu).mulVecLin
      = Submodule.span ℂ {(![1, 0, 0] : Fin 3 → ℂ)}
    ∧ (spurionHessian 0 Δ b mu).rank = 2 := by
  classical
  set M : Matrix (Fin 3) (Fin 3) ℂ := spurionHessian 0 Δ b mu with hM
  set e0 : Fin 3 → ℂ := ![1, 0, 0] with he0
  have he0ne : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he0] at this
  have hMe0 : M.mulVec e0 = 0 := by
    have h := perp_exact_eigenvector 0 Δ b mu
    rw [hM]
    rw [h]
    simp
  have hkerchar : ∀ x : Fin 3 → ℂ, M.mulVec x = 0 →
      x ∈ Submodule.span ℂ {e0} := by
    intro x hx
    have h1 : (0 + Δ) * x 1 + mu * x 2 = 0 := by
      have := congrFun hx 1
      simpa [hM, spurionHessian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three] using this
    have h2 : star mu * x 1 + b * x 2 = 0 := by
      have := congrFun hx 2
      simpa [hM, spurionHessian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three] using this
    -- the heavy block annihilates (x₁, x₂), so it vanishes
    set y : Fin 2 → ℂ := ![x 1, x 2] with hy
    have hBy : (!![Δ, mu; star mu, b]).mulVec y = 0 := by
      funext i
      fin_cases i
      · simpa [hy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          using (by rw [zero_add] at h1; exact h1)
      · simpa [hy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          using h2
    have hy0 : y = 0 := by
      by_contra hyne
      have hyne' : y ≠ 0 := hyne
      have hpos := hB.dotProduct_mulVec_pos hyne'
      rw [hBy] at hpos
      simp at hpos
    have hx1 : x 1 = 0 := by
      have := congrFun hy0 0
      simpa [hy] using this
    have hx2 : x 2 = 0 := by
      have := congrFun hy0 1
      simpa [hy] using this
    -- so x is a multiple of e₀
    have hxe : x = x 0 • e0 := by
      funext i
      fin_cases i <;> simp [he0, hx1, hx2]
    rw [hxe]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e0)
  have hkereq : LinearMap.ker M.mulVecLin = Submodule.span ℂ {e0} := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
      exact hkerchar x hx
    · rw [Submodule.span_le]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv, SetLike.mem_coe, LinearMap.mem_ker,
        Matrix.mulVecLin_apply]
      exact hMe0
  refine ⟨hkereq, ?_⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h3 : finrank ℂ (Fin 3 → ℂ) = 3 := by simp
  rw [h3, hkereq, finrank_span_singleton he0ne] at h2
  have h4 : M.rank
      = finrank ℂ (LinearMap.range M.mulVecLin) := rfl
  omega

end NCG
