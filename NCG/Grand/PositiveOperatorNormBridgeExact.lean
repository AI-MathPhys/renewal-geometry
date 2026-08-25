/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Norm bounds for positive operators via the Loewner order

For a positive operator `T` on a finite-dimensional inner product space, the strict norm bound
`‖T‖ < 1` is equivalent to the strict Loewner inequality `I - T ≻ 0`
(`opNorm_lt_one_iff_of_isPositive`).  The matrix form `norm_lt_one_iff_posDef_one_sub` uses the
`ℓ²` operator norm on `Matrix n n ℂ`.  This is the bridge that converts Schur-complement
(Loewner) criteria into the boxed operator-norm criteria of the manuscript.
-/

open scoped ComplexOrder InnerProductSpace
open Matrix RCLike

namespace NCG
namespace PositiveNormBridge

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- For a positive operator, `‖T‖ < 1` iff `re ⟪T x, x⟫ < ‖x‖²` for every `x ≠ 0`. -/
theorem opNorm_lt_one_iff_of_isPositive {T : E →L[ℂ] E} (hT : T.IsPositive) :
    ‖T‖ < 1 ↔ ∀ x : E, x ≠ 0 → re ⟪T x, x⟫_ℂ < ‖x‖ ^ 2 := by
  constructor
  · intro h x hx
    have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
    calc re ⟪T x, x⟫_ℂ ≤ ‖T x‖ * ‖x‖ := re_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖x‖ * ‖x‖ := by gcongr; exact T.le_opNorm x
      _ < 1 * ‖x‖ * ‖x‖ := by gcongr
      _ = ‖x‖ ^ 2 := by ring
  · intro h
    by_cases hE : Nontrivial E
    · -- the supremum of the Rayleigh quotient is an eigenvalue
      set μ : ℝ := ⨆ x : { x : E // x ≠ 0 }, re ⟪T x, x⟫_ℂ / ‖(x : E)‖ ^ 2 with hμ
      have hsym : (T : E →ₗ[ℂ] E).IsSymmetric := hT.isSymmetric
      have heig := hsym.hasEigenvalue_iSup_of_finiteDimensional
      obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
      have hv0 : v ≠ 0 := hv.2
      have hTv : T v = (μ : ℂ) • v := hv.apply_eq_smul
      have hvpos : 0 < ‖v‖ ^ 2 := by positivity
      have hre : re ⟪T v, v⟫_ℂ = μ * ‖v‖ ^ 2 := by
        rw [hTv, inner_smul_left, Complex.conj_ofReal, ← inner_self_eq_norm_sq (𝕜 := ℂ) v]
        simp
      have hμlt : μ < 1 := by
        have := h v hv0
        rw [hre] at this
        nlinarith
      have hμnn : 0 ≤ μ := by
        have := hT.re_inner_nonneg_left v
        rw [hre] at this
        nlinarith
      -- bound every Rayleigh quotient by `μ`
      have hbdd : BddAbove
          (Set.range fun x : { x : E // x ≠ 0 } => re ⟪T x, x⟫_ℂ / ‖(x : E)‖ ^ 2) := by
        refine ⟨‖T‖, ?_⟩
        rintro _ ⟨x, rfl⟩
        exact (le_abs_self _).trans (T.rayleighQuotient_le_norm x)
      rw [T.norm_eq_iSup_rayleighQuotient hsym]
      refine lt_of_le_of_lt (ciSup_le fun x => ?_) hμlt
      by_cases hx : x = 0
      · simp [hx, hμnn]
      · have hnn : 0 ≤ T.rayleighQuotient x := by
          unfold ContinuousLinearMap.rayleighQuotient
          exact div_nonneg (hT.re_inner_nonneg_left x) (by positivity)
        rw [abs_of_nonneg hnn]
        exact le_ciSup hbdd ⟨x, hx⟩
    · -- trivial space: `T = 0`
      rw [not_nontrivial_iff_subsingleton] at hE
      have : T = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]
      exact one_pos

end Operator

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator

theorem toEuclideanCLM_isPositive {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M).IsPositive := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hM

/-- The Rayleigh quadratic form of `toEuclideanCLM M` is the conjugate of `star x ⬝ᵥ M *ᵥ x`. -/
theorem re_inner_toEuclideanCLM (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    re ⟪Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M x, x⟫_ℂ
      = (star (WithLp.ofLp x) ⬝ᵥ M *ᵥ WithLp.ofLp x).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  have : WithLp.ofLp x ⬝ᵥ star (M *ᵥ WithLp.ofLp x)
      = star (star (WithLp.ofLp x) ⬝ᵥ M *ᵥ WithLp.ofLp x) := by
    rw [star_dotProduct, star_star, dotProduct_comm]
  rw [this]
  simp

omit [DecidableEq n] in
theorem norm_sq_eq_re_dotProduct (x : EuclideanSpace ℂ n) :
    ‖x‖ ^ 2 = (star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) x, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp

/-- **Norm bridge**: for a positive semidefinite matrix, `‖M‖ < 1 ⟺ I - M ≻ 0`
(`ℓ²` operator norm). -/
theorem norm_lt_one_iff_posDef_one_sub {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    ‖M‖ < 1 ↔ (1 - M).PosDef := by
  rw [Matrix.cstar_norm_def, opNorm_lt_one_iff_of_isPositive (toEuclideanCLM_isPositive hM)]
  have hH : (1 - M).IsHermitian := Matrix.isHermitian_one.sub hM.1
  constructor
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have hx' : (WithLp.toLp 2 x : EuclideanSpace ℂ n) ≠ 0 := by
      intro h0
      apply hx
      simpa using congrArg WithLp.ofLp h0
    have := h _ hx'
    rw [re_inner_toEuclideanCLM, norm_sq_eq_re_dotProduct] at this
    have him : (star x ⬝ᵥ M *ᵥ x).im = 0 := by
      have := hM.dotProduct_mulVec_nonneg x
      exact (Complex.nonneg_iff.mp this).2.symm
    have him' : (star x ⬝ᵥ x).im = 0 := by
      have := Matrix.PosSemidef.one.dotProduct_mulVec_nonneg x
      rw [one_mulVec] at this
      exact (Complex.nonneg_iff.mp this).2.symm
    rw [sub_mulVec, one_mulVec, dotProduct_sub, Complex.lt_def]
    simp only [Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im, him, him']
    exact ⟨by linarith, by simp⟩
  · intro h x hx
    have hx' : WithLp.ofLp x ≠ 0 := by
      intro h0
      apply hx
      ext i
      exact congrFun h0 i
    have := h.dotProduct_mulVec_pos hx'
    rw [sub_mulVec, one_mulVec, dotProduct_sub, Complex.lt_def] at this
    rw [re_inner_toEuclideanCLM, norm_sq_eq_re_dotProduct]
    have h1 := this.1
    simp only [Complex.sub_re, Complex.zero_re] at h1
    linarith

end Matrix

end PositiveNormBridge
end NCG
