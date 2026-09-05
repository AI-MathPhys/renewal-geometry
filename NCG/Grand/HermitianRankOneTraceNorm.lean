/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PrimitiveWeight
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hermitian trace norm of rank-one perturbations

This file supplies the finite-dimensional rank-one estimate used by robust
Choi-purity arguments.  For Euclidean vectors `x` and `y`,

`‖x x* - y y*‖₁ ≤ ‖x-y‖ (‖x‖ + ‖y‖)`.

The proof stays inside the repository's spectral Hermitian trace norm.  It
writes the difference as a difference of two positive rank-one matrices with
an optimally balanced scalar and applies `trNorm_le_of_sub`.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace HermitianRankOneTraceNorm

open Upstream.PrimitiveWeight

variable {n : ℕ}

/-- The rank-one positive matrix associated with a Euclidean vector. -/
def pureOuter (x : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec (fun i => x i) (fun i => star (x i))

theorem pureOuter_posSemidef (x : EuclideanSpace ℂ (Fin n)) :
    (pureOuter x).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star (fun i => x i)

theorem pureOuter_isHermitian (x : EuclideanSpace ℂ (Fin n)) :
    (pureOuter x).IsHermitian := (pureOuter_posSemidef x).1

/-- Scaling a vector scales its rank-one outer product by its squared
complex modulus. -/
theorem pureOuter_smul (c : ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    pureOuter (c • x) = (c * star c) • pureOuter x := by
  ext i j
  simp only [pureOuter, Matrix.vecMulVec_apply, WithLp.ofLp_smul,
    Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, star_mul]
  ring

/-- The trace of `x x*` is the squared Euclidean norm of `x`. -/
theorem pureOuter_trace (x : EuclideanSpace ℂ (Fin n)) :
    (pureOuter x).trace = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [pureOuter, Matrix.trace_vecMulVec]
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem pureOuter_smul_posSemidef (x : EuclideanSpace ℂ (Fin n))
    {c : ℝ} (hc : 0 ≤ c) :
    (((c : ℝ) : ℂ) • pureOuter x).PosSemidef := by
  exact Matrix.PosSemidef.smul (pureOuter_posSemidef x)
    (RCLike.ofReal_nonneg.mpr hc)

theorem pureOuter_smul_trace (x : EuclideanSpace ℂ (Fin n)) (c : ℝ) :
    ((((c : ℝ) : ℂ) • pureOuter x).trace).re = c * ‖x‖ ^ 2 := by
  rw [Matrix.trace_smul, pureOuter_trace]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem pureOuter_sub_isHermitian (x y : EuclideanSpace ℂ (Fin n)) :
    (pureOuter x - pureOuter y).IsHermitian :=
  (pureOuter_isHermitian x).sub (pureOuter_isHermitian y)

/-- On the positive cone, the Hermitian trace norm is the real trace. -/
theorem trNorm_eq_trace_of_posSemidef
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosSemidef) :
    trNorm X = X.trace.re := by
  rw [trNorm_def hX.1, hX.1.trace_eq_sum_eigenvalues]
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hX.eigenvalues_nonneg i)

/-- Triangle inequality for the repository's spectral Hermitian trace norm. -/
theorem trNorm_add_le {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    trNorm (X + Y) ≤ trNorm X + trNorm Y := by
  let hXY : (X + Y).IsHermitian := hX.add hY
  have hminus := one_sub_signOp_posSemidef hXY
  have hplus := one_add_signOp_posSemidef hXY
  have hXbound := re_trace_mul_le_trNorm hX hminus hplus
  have hYbound := re_trace_mul_le_trNorm hY hminus hplus
  rw [← re_trace_signOp_mul hXY, Matrix.mul_add, Matrix.trace_add, map_add]
  linarith

private theorem pureOuter_add_sub_identity
    (x y : EuclideanSpace ℂ (Fin n)) (s : ℝ) (hs : s ≠ 0) :
    let a := x - y
    let b := x + y
    let p := ((s : ℂ) • a) + (((s : ℂ)⁻¹) • b)
    let q := ((s : ℂ) • a) - (((s : ℂ)⁻¹) • b)
    ((1 / 4 : ℝ) : ℂ) • pureOuter p -
        ((1 / 4 : ℝ) : ℂ) • pureOuter q =
      pureOuter x - pureOuter y := by
  dsimp
  ext i j
  simp only [pureOuter, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, WithLp.ofLp_add, WithLp.ofLp_sub,
    WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [Complex.real_smul, star_add, star_sub, star_mul, star_inv₀,
    RCLike.star_def, Complex.conj_ofReal]
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp [hsc]
  norm_num
  ring

/-- Sharp rank-one perturbation bound in the Hermitian trace norm:
`‖x x* - y y*‖₁ ≤ ‖x-y‖ (‖x‖+‖y‖)`. -/
theorem trNorm_pureOuter_sub_le (x y : EuclideanSpace ℂ (Fin n)) :
    trNorm (pureOuter x - pureOuter y) ≤
      ‖x - y‖ * (‖x‖ + ‖y‖) := by
  by_cases ha : x - y = 0
  · have hxy : x = y := sub_eq_zero.mp ha
    subst y
    rw [sub_self]
    have hz : trNorm (0 : Matrix (Fin n) (Fin n) ℂ) = 0 :=
      (trNorm_eq_zero_iff Matrix.isHermitian_zero).2 rfl
    rw [hz]
    positivity
  by_cases hb : x + y = 0
  · have hy : y = -x := by
      calc y = (x + y) - x := by abel
        _ = -x := by rw [hb, zero_sub]
    subst y
    have hout : pureOuter (-x) = pureOuter x := by
      ext i j
      change (-x i) * star (-x j) = x i * star (x j)
      simp
    rw [hout, sub_self]
    have hz : trNorm (0 : Matrix (Fin n) (Fin n) ℂ) = 0 :=
      (trNorm_eq_zero_iff Matrix.isHermitian_zero).2 rfl
    rw [hz]
    positivity
  let a := x - y
  let b := x + y
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb
  let s : ℝ := Real.sqrt (‖b‖ / ‖a‖)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hnb hna)
  let p := ((s : ℂ) • a) + (((s : ℂ)⁻¹) • b)
  let q := ((s : ℂ) • a) - (((s : ℂ)⁻¹) • b)
  let P : Matrix (Fin n) (Fin n) ℂ :=
    ((1 / 4 : ℝ) : ℂ) • pureOuter p
  let Q : Matrix (Fin n) (Fin n) ℂ :=
    ((1 / 4 : ℝ) : ℂ) • pureOuter q
  have hP : P.PosSemidef := by
    exact pureOuter_smul_posSemidef p (by norm_num)
  have hQ : Q.PosSemidef := by
    exact pureOuter_smul_posSemidef q (by norm_num)
  have hdec : pureOuter x - pureOuter y = P - Q := by
    symm
    exact pureOuter_add_sub_identity x y s hs.ne'
  refine (trNorm_le_of_sub (pureOuter_sub_isHermitian x y) hP hQ hdec).trans ?_
  have hs2 : s ^ 2 = ‖b‖ / ‖a‖ := Real.sq_sqrt (div_nonneg hnb.le hna.le)
  have hsinv : s ≠ 0 := hs.ne'
  have hpar : ‖p‖ ^ 2 + ‖q‖ ^ 2 =
      2 * (s ^ 2 * ‖a‖ ^ 2 + (s⁻¹) ^ 2 * ‖b‖ ^ 2) := by
    have hp := parallelogram_law_with_norm ℂ
      (((s : ℂ) • a)) (((s : ℂ)⁻¹) • b)
    have hp' : ‖p‖ ^ 2 + ‖q‖ ^ 2 =
        2 * ((s * ‖a‖) ^ 2 + (s⁻¹ * ‖b‖) ^ 2) := by
      simpa only [p, q, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, norm_inv] using hp
    calc
      ‖p‖ ^ 2 + ‖q‖ ^ 2 =
          2 * ((s * ‖a‖) ^ 2 + (s⁻¹ * ‖b‖) ^ 2) := hp'
      _ = 2 * (s ^ 2 * ‖a‖ ^ 2 + (s⁻¹) ^ 2 * ‖b‖ ^ 2) := by ring
  have hbalance :
      (1 / 4 : ℝ) * (‖p‖ ^ 2 + ‖q‖ ^ 2) = ‖a‖ * ‖b‖ := by
    rw [hpar, hs2]
    have hs2ne : s ^ 2 ≠ 0 := pow_ne_zero 2 hsinv
    rw [show (s⁻¹) ^ 2 = (s ^ 2)⁻¹ by rw [inv_pow]]
    rw [hs2]
    field_simp [hna.ne', hnb.ne']
    ring
  have htrace : P.trace.re + Q.trace.re = ‖a‖ * ‖b‖ := by
    change ((((1 / 4 : ℝ) : ℂ) • pureOuter p).trace).re +
        ((((1 / 4 : ℝ) : ℂ) • pureOuter q).trace).re = ‖a‖ * ‖b‖
    rw [pureOuter_smul_trace, pureOuter_smul_trace, ← mul_add, hbalance]
  calc
    RCLike.re P.trace + RCLike.re Q.trace = ‖a‖ * ‖b‖ := htrace
    _ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
      dsimp [a, b]
      exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg _)

end HermitianRankOneTraceNorm
end NCG
