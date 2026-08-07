/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Mixing invariants of two residue squares
  (`thm:SM-mixing-invariants`, Gran-Tensor manuscript)

* `sm_mixing_invariants`: for rank-one spectral projections
  `P = uu*`, `Q = dd*` the pairwise panel is the squared
  eigenframe modulus, `Tr(PQ) = |⟨u,d⟩|²`, and the quartet
  panel is the boxed rephasing-covariant product
  `Tr(P_iQ_jP_kQ_ℓ) = V_ij·conj(V_kj)·V_kℓ·conj(V_iℓ)` — the
  displayed panels are exactly the eigenframe data.

Rendering disclosed: the reconstruction of `V` up to diagonal
rephasings and the closed Jarlskog formula
`Im Tr([A,B]³)/(6ΔΔ)` are the manuscript's bookkeeping over
these panels and remain conditional records of the audit.
-/

open Matrix

namespace NCG

/-- Rank-one products contract to a scalar times a rank-one. -/
lemma vecMulVec_mul_vecMulVec {n : Type*} [Fintype n]
    (a b c d : n → ℂ) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d
      = (b ⬝ᵥ c) • Matrix.vecMulVec a d := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun k _ => show
      Matrix.vecMulVec a b i k * Matrix.vecMulVec c d k j
        = (a i * d j) * (b k * c k) from by
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply]
    ring)]
  rw [← Finset.mul_sum,
    show (∑ k, b k * c k) = b ⬝ᵥ c from rfl]
  ring

/-- Trace of a rank-one operator. -/
lemma vecMulVec_trace {n : Type*} [Fintype n] (a b : n → ℂ) :
    (Matrix.vecMulVec a b).trace = b ⬝ᵥ a := by
  rw [Matrix.trace, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.vecMulVec_apply]
  ring

private lemma star_dot_conj {n : Type*} [Fintype n]
    (a b : n → ℂ) :
    star b ⬝ᵥ a = star (star a ⬝ᵥ b) := by
  rw [dotProduct, dotProduct, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul', Pi.star_apply, Pi.star_apply, star_star]
  ring

/-- `thm:SM-mixing-invariants`: the pairwise and quartet
spectral panels are the eigenframe data. -/
theorem sm_mixing_invariants {n : Type*} [Fintype n]
    (u d v w : n → ℂ) :
    ((Matrix.vecMulVec u (star u)
        * Matrix.vecMulVec d (star d)).trace
      = ((Complex.normSq (star u ⬝ᵥ d) : ℝ) : ℂ))
    ∧ ((Matrix.vecMulVec u (star u) * Matrix.vecMulVec d (star d)
        * (Matrix.vecMulVec v (star v)
          * Matrix.vecMulVec w (star w))).trace
      = (star u ⬝ᵥ d) * (star d ⬝ᵥ v)
        * ((star v ⬝ᵥ w) * (star w ⬝ᵥ u))) := by
  constructor
  · rw [vecMulVec_mul_vecMulVec, Matrix.trace_smul,
      vecMulVec_trace, smul_eq_mul, star_dot_conj u d,
      Complex.star_def, Complex.mul_conj]
  · rw [vecMulVec_mul_vecMulVec u (star u) d (star d),
      vecMulVec_mul_vecMulVec v (star v) w (star w),
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      vecMulVec_mul_vecMulVec u (star d) v (star w),
      smul_smul, Matrix.trace_smul, vecMulVec_trace,
      smul_eq_mul]
    ring

end NCG
