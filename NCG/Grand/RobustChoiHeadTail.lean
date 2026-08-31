/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HermitianRankOneTraceNorm

/-!
# Robust Choi head--tail trace-norm assembly

This file isolates the quantitative last step in the robust Choi-purity
argument.  A positive tail is combined with a leading rank-one Choi vector,
using the sharp rank-one perturbation estimate.  The scaled form records the
exact manuscript constants

`2 * sqrt δ + δ / d`.

The remaining channel-specific work is therefore cleanly separated: produce
the leading Choi vector, its positive spectral tail, and the polar-unitary
Hilbert--Schmidt estimate.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace RobustChoiHeadTail

open Upstream.PrimitiveWeight
open HermitianRankOneTraceNorm

variable {n : ℕ}

/-- A positive spectral tail adds exactly its trace to the rank-one
perturbation budget. -/
theorem head_tail_trNorm_bound
    (J T : Matrix (Fin n) (Fin n) ℂ)
    (x y : EuclideanSpace ℂ (Fin n)) {δ t : ℝ}
    (hJ : J = pureOuter x + T)
    (hT : T.PosSemidef)
    (hhead : ‖x - y‖ * (‖x‖ + ‖y‖) ≤ 2 * Real.sqrt δ)
    (htail : T.trace.re ≤ t) :
    trNorm (J - pureOuter y) ≤ 2 * Real.sqrt δ + t := by
  have hdec : J - pureOuter y =
      (pureOuter x - pureOuter y) + T := by
    rw [hJ]
    abel
  have hheadH := pureOuter_sub_isHermitian x y
  have hsum := trNorm_add_le hheadH hT.1
  rw [← hdec] at hsum
  have hrank := trNorm_pureOuter_sub_le x y
  have htailNorm := trNorm_eq_trace_of_posSemidef hT
  rw [htailNorm] at hsum
  linarith

/-- Scaled Choi form of `head_tail_trNorm_bound`.  If both leading vectors
have norm at most `sqrt d`, their distance is at most
`sqrt δ / sqrt d`, and the positive tail has trace at most `δ/d`, then the
exact robust bound is `2 sqrt δ + δ/d`. -/
theorem scaled_head_tail_trNorm_bound
    (J T : Matrix (Fin n) (Fin n) ℂ)
    (x y : EuclideanSpace ℂ (Fin n)) {d δ : ℝ}
    (hd : 0 < d) (hδ : 0 ≤ δ)
    (hJ : J = pureOuter x + T)
    (hT : T.PosSemidef)
    (hx : ‖x‖ ≤ Real.sqrt d)
    (hy : ‖y‖ ≤ Real.sqrt d)
    (hxy : ‖x - y‖ ≤ Real.sqrt δ / Real.sqrt d)
    (htail : T.trace.re ≤ δ / d) :
    trNorm (J - pureOuter y) ≤
      2 * Real.sqrt δ + δ / d := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hsum : ‖x‖ + ‖y‖ ≤ 2 * Real.sqrt d := by linarith
  have hq : 0 ≤ Real.sqrt δ / Real.sqrt d :=
    div_nonneg (Real.sqrt_nonneg _) hsd.le
  have hprod : ‖x - y‖ * (‖x‖ + ‖y‖) ≤
      (Real.sqrt δ / Real.sqrt d) * (2 * Real.sqrt d) :=
    mul_le_mul hxy hsum (by positivity) hq
  have hcancel : (Real.sqrt δ / Real.sqrt d) * (2 * Real.sqrt d) =
      2 * Real.sqrt δ := by
    field_simp [hsd.ne']
  apply head_tail_trNorm_bound J T x y hJ hT
  · rwa [hcancel] at hprod
  · exact htail

end RobustChoiHeadTail
end NCG
