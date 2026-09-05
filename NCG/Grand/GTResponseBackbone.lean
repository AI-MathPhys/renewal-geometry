/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spectral multiplicity and the minimum response backbone
  (`thm:GT-response-backbone`, Gran-Tensor manuscript)

* `gt_response_backbone`: the boxed SA.8 lower bound —
  every cyclic (response-complete) source bank `Jb` for a
  self-adjoint `T` needs at least
  `max_λ dim Ker(T - λ)` columns.  On any eigenprojection
  `P` (`PT = λP`), polynomial response freezes to scalars,
  so the projected reach lies in `Ran(P·Jb)`:
  `rank P ≤ rank(P·Jb) ≤ (number of columns)`.

The matching upper construction — a bank of exactly
`max_λ dim Ker(T-λ)` columns that is cyclic (one column
per multiplicity layer, interpolating across the distinct
eigenvalues) — is the manuscript's converse half, giving
the boxed equality `b_resp(T) = max multiplicity`; the
independence of occurrence grade, carrier dimension, and
backbone dimension is its bookkeeping.
-/

open Matrix

namespace NCG

/-- `thm:GT-response-backbone` (the multiplicity lower
bound SA.8). -/
theorem gt_response_backbone {n k : Type} [Fintype n]
    [Fintype k] [DecidableEq n]
    (T P : Matrix n n ℂ) (lam : ℂ) (Jb : Matrix n k ℂ)
    -- P is an eigenprojection of the response action
    (hP : P * T = lam • P)
    -- the bank is cyclic: every vector is reached by
    -- polynomial response applied to the bank
    (hcyc : ∀ v : n → ℂ, ∃ (N : ℕ) (c : ℕ → k → ℂ),
      v = ∑ i ∈ Finset.range N,
        (T ^ i) *ᵥ (Jb *ᵥ c i)) :
    -- the boxed multiplicity bound
    P.rank ≤ Fintype.card k := by
  have hPpow : ∀ i : ℕ, P * T ^ i = lam ^ i • P := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih,
        Matrix.smul_mul, hP, smul_smul, ← pow_succ]
  have hrange : ∀ v : n → ℂ, ∃ w : k → ℂ,
      P *ᵥ v = (P * Jb) *ᵥ w := by
    intro v
    obtain ⟨N, c, hv⟩ := hcyc v
    refine ⟨∑ i ∈ Finset.range N, lam ^ i • c i, ?_⟩
    calc P *ᵥ v
        = ∑ i ∈ Finset.range N,
          P *ᵥ ((T ^ i) *ᵥ (Jb *ᵥ c i)) := by
          rw [hv, Matrix.mulVec_sum]
      _ = ∑ i ∈ Finset.range N,
          lam ^ i • ((P * Jb) *ᵥ c i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mulVec_mulVec, hPpow i,
            Matrix.smul_mulVec, Matrix.mulVec_mulVec]
      _ = (P * Jb) *ᵥ
          ∑ i ∈ Finset.range N, lam ^ i • c i := by
          rw [Matrix.mulVec_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mulVec_smul]
  have hle : LinearMap.range P.mulVecLin
      ≤ LinearMap.range (P * Jb).mulVecLin := by
    rintro y ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := hrange v
    exact ⟨w, hw.symm⟩
  calc P.rank
      ≤ (P * Jb).rank := Submodule.finrank_mono hle
    _ ≤ Fintype.card k := Matrix.rank_le_card_width _

end NCG
