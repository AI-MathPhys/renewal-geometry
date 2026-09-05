/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rank–trace certificate for an indefinite compression
  (`thm:GT-rank-trace-indefinite`,
  Gran-Tensor manuscript)

* `gt_rank_trace_indefinite`: the boxed SC.7 —
  `‖P+Q‖_F² ≥ cTrP - (c²/4)r + 2cTrQ - c²b` for every
  `c > 0` — and the boxed SC.8 specialization at `c = 2` —
  `r ≥ 2TrP + 4TrQ - 4b - ‖P+Q‖_F²`.

The proof runs through an adapted orthonormal basis `V`
(unitary): a block `B` of at most `b` directions captures
the positive part of `Q` on the compressed diagonal
(`TrQ ≤ ∑_B diag`), a block `R` of at most `r` directions
carries `Ran P`, and the diagonal is nonpositive outside
the two blocks.  On these data the certificate is exact
real arithmetic: the Frobenius mass is unitarily invariant
and dominates the diagonal squares, and the pointwise
bounds `d² ≥ 2cd - c²` on `B`, `d² ≥ cd - c²/4` on `R`,
and `d² ≥ cd` outside (`d ≤ 0` there) sum to the boxed
display.  Constructing `V` from the spectral decomposition
of `Q` together with a basis of `Ran P` is the
manuscript's spectral layer; congruence invariance of the
inertia and the non-determination of the protected cross
orientation are its bookkeeping.
-/

open Matrix Finset

namespace NCG

/-- Frobenius square as the real trace of `XᴴX`. -/
theorem gt_frobenius_trace {n : Type} [Fintype n]
    (X : Matrix n n ℂ) :
    ((Xᴴ * X).trace).re
      = ∑ i, ∑ j, Complex.normSq (X i j) := by
  rw [Matrix.trace, Complex.re_sum]
  rw [show ∑ i, ∑ j, Complex.normSq (X i j)
      = ∑ j, ∑ i, Complex.normSq (X i j) from
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdiag : (Xᴴ * X).diag i
      = ∑ j, ((Complex.normSq (X j i) : ℝ) : ℂ) := by
    simp only [Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (star (X j i)) * X j i
        = ((Complex.normSq (X j i) : ℝ) : ℂ) from by
      rw [mul_comm, Complex.star_def,
        Complex.mul_conj]]
  rw [hdiag, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- `thm:GT-rank-trace-indefinite` (SC.7 and SC.8). -/
theorem gt_rank_trace_indefinite {n : Type} [Fintype n]
    [DecidableEq n]
    (P Q V : Matrix n n ℂ) (hV : Vᴴ * V = 1)
    (B R : Finset n) (hdisj : Disjoint B R)
    (r b : ℕ) (hr : R.card ≤ r) (hb : B.card ≤ b)
    -- the Q-positive block captures the Q trace on the
    -- adapted diagonal
    (hB : (Q.trace).re
      ≤ ∑ i ∈ B, ((Vᴴ * (P + Q) * V) i i).re)
    -- outside the adapted blocks the diagonal is
    -- nonpositive
    (hW : ∀ i, i ∉ B → i ∉ R →
      ((Vᴴ * (P + Q) * V) i i).re ≤ 0) :
    -- the boxed SC.7, for every c > 0
    (∀ c : ℝ, 0 < c →
      c * (P.trace).re - c ^ 2 / 4 * r
          + 2 * c * (Q.trace).re - c ^ 2 * b
        ≤ ∑ i, ∑ j, Complex.normSq ((P + Q) i j))
    -- the boxed SC.8 (the certificate at c = 2)
    ∧ ((r : ℝ) ≥ 2 * (P.trace).re + 4 * (Q.trace).re
        - 4 * b
        - ∑ i, ∑ j, Complex.normSq ((P + Q) i j)) := by
  have hVVH : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  set M := P + Q with hM
  set N := Vᴴ * M * V with hN
  -- trace invariance of the compression
  have htr : N.trace = M.trace := by
    rw [hN, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, hVVH, Matrix.mul_one]
  -- Frobenius invariance of the compression
  have hNN : Nᴴ * N = Vᴴ * ((Mᴴ * M) * V) := by
    rw [hN]
    have h1 : (Vᴴ * M * V)ᴴ * (Vᴴ * M * V)
        = Vᴴ * (Mᴴ * ((V * Vᴴ) * (M * V))) := by
      simp only [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [h1, hVVH, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  have htr2 : (Vᴴ * ((Mᴴ * M) * V)).trace
      = (Mᴴ * M).trace := by
    rw [Matrix.trace_mul_comm Vᴴ ((Mᴴ * M) * V),
      Matrix.mul_assoc (Mᴴ * M) V Vᴴ, hVVH,
      Matrix.mul_one]
  have hfrob : ∑ i, ∑ j, Complex.normSq (N i j)
      = ∑ i, ∑ j, Complex.normSq (M i j) := by
    rw [← gt_frobenius_trace, ← gt_frobenius_trace, hNN,
      htr2]
  -- diagonal domination of the Frobenius mass
  have hdiag : ∑ i, (N i i).re ^ 2
      ≤ ∑ i, ∑ j, Complex.normSq (N i j) := by
    apply Finset.sum_le_sum
    intro i _
    calc (N i i).re ^ 2 ≤ Complex.normSq (N i i) := by
          rw [Complex.normSq_apply]
          nlinarith [sq_nonneg (N i i).im]
      _ ≤ ∑ j, Complex.normSq (N i j) :=
          Finset.single_le_sum
            (fun j _ => Complex.normSq_nonneg _)
            (Finset.mem_univ i)
  -- the compressed diagonal sums to the joint trace
  have hdsum : ∑ i, (N i i).re
      = (P.trace).re + (Q.trace).re := by
    have h1 : (N.trace).re = ∑ i, (N i i).re := by
      rw [Matrix.trace, Complex.re_sum]
      rfl
    rw [← h1, htr, hM, Matrix.trace_add, Complex.add_re]
  -- partition of the index set
  have hsub : B ∪ R ⊆ univ := Finset.subset_univ _
  have hpart : ∀ f : n → ℝ,
      ∑ i, f i = ∑ i ∈ univ \ (B ∪ R), f i
        + (∑ i ∈ B, f i + ∑ i ∈ R, f i) := by
    intro f
    rw [← Finset.sum_union hdisj,
      Finset.sum_sdiff hsub]
  have main : ∀ c : ℝ, 0 < c →
      c * (P.trace).re - c ^ 2 / 4 * r
          + 2 * c * (Q.trace).re - c ^ 2 * b
        ≤ ∑ i, ∑ j, Complex.normSq ((P + Q) i j) := by
    intro c hc
    have hBb : ∑ i ∈ B, (2 * c * (N i i).re - c ^ 2)
        ≤ ∑ i ∈ B, (N i i).re ^ 2 :=
      Finset.sum_le_sum fun i _ => by
        nlinarith [sq_nonneg ((N i i).re - c)]
    have hRb : ∑ i ∈ R, (c * (N i i).re - c ^ 2 / 4)
        ≤ ∑ i ∈ R, (N i i).re ^ 2 :=
      Finset.sum_le_sum fun i _ => by
        nlinarith [sq_nonneg ((N i i).re - c / 2)]
    have hWb : ∑ i ∈ univ \ (B ∪ R), c * (N i i).re
        ≤ ∑ i ∈ univ \ (B ∪ R), (N i i).re ^ 2 :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_sdiff, Finset.mem_union] at hi
        have hile := hW i (fun h => hi.2 (Or.inl h))
          (fun h => hi.2 (Or.inr h))
        nlinarith [sq_nonneg (N i i).re,
          mul_nonpos_of_nonneg_of_nonpos hc.le hile]
    have eB : ∑ i ∈ B, (2 * c * (N i i).re - c ^ 2)
        = 2 * c * (∑ i ∈ B, (N i i).re)
          - c ^ 2 * B.card := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, mul_comm
          (B.card : ℝ)]
    have eR : ∑ i ∈ R, (c * (N i i).re - c ^ 2 / 4)
        = c * (∑ i ∈ R, (N i i).re)
          - c ^ 2 / 4 * R.card := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, mul_comm
          (R.card : ℝ)]
    have eW : ∑ i ∈ univ \ (B ∪ R), c * (N i i).re
        = c * ∑ i ∈ univ \ (B ∪ R), (N i i).re := by
      rw [← Finset.mul_sum]
    have hd2 := hpart (fun i => (N i i).re ^ 2)
    have hcard1 : (B.card : ℝ) ≤ b := by
      exact_mod_cast hb
    have hcard2 : (R.card : ℝ) ≤ r := by
      exact_mod_cast hr
    have hchain : ∑ i, (N i i).re ^ 2
        ≤ ∑ i, ∑ j, Complex.normSq (M i j) :=
      hfrob ▸ hdiag
    have hS : ∑ i ∈ B, (N i i).re + ∑ i ∈ R, (N i i).re
        + ∑ i ∈ univ \ (B ∪ R), (N i i).re
        = (P.trace).re + (Q.trace).re := by
      have h := hpart (fun i => (N i i).re)
      linarith [hdsum]
    have hkey : 2 * c * (∑ i ∈ B, (N i i).re)
        - c ^ 2 * B.card
        + (c * (∑ i ∈ R, (N i i).re)
            - c ^ 2 / 4 * R.card)
        + c * (∑ i ∈ univ \ (B ∪ R), (N i i).re)
        ≤ ∑ i, (N i i).re ^ 2 := by
      linarith [hBb, hRb, hWb, eB, eR, eW, hd2]
    have hring : 2 * c * (∑ i ∈ B, (N i i).re)
        - c ^ 2 * B.card
        + (c * (∑ i ∈ R, (N i i).re)
            - c ^ 2 / 4 * R.card)
        + c * (∑ i ∈ univ \ (B ∪ R), (N i i).re)
        = c * (∑ i ∈ B, (N i i).re
            + ∑ i ∈ R, (N i i).re
            + ∑ i ∈ univ \ (B ∪ R), (N i i).re)
          + c * (∑ i ∈ B, (N i i).re)
          - c ^ 2 * B.card - c ^ 2 / 4 * R.card := by
      ring
    have h1 : c * (∑ i ∈ B, (N i i).re
        + ∑ i ∈ R, (N i i).re
        + ∑ i ∈ univ \ (B ∪ R), (N i i).re)
        = c * ((P.trace).re + (Q.trace).re) := by
      rw [hS]
    have h2 : c * (Q.trace).re
        ≤ c * (∑ i ∈ B, (N i i).re) :=
      mul_le_mul_of_nonneg_left hB hc.le
    have h3 : c ^ 2 * (B.card : ℝ) ≤ c ^ 2 * b :=
      mul_le_mul_of_nonneg_left hcard1 (sq_nonneg c)
    have h4 : c ^ 2 / 4 * (R.card : ℝ) ≤ c ^ 2 / 4 * r :=
      mul_le_mul_of_nonneg_left hcard2
        (by positivity)
    have hring2 : c * ((P.trace).re + (Q.trace).re)
        + c * (Q.trace).re
        = c * (P.trace).re + 2 * c * (Q.trace).re := by
      ring
    linarith [hkey, hring, h1, h2, h3, h4, hchain,
      hring2]
  refine ⟨main, ?_⟩
  have h2 := main 2 (by norm_num)
  linarith [h2]

end NCG
