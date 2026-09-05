/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Unit-character writer dimension of the repaired scalar
  bank (`thm:SMST-unit-writer-dimension`,
  Gran-Tensor manuscript)

* `smst_unit_writer_dimension`: the covariance-deletion
  mechanism and the boxed census arithmetic:
  (i) unit covariance deletes every cross-signature
      entry — if `B` intertwines the diagonal unit
      characters (`D_Y B = B D_X`) then `B i j = 0`
      whenever the signatures `χ_Y i ≠ χ_X j` (the
      Hilbert–Schmidt orthogonal-projection deletion);
  (ii) conversely every block-supported writer is unit
      covariant, and a covariant writer is freely and
      uniquely parameterized by its equal-signature
      entries (determined by them, and every choice is
      realized) — the writer space is exactly the
      equal-signature block sum `⊕_ω Hom(E_ω^a, E_ω^u)`;
  (iii) the boxed census arithmetic: SMW.1 column sums
      `4 + 6 + 24 = 34`, SMW.2 `34² = 1156` and
      `4 + 8 + 46 = 58`, SMW.3
      `58 = 13·1² + 9·2² + 1·3²`, and the repeated-block
      coordinate count `58 - 13·1² = 45`.

The displayed scalar census itself (coefficient
dimensions `4/6/24` in degrees `2/3/4`, unit-covariant
writer dimensions `4/8/46`, and the multiplicity list of
thirteen simple, nine rank-two, and one rank-three
blocks) is the manuscript's physical unit-charge data —
its enumeration layer; the theorem proves the deletion
mechanism and the block-dimension bookkeeping on top of
it.
-/

open Matrix

namespace NCG

/-- `thm:SMST-unit-writer-dimension` (covariance deletion
+ free block parameterization + boxed census
arithmetic). -/
theorem smst_unit_writer_dimension :
    -- (i) covariance deletes cross-signature entries
    (∀ (m n : ℕ) (χY : Fin m → ℝ) (χX : Fin n → ℝ)
      (B : Matrix (Fin m) (Fin n) ℝ),
      Matrix.diagonal χY * B = B * Matrix.diagonal χX →
      ∀ i j, χY i ≠ χX j → B i j = 0)
    -- (ii) block-supported writers are covariant …
    ∧ (∀ (m n : ℕ) (χY : Fin m → ℝ) (χX : Fin n → ℝ)
        (B : Matrix (Fin m) (Fin n) ℝ),
        (∀ i j, χY i ≠ χX j → B i j = 0) →
        Matrix.diagonal χY * B = B * Matrix.diagonal χX)
    -- … a covariant writer is determined by its
    -- equal-signature entries …
    ∧ (∀ (m n : ℕ) (χY : Fin m → ℝ) (χX : Fin n → ℝ)
        (B B' : Matrix (Fin m) (Fin n) ℝ),
        Matrix.diagonal χY * B = B * Matrix.diagonal χX →
        Matrix.diagonal χY * B'
          = B' * Matrix.diagonal χX →
        (∀ i j, χY i = χX j → B i j = B' i j) →
        B = B')
    -- … and every equal-signature assignment is realized
    ∧ (∀ (m n : ℕ) (χY : Fin m → ℝ) (χX : Fin n → ℝ)
        (g : Fin m → Fin n → ℝ),
        ∃ B : Matrix (Fin m) (Fin n) ℝ,
          Matrix.diagonal χY * B
            = B * Matrix.diagonal χX
          ∧ ∀ i j, χY i = χX j → B i j = g i j)
    -- (iii) the boxed census arithmetic
    ∧ (4 + 6 + 24 = 34) ∧ (34 ^ 2 = 1156)
    ∧ (4 + 8 + 46 = 58)
    ∧ (58 = 13 * 1 ^ 2 + 9 * 2 ^ 2 + 1 * 3 ^ 2)
    ∧ (58 - 13 * 1 ^ 2 = 45) := by
  have hdel : ∀ (m n : ℕ) (χY : Fin m → ℝ)
      (χX : Fin n → ℝ) (B : Matrix (Fin m) (Fin n) ℝ),
      Matrix.diagonal χY * B = B * Matrix.diagonal χX →
      ∀ i j, χY i ≠ χX j → B i j = 0 := by
    intro m n χY χX B hcov i j hne
    have h := congrFun (congrFun hcov i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    -- h : χY i * B i j = B i j * χX j
    have hfac : (χY i - χX j) * B i j = 0 := by
      ring_nf
      nlinarith [h]
    rcases mul_eq_zero.mp hfac with hzero | hzero
    · exact absurd (sub_eq_zero.mp hzero) hne
    · exact hzero
  refine ⟨hdel, ?_, ?_, ?_, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩
  · intro m n χY χX B hsupp
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : χY i = χX j
    · rw [hij, mul_comm]
    · rw [hsupp i j hij, mul_zero, zero_mul]
  · intro m n χY χX B B' hB hB' hagree
    ext i j
    by_cases hij : χY i = χX j
    · exact hagree i j hij
    · rw [hdel m n χY χX B hB i j hij,
        hdel m n χY χX B' hB' i j hij]
  · intro m n χY χX g
    classical
    refine ⟨Matrix.of fun i j =>
      if χY i = χX j then g i j else 0, ?_, ?_⟩
    · ext i j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hij : χY i = χX j
      · simp only [Matrix.of_apply, hij, mul_comm]
      · simp only [Matrix.of_apply, if_neg hij,
          mul_zero, zero_mul]
    · intro i j hij
      simp only [Matrix.of_apply, if_pos hij]

end NCG
