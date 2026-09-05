/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Shared-edge normal current, reduction, and commutant
  (`thm:shared-edge-normal-current`, Gran-Tensor manuscript)

* `shared_edge_normal_current`:
  (i) nonadjacent vertex densities commute: operators on
      distinct Kronecker factors commute
      (`(A⊗1)(1⊗B) = (1⊗B)(A⊗1) = A⊗B`);
  (ii) the boxed edge current
      `j_e = -ih·[n_x, n_y] = 2hλλ'·Z_e` from the Pauli
      closure `[X,Y] = 2i·Z` of the extracted edge factor;
  (iii) the unbounded-normal-scale obstruction: a
      regulator-uniform current `|2hλλ'| ≥ κ*` with a bounded
      loading ratio `|λ| ≤ ρ|λ'|` forces
      `κ*/(2h) ≤ ρ·λ'²` — the coefficients grow like
      `h^{-1/2}`.

The full-tensor commutant clause is the proved Schur/two-block
engine (`smst_one_generation_audit`); the trace-orthogonality
of distinct edge currents is the manuscript's normalized-trace
bookkeeping.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- `thm:shared-edge-normal-current`. -/
theorem shared_edge_normal_current {n m : Type*} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m] :
    -- (i) nonadjacent densities commute across factors
    (∀ (A : Matrix n n ℂ) (B : Matrix m m ℂ),
      (A ⊗ₖ (1 : Matrix m m ℂ))
        * ((1 : Matrix n n ℂ) ⊗ₖ B)
      = ((1 : Matrix n n ℂ) ⊗ₖ B)
        * (A ⊗ₖ (1 : Matrix m m ℂ)))
    -- (ii) the boxed edge current `-ih[n_x,n_y] = 2hλλ'Z`
    ∧ (∀ (X Y Z : Matrix n n ℂ) (h lam lam' : ℝ),
        X * Y - Y * X = (2 * Complex.I) • Z →
        (-(Complex.I * h))
          • ((lam : ℂ) • X * ((lam' : ℂ) • Y)
            - (lam' : ℂ) • Y * ((lam : ℂ) • X))
        = ((2 * h * lam * lam' : ℝ) : ℂ) • Z)
    -- (iii) the unbounded-normal-scale obstruction
    ∧ (∀ h lam lam' κ ρ : ℝ, 0 < h → 0 < κ →
        0 ≤ ρ → |lam| ≤ ρ * |lam'| →
        κ ≤ |2 * h * lam * lam'| →
        κ / (2 * h) ≤ ρ * lam' ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro X Y Z h lam lam' hXY
    have hexp : (lam : ℂ) • X * ((lam' : ℂ) • Y)
        - (lam' : ℂ) • Y * ((lam : ℂ) • X)
        = ((lam : ℂ) * (lam' : ℂ)) • (X * Y - Y * X) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, smul_sub]
      rw [mul_comm (lam' : ℂ) (lam : ℂ)]
    rw [hexp, hXY, smul_smul, smul_smul]
    congr 1
    push_cast
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    ring_nf
    rw [show (Complex.I : ℂ) ^ 2 = -1 from by
      rw [sq]
      exact hI]
    ring
  · intro h lam lam' κ ρ hh hκ hρ hload hcur
    have habs : |2 * h * lam * lam'|
        = 2 * h * (|lam| * |lam'|) := by
      rw [abs_mul, abs_mul, abs_mul]
      rw [abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos hh]
      ring
    rw [habs] at hcur
    rw [div_le_iff₀ (by positivity)]
    have h1 : |lam| * |lam'| ≤ ρ * (|lam'| * |lam'|) := by
      calc |lam| * |lam'| ≤ (ρ * |lam'|) * |lam'| :=
            mul_le_mul_of_nonneg_right hload (abs_nonneg _)
        _ = ρ * (|lam'| * |lam'|) := by ring
    calc κ ≤ 2 * h * (|lam| * |lam'|) := hcur
      _ ≤ 2 * h * (ρ * (|lam'| * |lam'|)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ρ * lam' ^ 2 * (2 * h) := by
          rw [← sq, sq_abs]
          ring

end NCG
