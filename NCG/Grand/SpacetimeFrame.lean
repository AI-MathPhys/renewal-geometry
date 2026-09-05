/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Structured spacetime source-frame noncollapse
  (`thm:SMST-spacetime-frame`, Gran-Tensor manuscript)

* `smst_spacetime_frame`: with the least-positive-eigenvalue
  floor of a PSD block `A` encoded order-theoretically as
  `A·A - c•A ⪰ 0` (every positive eigenvalue is `≥ c`):
  (i) direct sums of blocks with a common floor `c` keep the
      floor `c` — the one-cell source synthesis has frame
      lower bound `c*` on the intended support;
  (ii) the Kronecker (determinant-source) product of floored
      blocks has the product floor `c·d`; iterated threefold
      this is the boxed determinant frame bound `c*³`;
  (iii) the collapse witness: an eigenvector with eigenvalue
      `μ` evaluates the source quadratic form to exactly
      `μ·‖v‖²`, so an intended positive eigenvalue tending
      to zero is an explicit collapsing source direction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

namespace NCG

private lemma posSemidef_fromBlocks_diag {a b : Type*}
    [Finite a] [Finite b]
    {M : Matrix a a ℂ} {N : Matrix b b ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    (fromBlocks M 0 0 N).PosSemidef := by
  classical
  haveI := Fintype.ofFinite a
  haveI := Fintype.ofFinite b
  have hfac : fromBlocks M 0 0 N
      = (fromBlocks (CFC.sqrt M) 0 0 (CFC.sqrt N))ᴴ
        * fromBlocks (CFC.sqrt M) 0 0 (CFC.sqrt N) := by
    rw [Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    simp [sqrt_isHermitian, sqrt_mul_self_eq _ hM,
      sqrt_mul_self_eq _ hN]
  rw [hfac]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `thm:SMST-spacetime-frame`. -/
theorem smst_spacetime_frame {a b : Type*} [Fintype a]
    [Fintype b] (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (c d : ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hc : 0 ≤ c)
    (hAf : (A * A - (c : ℂ) • A).PosSemidef)
    (hBf : (B * B - (d : ℂ) • B).PosSemidef) :
    -- (i) direct sums keep a common floor
    (∀ N : Matrix b b ℂ,
      (N * N - (c : ℂ) • N).PosSemidef →
      (fromBlocks A 0 0 N * fromBlocks A 0 0 N
        - (c : ℂ) • fromBlocks A 0 0 N).PosSemidef)
    -- (ii) determinant products multiply floors
    ∧ ((A ⊗ₖ B) * (A ⊗ₖ B)
        - ((c * d : ℝ) : ℂ) • (A ⊗ₖ B)).PosSemidef
    -- (iii) eigenvalue collapse witness
    ∧ (∀ (v : a → ℂ) (μ : ℂ), A *ᵥ v = μ • v →
        star v ⬝ᵥ (A *ᵥ v) = μ * (star v ⬝ᵥ v)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hNf
    have hprod : fromBlocks A 0 0 N * fromBlocks A 0 0 N
        = fromBlocks (A * A) 0 0 (N * N) := by
      rw [Matrix.fromBlocks_multiply]
      simp
    have hsmul : (c : ℂ) • fromBlocks A 0 0 N
        = fromBlocks ((c : ℂ) • A) 0 0 ((c : ℂ) • N) := by
      rw [Matrix.fromBlocks_smul]
      simp
    have hsub : fromBlocks (A * A) 0 0 (N * N)
        - fromBlocks ((c : ℂ) • A) 0 0 ((c : ℂ) • N)
        = fromBlocks (A * A - (c : ℂ) • A) 0 0
            (N * N - (c : ℂ) • N) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Matrix.fromBlocks]
    rw [hprod, hsmul, hsub]
    exact posSemidef_fromBlocks_diag hAf hNf
  · have hBB : (B * B).PosSemidef := by
      rw [show B * B = Bᴴ * B from by rw [hB.1]]
      exact Matrix.posSemidef_conjTranspose_mul_self B
    have hcA : ((c : ℂ) • A).PosSemidef :=
      hA.smul (by exact_mod_cast hc)
    have key : (A ⊗ₖ B) * (A ⊗ₖ B)
        - ((c * d : ℝ) : ℂ) • (A ⊗ₖ B)
        = (A * A - (c : ℂ) • A) ⊗ₖ (B * B)
          + ((c : ℂ) • A) ⊗ₖ (B * B - (d : ℂ) • B) := by
      rw [← Matrix.mul_kronecker_mul]
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.kroneckerMap_apply,
        smul_eq_mul]
      push_cast
      ring
    rw [key]
    exact (hAf.kronecker hBB).add (hcA.kronecker hBf)
  · intro v μ hv
    rw [hv, dotProduct_smul, smul_eq_mul]

end NCG
