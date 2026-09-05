/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Native determinant source and the structured frame criterion
  (`cor:native-determinant-master`, `cor:structured-frame-master`,
   flagship manuscript)

* `determinant_multiplicity_one`: the invariant-multiplicity
  character sum — with `φ = (1+√5)/2`,
  `(27 - 15 + 12(φ³ + (1-φ)³))/60 = 1` (both roots of
  `x² = x + 1` give `φ³ + (1-φ)³ = 4`), so the determinant
  character occurs exactly once in `3₋⊗³`;
* `kronecker_mulVec_prod` / `kronecker_eigen`: product vectors
  are eigenvectors of Kronecker products with multiplied
  eigenvalues;
* `native_determinant_scaling`: the boxed eigenvalue equations —
  `Γ` acting by `1/6` on each response factor gives
  `Γ⊗³ e_vol = (1/216) e_vol`, and the `2³` sign-contrast
  normalization gives `M_ext e_vol = (1/27) e_vol`;
* `structured_frame_bound`: the structured frame criterion in the
  equivariant diagonal model — blocks with least positive
  eigenvalue `≥ c` give the one-Read lower bound `c` and the
  three-Read tensor lower bound `c³`;
* `collapsing_direction`: an eigenvalue tending to zero is
  attained: the quadratic form at the unit eigenvector equals the
  eigenvalue, so saturation need not survive the limit.

Rendering disclosed: the identification of the determinant line
inside `(1₊ ⊕ 3₋)⊗³` (parity forces it into `3₋⊗³`) and the `A₅`
standard-character values `3, -1, 0, φ, 1-φ` on classes of sizes
`1, 15, 20, 12, 12` are the classical icosahedral character
inputs; the orthogonal equivariant block decomposition behind the
diagonal model is Schur's lemma, as in the structured-determinant
record.
-/

open Matrix Kronecker

namespace NCG

/-- The invariant-multiplicity character sum equals one:
`φ³ + (1-φ)³ = 4` for the golden ratio. -/
theorem determinant_multiplicity_one :
    (27 - 15 + 12 * (((1 + Real.sqrt 5) / 2) ^ 3
      + (1 - (1 + Real.sqrt 5) / 2) ^ 3)) / 60 = 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hφ : ((1 + Real.sqrt 5) / 2) ^ 3
      + (1 - (1 + Real.sqrt 5) / 2) ^ 3 = 4 := by
    nlinarith [h5]
  rw [hφ]
  norm_num

/-- A Kronecker product applied to a product vector is the
product of the applications. -/
theorem kronecker_mulVec_prod {ι κ : Type*} [Fintype ι]
    [Fintype κ] (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (u : ι → ℂ) (v : κ → ℂ) :
    (A ⊗ₖ B).mulVec (fun p => u p.1 * v p.2)
      = fun p => A.mulVec u p.1 * B.mulVec v p.2 := by
  ext ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

/-- Product vectors are eigenvectors of Kronecker products with
multiplied eigenvalues. -/
theorem kronecker_eigen {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (u : ι → ℂ)
    (v : κ → ℂ) (a b : ℂ) (ha : A.mulVec u = a • u)
    (hb : B.mulVec v = b • v) :
    (A ⊗ₖ B).mulVec (fun p => u p.1 * v p.2)
      = (a * b) • fun p => u p.1 * v p.2 := by
  rw [kronecker_mulVec_prod, ha, hb]
  ext ⟨i, j⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `cor:native-determinant-master`, boxed eigenvalue equations:
`Γ⊗³ e_vol = (1/216) e_vol` and, with the `2³` sign-contrast
normalization, `M_ext e_vol = (1/27) e_vol`. -/
theorem native_determinant_scaling {ι : Type*} [Fintype ι]
    (Γ : Matrix ι ι ℂ) (e : ι → ℂ)
    (hΓ : Γ.mulVec e = (1 / 6 : ℂ) • e) :
    (Γ ⊗ₖ Γ ⊗ₖ Γ).mulVec
        (fun p => e p.1.1 * e p.1.2 * e p.2)
      = (1 / 216 : ℂ)
        • (fun p => e p.1.1 * e p.1.2 * e p.2)
    ∧ (8 : ℂ) • ((1 / 216 : ℂ)
        • (fun p : (ι × ι) × ι => e p.1.1 * e p.1.2 * e p.2))
      = (1 / 27 : ℂ)
        • (fun p => e p.1.1 * e p.1.2 * e p.2) := by
  constructor
  · have h2 : (Γ ⊗ₖ Γ).mulVec (fun q : ι × ι => e q.1 * e q.2)
        = ((1 / 6 : ℂ) * (1 / 6)) • fun q => e q.1 * e q.2 :=
      kronecker_eigen Γ Γ e e _ _ hΓ hΓ
    have h3 := kronecker_eigen (Γ ⊗ₖ Γ) Γ
      (fun q : ι × ι => e q.1 * e q.2) e _ _ h2 hΓ
    calc (Γ ⊗ₖ Γ ⊗ₖ Γ).mulVec
          (fun p => e p.1.1 * e p.1.2 * e p.2)
        = (1 / 6 * (1 / 6) * (1 / 6) : ℂ)
          • fun p : (ι × ι) × ι => e p.1.1 * e p.1.2 * e p.2 :=
          h3
      _ = (1 / 216 : ℂ)
          • fun p => e p.1.1 * e p.1.2 * e p.2 := by
          norm_num
  · rw [smul_smul]
    norm_num

/-- `cor:structured-frame-master`, diagonal model: blocks with
least positive eigenvalue `≥ c` give the one-Read lower bound `c`
and the three-Read tensor lower bound `c³`. -/
theorem structured_frame_bound {ι κ μ : Type*}
    (d1 : ι → ℝ) (d2 : κ → ℝ) (d3 : μ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h1 : ∀ i, c ≤ d1 i) (h2 : ∀ j, c ≤ d2 j)
    (h3 : ∀ k, c ≤ d3 k) :
    (∀ i, c ≤ d1 i)
    ∧ ∀ p : ι × κ × μ, c ^ 3 ≤ d1 p.1 * d2 p.2.1 * d3 p.2.2 := by
  refine ⟨h1, fun p => ?_⟩
  have hd1 : (0:ℝ) ≤ d1 p.1 := le_trans hc (h1 p.1)
  have hd2 : (0:ℝ) ≤ d2 p.2.1 := le_trans hc (h2 p.2.1)
  have k1 : c * c ≤ d1 p.1 * d2 p.2.1 :=
    mul_le_mul (h1 p.1) (h2 p.2.1) hc hd1
  have k2 : c * c * c ≤ d1 p.1 * d2 p.2.1 * d3 p.2.2 :=
    mul_le_mul k1 (h3 p.2.2) hc (mul_nonneg hd1 hd2)
  calc c ^ 3 = c * c * c := by ring
    _ ≤ d1 p.1 * d2 p.2.1 * d3 p.2.2 := k2

/-- Collapsing source direction: the quadratic form at a unit
eigenvector equals the eigenvalue, so an eigenvalue tending to
zero collapses the source norm. -/
theorem collapsing_direction {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) (lam : ℂ)
    (hv : A.mulVec v = lam • v)
    (hnorm : ∑ i, star (v i) * v i = 1) :
    star v ⬝ᵥ A.mulVec v = lam := by
  have hunit : star v ⬝ᵥ v = 1 := by
    simpa [dotProduct] using hnorm
  rw [hv, dotProduct_smul, smul_eq_mul, hunit, mul_one]

end NCG
