/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.HodgeBSD

/-!
# Pseudodeterminant of a finite analytic jet

For a germ of exact order `r < m`, truncated multiplication vanishes on the
last `r` monomials.  After removing those kernel columns and the first `r`
zero rows, its canonical nonzero block is lower triangular with constant
diagonal `F r`.  This module computes the Gram determinant of that block.
-/

namespace NCG

open Matrix

/-- Canonical nonzero block of multiplication by an order-`r` germ modulo
`z^m`, in the monomial bases of the kernel complement and image. -/
def jetReducedMatrix (F : ℕ → ℂ) (m r : ℕ) :
    Matrix (Fin (m - r)) (Fin (m - r)) ℂ :=
  Matrix.of fun k j =>
    if (j : ℕ) ≤ (k : ℕ) then F (r + (k : ℕ) - (j : ℕ)) else 0

/-- The reduced block is literally the corresponding row/column submatrix of
the full truncated multiplication matrix. -/
theorem jetReducedMatrix_eq_jet_submatrix (F : ℕ → ℂ) {m r : ℕ}
    (hrm : r ≤ m) (hlow : ∀ i, i < r → F i = 0)
    (k j : Fin (m - r)) :
    jetMatrix F m
        ⟨r + (k : ℕ), by omega⟩
        ⟨(j : ℕ), by omega⟩
      = jetReducedMatrix F m r k j := by
  simp only [jetMatrix, jetReducedMatrix, Matrix.of_apply]
  by_cases hjk : (j : ℕ) ≤ (k : ℕ)
  · rw [if_pos hjk, if_pos (by omega)]
  · rw [if_neg hjk]
    by_cases hjrk : (j : ℕ) ≤ r + (k : ℕ)
    · rw [if_pos hjrk, hlow _ (by omega)]
    · rw [if_neg hjrk]

/-- Determinant of the canonical reduced multiplication block. -/
theorem jetReducedMatrix_det (F : ℕ → ℂ) (m r : ℕ) :
    (jetReducedMatrix F m r).det = F r ^ (m - r) := by
  have htri : (jetReducedMatrix F m r).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hji : (i : ℕ) < (j : ℕ) := hij
    simp only [jetReducedMatrix, Matrix.of_apply]
    rw [if_neg (by omega)]
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp [jetReducedMatrix]

/-- Pseudodeterminant of the analytic jet Gram: determinant of its canonical
nonzero reduced Gram block. -/
noncomputable def analyticJetPseudoDet (F : ℕ → ℂ) (m r : ℕ) : ℝ :=
  ((jetReducedMatrix F m r)ᴴ * jetReducedMatrix F m r).det.re

/-- The pseudodeterminant is the leading-coefficient magnitude raised to
twice the nonzero rank. -/
theorem analyticJetPseudoDet_eq (F : ℕ → ℂ) (m r : ℕ) :
    analyticJetPseudoDet F m r = ‖F r‖ ^ (2 * (m - r)) := by
  rw [analyticJetPseudoDet, Matrix.det_mul,
    Matrix.det_conjTranspose, jetReducedMatrix_det]
  rw [star_pow, ← mul_pow, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_norm_sq]
  norm_cast
  rw [← pow_mul]

/-- `thm:analytic-jet`: exact nullity together with the formerly missing
pseudodeterminant formula. -/
theorem analytic_jet_rank_and_leading_magnitude (F : ℕ → ℂ) {m r : ℕ}
    (hrm : r < m) (hlow : ∀ i, i < r → F i = 0) (hne : F r ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (jetMatrix F m).mulVecLin) = r
      ∧ analyticJetPseudoDet F m r = ‖F r‖ ^ (2 * (m - r)) := by
  constructor
  · simpa [Nat.min_eq_left hrm.le] using
      jet_nullity F hrm.le hlow hne
  · exact analyticJetPseudoDet_eq F m r

/-- The degree-one cohomology (cokernel) of the two-term square jet complex
has the same dimension as its degree-zero cohomology (kernel). -/
theorem analyticJetCokernelFinrank (F : ℕ → ℂ) {m r : ℕ}
    (hrm : r ≤ m) (hlow : ∀ i, i < r → F i = 0) (hne : F r ≠ 0) :
    Module.finrank ℂ
        ((Fin m → ℂ) ⧸ LinearMap.range (jetMatrix F m).mulVecLin) = r := by
  let L := (jetMatrix F m).mulVecLin
  change Module.finrank ℂ ((Fin m → ℂ) ⧸ LinearMap.range L) = r
  have hker : Module.finrank ℂ (LinearMap.ker L) = r := by
    dsimp [L]
    simpa [Nat.min_eq_left hrm] using jet_nullity F hrm hlow hne
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hquot := (LinearMap.range L).finrank_quotient_add_finrank
  have hspace : Module.finrank ℂ (Fin m → ℂ) = m := by simp
  rw [hker, hspace] at hrank
  rw [hspace] at hquot
  omega

/-- Product of the nonzero singular values, recovered as the positive square
root of the reduced Gram pseudodeterminant. -/
noncomputable def analyticJetNonzeroSingularProduct
    (F : ℕ → ℂ) (m r : ℕ) : ℝ :=
  Real.sqrt (analyticJetPseudoDet F m r)

theorem analyticJetNonzeroSingularProduct_eq (F : ℕ → ℂ) (m r : ℕ) :
    analyticJetNonzeroSingularProduct F m r = ‖F r‖ ^ (m - r) := by
  rw [analyticJetNonzeroSingularProduct, analyticJetPseudoDet_eq]
  have hpow : ‖F r‖ ^ (2 * (m - r)) = (‖F r‖ ^ (m - r)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow, Real.sqrt_sq (by positivity)]

/-- `prop:jet-cohomology`: both cohomology dimensions and the exact product
of the nonzero singular values of the differential. -/
theorem jet_cohomology_exact (F : ℕ → ℂ) {m r : ℕ}
    (hrm : r < m) (hlow : ∀ i, i < r → F i = 0) (hne : F r ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (jetMatrix F m).mulVecLin) = r
      ∧ Module.finrank ℂ
          ((Fin m → ℂ) ⧸ LinearMap.range (jetMatrix F m).mulVecLin) = r
      ∧ analyticJetNonzeroSingularProduct F m r = ‖F r‖ ^ (m - r) := by
  exact ⟨(analytic_jet_rank_and_leading_magnitude F hrm hlow hne).1,
    analyticJetCokernelFinrank F hrm.le hlow hne,
    analyticJetNonzeroSingularProduct_eq F m r⟩

end NCG
