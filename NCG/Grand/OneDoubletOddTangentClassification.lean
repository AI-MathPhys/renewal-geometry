/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MonoidalCAR
import NCG.Grand.ExactSourceSchurResidual

/-!
# Branch-complete one-doublet classification

This file completes the non-CAR clauses of `thm:SMST-monoidal-CAR`: the exact
two-slot Hilbert–Schmidt decomposition, the weak Schmidt line, the odd
provenance residual, and the rank-one conclusion for the complete microscopic
coefficient map.
-/

namespace NCG

open scoped BigOperators

/-- Algebraic Hilbert–Schmidt square.  It is real and nonnegative, but keeping
it in `ℂ` makes the finite Pythagorean calculation purely algebraic. -/
noncomputable def matrixHilbertSchmidtSquare {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℂ :=
  ∑ q : m × n, star (A q.1 q.2) * A q.1 q.2

private theorem complexStarMulSelf_eq_normSq (z : ℂ) :
    star z * z = (Complex.normSq z : ℂ) := by
  rw [show (star z : ℂ) = (starRingEnd ℂ) z from rfl,
    mul_comm ((starRingEnd ℂ) z) z]
  exact Complex.mul_conj z

theorem scalarSignedDiagonalPythagoras (a₁ a₂ σ : ℂ)
    (hσstar : star σ = σ) (hσsq : σ * σ = 1) :
    let g := (a₁ + σ * a₂) / 2
    star (a₁ - g) * (a₁ - g) +
        star (a₂ - σ * g) * (a₂ - σ * g) =
      (1 / 2 : ℂ) * star (a₁ - σ * a₂) * (a₁ - σ * a₂) := by
  dsimp
  simp only [map_sub, map_div₀, map_add, map_mul, map_ofNat]
  change (starRingEnd ℂ) σ = σ at hσstar
  rw [hσstar]
  field_simp
  have hσsq' : σ ^ 2 = 1 := by simpa [pow_two] using hσsq
  have hσcube : σ ^ 3 = σ := by
    calc
      σ ^ 3 = σ ^ 2 * σ := by ring
      _ = σ := by rw [hσsq', one_mul]
  have hσfour : σ ^ 4 = 1 := by
    calc
      σ ^ 4 = σ ^ 2 * σ ^ 2 := by ring
      _ = 1 := by rw [hσsq', one_mul]
  ring_nf
  rw [hσsq', hσcube, hσfour]
  ring

/-- Projection of the two slot coefficients onto the signed diagonal weak
line gives exactly one half of the signed slot mismatch. -/
theorem signedSlotHilbertSchmidtPythagoras {m n : Type*}
    [Fintype m] [Fintype n]
    (a₁ a₂ : Matrix m n ℂ) (σ : ℂ)
    (hσstar : star σ = σ) (hσsq : σ * σ = 1) :
    let g := (2 : ℂ)⁻¹ • (a₁ + σ • a₂)
    matrixHilbertSchmidtSquare (a₁ - g) +
        matrixHilbertSchmidtSquare (a₂ - σ • g) =
      (1 / 2 : ℂ) * matrixHilbertSchmidtSquare (a₁ - σ • a₂) := by
  dsimp
  unfold matrixHilbertSchmidtSquare
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ _
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  convert scalarSignedDiagonalPythagoras (a₁ i j) (a₂ i j) σ
    hσstar hσsq using 1 <;> norm_num <;> ring_nf

/-- The connected orthogonal summand simply adds to the exact signed-slot
Pythagorean identity. -/
theorem connectedAndSignedSlotHilbertSchmidtPythagoras
    {r s m n : Type*} [Fintype r] [Fintype s] [Fintype m] [Fintype n]
    (R : Matrix r s ℂ) (a₁ a₂ : Matrix m n ℂ) (σ : ℂ)
    (hσstar : star σ = σ) (hσsq : σ * σ = 1) :
    let g := (2 : ℂ)⁻¹ • (a₁ + σ • a₂)
    matrixHilbertSchmidtSquare R +
        matrixHilbertSchmidtSquare (a₁ - g) +
        matrixHilbertSchmidtSquare (a₂ - σ • g) =
      matrixHilbertSchmidtSquare R +
        (1 / 2 : ℂ) * matrixHilbertSchmidtSquare (a₁ - σ • a₂) := by
  dsimp
  rw [add_assoc, signedSlotHilbertSchmidtPythagoras a₁ a₂ σ hσstar hσsq]

/-- The normalized weak Schmidt line `(e₁ + σe₂)/√2`. -/
noncomputable def signedWeakSchmidtLine (σ : ℂ) :
    Matrix (Fin 2) (Fin 1) ℂ :=
  fun i _ => if i = 0 then (Real.sqrt 2 : ℂ)⁻¹
    else σ * (Real.sqrt 2 : ℂ)⁻¹

theorem signedWeakSchmidtLine_norm_one (σ : ℂ)
    (hσnorm : Complex.normSq σ = 1) :
    matrixHilbertSchmidtSquare (signedWeakSchmidtLine σ) = 1 := by
  unfold matrixHilbertSchmidtSquare signedWeakSchmidtLine
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, Finset.univ_unique,
    Finset.sum_singleton, Fin.mk_one, one_ne_zero,
    map_inv₀, Complex.conj_ofReal, map_mul]
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  rw [complexStarMulSelf_eq_normSq, complexStarMulSelf_eq_normSq,
    Complex.normSq_inv, Complex.normSq_mul, hσnorm,
    Complex.normSq_inv, Complex.normSq_ofReal]
  norm_num [hsqrt]

/-- Scalar odd provenance residual obtained by tracing the exact source Schur
residual. -/
noncomputable def oddProvenanceDefect {h e k : ℕ}
    (selected : Matrix (Fin h) (Fin e) ℂ)
    (complete : Matrix (Fin h) (Fin k) ℂ) : ℂ :=
  (sourceSchurResidual selected complete).trace

/-- The displayed odd provenance defect vanishes exactly when every complete
odd coefficient lies in the selected-phase tangent span. -/
theorem oddProvenanceDefect_eq_zero_iff_rangeIncluded {h e k : ℕ}
    (selected : Matrix (Fin h) (Fin e) ℂ)
    (complete : Matrix (Fin h) (Fin k) ℂ) :
    oddProvenanceDefect selected complete = 0 ↔
      SourceRangeIncluded complete selected := by
  have hpsd := sourceSchurResidual_posSemidef selected complete
  rw [oddProvenanceDefect, hpsd.trace_eq_zero_iff,
    sourceSchurResidual_eq_zero_iff_rangeIncluded]

/-- If all selected primitive tangents share one weak Schmidt line and the odd
provenance residual vanishes, the complete microscopic one-leg coefficient
map factors through that line and therefore has rank at most one. -/
theorem zeroOddProvenance_commonWeakLine_rankOne {h e k : ℕ}
    (line : Matrix (Fin h) (Fin 1) ℂ)
    (selected : Matrix (Fin h) (Fin e) ℂ)
    (complete : Matrix (Fin h) (Fin k) ℂ)
    (hline : ∃ coefficients : Matrix (Fin 1) (Fin e) ℂ,
      selected = line * coefficients)
    (hzero : oddProvenanceDefect selected complete = 0) :
    ∃ coefficients : Matrix (Fin 1) (Fin k) ℂ,
      complete = line * coefficients ∧ complete.rank ≤ 1 := by
  obtain ⟨selectedCoefficients, rfl⟩ := hline
  obtain ⟨T, hT⟩ :=
    (oddProvenanceDefect_eq_zero_iff_rangeIncluded
      (line * selectedCoefficients) complete).mp hzero
  refine ⟨selectedCoefficients * T, ?_, ?_⟩
  · rw [hT, Matrix.mul_assoc]
  · rw [hT, Matrix.mul_assoc]
    calc
      (line * (selectedCoefficients * T)).rank ≤ line.rank :=
        Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_width _
      _ = 1 := by simp

end NCG
