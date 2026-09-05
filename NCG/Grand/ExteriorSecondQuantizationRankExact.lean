/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExteriorSecondQuantizationUnitaryCovarianceExact

/-!
# Rank of finite exterior second quantization

This file proves the exact rank and source-minimal carrier formulas in
`cor:SMQG-exterior-rank` using the concrete compound-matrix realization of
finite exterior powers.
-/

open Matrix

namespace NCG
namespace ExteriorSecondQuantizationRank

open FiniteCompoundMatrixExteriorPower
open ExteriorSecondQuantizationUnitaryCovariance

variable {d r : ℕ}

/-- The concrete `r`th exterior basis is indexed by the `r`-subsets of a
`d`-element one-particle basis. -/
theorem gradeIdx_card (r d : ℕ) :
    Fintype.card (GradeIdx r d) = d.choose r := by
  classical
  let e : GradeIdx r d ≃
      ↥((Finset.univ : Finset (Fin d)).powersetCard r) :=
    { toFun := fun S => ⟨S.1, Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, S.2⟩⟩
      invFun := fun S => ⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩
      left_inv := fun S => by rfl
      right_inv := fun S => by rfl }
  calc
    Fintype.card (GradeIdx r d) =
        Fintype.card ↥((Finset.univ : Finset (Fin d)).powersetCard r) :=
      Fintype.card_congr e
    _ = ((Finset.univ : Finset (Fin d)).card).choose r := by
      rw [Fintype.card_coe, Finset.card_powersetCard]
    _ = d.choose r := by simp

/-- For a diagonal one-particle operator, the nonzero exterior basis vectors
are exactly the `r`-subsets of its nonzero diagonal coordinates. -/
theorem cmpd_diagonal_rank (v : Fin d → ℂ) :
    (cmpd r (Matrix.diagonal v)).rank =
      (Fintype.card {i // v i ≠ 0}).choose r := by
  classical
  rw [cmpd_diagonal, Matrix.rank_diagonal]
  simp only [Finset.prod_ne_zero_iff]
  let support : Finset (Fin d) := Finset.univ.filter fun i => v i ≠ 0
  let e : {S : GradeIdx r d // ∀ i ∈ S.1, v i ≠ 0} ≃
      ↥(support.powersetCard r) :=
    { toFun := fun S => ⟨S.1.1, by
          rw [Finset.mem_powersetCard]
          exact ⟨fun i hi => by
            simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
            exact S.2 i hi, S.1.2⟩⟩
      invFun := fun S => ⟨⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩,
        fun i hi => by
          have his := (Finset.mem_powersetCard.mp S.2).1 hi
          simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using his⟩
      left_inv := fun S => by rfl
      right_inv := fun S => by rfl }
  calc
    Fintype.card {S : GradeIdx r d // ∀ i ∈ S.1, v i ≠ 0} =
        Fintype.card ↥(support.powersetCard r) := Fintype.card_congr e
    _ = (support.card).choose r := by
      rw [Fintype.card_coe, Finset.card_powersetCard]
    _ = (Fintype.card {i // v i ≠ 0}).choose r := by
      congr 1
      rw [Fintype.card_subtype]

/-- The `r`th exterior power of a Hermitian matrix has rank equal to the
`r`th binomial coefficient of its one-particle rank. -/
theorem cmpd_rank_eq_choose_rank (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (r : ℕ) :
    (cmpd r P).rank = P.rank.choose r := by
  classical
  let U : Matrix (Fin d) (Fin d) ℂ := hP.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)
  have hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    hP.eigenvectorUnitary.property
  have hdec : P = U * D * Uᴴ := by
    have h := hP.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [U, D, Matrix.star_eq_conjTranspose] using h
  calc
    (cmpd r P).rank = (cmpd r (U * D * Uᴴ)).rank := by rw [hdec]
    _ = (cmpd r D).rank := by
      simpa only [exteriorGamma] using
        exteriorGamma_unitary_rank D U hU r
    _ = (Fintype.card {i // hP.eigenvalues i ≠ 0}).choose r := by
      rw [cmpd_diagonal_rank]
      simp [D, Function.comp_apply]
    _ = P.rank.choose r := by rw [hP.rank_eq_card_non_zero_eigs]

/-- The rank of the finite fermionic second quantization is the sum of the
ranks of all exterior grades. -/
noncomputable def exteriorGammaRank (P : Matrix (Fin d) (Fin d) ℂ) : ℕ :=
  ∑ r ∈ Finset.range (d + 1), (cmpd r P).rank

/-- Summing the exterior-grade ranks gives the exact Fock-space rank
`2 ^ rank P`. -/
theorem exteriorGammaRank_eq_two_pow_rank (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) :
    exteriorGammaRank P = 2 ^ P.rank := by
  classical
  unfold exteriorGammaRank
  simp_rw [cmpd_rank_eq_choose_rank P hP]
  rw [← Nat.sum_range_choose P.rank]
  symm
  have hrank : P.rank ≤ d := by
    simpa using Matrix.rank_le_card_width P
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hrank))
  intro r hrd hrqr
  have hlt : P.rank < r := by simp only [Finset.mem_range, not_lt] at hrqr; omega
  exact Nat.choose_eq_zero_of_lt hlt

/-- A concrete wedge basis for the source-minimal reflected carrier after
identifying `Ran P` with `ℂ^(rank P)`: the grade is bounded by the rank and
the second component is an `r`-element subset of a rank-sized basis. -/
abbrev SourceMinimalCarrier (P : Matrix (Fin d) (Fin d) ℂ) :=
  Σ r : Fin (P.rank + 1), GradeIdx r P.rank

/-- The source-minimal carrier has exactly `2 ^ rank P` basis vectors. -/
theorem sourceMinimalCarrier_card (P : Matrix (Fin d) (Fin d) ℂ) :
    Fintype.card (SourceMinimalCarrier P) = 2 ^ P.rank := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [gradeIdx_card]
  rw [Fin.sum_univ_eq_sum_range]
  simpa using Nat.sum_range_choose P.rank

/-- **`cor:SMQG-exterior-rank`.**  Exact exterior-grade rank, total
second-quantized rank, and the cardinality of the concrete source-minimal
carrier basis. -/
theorem smqg_exterior_rank (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) :
    (∀ r : ℕ, (cmpd r P).rank = P.rank.choose r) ∧
      exteriorGammaRank P = 2 ^ P.rank ∧
      Fintype.card (SourceMinimalCarrier P) = 2 ^ P.rank := by
  exact ⟨cmpd_rank_eq_choose_rank P hP,
    exteriorGammaRank_eq_two_pow_rank P hP,
    sourceMinimalCarrier_card P⟩

end ExteriorSecondQuantizationRank
end NCG
