/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.PositiveHeadTailEnclosure
import NCG.Upstream.FlagshipEasy
import NCG.Upstream.SemigroupLimit

/-!
# Regulated neutral-sector transfer contraction and mass gap

This file proves the operator and Hamiltonian clauses of the regulated
Yang--Mills criterion.  A positive head--tail transfer block is compared with
its two-dimensional scalar envelope.  The tail defect and mixing inequality
make the resulting `qReg` strictly smaller than one.  When the transfer is
`exp (-tau H)`, spectral mapping turns the same contraction estimate into a
strictly positive lower bound for every Hamiltonian eigenvalue.
-/

open Matrix Real
open scoped ComplexOrder Norms.L2Operator

namespace NCG

/-- Replacing the tail norm by its upper bound `1 - mu` can only increase the
sharp two-by-two comparison eigenvalue. -/
lemma head_tail_comparison_le_qReg (a b d mu : ℝ) (hd : d ≤ 1 - mu) :
    (a + d + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2 ≤ qReg a mu b := by
  obtain ⟨hqa, hqc, hroot⟩ := qReg_root a mu b
  set q := qReg a mu b with hq
  have hqd : d ≤ q := le_trans hd hqc
  have hright : 0 ≤ 2 * q - a - d := by linarith
  have hrad : 0 ≤ (a - d) ^ 2 + 4 * b ^ 2 := by positivity
  have hsquare :
      (a - d) ^ 2 + 4 * b ^ 2 ≤ (2 * q - a - d) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqa) (sub_nonneg.mpr (le_trans hd hqc))]
  have hsqrt : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) ≤ 2 * q - a - d := by
    rw [← Real.sqrt_sq hright]
    exact Real.sqrt_le_sqrt hsquare
  linarith

/-- Exact regulated contraction criterion for a positive head--tail transfer
block. -/
theorem regulated_neutral_sector_contraction {h t : Type*}
    [Fintype h] [Fintype t] [DecidableEq h] [DecidableEq t]
    (A : Matrix h h ℂ) (B : Matrix h t ℂ) (D : Matrix t t ℂ)
    (mu : ℝ) (hT : (Matrix.fromBlocks A B Bᴴ D).PosSemidef)
    (hmu : 0 < mu) (hD : ‖D‖ ≤ 1 - mu) (hA : ‖A‖ < 1)
    (hB : ‖B‖ ^ 2 < (1 - ‖A‖) * mu) :
    ‖Matrix.fromBlocks A B Bᴴ D‖ ≤ qReg ‖A‖ mu ‖B‖ ∧
      qReg ‖A‖ mu ‖B‖ < 1 := by
  constructor
  · exact (sharp_positive_head_tail_opNorm A B D hT).trans
      (head_tail_comparison_le_qReg ‖A‖ ‖B‖ ‖D‖ mu hD)
  · exact qReg_lt_one ‖A‖ mu ‖B‖ hA hmu hB

/-- A positive transfer eigenvalue inherits the logarithmic gap bound from
the regulated block contraction. -/
theorem regulated_transfer_eigenvalue_gap {h t : Type*}
    [Fintype h] [Fintype t] [DecidableEq h] [DecidableEq t]
    (A : Matrix h h ℂ) (B : Matrix h t ℂ) (D : Matrix t t ℂ)
    (mu tau eig : ℝ) (x : h ⊕ t → ℂ)
    (hT : (Matrix.fromBlocks A B Bᴴ D).PosSemidef)
    (hmu : 0 < mu) (hD : ‖D‖ ≤ 1 - mu) (hA : ‖A‖ < 1)
    (hB : ‖B‖ ^ 2 < (1 - ‖A‖) * mu) (htau : 0 < tau)
    (hx : x ≠ 0)
    (heig : Matrix.fromBlocks A B Bᴴ D *ᵥ x = (eig : ℂ) • x)
    (heigpos : 0 < eig) :
    -Real.log (qReg ‖A‖ mu ‖B‖) / tau ≤ -Real.log eig / tau ∧
      0 < -Real.log (qReg ‖A‖ mu ‖B‖) / tau := by
  obtain ⟨hTq, _⟩ := regulated_neutral_sector_contraction A B D mu hT hmu hD hA hB
  have hmul := Matrix.l2_opNorm_mulVec (Matrix.fromBlocks A B Bᴴ D)
    (WithLp.toLp 2 x)
  have hxnorm : 0 < ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (h ⊕ t))‖ :=
    norm_pos_iff.mpr (by simpa using hx)
  have heignorm :
      ‖(WithLp.toLp 2 ((eig : ℂ) • x) : EuclideanSpace ℂ (h ⊕ t))‖ =
        eig * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (h ⊕ t))‖ := by
    rw [WithLp.toLp_smul, norm_smul]
    simp [abs_of_pos heigpos]
  change ‖(WithLp.toLp 2
      (Matrix.fromBlocks A B Bᴴ D *ᵥ x) : EuclideanSpace ℂ (h ⊕ t))‖ ≤
        ‖Matrix.fromBlocks A B Bᴴ D‖ *
          ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (h ⊕ t))‖ at hmul
  rw [heig, heignorm] at hmul
  have heigq : eig ≤ qReg ‖A‖ mu ‖B‖ := by
    have : eig ≤ ‖Matrix.fromBlocks A B Bᴴ D‖ := by
      nlinarith
    exact this.trans hTq
  exact qReg_gap_positive ‖A‖ mu ‖B‖ tau eig hA hmu hB htau heigpos heigq

/-- Spectral mapping for `T = exp (-tau H)` upgrades the transfer contraction
to the manuscript's Hamiltonian mass-gap estimate. -/
theorem regulated_hamiltonian_eigenvalue_gap {h t : Type*}
    [Fintype h] [Fintype t] [DecidableEq h] [DecidableEq t]
    (A : Matrix h h ℂ) (B : Matrix h t ℂ) (D : Matrix t t ℂ)
    (H : EuclideanSpace ℂ (h ⊕ t) →L[ℂ] EuclideanSpace ℂ (h ⊕ t))
    (mu tau lambda : ℝ) (x : EuclideanSpace ℂ (h ⊕ t))
    (hT : (Matrix.fromBlocks A B Bᴴ D).PosSemidef)
    (hmu : 0 < mu) (hD : ‖D‖ ≤ 1 - mu) (hA : ‖A‖ < 1)
    (hB : ‖B‖ ^ 2 < (1 - ‖A‖) * mu) (htau : 0 < tau)
    (hx : x ≠ 0) (hHx : H x = (lambda : ℂ) • x)
    (htransfer : Matrix.toEuclideanCLM (𝕜 := ℂ)
      (Matrix.fromBlocks A B Bᴴ D) = NormedSpace.exp ((-tau) • H)) :
    -Real.log (qReg ‖A‖ mu ‖B‖) / tau ≤ lambda ∧
      0 < -Real.log (qReg ‖A‖ mu ‖B‖) / tau := by
  have hmap := Upstream.exp_smul_eigen hHx (-tau)
  have hTx : Matrix.fromBlocks A B Bᴴ D *ᵥ WithLp.ofLp x =
      (Real.exp (-tau * lambda) : ℂ) • WithLp.ofLp x := by
    apply WithLp.toLp_injective 2
    change Matrix.toEuclideanCLM (𝕜 := ℂ)
      (Matrix.fromBlocks A B Bᴴ D) x =
        (Real.exp (-tau * lambda) : ℂ) • x
    rw [htransfer]
    simpa only [neg_mul] using hmap
  have hgap := regulated_transfer_eigenvalue_gap A B D mu tau
    (Real.exp (-tau * lambda)) (WithLp.ofLp x) hT hmu hD hA hB htau
    (by simpa using hx) hTx (Real.exp_pos _)
  rw [Real.log_exp] at hgap
  constructor
  · calc
      -Real.log (qReg ‖A‖ mu ‖B‖) / tau ≤
          -(-tau * lambda) / tau := hgap.1
      _ = lambda := by field_simp
  · exact hgap.2

end NCG
