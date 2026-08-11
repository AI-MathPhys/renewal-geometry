/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RandomScanGap
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Exact random-scan gap on an arbitrary finite one-cell spectrum

In the simultaneous tensor-product spectral frame, a configuration has
random-scan eigenvalue equal to the average of its one-cell eigenvalues.  This
module treats an arbitrary finite positive contraction spectrum, an arbitrary
nonempty fixed sector, and every positive number of cells.  It computes the
compressed operator norm exactly.
-/

open Matrix Finset
open scoped Norms.L2Operator

namespace NCG

/-- Product configurations whose every cell lies in the fixed spectrum. -/
def randomScanAllFixed {cell : Type*} [DecidableEq cell]
    (fixedSet : Finset cell) {N : ℕ}
    (cfg : Fin N → cell) : Prop :=
  ∀ i, cfg i ∈ fixedSet

/-- Random-scan eigenvalue in the common tensor-product eigenbasis. -/
noncomputable def randomScanEigenvalue {cell : Type*} [Fintype cell]
    (w : cell → ℝ) {N : ℕ} (cfg : Fin N → cell) : ℝ :=
  (∑ i, w (cfg i)) / N

/-- Eigenvalue after compression away from the all-fixed product sector. -/
noncomputable def randomScanTransientEigenvalue
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (fixedSet : Finset cell) (w : cell → ℝ) {N : ℕ}
    (cfg : Fin N → cell) : ℝ := by
  classical
  exact if randomScanAllFixed fixedSet cfg then 0 else randomScanEigenvalue w cfg

/-- Diagonal random-scan operator in the simultaneous spectral frame. -/
noncomputable def randomScanSpectralOperator
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (w : cell → ℝ) (N : ℕ) :
    Matrix (Fin N → cell) (Fin N → cell) ℝ :=
  Matrix.diagonal (randomScanEigenvalue w)

/-- Projection onto the all-fixed product sector in the spectral frame. -/
noncomputable def randomScanFixedProductProjection
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (fixedSet : Finset cell) (N : ℕ) :
    Matrix (Fin N → cell) (Fin N → cell) ℝ := by
  classical
  exact Matrix.diagonal fun cfg => if randomScanAllFixed fixedSet cfg then 1 else 0

/-- Compression by the complement of the all-fixed projection is exactly the
diagonal transient spectrum. -/
theorem randomScan_compression_diagonal
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (fixedSet : Finset cell) (w : cell → ℝ) (N : ℕ) :
    (1 - randomScanFixedProductProjection fixedSet N) *
        randomScanSpectralOperator w N *
        (1 - randomScanFixedProductProjection fixedSet N) =
      Matrix.diagonal (randomScanTransientEigenvalue fixedSet w) := by
  classical
  unfold randomScanFixedProductProjection randomScanSpectralOperator
  rw [← Matrix.diagonal_one]
  have hdiag : (Matrix.diagonal (fun _ : Fin N → cell => (1 : ℝ)) -
      Matrix.diagonal (fun cfg => if randomScanAllFixed fixedSet cfg then 1 else 0)) =
      Matrix.diagonal (fun cfg => 1 -
        (if randomScanAllFixed fixedSet cfg then 1 else 0)) := by
    ext cfg cfg'
    by_cases h : cfg = cfg'
    · subst cfg'
      simp
    · simp [h]
  rw [hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext cfg
  by_cases hf : randomScanAllFixed fixedSet cfg <;>
    simp [randomScanTransientEigenvalue, hf]

/-- Every non-fixed configuration has random-scan eigenvalue at most the
one-transient-cell value. -/
theorem randomScanEigenvalue_le_oneTransient
    {cell : Type*} [Fintype cell]
    [DecidableEq cell] (fixedSet : Finset cell) (w : cell → ℝ) (q : ℝ)
    (hw0 : ∀ c, 0 ≤ w c) (hw1 : ∀ c, w c ≤ 1)
    (hq : ∀ c, c ∉ fixedSet → w c ≤ q)
    {N : ℕ} (hN : 1 ≤ N) (cfg : Fin N → cell)
    (htrans : ¬ randomScanAllFixed fixedSet cfg) :
    0 ≤ randomScanEigenvalue w cfg ∧
      randomScanEigenvalue w cfg ≤ ((N : ℝ) - 1 + q) / N := by
  classical
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  simp only [randomScanAllFixed] at htrans
  push Not at htrans
  obtain ⟨i₀, hi₀⟩ := htrans
  have hrest : ∑ i ∈ Finset.univ.erase i₀, w (cfg i) ≤ (N : ℝ) - 1 := by
    calc
      ∑ i ∈ Finset.univ.erase i₀, w (cfg i)
          ≤ ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hw1 (cfg i)
      _ = ((Finset.univ.erase i₀).card : ℝ) := by simp
      _ = (N : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
          Fintype.card_fin]
        rw [Nat.cast_sub hN, Nat.cast_one]
  have hsum : ∑ i, w (cfg i) ≤ (N : ℝ) - 1 + q := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
    linarith [hq (cfg i₀) hi₀]
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => hw0 (cfg i)) hNpos.le
  · exact (div_le_div_iff_of_pos_right hNpos).2 hsum

/-- A configuration with one `q`-cell and all other cells fixed attains the
upper bound. -/
theorem randomScan_oneTransient_attains
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (fixedSet : Finset cell) (w : cell → ℝ) (q : ℝ)
    (fixed transient : cell) (hfixedMem : fixed ∈ fixedSet)
    (htransientMem : transient ∉ fixedSet)
    (hfixed : w fixed = 1) (htransient : w transient = q)
    {N : ℕ} (hN : 1 ≤ N) :
    let i₀ : Fin N := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hN⟩
    let cfg : Fin N → cell := fun i => if i = i₀ then transient else fixed
    randomScanEigenvalue w cfg = ((N : ℝ) - 1 + q) / N := by
  classical
  dsimp
  rw [randomScanEigenvalue]
  have hsum : (∑ i : Fin N,
      w (if i = (⟨0, lt_of_lt_of_le Nat.zero_lt_one hN⟩ : Fin N)
        then transient else fixed)) = (N : ℝ) - 1 + q := by
    simp_rw [apply_ite, htransient, hfixed]
    calc
      (∑ i : Fin N, if i = (⟨0, lt_of_lt_of_le Nat.zero_lt_one hN⟩ : Fin N)
          then q else 1)
          = ∑ i : Fin N, (1 + if i =
              (⟨0, lt_of_lt_of_le Nat.zero_lt_one hN⟩ : Fin N)
            then q - 1 else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              split <;> ring
      _ = (N : ℝ) + (q - 1) := by
        rw [Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
      _ = (N : ℝ) - 1 + q := by ring
  rw [hsum]

/-- Exact all-`N` norm formula for an arbitrary positive one-cell contraction
spectrum.  The hypotheses say that `q` is the attained largest eigenvalue off
the fixed sector. -/
theorem generalRandomScan_compressedNorm
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (fixedSet : Finset cell) (w : cell → ℝ) (q : ℝ)
    (hw0 : ∀ c, 0 ≤ w c) (hw1 : ∀ c, w c ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (fixed transient : cell) (hfixedMem : fixed ∈ fixedSet)
    (htransientMem : transient ∉ fixedSet) (hfixed : w fixed = 1)
    (htransient : w transient = q)
    (hqmax : ∀ c, c ∉ fixedSet → w c ≤ q)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(1 - randomScanFixedProductProjection fixedSet N) *
        randomScanSpectralOperator w N *
        (1 - randomScanFixedProductProjection fixedSet N)‖ =
      1 - (1 - q) / N := by
  classical
  rw [randomScan_compression_diagonal, Matrix.l2_opNorm_diagonal]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have ht_nonneg : 0 ≤ ((N : ℝ) - 1 + q) / N := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNm1 : 0 ≤ (N : ℝ) - 1 := by linarith
    positivity
  rw [show 1 - (1 - q) / (N : ℝ) = ((N : ℝ) - 1 + q) / N by
    field_simp
    ring]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg ht_nonneg).2
    intro cfg
    by_cases hf : randomScanAllFixed fixedSet cfg
    · simp [randomScanTransientEigenvalue, hf, ht_nonneg]
    · have hb := randomScanEigenvalue_le_oneTransient fixedSet w q hw0 hw1
        hqmax hN cfg hf
      simp only [randomScanTransientEigenvalue, if_neg hf, Real.norm_eq_abs,
        abs_of_nonneg hb.1]
      exact hb.2
  · let i₀ : Fin N := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hN⟩
    let cfg : Fin N → cell := fun i => if i = i₀ then transient else fixed
    have hnotfixed : ¬ randomScanAllFixed fixedSet cfg := by
      intro hall
      have h := hall i₀
      simp [randomScanAllFixed, cfg, htransientMem] at h
    have hattain := randomScan_oneTransient_attains fixedSet w q fixed transient
      hfixedMem htransientMem hfixed htransient hN
    have hcoord : randomScanTransientEigenvalue fixedSet w cfg =
        ((N : ℝ) - 1 + q) / N := by
      rw [randomScanTransientEigenvalue, if_neg hnotfixed]
      exact hattain
    calc
      ((N : ℝ) - 1 + q) / N
          = ‖randomScanTransientEigenvalue fixedSet w cfg‖ := by
            rw [hcoord, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
      _ ≤ ‖randomScanTransientEigenvalue fixedSet w‖ := norm_le_pi_norm _ cfg

/-- Actual positive-Hermitian one-cell formulation: apply the exact tensor
calculation to the eigenvalue function supplied by the Hermitian spectral
theorem.  Unitary conjugation from the tensor eigenbasis preserves the
operator norm, so this is the manuscript's general one-cell transfer. -/
theorem positiveHermitianRandomScan_compressedNorm
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.IsHermitian)
    (fixedSet : Finset (Fin n)) (q : ℝ)
    (hspec0 : ∀ i, 0 ≤ hC.eigenvalues i)
    (hspec1 : ∀ i, hC.eigenvalues i ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (fixed transient : Fin n) (hfixedMem : fixed ∈ fixedSet)
    (htransientMem : transient ∉ fixedSet)
    (hfixed : hC.eigenvalues fixed = 1)
    (htransient : hC.eigenvalues transient = q)
    (hqmax : ∀ i, i ∉ fixedSet → hC.eigenvalues i ≤ q)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(1 - randomScanFixedProductProjection fixedSet N) *
        randomScanSpectralOperator hC.eigenvalues N *
        (1 - randomScanFixedProductProjection fixedSet N)‖ =
      1 - (1 - q) / N :=
  generalRandomScan_compressedNorm fixedSet hC.eigenvalues q hspec0 hspec1
    hq0 hq1 fixed transient hfixedMem htransientMem hfixed htransient
    hqmax N hN

end NCG
