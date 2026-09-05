import NCG.Grand.GeneralRandomScanTensorGap

/-!
# Actual tensor-product random-scan operator

`GeneralRandomScanTensorGap` computed the diagonal spectrum.  This file closes
the remaining fidelity gap by constructing the local tensor lift itself.  A
matrix entry of `Cᵢ` is the one-cell entry at coordinate `i`, provided every
other tensor coordinate agrees.  For a diagonalized positive one-cell
transfer, the uniform average is proved equal—not merely analogous—to the
previous spectral operator, so its compressed norm formula applies to the
actual tensor update.
-/

open Matrix Finset
open scoped BigOperators Norms.L2Operator

namespace NCG.RandomScanTensorOperator

/-- The actual one-cell operator `Cᵢ` on the product basis: coordinate `i` is
updated by `C` and every other coordinate is retained. -/
noncomputable def localTensorUpdate
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (C : Matrix cell cell ℝ) {N : ℕ} (i : Fin N) :
    Matrix (Fin N → cell) (Fin N → cell) ℝ := by
  classical
  exact fun cfg cfg' =>
    if ∀ j, j ≠ i → cfg j = cfg' j then C (cfg i) (cfg' i) else 0

/-- One uniformly selected tensor coordinate is updated at a global step. -/
noncomputable def randomScanTensorOperator
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (C : Matrix cell cell ℝ) (N : ℕ) :
    Matrix (Fin N → cell) (Fin N → cell) ℝ :=
  (N : ℝ)⁻¹ • ∑ i : Fin N, localTensorUpdate C i

/-- The tensor lift of a diagonal one-cell operator is the diagonal operator
whose product-basis eigenvalue reads the selected coordinate. -/
theorem localTensorUpdate_diagonal
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (w : cell → ℝ) {N : ℕ} (i : Fin N) :
    localTensorUpdate (Matrix.diagonal w) i =
      Matrix.diagonal (fun cfg : Fin N → cell => w (cfg i)) := by
  classical
  ext cfg cfg'
  by_cases hcfg : cfg = cfg'
  · subst cfg'
    simp [localTensorUpdate]
  · by_cases hi : cfg i = cfg' i
    · have hrest : ¬ ∀ j, j ≠ i → cfg j = cfg' j := by
        intro hall
        apply hcfg
        funext j
        by_cases hj : j = i
        · simpa [hj] using hi
        · exact hall j hj
      simp [localTensorUpdate, hcfg, hi, hrest, Matrix.diagonal_apply]
    · simp [localTensorUpdate, hcfg, hi, Matrix.diagonal_apply]

/-- The average of the actual local tensor lifts is exactly the spectral-frame
random-scan matrix used in the norm calculation. -/
theorem randomScanTensorOperator_diagonal
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (w : cell → ℝ) (N : ℕ) :
    randomScanTensorOperator (Matrix.diagonal w) N =
      NCG.randomScanSpectralOperator w N := by
  classical
  unfold randomScanTensorOperator NCG.randomScanSpectralOperator
  simp_rw [localTensorUpdate_diagonal]
  ext cfg cfg'
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  by_cases hcfg : cfg = cfg'
  · subst cfg'
    simp [NCG.randomScanEigenvalue, div_eq_mul_inv, mul_comm]
  · simp [Matrix.diagonal_apply, hcfg]

/-- Exact compressed norm formula for the actual tensor random-scan operator
in the one-cell eigenbasis. -/
theorem actual_randomScan_compressedNorm
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (fixedSet : Finset cell) (w : cell → ℝ) (q : ℝ)
    (hw0 : ∀ c, 0 ≤ w c) (hw1 : ∀ c, w c ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (fixed transient : cell) (hfixedMem : fixed ∈ fixedSet)
    (htransientMem : transient ∉ fixedSet) (hfixed : w fixed = 1)
    (htransient : w transient = q)
    (hqmax : ∀ c, c ∉ fixedSet → w c ≤ q)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(1 - NCG.randomScanFixedProductProjection fixedSet N) *
        randomScanTensorOperator (Matrix.diagonal w) N *
        (1 - NCG.randomScanFixedProductProjection fixedSet N)‖ =
      1 - (1 - q) / N := by
  rw [randomScanTensorOperator_diagonal]
  exact NCG.generalRandomScan_compressedNorm fixedSet w q hw0 hw1 hq0 hq1
    fixed transient hfixedMem htransientMem hfixed htransient hqmax N hN

/-- The exact gap is `(1-q)/N`, hence it tends to zero under the fixed-rate
global random-scan clock. -/
theorem randomScan_gap_tends_to_zero (q : ℝ) :
    Filter.Tendsto (fun N : ℕ => (1 - q) / (N + 1 : ℝ)) Filter.atTop (nhds 0) := by
  have hN : Filter.Tendsto (fun N : ℕ => (N + 1 : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1)))
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hN) :
      Filter.Tendsto (fun N : ℕ => (1 - q) * (N + 1 : ℝ)⁻¹)
        Filter.atTop (nhds ((1 - q) * 0)))

/-- Bundled countertheorem, including the actual tensor construction and the
collapse of the global spectral gap. -/
theorem random_scan_scheduling_closes_independent_local_gaps
    {cell : Type*} [Fintype cell] [DecidableEq cell]
    (fixedSet : Finset cell) (w : cell → ℝ) (q : ℝ)
    (hw0 : ∀ c, 0 ≤ w c) (hw1 : ∀ c, w c ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (fixed transient : cell) (hfixedMem : fixed ∈ fixedSet)
    (htransientMem : transient ∉ fixedSet) (hfixed : w fixed = 1)
    (htransient : w transient = q)
    (hqmax : ∀ c, c ∉ fixedSet → w c ≤ q) :
    (∀ N : ℕ, 1 ≤ N →
      ‖(1 - NCG.randomScanFixedProductProjection fixedSet N) *
          randomScanTensorOperator (Matrix.diagonal w) N *
          (1 - NCG.randomScanFixedProductProjection fixedSet N)‖ =
        1 - (1 - q) / N) ∧
      Filter.Tendsto (fun N : ℕ => (1 - q) / (N + 1 : ℝ))
        Filter.atTop (nhds 0) := by
  refine ⟨fun N hN => ?_, randomScan_gap_tends_to_zero q⟩
  exact actual_randomScan_compressedNorm fixedSet w q hw0 hw1 hq0 hq1
    fixed transient hfixedMem htransientMem hfixed htransient hqmax N hN

end NCG.RandomScanTensorOperator
