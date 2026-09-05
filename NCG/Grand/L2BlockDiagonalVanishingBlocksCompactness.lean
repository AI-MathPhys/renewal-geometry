import NCG.Grand.L2BlockDiagonalCompactness

/-!
# Compactness of block-diagonal operators with vanishing blocks

A block-diagonal operator on `ℓ²(ℕ,E)` is compact when the fibre is
finite-dimensional and the block operator norms tend to zero.  The proof is
the canonical finite-coordinate compression argument.
-/

noncomputable section

open Filter Topology
open scoped lp

namespace NCG

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [FiniteDimensional ℂ E]

/-- A block-diagonal operator with block norms tending to zero is compact. -/
theorem IsL2BlockDiagonal.isCompactOperator_of_tendsto_norm_atTop_zero
    {T : ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E)} {M : ℕ → E →L[ℂ] E}
    (hdiag : IsL2BlockDiagonal T M)
    (hzero : Tendsto (fun n ↦ ‖M n‖) atTop (𝓝 0)) :
    IsCompactOperator (T : ℓ²(ℕ, E) → ℓ²(ℕ, E)) := by
  apply isCompactOperator_of_finsetScreen_compression_approx_arbitrarily
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hzero) (ε / 2) hε2
  refine ⟨Finset.range N, ?_⟩
  have htail := hdiag.norm_sub_screenCompression_le_of_outside
    (Finset.range N) (ε / 2) hε2.le (fun i hi x ↦ by
      have hiN : N ≤ i := by simpa using hi
      have hMi : ‖M i‖ < ε / 2 := by
        have := hN i hiN
        simpa [Real.dist_eq] using this
      exact (ContinuousLinearMap.le_opNorm (M i) x).trans
        (mul_le_mul_of_nonneg_right hMi.le (norm_nonneg x)))
  exact htail.trans_lt (by linarith)

end NCG
