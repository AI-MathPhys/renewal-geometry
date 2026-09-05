import NCG.Grand.L2BlockDiagonalScreens

/-!
# Norm convergence of block-diagonal `ℓ²` operators from finite screens

Uniform convergence of the blocks on every fixed finite coordinate screen,
together with eventually uniform smallness of the stage and limit blocks off
one sufficiently large screen, implies global operator-norm convergence of
the corresponding block-diagonal operators.
-/

noncomputable section

open Filter Topology
open scoped lp

namespace NCG

variable {ι E : Type*}
variable [DecidableEq ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The finite-box plus tail convergence theorem for arbitrary block-diagonal
operators on an infinite `ℓ²` direct sum. -/
theorem tendsto_l2BlockDiagonal_of_finiteScreens_eventualTails
    (Tn : ℕ → ℓ²(ι, E) →L[ℂ] ℓ²(ι, E))
    (T : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E))
    (Mn : ℕ → ι → E →L[ℂ] E) (M : ι → E →L[ℂ] E)
    (s : ℕ → Finset ι)
    (hdiagN : ∀ n, IsL2BlockDiagonal (Tn n) (Mn n))
    (hdiag : IsL2BlockDiagonal T M)
    (hlocal : ∀ radius (ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop, ∀ i ∈ s radius,
        ‖Mn n i - M i‖ < ε)
    (htail : ∀ ε > 0, ∃ radius,
      (∀ᶠ n in atTop, ∀ i ∉ s radius, ‖Mn n i‖ < ε) ∧
      ∀ i ∉ s radius, ‖M i‖ < ε) :
    Tendsto Tn atTop (𝓝 T) := by
  apply tendsto_operatorNorm_of_screenCompression_eventualTails
    Tn T (fun radius ↦ l2FinsetScreen (E := E) (s radius))
  · intro radius
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlocal radius (ε / 2) hε2)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_eq_norm]
    have hbound := IsL2BlockDiagonal.norm_screenCompression_sub_le_of_inside
      (hdiagN n) hdiag (s radius) (ε / 2) hε2.le
      (fun i hi x ↦ by
        exact (ContinuousLinearMap.le_opNorm (Mn n i - M i) x).trans
          (mul_le_mul_of_nonneg_right (hN n hn i hi).le (norm_nonneg x)))
    exact hbound.trans_lt (by linarith)
  · intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    obtain ⟨radius, htailN, htailLimit⟩ := htail (ε / 2) hε2
    refine ⟨radius, ?_, ?_⟩
    · filter_upwards [htailN] with n hn
      have hbound :=
        IsL2BlockDiagonal.norm_sub_screenCompression_le_of_outside
          (hdiagN n) (s radius) (ε / 2) hε2.le
          (fun i hi x ↦
            (ContinuousLinearMap.le_opNorm (Mn n i) x).trans
              (mul_le_mul_of_nonneg_right (hn i hi).le (norm_nonneg x)))
      exact hbound.trans_lt (by linarith)
    · rw [norm_sub_rev]
      have hbound :=
        IsL2BlockDiagonal.norm_sub_screenCompression_le_of_outside
          hdiag (s radius) (ε / 2) hε2.le
          (fun i hi x ↦
            (ContinuousLinearMap.le_opNorm (M i) x).trans
              (mul_le_mul_of_nonneg_right (htailLimit i hi).le (norm_nonneg x)))
      exact hbound.trans_lt (by linarith)

end NCG
