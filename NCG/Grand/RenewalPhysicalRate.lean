import NCG.Grand.PhysicalRate

/-! # physical-time rate consequences -/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- `thm:renewal-physical-rate`, assembled norm estimates and the exact
finite compact-window bound underlying the manuscript's little-`o` passage. -/
theorem renewal_physical_rate_exact
    {H E : Type*} [Fintype H] [Fintype E]
    [DecidableEq H] [DecidableEq E]
    (T : Matrix H H ℂ) (V : Matrix H E ℂ) (W : Matrix E E ℂ)
    (lam lam' τ ε horizon : ℝ)
    (hT : ‖T‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    (hVstar : ‖Vᴴ‖ ≤ 1)
    (hVW : ‖V * W‖ ≤ Real.exp (-(lam * τ)))
    (hres : ‖T * V - V * W‖ ≤ ε)
    (hε : 0 ≤ ε) (hτ : 0 < τ) (hhorizon : 0 ≤ horizon) :
    ‖T * V‖ ≤ Real.exp (-(lam * τ)) + ε
      ∧ ‖Vᴴ * T * V‖ ≤ Real.exp (-(lam * τ)) + ε
      ∧ (ε ≤ Real.exp (-(lam' * τ)) - Real.exp (-(lam * τ)) →
          ‖T * V‖ ≤ Real.exp (-(lam' * τ))
            ∧ ‖Vᴴ * T * V‖ ≤ Real.exp (-(lam' * τ)))
      ∧ (∀ n : ℕ, ‖T ^ n * V - V * W ^ n‖ ≤ n * ε)
      ∧ (∀ n : ℕ, (n : ℝ) * τ ≤ horizon + τ →
          (n : ℝ) * ε ≤ (horizon + τ) * (ε / τ)) := by
  have hbase := renewal_physical_rate T V W hT hW
  have hTV : ‖T * V‖ ≤ Real.exp (-(lam * τ)) + ε :=
    le_trans hbase.1 (add_le_add hVW hres)
  have hK : ‖Vᴴ * T * V‖ ≤ Real.exp (-(lam * τ)) + ε := by
    calc
      ‖Vᴴ * T * V‖ = ‖Vᴴ * (T * V)‖ := by
        rw [Matrix.mul_assoc]
      _ ≤ ‖Vᴴ‖ * ‖T * V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * (Real.exp (-(lam * τ)) + ε) := by
        exact mul_le_mul hVstar hTV (norm_nonneg _)
          (by positivity)
      _ = Real.exp (-(lam * τ)) + ε := one_mul _
  refine ⟨hTV, hK, ?_, ?_, ?_⟩
  · intro hbudget
    constructor <;> linarith
  · intro n
    exact le_trans (hbase.2 n)
      (mul_le_mul_of_nonneg_left hres (Nat.cast_nonneg n))
  · intro n hn
    have hratio : 0 ≤ ε / τ := div_nonneg hε hτ.le
    have hmul := mul_le_mul_of_nonneg_right hn hratio
    have heq : (n : ℝ) * τ * (ε / τ) = (n : ℝ) * ε := by
      field_simp
    rw [heq] at hmul
    exact hmul

end NCG
