import NCG.Grand.L2BlockDiagonalVanishingBlocksCompactness
import NCG.Grand.ToeplitzUnilateralShiftScreenObstructionExact

/-!
# Compact resolvent of the Toeplitz number operator

On `ℓ²(ℕ,ℂ)`, the resolvent of the number operator at `i` is the diagonal
operator with coefficient `(n-i)⁻¹` on the `n`th coordinate.  This file
constructs that bounded operator, proves its blocks vanish at infinity, and
deduces compactness.
-/

noncomputable section

open Filter Topology
open scoped lp

namespace NCG
namespace ToeplitzScreenObstruction

/-- The scalar block `(n-i)⁻¹` of the number-operator resolvent. -/
def numberResolventBlock (n : ℕ) : ℂ →L[ℂ] ℂ :=
  ((n : ℂ) - Complex.I)⁻¹ • (1 : ℂ →L[ℂ] ℂ)

@[simp]
theorem numberResolventBlock_apply (n : ℕ) (z : ℂ) :
    numberResolventBlock n z = ((n : ℂ) - Complex.I)⁻¹ * z := by
  simp [numberResolventBlock, smul_eq_mul]

theorem one_le_norm_natCast_sub_I (n : ℕ) :
    1 ≤ ‖(n : ℂ) - Complex.I‖ := by
  have h := Complex.abs_im_le_norm ((n : ℂ) - Complex.I)
  simpa using h

theorem norm_numberResolventBlock_apply_le (n : ℕ) (z : ℂ) :
    ‖numberResolventBlock n z‖ ≤ 1 * ‖z‖ := by
  rw [numberResolventBlock_apply, norm_mul, norm_inv]
  exact mul_le_mul_of_nonneg_right
    (inv_le_one_of_one_le₀ (one_le_norm_natCast_sub_I n)) (norm_nonneg z)

/-- The bounded diagonal resolvent `(N-i)⁻¹`. -/
def numberResolvent : H →L[ℂ] H :=
  l2BlockDiagonal numberResolventBlock 1 zero_le_one
    norm_numberResolventBlock_apply_le

@[simp]
theorem numberResolvent_apply (f : H) (n : ℕ) :
    numberResolvent f n = ((n : ℂ) - Complex.I)⁻¹ * f n :=
  rfl

theorem numberResolvent_isL2BlockDiagonal :
    IsL2BlockDiagonal numberResolvent numberResolventBlock :=
  fun _ _ ↦ rfl

/-- The resolvent block norms vanish at infinity. -/
theorem tendsto_norm_numberResolventBlock_zero :
    Tendsto (fun n ↦ ‖numberResolventBlock n‖) atTop (𝓝 0) := by
  have hcoeff :
      Tendsto (fun n : ℕ ↦ ‖((n : ℂ) - Complex.I)⁻¹‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    filter_upwards [eventually_atTop.2 ⟨1, fun _ h ↦ h⟩] with n hn
    rw [norm_inv]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hden : (n : ℝ) ≤ ‖(n : ℂ) - Complex.I‖ := by
      have h := Complex.abs_re_le_norm ((n : ℂ) - Complex.I)
      simpa [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)] using h
    exact inv_anti₀ hnpos hden
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hcoeff
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  simp [numberResolventBlock, norm_smul]

/-- The explicit number-operator resolvent is compact. -/
theorem numberResolvent_isCompactOperator :
    IsCompactOperator (numberResolvent : H → H) :=
  IsL2BlockDiagonal.isCompactOperator_of_tendsto_norm_atTop_zero
    numberResolvent_isL2BlockDiagonal tendsto_norm_numberResolventBlock_zero

/-- No diagonal resolvent coefficient vanishes. -/
theorem numberResolvent_coefficient_ne_zero (n : ℕ) :
    ((n : ℂ) - Complex.I)⁻¹ ≠ 0 := by
  apply inv_ne_zero
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- The explicit number-operator resolvent is injective. -/
theorem numberResolvent_injective : Function.Injective numberResolvent := by
  intro f g hfg
  apply lp.ext
  funext n
  have hn : ((n : ℂ) - Complex.I)⁻¹ * f n =
      ((n : ℂ) - Complex.I)⁻¹ * g n := by
    simpa only [numberResolvent_apply] using congrArg (fun u : H ↦ u n) hfg
  exact mul_left_cancel₀ (numberResolvent_coefficient_ne_zero n) hn

end ToeplitzScreenObstruction
end NCG
