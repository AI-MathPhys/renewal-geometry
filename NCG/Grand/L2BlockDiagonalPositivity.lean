/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.L2BlockDiagonal
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positivity of block-diagonal `ℓ²` operators

A uniformly bounded block-diagonal operator on an `ℓ²` direct sum is
positive whenever every fibre block is positive.
-/

open scoped InnerProduct lp

noncomputable section

namespace NCG

variable {ι E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Fibrewise positivity passes to a uniformly bounded block-diagonal
operator on `ℓ²`. -/
theorem l2BlockDiagonal_isPositive
    (M : ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i x, ‖M i x‖ ≤ C * ‖x‖)
    (hpositive : ∀ i, (M i).IsPositive) :
    (l2BlockDiagonal M C hC hM).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro f
  rw [lp.inner_eq_tsum]
  simp only [l2BlockDiagonal_apply]
  let term : ι → ℂ := fun i ↦ inner ℂ (M i (f i)) (f i)
  have hsum : Summable term := by
    exact lp.summable_inner (l2BlockDiagonal M C hC hM f) f
  have hre :
      Complex.re (∑' i, term i) = ∑' i, Complex.re (term i) :=
    hsum.map_tsum Complex.reCLM Complex.reCLM.continuous
  have hsumRe : Summable (fun i ↦ Complex.re (term i)) :=
    hsum.map Complex.reCLM Complex.reCLM.continuous
  have hofReal :
      ((∑' i, Complex.re (term i) : ℝ) : ℂ) =
        ∑' i, ((Complex.re (term i) : ℝ) : ℂ) :=
    hsumRe.map_tsum Complex.ofRealCLM Complex.ofRealCLM.continuous
  constructor
  · change ((Complex.re (∑' i, term i) : ℝ) : ℂ) = ∑' i, term i
    rw [hre, hofReal]
    apply tsum_congr
    intro i
    exact ((ContinuousLinearMap.isPositive_iff_complex (M i)).mp
      (hpositive i) (f i)).1
  · change 0 ≤ Complex.re (∑' i, term i)
    rw [hre]
    exact tsum_nonneg fun i ↦
      ((ContinuousLinearMap.isPositive_iff_complex (M i)).mp
        (hpositive i) (f i)).2

end NCG
