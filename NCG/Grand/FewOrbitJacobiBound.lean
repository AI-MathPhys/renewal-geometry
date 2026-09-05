/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ShiftedJacobiPartialIsometry
import Mathlib.Analysis.Real.Sqrt

/-!
# Few quotient-complete character orbits

The shifted Jacobi module supplies the sharp nonprincipal entry bound.  This
file proves the remaining support-cardinality `l1`--`l2` and lag-summation
estimate used in `thm:ar-few-orbit`, together with the rank-threshold exponent
calculation.  The statement is written for absolute values of the collected
character coefficients, exactly the scalar majorant obtained after the first
triangle inequality in the manuscript proof.
-/

open scoped BigOperators

namespace NCG

/-- Finite `l1` norm of a coefficient bank. -/
noncomputable def finiteL1 {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  ∑ i, |x i|

/-- Squared finite `l2` norm of a coefficient bank. -/
noncomputable def finiteL2Sq {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  ∑ i, |x i| ^ 2

/-- On an `R`-element character support, `‖x‖₁ ≤ √R ‖x‖₂`. -/
theorem finiteL1_le_card_sqrt_mul_l2 {I : Type*} [Fintype I]
    (x : I → ℝ) :
    finiteL1 x ≤ Real.sqrt (Fintype.card I) * Real.sqrt (finiteL2Sq x) := by
  unfold finiteL1 finiteL2Sq
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun _ : I => (1 : ℝ)) (fun i => |x i|)
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- Entrywise Jacobi control plus two support bounds gives the
`√(R_L R_R)` bilinear estimate. -/
theorem fewOrbit_entrywise_bilinear
    {L R : Type*} [Fintype L] [Fintype R]
    (eta : ℝ) (heta : 0 ≤ eta)
    (K : L → R → ℝ) (hK : ∀ i j, |K i j| ≤ eta)
    (u : L → ℝ) (v : R → ℝ) :
    |∑ i, ∑ j, u i * K i j * v j|
      ≤ eta * Real.sqrt (Fintype.card L * Fintype.card R)
          * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v) := by
  calc
    |∑ i, ∑ j, u i * K i j * v j|
        ≤ ∑ i, ∑ j, |u i * K i j * v j| := by
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |u i| * eta * |v j| := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hK i j) (abs_nonneg (u i)))
            (abs_nonneg (v j))
    _ = eta * finiteL1 u * finiteL1 v := by
          simp only [finiteL1]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          ring
    _ ≤ eta * (Real.sqrt (Fintype.card L) * Real.sqrt (finiteL2Sq u))
          * (Real.sqrt (Fintype.card R) * Real.sqrt (finiteL2Sq v)) := by
          have hu := finiteL1_le_card_sqrt_mul_l2 u
          have hv := finiteL1_le_card_sqrt_mul_l2 v
          have hLu : 0 ≤ finiteL1 u := by
            exact Finset.sum_nonneg fun i _ => abs_nonneg (u i)
          have hLv : 0 ≤ finiteL1 v := by
            exact Finset.sum_nonneg fun i _ => abs_nonneg (v i)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hu heta) hv hLv
            (mul_nonneg heta (mul_nonneg (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)))
    _ = eta * Real.sqrt (Fintype.card L * Fintype.card R)
          * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card L))]
          push_cast
          ring

/-- Summing lags costs only their `l1` weight. -/
theorem fewOrbit_lag_sum
    {H L R : Type*} [Fintype H] [Fintype L] [Fintype R]
    (eta W : ℝ) (heta : 0 ≤ eta)
    (w : H → ℝ) (hw : finiteL1 w ≤ W)
    (K : H → L → R → ℝ) (hK : ∀ h i j, |K h i j| ≤ eta)
    (u : L → ℝ) (v : R → ℝ) :
    |∑ h, w h * (∑ i, ∑ j, u i * K h i j * v j)|
      ≤ W * eta * Real.sqrt (Fintype.card L * Fintype.card R)
          * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v) := by
  have hL1w : 0 ≤ finiteL1 w := by
    exact Finset.sum_nonneg fun i _ => abs_nonneg (w i)
  have hW : 0 ≤ W := le_trans hL1w hw
  calc
    |∑ h, w h * (∑ i, ∑ j, u i * K h i j * v j)|
        ≤ ∑ h, |w h| * |∑ i, ∑ j, u i * K h i j * v j| := by
          simpa [abs_mul] using Finset.abs_sum_le_sum_abs
            (s := Finset.univ)
            (f := fun h => w h * (∑ i, ∑ j, u i * K h i j * v j))
    _ ≤ ∑ h, |w h| *
          (eta * Real.sqrt (Fintype.card L * Fintype.card R)
            * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v)) := by
          gcongr with h
          exact fewOrbit_entrywise_bilinear eta heta (K h) (hK h) u v
    _ = finiteL1 w * eta * Real.sqrt (Fintype.card L * Fintype.card R)
          * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v) := by
          simp only [finiteL1]
          rw [← Finset.sum_mul]
          ring
    _ ≤ W * eta * Real.sqrt (Fintype.card L * Fintype.card R)
          * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v) := by
          let C := eta * Real.sqrt (Fintype.card L * Fintype.card R)
            * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v)
          have hC : 0 ≤ C := by
            dsimp [C]
            positivity
          calc
            finiteL1 w * eta * Real.sqrt (Fintype.card L * Fintype.card R)
                * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v)
                = finiteL1 w * C := by ring
            _ ≤ W * C := mul_le_mul_of_nonneg_right hw hC
            _ = W * eta * Real.sqrt (Fintype.card L * Fintype.card R)
                * Real.sqrt (finiteL2Sq u) * Real.sqrt (finiteL2Sq v) := by ring

/-- The manuscript exponent check: `H q⁻¹/² = Y⁻¹/20` and a character-rank
factor at most `Y¹/20` cancel exactly. -/
theorem fewOrbit_rank_threshold_exponent (Y : ℝ) (hY : 0 < Y) :
    Y ^ ((1 : ℝ) / 5) * (Y ^ ((1 : ℝ) / 2)) ^ (-(1 : ℝ) / 2)
        * Y ^ ((1 : ℝ) / 20) = 1 := by
  rw [← Real.rpow_mul hY.le]
  rw [← Real.rpow_add hY]
  rw [← Real.rpow_add hY]
  norm_num

/-- `thm:ar-few-orbit`: the finite support/rank assembly.  Substituting the
sharp Jacobi entry estimate from `shiftedCharacterCoefficient_norm_le` for
`eta`, and the quotient Plancherel identities for the two displayed `l2`
norms, is the manuscript's normalized integral formula. -/
theorem ar_few_orbit_finite_assembly :
    (∀ {I : Type*} [Fintype I] (x : I → ℝ),
      finiteL1 x ≤ Real.sqrt (Fintype.card I) * Real.sqrt (finiteL2Sq x))
    ∧ (∀ (Y : ℝ), 0 < Y →
      Y ^ ((1 : ℝ) / 5) * (Y ^ ((1 : ℝ) / 2)) ^ (-(1 : ℝ) / 2)
        * Y ^ ((1 : ℝ) / 20) = 1) :=
  ⟨finiteL1_le_card_sqrt_mul_l2, fewOrbit_rank_threshold_exponent⟩

end NCG
