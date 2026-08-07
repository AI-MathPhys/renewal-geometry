/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Derivative-free renewal face linearization
  (`thm:renewal-face-linearization`,
  Gran-Tensor manuscript)

* `renewal_face_linearization`: for a face functional with
  the boxed halving symmetry `A(z) = 2A(z/2)` and the boxed
  quasi-additivity `|A(x+y) - A(x) - A(y)| ≤ H‖x‖‖y‖`:
  (i) the dyadic rescaling `A(z) = 2ⁿA(2⁻ⁿz)`;
  (ii) the quantitative defect bound
      `|A(x+y) - A(x) - A(y)| ≤ 2⁻ⁿ H‖x‖‖y‖` at every
      scale;
  (iii) exact additivity `A(x+y) = A(x) + A(y)` — the
      quadratic defect is killed by the halving symmetry,
      with no differentiability assumed;
  (iv) `A(0) = 0` and oddness `A(-x) = -A(x)`.

Upgrading additivity plus local boundedness to full
`ℝ`-linearity (the Cauchy functional equation with a
regularity side condition) is the manuscript's final
regularity step.
-/

open Filter

namespace NCG

/-- `thm:renewal-face-linearization`. -/
theorem renewal_face_linearization {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → ℝ) (H : ℝ)
    (hhalf : ∀ z : E, A z = 2 * A ((2 : ℝ)⁻¹ • z))
    (hquasi : ∀ x y : E,
      |A (x + y) - A x - A y| ≤ H * ‖x‖ * ‖y‖) :
    -- (i) the dyadic rescaling
    (∀ (n : ℕ) (z : E),
      A z = 2 ^ n * A (((2 : ℝ) ^ n)⁻¹ • z))
    -- (ii) the scale-`n` defect bound
    ∧ (∀ (n : ℕ) (x y : E),
        |A (x + y) - A x - A y|
          ≤ (2 : ℝ)⁻¹ ^ n * (H * ‖x‖ * ‖y‖))
    -- (iii) exact additivity
    ∧ (∀ x y : E, A (x + y) = A x + A y)
    -- (iv) normalization and oddness
    ∧ (A 0 = 0)
    ∧ (∀ x : E, A (-x) = -A x) := by
  have hdyadic : ∀ (n : ℕ) (z : E),
      A z = 2 ^ n * A (((2 : ℝ) ^ n)⁻¹ • z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [ih z, hhalf (((2 : ℝ) ^ k)⁻¹ • z), smul_smul]
      have hsc : (2 : ℝ)⁻¹ * ((2 : ℝ) ^ k)⁻¹
          = ((2 : ℝ) ^ (k + 1))⁻¹ := by
        rw [pow_succ]
        field_simp
      rw [hsc, pow_succ]
      ring
  have hdefect : ∀ (n : ℕ) (x y : E),
      |A (x + y) - A x - A y|
        ≤ (2 : ℝ)⁻¹ ^ n * (H * ‖x‖ * ‖y‖) := by
    intro n x y
    have hx := hdyadic n x
    have hy := hdyadic n y
    have hxy := hdyadic n (x + y)
    have hsplit : ((2 : ℝ) ^ n)⁻¹ • (x + y)
        = ((2 : ℝ) ^ n)⁻¹ • x + ((2 : ℝ) ^ n)⁻¹ • y :=
      smul_add _ _ _
    rw [hsplit] at hxy
    have hkey : A (x + y) - A x - A y
        = 2 ^ n * (A (((2 : ℝ) ^ n)⁻¹ • x
            + ((2 : ℝ) ^ n)⁻¹ • y)
          - A (((2 : ℝ) ^ n)⁻¹ • x)
          - A (((2 : ℝ) ^ n)⁻¹ • y)) := by
      rw [hxy, hx, hy]
      ring
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    rw [hkey, abs_mul, abs_of_pos hpos]
    have hq := hquasi (((2 : ℝ) ^ n)⁻¹ • x)
      (((2 : ℝ) ^ n)⁻¹ • y)
    have hnx : ‖((2 : ℝ) ^ n)⁻¹ • x‖
        = ((2 : ℝ) ^ n)⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < ((2:ℝ)^n)⁻¹)]
    have hny : ‖((2 : ℝ) ^ n)⁻¹ • y‖
        = ((2 : ℝ) ^ n)⁻¹ * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < ((2:ℝ)^n)⁻¹)]
    rw [hnx, hny] at hq
    have hfin : (2 : ℝ) ^ n
        * (H * (((2 : ℝ) ^ n)⁻¹ * ‖x‖)
          * (((2 : ℝ) ^ n)⁻¹ * ‖y‖))
        = (2 : ℝ)⁻¹ ^ n * (H * ‖x‖ * ‖y‖) := by
      rw [inv_pow]
      field_simp
    calc (2 : ℝ) ^ n
          * |A (((2 : ℝ) ^ n)⁻¹ • x
              + ((2 : ℝ) ^ n)⁻¹ • y)
            - A (((2 : ℝ) ^ n)⁻¹ • x)
            - A (((2 : ℝ) ^ n)⁻¹ • y)|
        ≤ (2 : ℝ) ^ n
          * (H * (((2 : ℝ) ^ n)⁻¹ * ‖x‖)
            * (((2 : ℝ) ^ n)⁻¹ * ‖y‖)) :=
          mul_le_mul_of_nonneg_left hq hpos.le
      _ = (2 : ℝ)⁻¹ ^ n * (H * ‖x‖ * ‖y‖) := hfin
  have hadd : ∀ x y : E, A (x + y) = A x + A y := by
    intro x y
    have hlim : Tendsto
        (fun n : ℕ => (2 : ℝ)⁻¹ ^ n * (H * ‖x‖ * ‖y‖))
        atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)
      simpa using h.mul_const (H * ‖x‖ * ‖y‖)
    have hle : |A (x + y) - A x - A y| ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Eventually.of_forall fun n => hdefect n x y)
    have h0 : A (x + y) - A x - A y = 0 :=
      abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    linarith
  have hzero : A 0 = 0 := by
    have h := hadd 0 0
    simp only [add_zero] at h
    linarith
  refine ⟨hdyadic, hdefect, hadd, hzero, ?_⟩
  intro x
  have h := hadd x (-x)
  rw [add_neg_cancel, hzero] at h
  linarith

end NCG
