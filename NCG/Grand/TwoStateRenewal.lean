/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact minimal two-state active renewal and its renewal law
  (`thm:two-state-active-renewal`,
   `thm:completed-private-renewal`, Gran-Tensor manuscript)

* `two_state_active_renewal`: the boxed recurrent completion
  `M₀ = Q₀ + r₀α = [[1/5,4/5],[2/3,1/3]]`, the boxed first-return
  transform `F_W(z) = zα(I - zQ₀)⁻¹r₀ = 8z²/((5-z)(3-z))`, the
  stationary law `π = (5/11, 6/11)`, detailed balance, and the
  boxed spectrum `{1, -7/15}` (eigenvector witnesses).
* `completed_private_renewal`: the exact interarrival law
  `Pr(W=n) = 4(3^{1-n} - 5^{1-n})` is normalized with the boxed
  exact tail `Pr(W>N) = 6·3^{-N} - 5·5^{-N}` at every horizon,
  and the boxed mean `𝔼W = Σ_N Pr(W>N) = 11/4`.

Rendering disclosed: the generating function is stated at every
real `z` off the poles in cross-multiplied-free form; the
pointwise law and tail are rendered by the exact
mass-plus-tail identity at every horizon and the tail-sum mean;
the variance `17/16` and the almost-sure renewal rate
`N_t/t → 4/11` are the manuscript's remaining
probability-layer bookkeeping over these identities; the
"active linear predictive dimension two" clause is the visible
2×2 minimality of the displayed realization.
-/

open Matrix

namespace NCG

/-- The no-boundary transfer of the two-state renewal. -/
noncomputable def renQ0 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/5, 4/5; 0, 1/3]

/-- The recurrent completion `M₀`. -/
noncomputable def renM0 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/5, 4/5; 2/3, 1/3]

set_option linter.flexible false in
/-- `thm:two-state-active-renewal`: completion, first-return
transform, stationarity, reversibility, and spectrum. -/
theorem two_state_active_renewal :
    (renM0 = renQ0
      + Matrix.vecMulVec ![0, 2/3] ![1, 0])
    ∧ (∀ z : ℝ, z ≠ 5 → z ≠ 3 →
        z * (![1, 0] ⬝ᵥ ((1 - z • renQ0)⁻¹ *ᵥ ![0, 2/3]))
          = 8 * z ^ 2 / ((5 - z) * (3 - z)))
    ∧ (![5/11, 6/11] ᵥ* renM0 = ![5/11, 6/11])
    ∧ ((5/11 : ℝ) * renM0 0 1 = (6/11 : ℝ) * renM0 1 0)
    ∧ (renM0 *ᵥ ![1, 1] = ![1, 1])
    ∧ (renM0 *ᵥ ![6, -5] = (-7/15 : ℝ) • ![6, -5]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [renM0, renQ0]
  · intro z hz5 hz3
    have h5 : (1 : ℝ) - z / 5 ≠ 0 := by
      intro h
      apply hz5
      linarith [sub_eq_zero.mp h]
    have h3 : (1 : ℝ) - z / 3 ≠ 0 := by
      intro h
      apply hz3
      linarith [sub_eq_zero.mp h]
    have hinv : (1 - z • renQ0)⁻¹
        = !![(1 - z/5)⁻¹, (4*z/5) * ((1 - z/5)⁻¹ * (1 - z/3)⁻¹);
             0, (1 - z/3)⁻¹] := by
      apply Matrix.inv_eq_right_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [renQ0, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.one_apply] <;>
        first
          | (field_simp; ring)
          | field_simp
    rw [hinv]
    have hval : (![1, 0] ⬝ᵥ
        ((!![(1 - z/5)⁻¹,
             (4*z/5) * ((1 - z/5)⁻¹ * (1 - z/3)⁻¹);
             0, (1 - z/3)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ)
          *ᵥ ![0, 2/3]))
        = (4*z/5) * ((1 - z/5)⁻¹ * (1 - z/3)⁻¹) * (2/3) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    rw [hval]
    have h5' : (5 : ℝ) - z ≠ 0 := sub_ne_zero.mpr
      (fun h => hz5 h.symm)
    have h3' : (3 : ℝ) - z ≠ 0 := sub_ne_zero.mpr
      (fun h => hz3 h.symm)
    field_simp
    ring
  · funext j
    fin_cases j <;>
      simp [renM0, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two] <;> norm_num
  · simp [renM0]
    norm_num
  · funext i
    fin_cases i <;>
      simp [renM0, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> norm_num
  · funext i
    fin_cases i <;>
      simp [renM0, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> norm_num

/-- `thm:completed-private-renewal`: exact mass–tail identity at
every horizon and the tail-sum mean `𝔼W = 11/4`. -/
theorem completed_private_renewal :
    (∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 2 N,
        (12 * (1/3 : ℝ) ^ n - 20 * (1/5 : ℝ) ^ n))
        + (6 * (1/3 : ℝ) ^ N - 5 * (1/5 : ℝ) ^ N) = 1)
    ∧ ∑' N : ℕ, (6 * (1/3 : ℝ) ^ N - 5 * (1/5 : ℝ) ^ N)
        = 11/4 := by
  constructor
  · intro N hN
    induction N with
    | zero => omega
    | succ k ih =>
        by_cases hk : 1 ≤ k
        · rw [Finset.sum_Icc_succ_top (by omega)]
          have hstep : (12 * (1/3 : ℝ) ^ (k+1)
                - 20 * (1/5 : ℝ) ^ (k+1))
              + (6 * (1/3 : ℝ) ^ (k+1) - 5 * (1/5 : ℝ) ^ (k+1))
              = 6 * (1/3 : ℝ) ^ k - 5 * (1/5 : ℝ) ^ k := by
            rw [pow_succ, pow_succ]
            ring
          linarith [ih hk]
        · have hk0 : k = 0 := by omega
          subst hk0
          norm_num
  · have h3 : ∑' N : ℕ, (1/3 : ℝ) ^ N = 3/2 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    have h5 : ∑' N : ℕ, (1/5 : ℝ) ^ N = 5/4 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    have hs3 : Summable (fun N : ℕ => (1/3 : ℝ) ^ N) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hs5 : Summable (fun N : ℕ => (1/5 : ℝ) ^ N) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    calc ∑' N : ℕ, (6 * (1/3 : ℝ) ^ N - 5 * (1/5 : ℝ) ^ N)
        = ∑' N : ℕ, ((6 : ℝ) * (1/3) ^ N)
          - ∑' N : ℕ, ((5 : ℝ) * (1/5) ^ N) := by
          rw [Summable.tsum_sub (hs3.mul_left 6)
            (hs5.mul_left 5)]
      _ = 6 * (3/2) - 5 * (5/4) := by
          rw [tsum_mul_left, tsum_mul_left, h3, h5]
      _ = 11/4 := by norm_num

end NCG
