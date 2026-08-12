/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTypeClosure

/-!
# Exponentially weighted finite-type inverse closure

This file completes the weight/Schur layer of
`thm:renewal-finite-type-closure`.  It proves the exponential corner estimate
from the conjugated inverse, and proves the two-sided Schur estimate for every
finite natural exponent by applying finite Jensen to each normalized row.
-/

open scoped BigOperators

noncomputable section

namespace NCG

/-- The exact Combes--Thomas corner identity plus Neumann closure gives the
displayed exponentially decaying inverse corner. -/
theorem exponential_conjugation_corner_decay
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
    (D E Di W Px Py : A) (σ b μ δ : ℝ)
    (hσ : 0 < σ) (hb : 0 ≤ b) (hbσ : b < σ)
    (hDDi : D * Di = 1) (hDiD : Di * D = 1)
    (hDi : ‖Di‖ ≤ 1 / σ) (hE : ‖E‖ ≤ b)
    (hW1 : (D + E) * W = 1) (hW2 : W * (D + E) = 1)
    (hPx : ‖Px‖ ≤ 1) (hPy : ‖Py‖ ≤ 1)
    (hμ : 0 ≤ μ) (hδ : 0 ≤ δ)
    (hcorner : Px * Di * Py =
      Real.exp (-μ * δ) • (Px * W * Py)) :
    ‖Px * Di * Py‖ ≤ Real.exp (-μ * δ) / (σ - b) := by
  have hW : ‖W‖ ≤ 1 / (σ - b) :=
    (renewal_finite_type_closure (ι := Fin 1) (τ := Fin 1)).2.2
      (A := A) D E Di W σ b
      hσ hb hbσ hDDi hDiD hDi hE hW1 hW2
  have hσb : 0 < σ - b := sub_pos.mpr hbσ
  have hPW : ‖Px * W * Py‖ ≤ 1 / (σ - b) := by
    calc
      ‖Px * W * Py‖ ≤ ‖Px * W‖ * ‖Py‖ := norm_mul_le _ _
      _ ≤ (‖Px‖ * ‖W‖) * ‖Py‖ := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ (1 * (1 / (σ - b))) * 1 := by
        gcongr
      _ = 1 / (σ - b) := by ring
  rw [hcorner, norm_smul]
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hm : Real.exp (-μ * δ) * ‖Px * W * Py‖ ≤
      Real.exp (-μ * δ) * (1 / (σ - b)) :=
    mul_le_mul_of_nonneg_left hPW (Real.exp_pos (-μ * δ)).le
  simpa [div_eq_mul_inv] using hm

/-- A finite Jensen lemma for a nonnegative row whose total mass is bounded
by `R`. -/
theorem row_sum_power_bound {J : Type*} [Fintype J]
    (k f : J → ℝ) (R : ℝ) (p : ℕ)
    (hk : ∀ j, 0 ≤ k j) (hf : ∀ j, 0 ≤ f j)
    (hR : ∑ j, k j ≤ R) (hp : 1 ≤ p) :
    (∑ j, k j * f j) ^ p ≤
      R ^ (p - 1) * ∑ j, k j * f j ^ p := by
  let r : ℝ := ∑ j, k j
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun j _ => hk j
  by_cases hr : r = 0
  · have hk0 : ∀ j, k j = 0 := by
      intro j
      apply le_antisymm
      · have hj : k j ≤ ∑ x, k x :=
          Finset.single_le_sum (fun x _ => hk x) (Finset.mem_univ j)
        simpa [r, hr] using hj
      · exact hk j
    simp [hk0, Nat.ne_of_gt hp]
  · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hJensen := Real.pow_arith_mean_le_arith_mean_pow
      Finset.univ (fun j => k j / r) f
      (fun j _ => div_nonneg (hk j) hrp.le)
      (by simp [← Finset.sum_div, r, hr])
      (fun j _ => hf j) p
    have hnormalized :
        (∑ j, (k j / r) * f j) = (∑ j, k j * f j) / r := by
      calc
        (∑ j, (k j / r) * f j) = ∑ j, (k j * f j) / r := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j, k j * f j) / r := by rw [Finset.sum_div]
    have hnormalizedP :
        (∑ j, (k j / r) * f j ^ p) =
          (∑ j, k j * f j ^ p) / r := by
      calc
        (∑ j, (k j / r) * f j ^ p) = ∑ j, (k j * f j ^ p) / r := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j, k j * f j ^ p) / r := by rw [Finset.sum_div]
    rw [hnormalized, hnormalizedP] at hJensen
    have hrow :
        (∑ j, k j * f j) ^ p ≤
          r ^ (p - 1) * ∑ j, k j * f j ^ p := by
      have hrpow : 0 < r ^ p := pow_pos hrp p
      have hm := mul_le_mul_of_nonneg_left hJensen hrpow.le
      rw [div_pow] at hm
      have hpow_split : r ^ p = r ^ (p - 1) * r := by
        conv_lhs => rw [show p = (p - 1) + 1 by omega]
        simp [pow_add]
      rw [hpow_split] at hm
      field_simp [hr] at hm
      exact hm
    have hrR : r ≤ R := hR
    have hpow : r ^ (p - 1) ≤ R ^ (p - 1) :=
      pow_le_pow_left₀ hr0 hrR _
    exact hrow.trans <| mul_le_mul_of_nonneg_right hpow
      (Finset.sum_nonneg fun j _ => mul_nonneg (hk j) (pow_nonneg (hf j) _))

/-- Two-sided weighted Schur bound in power form.  Taking `p`-th roots gives
`‖K‖_{p→p} ≤ R^(1-1/p) C^(1/p)` for every finite `p`. -/
theorem two_sided_schur_power_bound
    {I J : Type*} [Fintype I] [Fintype J]
    (K : I → J → ℝ) (f : J → ℝ) (R C : ℝ) (p : ℕ)
    (hK : ∀ i j, 0 ≤ K i j) (hf : ∀ j, 0 ≤ f j)
    (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hrow : ∀ i, ∑ j, K i j ≤ R)
    (hcol : ∀ j, ∑ i, K i j ≤ C) (hp : 1 ≤ p) :
    ∑ i, (∑ j, K i j * f j) ^ p ≤
      R ^ (p - 1) * C * ∑ j, f j ^ p := by
  calc
    ∑ i, (∑ j, K i j * f j) ^ p
        ≤ ∑ i, R ^ (p - 1) * ∑ j, K i j * f j ^ p :=
      Finset.sum_le_sum fun i _ =>
        row_sum_power_bound (K i) f R p (hK i) hf (hrow i) hp
    _ = R ^ (p - 1) * ∑ j, (∑ i, K i j) * f j ^ p := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ ≤ R ^ (p - 1) * ∑ j, C * f j ^ p := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (pow_nonneg (hf j) _))
        (pow_nonneg hR0 _)
    _ = R ^ (p - 1) * C * ∑ j, f j ^ p := by
      rw [← Finset.mul_sum]
      ring

/-- Forward and backward exponential volume bounds turn pointwise
Combes--Thomas decay into the two-sided Schur hypotheses, hence into every
finite `L^p` inverse bound. -/
theorem exponential_decay_all_finite_lp
    {X : Type*} [Fintype X]
    (K : X → X → ℝ) (dist : X → X → ℝ)
    (μ C Vforward Vbackward : ℝ) (p : ℕ)
    (hC : 0 ≤ C) (hVforward : 0 ≤ Vforward)
    (hVbackward : 0 ≤ Vbackward)
    (hK : ∀ x y, 0 ≤ K x y)
    (hdecay : ∀ x y, K x y ≤ C * Real.exp (-μ * dist x y))
    (hforward : ∀ x, ∑ y, Real.exp (-μ * dist x y) ≤ Vforward)
    (hbackward : ∀ y, ∑ x, Real.exp (-μ * dist x y) ≤ Vbackward)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (hp : 1 ≤ p) :
    ∑ x, (∑ y, K x y * f y) ^ p ≤
      (C * Vforward) ^ (p - 1) * (C * Vbackward) *
        ∑ y, f y ^ p := by
  have hr : ∀ x, ∑ y, K x y ≤ C * Vforward := by
    intro x
    calc
      ∑ y, K x y ≤ ∑ y, C * Real.exp (-μ * dist x y) :=
        Finset.sum_le_sum fun y _ => hdecay x y
      _ = C * ∑ y, Real.exp (-μ * dist x y) := by rw [Finset.mul_sum]
      _ ≤ C * Vforward := mul_le_mul_of_nonneg_left (hforward x) hC
  have hc : ∀ y, ∑ x, K x y ≤ C * Vbackward := by
    intro y
    calc
      ∑ x, K x y ≤ ∑ x, C * Real.exp (-μ * dist x y) :=
        Finset.sum_le_sum fun x _ => hdecay x y
      _ = C * ∑ x, Real.exp (-μ * dist x y) := by rw [Finset.mul_sum]
      _ ≤ C * Vbackward := mul_le_mul_of_nonneg_left (hbackward y) hC
  exact two_sided_schur_power_bound K f (C * Vforward) (C * Vbackward) p
    hK hf (mul_nonneg hC hVforward) (mul_nonneg hC hVbackward) hr hc hp

end NCG
