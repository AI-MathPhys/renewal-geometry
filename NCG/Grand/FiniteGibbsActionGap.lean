/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Finite Gibbs rows and the entropy-proximal action gap

This module proves the finite probability theorem used by
`cor:accepted-Gibbs-gap`: the normalized Gibbs tilt is the unique minimizer of
the entropy-proximal objective, and the excess objective is exactly a scaled
Kullback--Leibler divergence.
-/

open Finset
open InformationTheory

namespace NCG

variable {Y : Type*} [Fintype Y]

/-- Kullback--Leibler divergence of two strictly positive finite rows. -/
noncomputable def finiteKL (q p : Y → ℝ) : ℝ :=
  ∑ y, q y * Real.log (q y / p y)

/-- Partition function of a finite Gibbs tilt. -/
noncomputable def gibbsPartition (p c : Y → ℝ) (η : ℝ) : ℝ :=
  ∑ y, p y * Real.exp (-η * c y)

/-- Normalized finite Gibbs row. -/
noncomputable def gibbsRow (p c : Y → ℝ) (η : ℝ) (y : Y) : ℝ :=
  p y * Real.exp (-η * c y) / gibbsPartition p c η

/-- Entropy-proximal common-action objective. -/
noncomputable def entropyProximalObjective
    (q p c : Y → ℝ) (η : ℝ) : ℝ :=
  ∑ y, q y * c y + η⁻¹ * finiteKL q p

lemma finiteKL_eq_sum_klFun (q p : Y → ℝ)
    (hp : ∀ y, 0 < p y) (hqsum : ∑ y, q y = 1)
    (hpsum : ∑ y, p y = 1) :
    finiteKL q p = ∑ y, p y * klFun (q y / p y) := by
  unfold finiteKL
  calc
    ∑ y, q y * Real.log (q y / p y)
        = ∑ y, (p y * klFun (q y / p y) - p y + q y) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [klFun_apply]
            field_simp [ne_of_gt (hp y)]
            <;> ring
    _ = ∑ y, p y * klFun (q y / p y) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hqsum, hpsum]
          ring

/-- Gibbs' inequality for strictly positive finite probability rows, including
its sharp equality case. -/
theorem finiteKL_nonneg_eq_iff (q p : Y → ℝ)
    (hq : ∀ y, 0 < q y) (hp : ∀ y, 0 < p y)
    (hqsum : ∑ y, q y = 1) (hpsum : ∑ y, p y = 1) :
    0 ≤ finiteKL q p ∧ (finiteKL q p = 0 ↔ q = p) := by
  have hrewrite := finiteKL_eq_sum_klFun q p hp hqsum hpsum
  have hterm : ∀ y ∈ Finset.univ,
      0 ≤ p y * klFun (q y / p y) := by
    intro y _
    exact mul_nonneg (le_of_lt (hp y))
      (klFun_nonneg (le_of_lt (div_pos (hq y) (hp y))))
  constructor
  · rw [hrewrite]
    exact Finset.sum_nonneg hterm
  · constructor
    · intro hzero
      apply funext
      intro y
      have hall : ∀ z ∈ Finset.univ,
          p z * klFun (q z / p z) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hterm).mp (hrewrite ▸ hzero)
      have hkl : klFun (q y / p y) = 0 := by
        exact (mul_eq_zero.mp (hall y (Finset.mem_univ y))).resolve_left
          (ne_of_gt (hp y))
      have hratio : q y / p y = 1 :=
        (klFun_eq_zero_iff
          (le_of_lt (div_pos (hq y) (hp y)))).mp hkl
      exact (div_eq_one_iff_eq (ne_of_gt (hp y))).mp hratio
    · intro h
      subst q
      unfold finiteKL
      simp [ne_of_gt (hp _)]

/-- The Gibbs partition is positive, and the Gibbs row is a strictly positive
probability row. -/
theorem gibbsRow_probability [Nonempty Y] (p c : Y → ℝ) (η : ℝ)
    (hp : ∀ y, 0 < p y) :
    0 < gibbsPartition p c η
      ∧ (∀ y, 0 < gibbsRow p c η y)
      ∧ ∑ y, gibbsRow p c η y = 1 := by
  have hZ : 0 < gibbsPartition p c η := by
    unfold gibbsPartition
    exact Finset.sum_pos
      (fun y _ => mul_pos (hp y) (Real.exp_pos _)) Finset.univ_nonempty
  refine ⟨hZ, ?_, ?_⟩
  · intro y
    exact div_pos (mul_pos (hp y) (Real.exp_pos _)) hZ
  · unfold gibbsRow gibbsPartition
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hZ)

/-- Log-likelihood identity for the Gibbs tilt. -/
lemma log_ratio_gibbsRow [Nonempty Y] (q p c : Y → ℝ) (η : ℝ)
    (hq : ∀ y, 0 < q y) (hp : ∀ y, 0 < p y) :
    ∀ y, Real.log (q y / gibbsRow p c η y)
      = Real.log (q y / p y) + η * c y
          + Real.log (gibbsPartition p c η) := by
  have hZ := (gibbsRow_probability p c η hp).1
  intro y
  unfold gibbsRow
  rw [Real.log_div (ne_of_gt (hq y))
      (ne_of_gt (div_pos (mul_pos (hp y) (Real.exp_pos _)) hZ)),
    Real.log_div (ne_of_gt (mul_pos (hp y) (Real.exp_pos _)))
      (ne_of_gt hZ),
    Real.log_mul (ne_of_gt (hp y)) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp,
    Real.log_div (ne_of_gt (hq y)) (ne_of_gt (hp y))]
  ring

/-- The entropy-proximal objective differs from its optimum by precisely the
scaled KL divergence to the Gibbs row. -/
theorem entropyProximalObjective_gap [Nonempty Y]
    (q p c : Y → ℝ) (η : ℝ)
    (hη : 0 < η) (hq : ∀ y, 0 < q y) (hp : ∀ y, 0 < p y)
    (hqsum : ∑ y, q y = 1) :
    entropyProximalObjective q p c η
      = η⁻¹ * finiteKL q (gibbsRow p c η)
          - η⁻¹ * Real.log (gibbsPartition p c η) := by
  have hlog := log_ratio_gibbsRow q p c η hq hp
  have hKL : finiteKL q (gibbsRow p c η)
      = finiteKL q p + η * (∑ y, q y * c y)
          + Real.log (gibbsPartition p c η) := by
    unfold finiteKL
    calc
      ∑ y, q y * Real.log (q y / gibbsRow p c η y)
          = ∑ y, (q y * Real.log (q y / p y)
              + η * (q y * c y)
              + q y * Real.log (gibbsPartition p c η)) := by
                apply Finset.sum_congr rfl
                intro y _
                rw [hlog y]
                ring
      _ = finiteKL q p + η * (∑ y, q y * c y)
            + Real.log (gibbsPartition p c η) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← Finset.mul_sum, ← Finset.sum_mul, hqsum, one_mul]
              rfl
  unfold entropyProximalObjective
  rw [hKL]
  field_simp [ne_of_gt hη]
  <;> ring

/-- The normalized Gibbs row is the unique entropy-proximal probability row;
the row-wise action gap is its scaled KL divergence. -/
theorem finite_gibbs_action_gap_exact [Nonempty Y]
    (p c : Y → ℝ) (η : ℝ) (hp : ∀ y, 0 < p y)
    (hpsum : ∑ y, p y = 1) (hη : 0 < η) :
    let qstar := gibbsRow p c η
    (∀ y, 0 < qstar y)
    ∧ (∑ y, qstar y = 1)
    ∧ (∀ q : Y → ℝ, (∀ y, 0 < q y) → (∑ y, q y = 1) →
        entropyProximalObjective qstar p c η
          ≤ entropyProximalObjective q p c η)
    ∧ (∀ q : Y → ℝ, (∀ y, 0 < q y) → (∑ y, q y = 1) →
        (entropyProximalObjective q p c η
            - entropyProximalObjective qstar p c η
              = η⁻¹ * finiteKL q qstar)
        ∧ (entropyProximalObjective q p c η
              = entropyProximalObjective qstar p c η ↔ q = qstar)) := by
  dsimp only
  have hqstar := gibbsRow_probability p c η hp
  refine ⟨hqstar.2.1, hqstar.2.2, ?_, ?_⟩
  · intro q hq hqsum
    have hqGap := entropyProximalObjective_gap q p c η hη hq hp hqsum
    have hsGap := entropyProximalObjective_gap (gibbsRow p c η) p c η
      hη hqstar.2.1 hp hqstar.2.2
    have hKL := finiteKL_nonneg_eq_iff q (gibbsRow p c η)
      hq hqstar.2.1 hqsum hqstar.2.2
    have hself : finiteKL (gibbsRow p c η) (gibbsRow p c η) = 0 :=
      (finiteKL_nonneg_eq_iff (gibbsRow p c η) (gibbsRow p c η)
        hqstar.2.1 hqstar.2.1 hqstar.2.2 hqstar.2.2).2.mpr rfl
    rw [hqGap, hsGap, hself, mul_zero, zero_sub]
    simpa only [zero_sub] using
      sub_le_sub_right (mul_nonneg (le_of_lt (inv_pos.mpr hη)) hKL.1)
        (η⁻¹ * Real.log (gibbsPartition p c η))
  · intro q hq hqsum
    have hqGap := entropyProximalObjective_gap q p c η hη hq hp hqsum
    have hsGap := entropyProximalObjective_gap (gibbsRow p c η) p c η
      hη hqstar.2.1 hp hqstar.2.2
    have hself : finiteKL (gibbsRow p c η) (gibbsRow p c η) = 0 :=
      (finiteKL_nonneg_eq_iff (gibbsRow p c η) (gibbsRow p c η)
        hqstar.2.1 hqstar.2.1 hqstar.2.2 hqstar.2.2).2.mpr rfl
    have hKL := finiteKL_nonneg_eq_iff q (gibbsRow p c η)
      hq hqstar.2.1 hqsum hqstar.2.2
    constructor
    · rw [hqGap, hsGap, hself]
      ring
    ·
      constructor
      · intro heqObj
        have hz : η⁻¹ * finiteKL q (gibbsRow p c η) = 0 := by
          rw [hqGap, hsGap, hself, mul_zero] at heqObj
          linarith
        have : finiteKL q (gibbsRow p c η) = 0 :=
          (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (ne_of_gt hη))
        exact hKL.2.mp this
      · intro heq
        subst q
        rfl

/-- A strictly positive stationary average of Gibbs action gaps vanishes
exactly when every observed row obeys the common-action likelihood-ratio
identity. -/
theorem stationary_gibbs_gap_eq_zero_iff
    {Θ : Type*} [Fintype Θ] [Nonempty Y]
    (π : Θ → ℝ) (K p c : Θ → Y → ℝ) (η : ℝ)
    (hπ : ∀ θ, 0 < π θ) (hη : 0 < η)
    (hK : ∀ θ y, 0 < K θ y) (hp : ∀ θ y, 0 < p θ y)
    (hKsum : ∀ θ, ∑ y, K θ y = 1) :
    (∑ θ, π θ * (η⁻¹ * finiteKL (K θ) (gibbsRow (p θ) (c θ) η)) = 0)
      ↔ ∀ θ y,
        K θ y / p θ y
          = Real.exp (-η * c θ y) / gibbsPartition (p θ) (c θ) η := by
  have hqstar (θ : Θ) := gibbsRow_probability (p θ) (c θ) η (hp θ)
  have hKL (θ : Θ) := finiteKL_nonneg_eq_iff
    (K θ) (gibbsRow (p θ) (c θ) η)
    (hK θ) (hqstar θ).2.1 (hKsum θ) (hqstar θ).2.2
  have hterm : ∀ θ ∈ Finset.univ,
      0 ≤ π θ * (η⁻¹ * finiteKL (K θ) (gibbsRow (p θ) (c θ) η)) := by
    intro θ _
    exact mul_nonneg (le_of_lt (hπ θ))
      (mul_nonneg (le_of_lt (inv_pos.mpr hη)) (hKL θ).1)
  have hrow (θ : Θ) :
      K θ = gibbsRow (p θ) (c θ) η ↔
        ∀ y, K θ y / p θ y
          = Real.exp (-η * c θ y) / gibbsPartition (p θ) (c θ) η := by
    constructor
    · intro heq y
      rw [heq]
      unfold gibbsRow
      field_simp [ne_of_gt (hp θ y)]
    · intro hratio
      funext y
      have hy := hratio y
      unfold gibbsRow
      field_simp [ne_of_gt (hp θ y)] at hy ⊢
      exact hy
  constructor
  · intro havg θ y
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp havg
    have hprod := hall θ (Finset.mem_univ θ)
    have hinvkl : η⁻¹ * finiteKL (K θ) (gibbsRow (p θ) (c θ) η) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hπ θ))
    have hzero : finiteKL (K θ) (gibbsRow (p θ) (c θ) η) = 0 :=
      (mul_eq_zero.mp hinvkl).resolve_left (inv_ne_zero (ne_of_gt hη))
    exact (hrow θ).mp ((hKL θ).2.mp hzero) y
  · intro hratio
    apply (Finset.sum_eq_zero_iff_of_nonneg hterm).mpr
    intro θ _
    have heq : K θ = gibbsRow (p θ) (c θ) η :=
      (hrow θ).mpr (hratio θ)
    rw [(hKL θ).2.mpr heq, mul_zero, mul_zero]

end NCG
