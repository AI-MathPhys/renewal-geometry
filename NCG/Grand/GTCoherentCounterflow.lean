/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Orthogonal signed-coherence decomposition
  (`thm:GT-coherent-counterflow`,
  Gran-Tensor manuscript)

* `gt_coherent_counterflow`: for a finite fully-supported
  signed measure `μ` with total variation `T = ∑|μ|` and
  resultant `S = ∑μ` (SC.1: `μ_coh = (S/T)|μ|`,
  `μ_cf = μ - μ_coh`, `κ_cf = (T²-S²)/(2T)`),
  (i) the counterflow carries zero resultant
      (`∑ μ_cf = 0`) — the split is the orthogonal
      projection onto constants in `L²(|μ|)`;
  (ii) the boxed `μ_cf = κ_cf(P⁺ - P⁻)`: both Jordan
      masses of the counterflow equal `κ_cf`
      (`∑ μ_cf⁺ = κ_cf = ∑ μ_cf⁻`);
  (iii) the boxed residual norm
      `‖dμ/d|μ| - S/T‖²_{L²(|μ|)} = 2κ_cf`;
  (iv) the boxed SC.3 observable split
      `∫f dμ = S f⁰ + (∫f dμ_cf⁺ - ∫f dμ_cf⁻)` with
      `f⁰ = T⁻¹∫f d|μ|` — total variation, coherent
      resultant, and counterflow are separate retained
      coordinates.

The measure-theoretic packaging (Jordan decomposition of a
general signed measure; the normalized parts `P±` when
`κ_cf > 0`) is the manuscript's `L²(|μ|)` layer — here the
Jordan parts appear unnormalized, which is the same boxed
display multiplied through by `κ_cf`.
-/

open Finset

namespace NCG

/-- `thm:GT-coherent-counterflow` (SC.1–SC.3 on a finite
fully-supported carrier). -/
theorem gt_coherent_counterflow {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (hsupp : ∀ i, μ i ≠ 0)
    (hT : 0 < ∑ i, |μ i|) :
    -- (i) the counterflow has zero resultant
    (∑ i, (μ i - (∑ j, μ j) / (∑ j, |μ j|) * |μ i|) = 0)
    -- (ii) both Jordan masses of the counterflow are κ_cf
    ∧ (∑ i, max (μ i - (∑ j, μ j) / (∑ j, |μ j|)
          * |μ i|) 0
        = ((∑ j, |μ j|) ^ 2 - (∑ j, μ j) ^ 2)
          / (2 * ∑ j, |μ j|))
    ∧ (∑ i, max (-(μ i - (∑ j, μ j) / (∑ j, |μ j|)
          * |μ i|)) 0
        = ((∑ j, |μ j|) ^ 2 - (∑ j, μ j) ^ 2)
          / (2 * ∑ j, |μ j|))
    -- (iii) the boxed L²(|μ|) residual norm
    ∧ (∑ i, |μ i| * (μ i / |μ i|
          - (∑ j, μ j) / (∑ j, |μ j|)) ^ 2
        = 2 * (((∑ j, |μ j|) ^ 2 - (∑ j, μ j) ^ 2)
          / (2 * ∑ j, |μ j|)))
    -- (iv) the boxed SC.3 observable split
    ∧ (∀ f : Ω → ℝ,
        ∑ i, f i * μ i
          = (∑ j, μ j) * ((∑ i, f i * |μ i|)
              / (∑ j, |μ j|))
            + (∑ i, f i * max (μ i - (∑ j, μ j)
                / (∑ j, |μ j|) * |μ i|) 0
              - ∑ i, f i * max (-(μ i - (∑ j, μ j)
                / (∑ j, |μ j|) * |μ i|)) 0)) := by
  set T := ∑ j, |μ j| with hTdef
  set S := ∑ j, μ j with hSdef
  have hTne : T ≠ 0 := ne_of_gt hT
  -- |S| ≤ T
  have hST : |S| ≤ T := by
    rw [hSdef, hTdef]
    exact Finset.abs_sum_le_sum_abs _ _
  have hS1 : S / T ≤ 1 := by
    rw [div_le_one hT]
    exact le_trans (le_abs_self S) hST
  have hS2 : -1 ≤ S / T := by
    rw [le_div_iff₀ hT]
    have := neg_abs_le S
    linarith
  -- pointwise Jordan identities for the counterflow
  have hpos : ∀ i, max (μ i - S / T * |μ i|) 0
      = (1 - S / T) * max (μ i) 0 := by
    intro i
    rcases lt_or_ge (μ i) 0 with h | h
    · rw [abs_of_neg h, max_eq_right (le_of_lt h),
        max_eq_right (by nlinarith), mul_zero]
    · rw [abs_of_nonneg h, max_eq_left h,
        max_eq_left (by nlinarith)]
      ring
  have hneg : ∀ i, max (-(μ i - S / T * |μ i|)) 0
      = (1 + S / T) * max (-(μ i)) 0 := by
    intro i
    rcases lt_or_ge (μ i) 0 with h | h
    · rw [abs_of_neg h,
        max_eq_left (by nlinarith : (0:ℝ) ≤ -(μ i)),
        max_eq_left (by nlinarith)]
      ring
    · rw [abs_of_nonneg h,
        max_eq_right (by nlinarith : -(μ i) ≤ 0),
        max_eq_right (by nlinarith), mul_zero]
  -- half-sum identities for the Jordan parts of μ
  have hmax : ∀ i, max (μ i) 0 = (μ i + |μ i|) / 2 := by
    intro i
    rcases lt_or_ge (μ i) 0 with h | h
    · rw [abs_of_neg h, max_eq_right (le_of_lt h)]
      ring
    · rw [abs_of_nonneg h, max_eq_left h]
      ring
  have hmaxneg : ∀ i, max (-(μ i)) 0
      = (|μ i| - μ i) / 2 := by
    intro i
    rcases lt_or_ge (μ i) 0 with h | h
    · rw [abs_of_neg h,
        max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonneg h,
        max_eq_right (by linarith)]
      ring
  have hMp : ∑ i, max (μ i) 0 = (S + T) / 2 := by
    rw [Finset.sum_congr rfl fun i _ => hmax i,
      ← Finset.sum_div, Finset.sum_add_distrib,
      ← hSdef, ← hTdef]
  have hMm : ∑ i, max (-(μ i)) 0 = (T - S) / 2 := by
    rw [Finset.sum_congr rfl fun i _ => hmaxneg i,
      ← Finset.sum_div, Finset.sum_sub_distrib,
      ← hSdef, ← hTdef]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← hSdef, ← hTdef]
    field_simp
    ring_nf
  · rw [Finset.sum_congr rfl fun i _ => hpos i,
      ← Finset.mul_sum, hMp]
    field_simp
    ring
  · rw [Finset.sum_congr rfl fun i _ => hneg i,
      ← Finset.mul_sum, hMm]
    field_simp
    ring
  · have hterm : ∀ i, |μ i| * (μ i / |μ i| - S / T) ^ 2
        = |μ i| - 2 * (S / T) * μ i
          + (S / T) ^ 2 * |μ i| := by
      intro i
      have habs : |μ i| ≠ 0 := abs_ne_zero.mpr (hsupp i)
      have hsq : (μ i / |μ i|) ^ 2 = 1 := by
        rw [div_pow, sq_abs]
        field_simp [hsupp i]
      have hcancel : μ i / |μ i| * |μ i| = μ i :=
        div_mul_cancel₀ _ habs
      calc |μ i| * (μ i / |μ i| - S / T) ^ 2
          = (μ i / |μ i|) ^ 2 * |μ i|
            - 2 * (S / T) * (μ i / |μ i| * |μ i|)
            + (S / T) ^ 2 * |μ i| := by ring
        _ = |μ i| - 2 * (S / T) * μ i
            + (S / T) ^ 2 * |μ i| := by
            rw [hsq, hcancel, one_mul]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← hSdef,
      ← hTdef]
    field_simp
    ring
  · intro f
    have hpt : ∀ i,
        f i * max (μ i - S / T * |μ i|) 0
          - f i * max (-(μ i - S / T * |μ i|)) 0
        = f i * (μ i - S / T * |μ i|) := by
      intro i
      rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i _ => hpt i]
    have hexp : ∑ i, f i * (μ i - S / T * |μ i|)
        = ∑ i, f i * μ i
          - S / T * ∑ i, f i * |μ i| := by
      rw [Finset.sum_congr rfl (fun i _ =>
        mul_sub (f i) (μ i) (S / T * |μ i|)),
        Finset.sum_sub_distrib]
      congr 1
      calc ∑ i, f i * (S / T * |μ i|)
          = ∑ i, S / T * (f i * |μ i|) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = S / T * ∑ i, f i * |μ i| :=
            (Finset.mul_sum _ _ _).symm
    rw [hexp]
    field_simp
    ring

end NCG
