/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find

/-!
# Simultaneous diagonal convergence

This file supplies a metric diagonal-selection theorem for two coupled convergences.  It is
designed for recovery arguments: one coordinate controls vectors in a common carrier and the
other controls their energies.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v

/-- A sequence asymptotic to a convergent comparison sequence has the same limit. -/
theorem tendsto_of_dist_tendsto_zero_of_tendsto
    {X : Type u} [PseudoMetricSpace X]
    (f g : ℕ → X) (a : X)
    (hfg : Tendsto (fun n ↦ dist (f n) (g n)) atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hga := tendsto_iff_dist_tendsto_zero.mp hg
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ dist_nonneg
  · exact Eventually.of_forall fun n ↦ dist_triangle (f n) (g n) a
  · simpa using hfg.add hga

/-- Given two arrays converging along every row, and convergent row limits, one cofinal diagonal
makes both coordinates converge simultaneously. -/
theorem exists_diagonal_tendsto_pair
    {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (g : ℕ → ℕ → X) (b : ℕ → X) (a : X)
    (u : ℕ → ℕ → Y) (c : ℕ → Y) (d : Y)
    (hg : ∀ m, Tendsto (g m) atTop (𝓝 (b m)))
    (hb : Tendsto b atTop (𝓝 a))
    (hu : ∀ m, Tendsto (u m) atTop (𝓝 (c m)))
    (hc : Tendsto c atTop (𝓝 d)) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      Tendsto (fun n ↦ g (φ n) n) atTop (𝓝 a) ∧
        Tendsto (fun n ↦ u (φ n) n) atTop (𝓝 d) := by
  classical
  let δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hδpos : ∀ m, 0 < δ m := by
    intro m
    dsimp [δ]
    positivity
  have hgThreshold : ∀ m, ∃ N, ∀ n ≥ N,
      dist (g m n) (b m) < δ m := by
    intro m
    exact (Metric.tendsto_atTop.mp (hg m)) (δ m) (hδpos m)
  have huThreshold : ∀ m, ∃ N, ∀ n ≥ N,
      dist (u m n) (c m) < δ m := by
    intro m
    exact (Metric.tendsto_atTop.mp (hu m)) (δ m) (hδpos m)
  choose Ng hNg using hgThreshold
  choose Nu hNu using huThreshold
  let N : ℕ → ℕ := fun m ↦ max m (max (Ng m) (Nu m))
  let φ : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun m ↦ N m ≤ n) n
  have hφ : Tendsto φ atTop atTop := by
    rw [tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop (N m)] with n hn
    apply Nat.le_findGreatest
    · exact (le_max_left m _).trans hn
    · exact hn
  have hφSpec : ∀ᶠ n in atTop, N (φ n) ≤ n := by
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    change N (Nat.findGreatest (fun m ↦ N m ≤ n) n) ≤ n
    exact Nat.findGreatest_spec (P := fun m ↦ N m ≤ n) (Nat.zero_le n) hn
  have hδ : Tendsto (fun n ↦ δ (φ n)) atTop (𝓝 0) := by
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ
  have hgClose : Tendsto
      (fun n ↦ dist (g (φ n) n) (b (φ n))) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ dist_nonneg
    · filter_upwards [hφSpec] with n hn
      exact (hNg (φ n) n ((le_max_left (Ng (φ n)) _).trans
        ((le_max_right (φ n) _).trans hn))).le
    · exact hδ
  have huClose : Tendsto
      (fun n ↦ dist (u (φ n) n) (c (φ n))) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ dist_nonneg
    · filter_upwards [hφSpec] with n hn
      exact (hNu (φ n) n ((le_max_right (Ng (φ n)) (Nu (φ n))).trans
        ((le_max_right (φ n) _).trans hn))).le
    · exact hδ
  refine ⟨φ, hφ, ?_, ?_⟩
  · exact tendsto_of_dist_tendsto_zero_of_tendsto
      (fun n ↦ g (φ n) n) (fun n ↦ b (φ n)) a hgClose (hb.comp hφ)
  · exact tendsto_of_dist_tendsto_zero_of_tendsto
      (fun n ↦ u (φ n) n) (fun n ↦ c (φ n)) d huClose (hc.comp hφ)

end NCG
