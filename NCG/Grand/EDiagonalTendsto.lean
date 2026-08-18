/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DiagonalTendsto
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Simultaneous diagonal convergence with an extended-metric coordinate

This variant of the metric diagonal selector allows the second coordinate to carry an extended
metric.  It is needed for ENNReal energies, whose natural mathlib topology is emetric rather than
pseudometric.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v

/-- An extended-metric sequence asymptotic to a convergent comparison sequence has the same
limit. -/
theorem tendsto_of_edist_tendsto_zero_of_tendsto
    {Y : Type v} [PseudoEMetricSpace Y]
    (f g : ℕ → Y) (a : Y)
    (hfg : Tendsto (fun n ↦ edist (f n) (g n)) atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  rw [EMetric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hsum : ε / 2 + ε / 2 = ε := ENNReal.add_halves ε
  have hclose : ∀ᶠ n in atTop, edist (f n) (g n) < ε / 2 :=
    hfg.eventually (Iio_mem_nhds hhalf)
  have hlimit := (EMetric.tendsto_nhds.mp hg) (ε / 2) hhalf
  filter_upwards [hclose, hlimit] with n hnClose hnLimit
  calc
    edist (f n) a ≤ edist (f n) (g n) + edist (g n) a := edist_triangle _ _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hnClose hnLimit
    _ = ε := hsum

/-- A metric coordinate and an extended-metric coordinate can be diagonalized simultaneously. -/
theorem exists_diagonal_tendsto_pair_emetric
    {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoEMetricSpace Y]
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
  let ε : ℕ → ENNReal := fun m ↦ ENNReal.ofReal (δ m)
  have hδpos : ∀ m, 0 < δ m := by
    intro m
    dsimp [δ]
    positivity
  have hεpos : ∀ m, 0 < ε m := by
    intro m
    exact ENNReal.ofReal_pos.mpr (hδpos m)
  have hgThreshold : ∀ m, ∃ N, ∀ n ≥ N,
      dist (g m n) (b m) < δ m := by
    intro m
    exact (Metric.tendsto_atTop.mp (hg m)) (δ m) (hδpos m)
  have huThreshold : ∀ m, ∃ N, ∀ n ≥ N,
      edist (u m n) (c m) < ε m := by
    intro m
    exact (EMetric.tendsto_atTop.mp (hu m)) (ε m) (hεpos m)
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
  have hδ : Tendsto (fun n ↦ δ (φ n)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ
  have hε : Tendsto (fun n ↦ ε (φ n)) atTop (𝓝 0) := by
    simpa [ε] using ENNReal.tendsto_ofReal hδ
  have hgClose : Tendsto
      (fun n ↦ dist (g (φ n) n) (b (φ n))) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ dist_nonneg
    · filter_upwards [hφSpec] with n hn
      exact (hNg (φ n) n ((le_max_left (Ng (φ n)) _).trans
        ((le_max_right (φ n) _).trans hn))).le
    · exact hδ
  have huClose : Tendsto
      (fun n ↦ edist (u (φ n) n) (c (φ n))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hε
    · exact Eventually.of_forall fun _ ↦ bot_le
    · filter_upwards [hφSpec] with n hn
      exact (hNu (φ n) n ((le_max_right (Ng (φ n)) (Nu (φ n))).trans
        ((le_max_right (φ n) _).trans hn))).le
  refine ⟨φ, hφ, ?_, ?_⟩
  · exact tendsto_of_dist_tendsto_zero_of_tendsto
      (fun n ↦ g (φ n) n) (fun n ↦ b (φ n)) a hgClose (hb.comp hφ)
  · exact tendsto_of_edist_tendsto_zero_of_tendsto
      (fun n ↦ u (φ n) n) (fun n ↦ c (φ n)) d huClose (hc.comp hφ)

end NCG
