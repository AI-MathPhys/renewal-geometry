/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DiagonalTendsto
import Mathlib.Topology.Bases

/-!
# Simultaneous diagonal convergence with a topological coordinate

The first coordinate is metric, while the second only needs a first-countable topology.  This
is the appropriate diagonal principle for order-topological extended numbers such as `ENNReal`.
-/

open Filter Topology Set

noncomputable section

namespace NCG

universe u v

/-- Rowwise convergence in a metric coordinate and a first-countable topological coordinate
admits one cofinal diagonal preserving both limits. -/
theorem exists_diagonal_tendsto_pair_topological
    {X : Type u} {Y : Type v} [PseudoMetricSpace X]
    [TopologicalSpace Y] [FirstCountableTopology Y]
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
  obtain ⟨U, hU, hUbasis⟩ := (nhds_basis_opens d).exists_antitone_subbasis
  have hcThreshold : ∀ m, ∃ r ≥ m, c r ∈ U m := by
    intro m
    have hevent := hc.eventually ((hU m).2.mem_nhds (hU m).1)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    exact ⟨max m N, le_max_left _ _, hN _ (le_max_right _ _)⟩
  choose R hRm hRc using hcThreshold
  have hR : Tendsto R atTop atTop := by
    rw [tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop m] with k hk
    exact hk.trans (hRm k)
  let δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hδpos : ∀ m, 0 < δ m := by
    intro m
    dsimp [δ]
    positivity
  have hgThreshold : ∀ m, ∃ N, ∀ n ≥ N,
      dist (g (R m) n) (b (R m)) < δ m := by
    intro m
    exact (Metric.tendsto_atTop.mp (hg (R m))) (δ m) (hδpos m)
  have huThreshold : ∀ m, ∃ N, ∀ n ≥ N, u (R m) n ∈ U m := by
    intro m
    exact eventually_atTop.1
      ((hu (R m)).eventually ((hU m).2.mem_nhds (hRc m)))
  choose Ng hNg using hgThreshold
  choose Nu hNu using huThreshold
  let N : ℕ → ℕ := fun m ↦ max m (max (Ng m) (Nu m))
  let κ : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun m ↦ N m ≤ n) n
  have hκ : Tendsto κ atTop atTop := by
    rw [tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop (N m)] with n hn
    apply Nat.le_findGreatest
    · exact (le_max_left m _).trans hn
    · exact hn
  have hκSpec : ∀ᶠ n in atTop, N (κ n) ≤ n := by
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    change N (Nat.findGreatest (fun m ↦ N m ≤ n) n) ≤ n
    exact Nat.findGreatest_spec (P := fun m ↦ N m ≤ n) (Nat.zero_le n) hn
  let φ : ℕ → ℕ := fun n ↦ R (κ n)
  have hφ : Tendsto φ atTop atTop := hR.comp hκ
  have hδ : Tendsto (fun n ↦ δ (κ n)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hκ
  have hgClose : Tendsto
      (fun n ↦ dist (g (φ n) n) (b (φ n))) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ dist_nonneg
    · filter_upwards [hκSpec] with n hn
      exact (hNg (κ n) n ((le_max_left (Ng (κ n)) _).trans
        ((le_max_right (κ n) _).trans hn))).le
    · exact hδ
  have huBasis : ∀ᶠ n in atTop, u (φ n) n ∈ U (κ n) := by
    filter_upwards [hκSpec] with n hn
    exact hNu (κ n) n ((le_max_right (Ng (κ n)) (Nu (κ n))).trans
      ((le_max_right (κ n) _).trans hn))
  have huDiagonal : Tendsto (fun n ↦ u (φ n) n) atTop (𝓝 d) := by
    refine hUbasis.toHasBasis.tendsto_right_iff.2 ?_
    intro m _
    filter_upwards [huBasis, hκ.eventually (eventually_ge_atTop m)] with n hn hmn
    exact hUbasis.antitone hmn hn
  refine ⟨φ, hφ, ?_, huDiagonal⟩
  exact tendsto_of_dist_tendsto_zero_of_tendsto
    (fun n ↦ g (φ n) n) (fun n ↦ b (φ n)) a hgClose (hb.comp hφ)

end NCG
