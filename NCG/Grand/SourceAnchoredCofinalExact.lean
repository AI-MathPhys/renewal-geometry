/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRecurrenceAndPredictiveCarriers

/-!
# Source-anchored cofinal descent and process-paid cofinality

Exact encodings of `thm:GT-source-anchored-cofinal-descent` and
`cor:GT-process-paid-cofinal`.

* `crossingLevel` (GW.11): `H_* = min {H : ∑_{h ≤ H} δ_h > A_{h₀-1} - A_* + E_*}`,
  which exists under the divergence (GW.10) (`exists_crossing_level`);
* `no_history_crosses` : a history with margins `δ_h` and joint balance
  (GW.9) cannot cross level `H_*` (the contradiction is
  `FiniteRecurrenceAndPredictiveCarriers.source_anchored_crossing_bound`);
* `process_paid_summable` (GW.8a): under (SC.4e) `c_j ≤ p_j + ε_j` and the
  stock identity bound (SC.4b) `∑_{j<N} p_j ≤ B₀ + ∑_{j<N} (i_j + r_j)` with
  summable inflow, replenishment and comparison error, the declared debits are
  summable; `no_cofinal_family`: a cofinal family with `∑ δ_j = ∞` and
  `δ_j ≤ c_j` is impossible.
-/

open Finset

namespace NCG
namespace SourceAnchoredCofinal

/-- Partial margin sums `∑_{h=h₀}^{H} δ_h`, indexed by `H - h₀ + 1` terms from `h₀`. -/
def marginSum (δ : ℕ → ℝ) (h₀ H : ℕ) : ℝ := ∑ h ∈ Finset.Icc h₀ H, δ h

/-- **(GW.10 ⇒ existence of GW.11)**: divergent margins eventually exceed any
budget. -/
theorem exists_crossing_level (δ : ℕ → ℝ) (h₀ : ℕ)
    (hdiv : ∀ C : ℝ, ∃ H, C < marginSum δ h₀ H) (budget : ℝ) :
    ∃ H, budget < marginSum δ h₀ H :=
  hdiv budget

/-- The crossing level `H_*(s)`, the least `H` whose margin sum exceeds the
budget `A_{h₀-1} - A_* + E_*`. -/
noncomputable def crossingLevel (δ : ℕ → ℝ) (h₀ : ℕ) (budget : ℝ)
    (hex : ∃ H, budget < marginSum δ h₀ H) : ℕ :=
  Nat.find hex

theorem crossingLevel_spec (δ : ℕ → ℝ) (h₀ : ℕ) (budget : ℝ)
    (hex : ∃ H, budget < marginSum δ h₀ H) :
    budget < marginSum δ h₀ (crossingLevel δ h₀ budget hex) :=
  Nat.find_spec hex

theorem crossingLevel_min (δ : ℕ → ℝ) (h₀ : ℕ) (budget : ℝ)
    (hex : ∃ H, budget < marginSum δ h₀ H) (H : ℕ) (hH : H < crossingLevel δ h₀ budget hex) :
    marginSum δ h₀ H ≤ budget :=
  le_of_not_gt (Nat.find_min hex hH)

/-- **No history crosses `H_*`**: a history whose realized costs through level
`H` are at least the margins and satisfy the joint balance
`A_H + ∑ c_h ≤ A_{h₀-1} + E_H`, `A_H ≥ A_*`, `E_H ≤ E_*` cannot have
`H = H_*`. -/
theorem no_history_crosses (δ c : ℕ → ℝ) (h₀ : ℕ) (Aprev Astar Estar : ℝ)
    (hex : ∃ H, Aprev - Astar + Estar < marginSum δ h₀ H)
    (H : ℕ) (hH : H = crossingLevel δ h₀ (Aprev - Astar + Estar) hex)
    (hmargin : ∀ h, h₀ ≤ h → h ≤ H → δ h ≤ c h)
    (AH EH : ℝ) (hbalance : AH + ∑ h ∈ Finset.Icc h₀ H, c h ≤ Aprev + EH)
    (hA : Astar ≤ AH) (hE : EH ≤ Estar) : False := by
  have h1 : marginSum δ h₀ H ≤ ∑ h ∈ Finset.Icc h₀ H, c h := by
    unfold marginSum
    refine Finset.sum_le_sum fun h hh => ?_
    rw [Finset.mem_Icc] at hh
    exact hmargin h hh.1 hh.2
  have h2 := crossingLevel_spec δ h₀ (Aprev - Astar + Estar) hex
  rw [← hH] at h2
  linarith

/-- The crossing bound in the form of
`FiniteRecurrenceAndPredictiveCarriers.source_anchored_crossing_bound`. -/
theorem crossing_bound {H : ℕ} (δ : ℕ → ℝ) (budget : ℝ)
    (hcross : ∀ h, h ≤ H → (Finset.range (h + 1)).sum δ ≤ budget)
    (hexceed : budget < (Finset.range (H + 1)).sum δ) : False :=
  FiniteRecurrenceAndPredictiveCarriers.source_anchored_crossing_bound δ budget hcross hexceed

/-! ### Process-paid cofinality (GW.8a) -/

/-- **(GW.8a)**: declared debits paid by a finite stock are summable. -/
theorem process_paid_summable (c p i r ε : ℕ → ℝ) (B₀ : ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hpaid : ∀ j, c j ≤ p j + ε j)
    (hstock : ∀ N, ∑ j ∈ Finset.range N, p j ≤ B₀ + ∑ j ∈ Finset.range N, (i j + r j))
    (hi : Summable i) (hr : Summable r) (hε : Summable ε)
    (hi0 : ∀ j, 0 ≤ i j) (hr0 : ∀ j, 0 ≤ r j) (hε0 : ∀ j, 0 ≤ ε j) :
    Summable c := by
  refine summable_of_sum_range_le hc (c := B₀ + (∑' j, i j + ∑' j, r j) + ∑' j, ε j) fun N => ?_
  calc ∑ j ∈ Finset.range N, c j ≤ ∑ j ∈ Finset.range N, (p j + ε j) :=
        Finset.sum_le_sum fun j _ => hpaid j
    _ = ∑ j ∈ Finset.range N, p j + ∑ j ∈ Finset.range N, ε j := Finset.sum_add_distrib
    _ ≤ (B₀ + ∑ j ∈ Finset.range N, (i j + r j)) + ∑ j ∈ Finset.range N, ε j := by
        gcongr; exact hstock N
    _ = B₀ + (∑ j ∈ Finset.range N, i j + ∑ j ∈ Finset.range N, r j)
          + ∑ j ∈ Finset.range N, ε j := by rw [Finset.sum_add_distrib]
    _ ≤ B₀ + (∑' j, i j + ∑' j, r j) + ∑' j, ε j := by
        gcongr
        · exact hi.sum_le_tsum _ (fun j _ => hi0 j)
        · exact hr.sum_le_tsum _ (fun j _ => hr0 j)
        · exact hε.sum_le_tsum _ (fun j _ => hε0 j)

/-- A cofinal family (`δ_j ≤ c_j`, `∑ δ_j = ∞`) is impossible once the debits
are summable. -/
theorem no_cofinal_family (c δ : ℕ → ℝ) (hc : Summable c)
    (hδ0 : ∀ j, 0 ≤ δ j) (hle : ∀ j, δ j ≤ c j) (hdiv : ¬ Summable δ) : False :=
  hdiv (Summable.of_nonneg_of_le hδ0 hle hc)

end SourceAnchoredCofinal
end NCG
