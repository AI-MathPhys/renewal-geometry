/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.FiniteNoGoCounterexamples

/-!
# Protected-ledger obstruction to uniform coercivity

This is the concrete contrapositive behind `cor:protected-ledger-short`.
Keeping every deterministic history-copy direction while demanding a fixed
transient contraction factor strictly below one forces the physical metric
condition numbers to escape every finite bound.
-/

open Matrix Filter

namespace NCG

/-- A uniform contraction gap on growing point-readable ledger shifts forces
the Rayleigh condition-number ratios `M_N / m_N` to be unbounded. -/
theorem protectedLedgerConditionNumbersUnbounded
    (G : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ)
    (m M : ℕ → ℝ) (q : ℝ)
    (hm : ∀ N, 0 < m N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hlow : ∀ N (x : Fin N → ℝ),
      m N * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G N *ᵥ x))
    (hupp : ∀ N (x : Fin N → ℝ),
      x ⬝ᵥ (G N *ᵥ x) ≤ M N * (x ⬝ᵥ x))
    (hcontr : ∀ N (x : Fin N → ℝ),
      (ledgerShift N *ᵥ x) ⬝ᵥ (G N *ᵥ (ledgerShift N *ᵥ x))
        ≤ q ^ 2 * (x ⬝ᵥ (G N *ᵥ x))) :
    ∀ κ : ℝ, 1 ≤ κ → ∃ N, κ * m N < M N := by
  intro κ hκ
  by_contra hbounded
  push Not at hbounded
  have hgap := growingLedgerGapExact κ G m M (fun _ => q)
    hm (fun _ => hq0) hbounded hlow hupp hcontr
  have hevent : ∀ᶠ N in atTop, q < q := hgap.2.1 q hq1
  exact (Filter.Eventually.exists hevent).elim fun _ h => (lt_irrefl q h)

end NCG
