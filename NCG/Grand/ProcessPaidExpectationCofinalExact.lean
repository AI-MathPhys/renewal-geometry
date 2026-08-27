/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProcessStockJordanExact
import NCG.Grand.SourceAnchoredCofinalExact

/-!
# Process-paid recurrence in expectation

This lifts the scalar summability lemma to the filtered probability-space
stock process of `ProcessStockJordanExact`, closing
`cor:GT-process-paid-cofinal` at its literal expectation level.
-/

open MeasureTheory

namespace NCG
namespace ProcessPaidExpectation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **(GW.8a)** on the actual process filtration: the Jordan stock identity,
the ordered action-to-stock law, and finite expected inflow, replenishment and
comparison error imply summability of the expected declared debits. -/
theorem expected_debits_summable
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (B i c ε : ℕ → Ω → ℝ)
    (hBint : ∀ n, Integrable (B n) μ)
    (hiint : ∀ n, Integrable (i (n + 1)) μ)
    (hcint : ∀ n, Integrable (c n) μ)
    (hεint : ∀ n, Integrable (ε n) μ)
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hi0 : ∀ n ω, 0 ≤ i (n + 1) ω)
    (hc0 : ∀ n ω, 0 ≤ c n ω)
    (hε0 : ∀ n ω, 0 ≤ ε n ω)
    (hordered : ∀ n ω,
      (μ[B (n + 1) | ℱ n]) ω ≤
        B n ω + i (n + 1) ω - c n ω + ε n ω)
    (hiSum : Summable (fun n => ∫ ω, i (n + 1) ω ∂μ))
    (hrSum : Summable (fun n =>
      ∫ ω, StockJordan.repl μ ℱ B i n ω ∂μ))
    (hεSum : Summable (fun n => ∫ ω, ε n ω ∂μ)) :
    Summable (fun n => ∫ ω, c n ω ∂μ) := by
  let cE : ℕ → ℝ := fun n => ∫ ω, c n ω ∂μ
  let pE : ℕ → ℝ := fun n =>
    ∫ ω, StockJordan.pay μ ℱ B i n ω ∂μ
  let iE : ℕ → ℝ := fun n => ∫ ω, i (n + 1) ω ∂μ
  let rE : ℕ → ℝ := fun n =>
    ∫ ω, StockJordan.repl μ ℱ B i n ω ∂μ
  let εE : ℕ → ℝ := fun n => ∫ ω, ε n ω ∂μ
  apply SourceAnchoredCofinal.process_paid_summable
    cE pE iE rE εE (∫ ω, B 0 ω ∂μ)
  · intro n
    exact integral_nonneg (hc0 n)
  · intro n
    have hpint := StockJordan.integrable_pay μ ℱ B i n (hBint n) (hiint n)
    have hmono := integral_mono_ae (hcint n) (hpint.add (hεint n))
      (Filter.Eventually.of_forall fun ω =>
        StockJordan.debit_le_pay μ ℱ B i n (c n) (ε n) ω (hordered n ω))
    dsimp [cE, pE, εE]
    change (∫ x, c n x ∂μ) ≤
      ∫ x, StockJordan.pay μ ℱ B i n x + ε n x ∂μ at hmono
    rwa [integral_add hpint (hεint n)] at hmono
  · intro N
    have hbal := StockJordan.stock_balance μ ℱ B i hBint hiint N
    have hBN : 0 ≤ ∫ ω, B N ω ∂μ := integral_nonneg (hB0 N)
    dsimp [pE, iE, rE]
    rw [Finset.sum_add_distrib]
    linarith
  · exact hiSum
  · exact hrSum
  · exact hεSum
  · intro n
    exact integral_nonneg (hi0 n)
  · intro n
    exact integral_nonneg fun ω => le_max_right _ _
  · intro n
    exact integral_nonneg (hε0 n)

/-- A divergent deterministic cofinal margin cannot be dominated by the
expected costs of a process whose expected debits are summable. -/
theorem no_expected_cofinal_family
    (cE δ : ℕ → ℝ) (hc : Summable cE)
    (hδ0 : ∀ n, 0 ≤ δ n) (hmargin : ∀ n, δ n ≤ cE n)
    (hdiv : ¬ Summable δ) : False :=
  SourceAnchoredCofinal.no_cofinal_family cE δ hc hδ0 hmargin hdiv

/-- Process-level bundle of `cor:GT-process-paid-cofinal`: finite expected
stock accounting gives finite total expected debit and excludes every
divergent cofinal margin family. -/
theorem process_paid_cofinal_exact
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (B i c ε : ℕ → Ω → ℝ)
    (hBint : ∀ n, Integrable (B n) μ)
    (hiint : ∀ n, Integrable (i (n + 1)) μ)
    (hcint : ∀ n, Integrable (c n) μ)
    (hεint : ∀ n, Integrable (ε n) μ)
    (hB0 : ∀ n ω, 0 ≤ B n ω)
    (hi0 : ∀ n ω, 0 ≤ i (n + 1) ω)
    (hc0 : ∀ n ω, 0 ≤ c n ω)
    (hε0 : ∀ n ω, 0 ≤ ε n ω)
    (hordered : ∀ n ω,
      (μ[B (n + 1) | ℱ n]) ω ≤
        B n ω + i (n + 1) ω - c n ω + ε n ω)
    (hiSum : Summable (fun n => ∫ ω, i (n + 1) ω ∂μ))
    (hrSum : Summable (fun n =>
      ∫ ω, StockJordan.repl μ ℱ B i n ω ∂μ))
    (hεSum : Summable (fun n => ∫ ω, ε n ω ∂μ)) :
    Summable (fun n => ∫ ω, c n ω ∂μ)
      ∧ ∀ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) →
        (∀ n, δ n ≤ ∫ ω, c n ω ∂μ) → ¬ Summable δ → False := by
  have hcSum := expected_debits_summable μ ℱ B i c ε
    hBint hiint hcint hεint hB0 hi0 hc0 hε0 hordered
    hiSum hrSum hεSum
  exact ⟨hcSum, fun δ hδ0 hmargin hdiv =>
    no_expected_cofinal_family _ δ hcSum hδ0 hmargin hdiv⟩

end ProcessPaidExpectation
end NCG
