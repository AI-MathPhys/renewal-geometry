/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FarkasOneHistoryProjectionExact

/-!
# Arithmetic projection of one common history

Simultaneous heterogeneous physical projections of a single finite history,
together with the positive-extension/Farkas alternative and the explicit
pairwise-marginal obstruction.
-/

open Finset Matrix

namespace NCG
namespace ArithmeticCommonHistoryProjectionExact

open FarkasOneHistory

/-- All four declared physical/arithmetic branches have the one common
population value when their writers are pullbacks of the same history writer.
The same theorem packages the exact positive-extension/Farkas alternative and
the concrete parity obstruction to replacing a common cylinder by pairwise
marginals. -/
theorem arithmetic_projection_of_one_common_history
    {Ω Bs Bf Bc Ba R C : Type*}
    [Fintype Ω] [Fintype Bs] [Fintype Bf] [Fintype Bc] [Fintype Ba]
    [Fintype R] [Fintype C]
    [DecidableEq Bs] [DecidableEq Bf] [DecidableEq Bc] [DecidableEq Ba]
    [DecidableEq R] [DecidableEq C]
    (Λ : Ω → ℝ) (wH : Ω → ℝ)
    (πs : Ω → Bs) (ws : Bs → ℝ)
    (πf : Ω → Bf) (wf : Bf → ℝ)
    (πc : Ω → Bc) (wc : Bc → ℝ)
    (πa : Ω → Ba) (wa : Ba → ℝ)
    (hs : ∀ ω, Λ ω ≠ 0 → ws (πs ω) = wH ω)
    (hf : ∀ ω, Λ ω ≠ 0 → wf (πf ω) = wH ω)
    (hc : ∀ ω, Λ ω ≠ 0 → wc (πc ω) = wH ω)
    (ha : ∀ ω, Λ ω ≠ 0 → wa (πa ω) = wH ω)
    (M : Matrix R C ℝ) (d : R → ℝ) :
    let J := ∑ ω, Λ ω * wH ω
    (∑ b, (∑ ω ∈ univ.filter (fun ω => πs ω = b), Λ ω) * ws b = J) ∧
    (∑ b, (∑ ω ∈ univ.filter (fun ω => πf ω = b), Λ ω) * wf b = J) ∧
    (∑ b, (∑ ω ∈ univ.filter (fun ω => πc ω = b), Λ ω) * wc b = J) ∧
    (∑ b, (∑ ω ∈ univ.filter (fun ω => πa ω = b), Λ ω) * wa b = J) ∧
    (((∃ l : C → ℝ, (∀ j, 0 ≤ l j) ∧ M *ᵥ l = d) ∨
        (∃ y : R → ℝ, (∀ j, 0 ≤ (Mᵀ *ᵥ y) j) ∧ y ⬝ᵥ d < 0)) ∧
      ¬ ((∃ l : C → ℝ, (∀ j, 0 ≤ l j) ∧ M *ᵥ l = d) ∧
        (∃ y : R → ℝ, (∀ j, 0 ≤ (Mᵀ *ᵥ y) j) ∧ y ⬝ᵥ d < 0))) ∧
    (∀ a b : Bool,
      (∑ ω, if ω.1 = a ∧ ω.2.1 = b then evenLaw ω else 0) =
        (∑ ω, if ω.1 = a ∧ ω.2.1 = b then oddLaw ω else 0)) ∧
    (∑ ω, evenLaw ω * parity ω = 1 ∧
      ∑ ω, oddLaw ω * parity ω = -1) := by
  dsimp
  refine ⟨pushforward_expectation Λ πs ws wH hs,
    pushforward_expectation Λ πf wf wH hf,
    pushforward_expectation Λ πc wc wH hc,
    pushforward_expectation Λ πa wa wH ha,
    farkas_alternative M d, ?_, parity_laws_triple_expectation⟩
  intro a b
  exact (parity_laws_pairwise_marginals a b).1

end ArithmeticCommonHistoryProjectionExact
end NCG
