/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TrineComplexAcquisitionAndTransport

/-!
# Trine transport: remaining exact clauses

Completes `thm:GT-trine-slack-transport` and `thm:GT-trine-cofinal`
on top of `TrineComplexAcquisitionAndTransport`:

* `partition_zero_positive_carrier`: a partition zero
  `ζ_C(𝖢) = 0` coexisting with a strictly positive carrier mass
  `τ_C(𝖢) > 0` (explicit two-point witness);
* `trine_payoff_transport`: the boxed payoff bound
  `|∫A dζ_X - ∫A∘π dζ_Y| ≤ ‖A‖_∞·ε^tri` from total-variation
  duality and the trine transport estimate;
* `slack_tendsto`: the slack measure is continuous along convergent
  carrier/complex sequences (`μ ↦ |μ|` is 1-Lipschitz), so the
  inherited/cancellation slack has a unique limit;
* `normalized_amplitude_tendsto`: normalized amplitudes converge
  under a uniform nonzero partition floor.
-/

open Finset Filter Topology

namespace NCG
namespace TrineComplexAcquisitionAndTransport

open FiniteTargetProjectionAndQuotients AcceptedActionInformationPythagoras

/-- **Partition zero with positive carrier**: two opposite-phase arms of
equal weight give `ζ(𝖢) = 0` while `τ(𝖢) = 2 > 0`. -/
theorem partition_zero_positive_carrier :
    ∃ (τ : Fin 2 → ℝ) (ζ : Fin 2 → ℂ),
      (∀ x, 0 ≤ τ x) ∧ (∀ x, 2 * ‖ζ x‖ ≤ τ x) ∧
      (∑ x, ζ x) = 0 ∧ 0 < ∑ x, τ x := by
  refine ⟨![2, 2], ![1, -1], ?_, ?_, ?_, ?_⟩
  · intro x; fin_cases x <;> norm_num
  · intro x; fin_cases x <;> norm_num
  · simp [Fin.sum_univ_two]
  · simp [Fin.sum_univ_two]

/-- Total-variation duality: a bounded payoff against a complex measure is
bounded by `‖A‖_∞` times the total variation. -/
theorem complexIntegral_le_sup_mul_variation {X : Type*} [Fintype X]
    (ζ : X → ℂ) (A : X → ℂ) (M : ℝ) (hA : ∀ x, ‖A x‖ ≤ M) :
    ‖complexIntegral ζ A‖ ≤ M * complexVariation ζ := by
  unfold complexIntegral complexVariation
  calc ‖∑ x, ζ x * A x‖ ≤ ∑ x, ‖ζ x * A x‖ := norm_sum_le _ _
    _ = ∑ x, ‖ζ x‖ * ‖A x‖ := by simp
    _ ≤ ∑ x, ‖ζ x‖ * M :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hA x) (norm_nonneg _)
    _ = M * ∑ x, ‖ζ x‖ := by rw [← Finset.sum_mul]; ring

/-- **Boxed payoff transport**:
`|∫A dζ_X - ∫A∘π dζ_Y| ≤ ‖A‖_∞·ε` whenever the transported complex
measures are within `ε` in total variation. -/
theorem trine_payoff_transport {ΩY X : Type*} [Fintype ΩY] [Fintype X]
    [DecidableEq X] (π : ΩY → X) (ζX : X → ℂ) (ζY : ΩY → ℂ)
    (A : X → ℂ) (M ε : ℝ) (hA : ∀ x, ‖A x‖ ≤ M)
    (hε : complexVariation (fun x => ζX x - complexPushforward π ζY x)
      ≤ ε) (hM : 0 ≤ M) :
    ‖complexIntegral ζX A
        - complexIntegral ζY (fun ω => A (π ω))‖ ≤ M * ε := by
  rw [complex_pushforward_change_variables π ζY A]
  have hdiff : complexIntegral ζX A
      - complexIntegral (complexPushforward π ζY) A
      = complexIntegral (fun x => ζX x - complexPushforward π ζY x) A := by
    unfold complexIntegral
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hdiff]
  calc ‖complexIntegral (fun x => ζX x - complexPushforward π ζY x) A‖
      ≤ M * complexVariation
          (fun x => ζX x - complexPushforward π ζY x) :=
        complexIntegral_le_sup_mul_variation _ A M hA
    _ ≤ M * ε := mul_le_mul_of_nonneg_left hε hM

/-- **Slack continuity**: along convergent carrier and complex sequences
the slack measure converges (the modulus is 1-Lipschitz). -/
theorem slack_tendsto {X : Type*}
    (τ : ℕ → X → ℝ) (ζ : ℕ → X → ℂ) (τlim : X → ℝ) (ζlim : X → ℂ)
    (hτ : ∀ x, Tendsto (fun n => τ n x) atTop (𝓝 (τlim x)))
    (hζ : ∀ x, Tendsto (fun n => ζ n x) atTop (𝓝 (ζlim x))) (x : X) :
    Tendsto (fun n => slack (τ n) (ζ n) x) atTop
      (𝓝 (slack τlim ζlim x)) := by
  unfold slack
  exact (hτ x).sub (((hζ x).norm).const_mul 2)

/-- **Normalized amplitudes** converge once the partition amplitudes have
a nonzero limit (uniform floor): division is continuous on that branch. -/
theorem normalized_amplitude_tendsto {X : Type*}
    (τ : ℕ → X → ℝ) (ζ : ℕ → X → ℂ) (τlim : X → ℝ) (ζlim : X → ℂ)
    (hτ : ∀ x, Tendsto (fun n => τ n x) atTop (𝓝 (τlim x)))
    (hζ : ∀ x, Tendsto (fun n => ζ n x) atTop (𝓝 (ζlim x)))
    (x : X) (hfloor : τlim x ≠ 0) :
    Tendsto (fun n => ζ n x / (τ n x : ℂ)) atTop
      (𝓝 (ζlim x / (τlim x : ℂ))) := by
  have hτC : Tendsto (fun n => (τ n x : ℂ)) atTop (𝓝 (τlim x : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (hτ x)
  have hne : (τlim x : ℂ) ≠ 0 := by exact_mod_cast hfloor
  exact (hζ x).div hτC hne

end TrineComplexAcquisitionAndTransport
end NCG
