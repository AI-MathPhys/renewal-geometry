/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WardCurrentScalars
import NCG.Grand.TwoStateRenewal

/-!
# Fisher information under parameter-independent acceptance

This file formalizes the finite-experiment calculation used by
`cor:SMST-sign-information-rate`: an accepted experiment is mixed with one
parameter-independent rejected outcome, so the rejected score is zero and the
Fisher form is multiplied by the acceptance probability.
-/

open Matrix

namespace NCG

/-- Fisher Gram of a finite real score family. -/
noncomputable def finiteFisherForm {Ω K : Type*}
    [Fintype Ω] [Fintype K] (p : Ω → ℝ) (score : Ω → K → ℝ) :
    Matrix K K ℝ :=
  ∑ ω, p ω • Matrix.vecMulVec (score ω) (score ω)

/-- Add a single rejected outcome, accepted independently with probability
`θ`. -/
noncomputable def acceptedMixtureProbability {Ω : Type*}
    (θ : ℝ) (p : Ω → ℝ) : Ω ⊕ Unit → ℝ
  | Sum.inl ω => θ * p ω
  | Sum.inr _ => 1 - θ

/-- The full score is the conditional accepted score on accepted outcomes and
zero on the parameter-independent rejected outcome. -/
noncomputable def acceptedMixtureScore {Ω K : Type*}
    (score : Ω → K → ℝ) : Ω ⊕ Unit → K → ℝ
  | Sum.inl ω => score ω
  | Sum.inr _ => 0

/-- Parameter-independent acceptance multiplies the complete Fisher matrix by
the acceptance probability. -/
theorem accepted_mixture_fisher_scaling {Ω K : Type*}
    [Fintype Ω] [Fintype K] (θ : ℝ) (p : Ω → ℝ)
    (score : Ω → K → ℝ) :
    finiteFisherForm (acceptedMixtureProbability θ p)
        (acceptedMixtureScore score)
      = θ • finiteFisherForm p score := by
  ext i j
  simp [finiteFisherForm, acceptedMixtureProbability,
    acceptedMixtureScore]
  simp only [Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by
    ring

/-- At completed-private opportunity rate `4/11`, the raw-time Fisher form is
`(4/11) θ` times the accepted Fisher form. -/
theorem accepted_sign_raw_time_fisher {Ω K : Type*}
    [Fintype Ω] [Fintype K] (θ : ℝ) (p : Ω → ℝ)
    (score : Ω → K → ℝ) :
    (4 / 11 : ℝ) •
        finiteFisherForm (acceptedMixtureProbability θ p)
          (acceptedMixtureScore score)
      = ((4 / 11 : ℝ) * θ) • finiteFisherForm p score := by
  rw [accepted_mixture_fisher_scaling, smul_smul]

/-- The completed-private inter-opportunity law has mean `11/4`, the renewal
constant whose reciprocal is the raw-time opportunity rate `4/11`. -/
theorem completed_private_mean_for_information_rate :
    ∑' N : ℕ, (6 * (1 / 3 : ℝ) ^ N - 5 * (1 / 5 : ℝ) ^ N)
      = 11 / 4 :=
  completed_private_renewal.2

/-- Positive acceptance cannot collapse a positive accepted-sign frame. -/
theorem accepted_sign_frame_remains_positive {K : Type*} [Finite K]
    (Iacc : Matrix K K ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hI : Iacc.PosDef) :
    (θ • Iacc).PosDef ∧
      (((4 / 11 : ℝ) * θ) • Iacc).PosDef := by
  constructor
  · exact hI.smul hθ
  · exact hI.smul (mul_pos (by norm_num) hθ)

/-- `cor:SMST-sign-information-rate`, including the finite experiment that
produces the opportunity scaling, the renewal-rate scaling, and preservation
of positive definiteness. -/
theorem smst_sign_information_rate_exact {Ω K : Type*}
    [Fintype Ω] [Fintype K] (θ : ℝ) (p : Ω → ℝ)
    (score : Ω → K → ℝ) (hθ : 0 < θ)
    (hI : (finiteFisherForm p score).PosDef) :
    finiteFisherForm (acceptedMixtureProbability θ p)
        (acceptedMixtureScore score)
        = θ • finiteFisherForm p score
    ∧ (∑' N : ℕ,
        (6 * (1 / 3 : ℝ) ^ N - 5 * (1 / 5 : ℝ) ^ N)) = 11 / 4
    ∧ (4 / 11 : ℝ) •
        finiteFisherForm (acceptedMixtureProbability θ p)
          (acceptedMixtureScore score)
        = ((4 / 11 : ℝ) * θ) • finiteFisherForm p score
    ∧ (θ • finiteFisherForm p score).PosDef
    ∧ (((4 / 11 : ℝ) * θ) • finiteFisherForm p score).PosDef := by
  exact ⟨accepted_mixture_fisher_scaling θ p score,
    completed_private_mean_for_information_rate,
    accepted_sign_raw_time_fisher θ p score,
    (accepted_sign_frame_remains_positive
      (finiteFisherForm p score) θ hθ hI).1,
    (accepted_sign_frame_remains_positive
      (finiteFisherForm p score) θ hθ hI).2⟩

end NCG
