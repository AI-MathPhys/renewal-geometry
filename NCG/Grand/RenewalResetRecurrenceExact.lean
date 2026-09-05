/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PowerSummabilitySpectralRadius

/-!
# Reset and finite survivor recurrence

The analytic core of `thm:GT-renewal-reset-recurrence` is the exact finite
Banach-algebra criterion saying that survivor powers vanish precisely when the
survivor spectral radius is below one.  This file records that criterion and
the reset/recurrence conjunction used by an ordinary marked-renewal packet.
-/

open Filter Topology
open scoped NNReal ENNReal

namespace NCG
namespace RenewalResetRecurrenceExact

/-! ## Rank-one normalized post-completion panels -/

/-- Linear rank of an exhaustive post-completion Hankel panel. -/
def PostCompletionPanelRankOne
    {H F : Type*} [Fintype H] [Fintype F]
    (column : H → F → ℂ) : Prop :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range column)) = 1

/-- For normalized future columns, linear rank one is equivalent to one common
conditional future law.  Normalization at the empty future removes the scalar
ambiguity in a one-dimensional span. -/
theorem postCompletionPanel_rankOne_iff_all_futureLaws_equal
    {H F : Type*} [Fintype H] [Fintype F] [Nonempty H]
    (empty : F) (column : H → F → ℂ)
    (hnorm : ∀ h, column h empty = 1) :
    PostCompletionPanelRankOne column ↔
      ∀ h₁ h₂, column h₁ = column h₂ := by
  classical
  let h₀ : H := Classical.choice inferInstance
  have hne : column h₀ ≠ 0 := by
    intro hz
    have := congrFun hz empty
    simp [hnorm] at this
  constructor
  · intro hrank h₁ h₂
    let S := Submodule.span ℂ (Set.range column)
    have hmem0 : column h₀ ∈ S :=
      Submodule.subset_span (Set.mem_range_self h₀)
    have hS : S = ℂ ∙ column h₀ :=
      eq_span_singleton_of_mem_of_finrank_eq_one
        hrank hmem0 hne
    have scalar_eq_one (h : H) :
        ∃ c : ℂ, c = 1 ∧ c • column h₀ = column h := by
      have hmem : column h ∈ S :=
        Submodule.subset_span (Set.mem_range_self h)
      rw [hS, Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have he := congrFun hc empty
      have hc1 : c = 1 := by simpa [hnorm] using he
      exact ⟨c, hc1, hc⟩
    obtain ⟨c₁, hc₁, hcol₁⟩ := scalar_eq_one h₁
    obtain ⟨c₂, hc₂, hcol₂⟩ := scalar_eq_one h₂
    calc
      column h₁ = column h₀ := by simpa [hc₁] using hcol₁.symm
      _ = column h₂ := by simpa [hc₂] using hcol₂
  · intro hall
    have hrange : Set.range column = {column h₀} := by
      ext v
      constructor
      · rintro ⟨h, rfl⟩
        simp [hall h h₀]
      · intro hv
        simp only [Set.mem_singleton_iff] at hv
        exact ⟨h₀, hv.symm⟩
    unfold PostCompletionPanelRankOne
    rw [hrange]
    exact finrank_span_singleton hne

/-- Powers of a complex Banach-algebra element converge to zero in norm iff
its spectral radius is strictly below one. -/
theorem tendsto_norm_powers_iff_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Nontrivial A] [NormOneClass A] (a : A) :
    Tendsto (fun n : ℕ => ‖a ^ n‖) atTop (𝓝 0) ↔
      spectralRadius ℂ a < 1 := by
  constructor
  · intro hzero
    have hevent : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ < 1 :=
      (tendsto_order.1 hzero).2 1 zero_lt_one
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    have hp : ‖a ^ (N + 1)‖ < 1 := hN (N + 1) (Nat.le_succ N)
    have hp' : (‖a ^ (N + 1)‖₊ : ℝ≥0∞) < 1 := by
      exact_mod_cast hp
    calc
      spectralRadius ℂ a
          ≤ (‖a ^ (N + 1)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) *
              (‖(1 : A)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) :=
        spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ a N
      _ = (‖a ^ (N + 1)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) := by simp
      _ < 1 := ENNReal.rpow_lt_one hp' (by positivity)
  · intro hradius
    exact (summable_norm_powers_iff_spectralRadius_lt_one a).2 hradius
      |>.tendsto_atTop_zero

/-- Almost-sure finite completion for a finite survivor transfer is norm
extinction of all survivor powers.  In finite dimension this is equivalent to
the usual decay of every initial survivor mass. -/
def NextCompletionAlmostSure
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (Q : A) : Prop :=
  Tendsto (fun n : ℕ => ‖Q ^ n‖) atTop (𝓝 0)

/-- The boxed recurrence criterion `(RN.0b)`. -/
theorem nextCompletionAlmostSure_iff_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Nontrivial A] [NormOneClass A] (Q : A) :
    NextCompletionAlmostSure Q ↔ spectralRadius ℂ Q < 1 :=
  tendsto_norm_powers_iff_spectralRadius_lt_one Q

/-- Finite predictive data needed for the reset/renewal criterion.  The reset
clause is independent of the survivor transfer and is deliberately retained
as a separate field. -/
structure PredictiveRenewalPacket
    (A : Type*) [NormedRing A] [NormedAlgebra ℂ A] where
  /-- All completion letters land in one minimal predictive future class. -/
  resetRankOne : Prop
  /-- The noncompletion survivor transfer reachable from that class. -/
  survivor : A

/-- Ordinary marked renewal is exactly rank-one predictive reset together
with almost-sure finite completion. -/
def IsOrdinaryMarkedRenewal
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (P : PredictiveRenewalPacket A) : Prop :=
  P.resetRankOne ∧ NextCompletionAlmostSure P.survivor

/-- The boxed conjunction `(RN.0c)`, with recurrence rewritten spectrally. -/
theorem ordinaryMarkedRenewal_iff_reset_and_spectralRadius
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Nontrivial A] [NormOneClass A] (P : PredictiveRenewalPacket A) :
    IsOrdinaryMarkedRenewal P ↔
      P.resetRankOne ∧ spectralRadius ℂ P.survivor < 1 := by
  simp only [IsOrdinaryMarkedRenewal,
    nextCompletionAlmostSure_iff_spectralRadius_lt_one]

/-- Successive excursion words are independent with common law `μ` exactly
when every finite joint word probability factors into the corresponding
one-excursion probabilities. -/
def ExcursionWordsIID {W : Type*}
    (joint : List W → ℝ) (μ : W → ℝ) : Prop :=
  ∀ words, joint words = (words.map μ).prod

/-- The one-excursion law is uniquely determined by the predictive joint
table: its value is the singleton-excursion probability. -/
theorem excursionWordLaw_unique_of_factorization
    {W : Type*} (joint : List W → ℝ) (μ ν : W → ℝ)
    (hμ : ExcursionWordsIID joint μ) (hν : ExcursionWordsIID joint ν) :
    μ = ν := by
  funext w
  have hμw := hμ [w]
  have hνw := hν [w]
  simpa using hμw.symm.trans hνw

/-- The waiting-time law is then uniquely derived by summing the unique
excursion-word law over words of each duration. -/
theorem waitingTimeLaw_unique_of_excursionLaw_unique
    {W : Type*} [Fintype W] (duration : W → ℕ) (μ ν : W → ℝ)
    (hμν : μ = ν) :
    (fun n => ∑ w : W, if duration w = n then μ w else 0) =
      fun n => ∑ w : W, if duration w = n then ν w else 0 := by
  subst ν
  rfl

/-- Reset and recurrence are logically independent: any prescribed pair of
truth values is represented by a finite scalar survivor packet.  `Q = 0`
is recurrent and `Q = 1` is a closed survivor class. -/
theorem reset_recurrence_all_four_witnesses (reset recurrent : Bool) :
    ∃ P : PredictiveRenewalPacket ℂ,
      (P.resetRankOne ↔ reset = true) ∧
      (NextCompletionAlmostSure P.survivor ↔ recurrent = true) := by
  let Q : ℂ := if recurrent then 0 else 1
  let P : PredictiveRenewalPacket ℂ :=
    { resetRankOne := reset = true
      survivor := Q }
  refine ⟨P, Iff.rfl, ?_⟩
  cases recurrent <;> simp [P, Q, NextCompletionAlmostSure]

end RenewalResetRecurrenceExact
end NCG
