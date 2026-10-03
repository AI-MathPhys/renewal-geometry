/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Gravity.ADMReconstructionAssembly
import RenewalGeometry.Gravity.RootRaceScoreGeneral

/-!
# `mt:adm` with clause (ii) on the twelve oriented roots (emergent-spacetime manuscript)

`ADMReconstruction.adm_reconstruction` states clause (ii) for six rates.  The manuscript races
the twelve oriented roots `±r_a` with rates `k_a^±`.  Here clause (ii) is restated as
`clauseIIOrientedRace`: for EVERY finite family of positive directed rates (in particular the
twelve oriented roots, `RootRaceScore.OrientedRoot`, of cardinality `12`) the winner–waiting
statistics form a faithful coordinate system (`lem:supp-race-score`):

* the log-rate score Gram is `𝔼[s_b s_c] = δ_{bc} k_b/K` and positive definite;
* the rates are recovered from the winner probabilities and the mean waiting time
  (`k_b = ℙ(A=b)/𝔼T`), so two positive rate vectors with the same winner–waiting statistics
  coincide;
* winner probabilities alone have covariance `diag(p) - p pᵀ`, singular in the all-ones
  direction, and are invariant under common rescaling (they lose the common scale).

`adm_reconstruction_orientedRace` proves clauses (i), (ii) [oriented-root version], (iii)–(vii)
together.
-/

open Matrix Module

namespace RenewalGeometry

namespace ADMReconstruction

open RootRaceScore

/-- `mt:adm` (ii), faithful rendering: the winner–waiting statistics of a positive exponential
race over any finite family of directed branches are a faithful coordinate system, while the
winner law alone loses the common scale; instantiated at the twelve oriented `A₃` roots. -/
def clauseIIOrientedRace : Prop :=
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℝ), (∀ a, 0 < k a) →
    scoreGram k = diagonal (winnerProb k) ∧ (scoreGram k).PosDef ∧
    winnerCovarianceGram k = winnerCovariance (winnerProb k) ∧
    (Nonempty ι → ¬ (winnerCovariance (winnerProb k)).PosDef) ∧
    (∀ c : ℝ, c ≠ 0 → winnerProb (c • k) = winnerProb k) ∧
    (∀ k' : ι → ℝ, (∀ a, 0 < k' a) →
      (∀ b, raceExpectation k (fun a _ => winnerIndicator b a)
        = raceExpectation k' (fun a _ => winnerIndicator b a)) →
      raceExpectation k (fun _ t => t) = raceExpectation k' (fun _ t => t) → k = k')) ∧
  Fintype.card OrientedRoot = 12 ∧
  ∀ k : OrientedRoot → ℝ, (∀ a, 0 < k a) →
    scoreGram k = diagonal (winnerProb k) ∧ (scoreGram k).PosDef ∧
    winnerCovarianceGram k = winnerCovariance (winnerProb k) ∧
    winnerCovariance (winnerProb k) *ᵥ (fun _ => 1) = 0 ∧
    ¬ (winnerCovariance (winnerProb k)).PosDef ∧
    (∀ c : ℝ, c ≠ 0 → winnerProb (c • k) = winnerProb k) ∧
    (∀ k' : OrientedRoot → ℝ, (∀ a, 0 < k' a) →
      (∀ b, raceExpectation k (fun a _ => winnerIndicator b a)
        = raceExpectation k' (fun a _ => winnerIndicator b a)) →
      raceExpectation k (fun _ t => t) = raceExpectation k' (fun _ t => t) → k = k')

theorem clauseIIOrientedRace_holds : clauseIIOrientedRace :=
  ⟨fun k hk => ⟨scoreGram_eq hk, scoreGram_posDef hk, winnerCovarianceGram_eq hk,
      fun ⟨b⟩ => winnerCovariance_not_posDef hk b, fun _ hc => winnerProb_smul k hc,
      fun _ hk' hwin hwait => rates_eq_of_winner_waiting hk hk' hwin hwait⟩,
    card_orientedRoot, orientedRootRace_score_faithful⟩

/-- **`mt:adm`, minimal faithful `3+1` ADM reconstruction**, with clause (ii) stated for the
twelve oriented roots (and every finite directed race). -/
theorem adm_reconstruction_orientedRace :
    clauseI ∧ clauseIIOrientedRace ∧ clauseIII ∧ clauseIV ∧ clauseV ∧ clauseVI ∧
      clauseVII := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := adm_reconstruction
  exact ⟨h1, clauseIIOrientedRace_holds, h3, h4, h5, h6, h7⟩

end ADMReconstruction

end RenewalGeometry
