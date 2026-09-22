/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# A finite execution certificate for the proposal floor
  (`lem:supp-executed-proposal-floor`, emergent spacetime)

A launch race with finitely many bins `0, …, J-1` (the manuscript's
`1, …, J`, shifted by one).  Conditional on no earlier launch, `a l`
is the probability of any launch and `f l` the probability of a
predictor-marked launch in bin `l`; `S l = ∏_{i<l} (1 - a i)` is
the no-launch survival (`S 0 = 1`).

* `survivalProduct_telescope` — `∑_{l<J} S l · a l = 1 - S J`;
* `proposal_floor_arith` — the finite arithmetic certificate
  `ρ_* (1 - e^{-A_*}) ≤ ∑_{l<J} S l · f l` from
  `f l ≥ ρ_* a l` and `-log S_J ≥ A_*`;
* `executed_proposal_floor` — the boxed floor
  `p(𝒢) ≥ q_* ρ_* (1 - e^{-A_*})` on a probability space: the
  no-earlier-launch events `N l` (decreasing, `N 0 = univ`), the
  predictor-marked first-launch events `P l ⊆ N l \ N (l+1)`, the
  conditional launch and predictor-launch probabilities rendered
  as `μ(N l \ N (l+1)) = a l · μ(N l)`, `μ(P l) = f l · μ(N l)`,
  and the conditional execution floor `μ(𝒢 ∩ P l) ≥ q_* μ(P l)`.
-/

namespace RenewalGeometry

open MeasureTheory

/-- The no-launch survival `S l = ∏_{i<l} (1 - a i)` of
`lem:supp-executed-proposal-floor` (`S 0 = 1`). -/
def survivalProduct (a : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∏ i ∈ Finset.range l, (1 - a i)

/-- `lem:supp-executed-proposal-floor` (telescoping): since
`S l · a l = S l - S (l+1)`, the first-launch probabilities sum to
`∑_{l<J} S l · a l = 1 - S J`. -/
theorem survivalProduct_telescope (a : ℕ → ℝ) (J : ℕ) :
    ∑ l ∈ Finset.range J, survivalProduct a l * a l
      = 1 - survivalProduct a J := by
  induction J with
  | zero => simp [survivalProduct]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [survivalProduct, Finset.prod_range_succ]
      ring

/-- `lem:supp-executed-proposal-floor` (arithmetic certificate): with
`0 ≤ S l`, the launch share `ρ_* a l ≤ f l`, and `A_* ≤ -log S_J`,
the predictor launch probability `∑_{l<J} S l · f l` is at least
`ρ_* (1 - S J) ≥ ρ_* (1 - e^{-A_*})`. -/
theorem proposal_floor_arith (a f : ℕ → ℝ) (J : ℕ) (ρ A : ℝ)
    (hS : ∀ l, 0 ≤ survivalProduct a l)
    (hshare : ∀ l, ρ * a l ≤ f l)
    (hA : A ≤ -Real.log (survivalProduct a J)) (hρ : 0 ≤ ρ) :
    ρ * (1 - Real.exp (-A))
      ≤ ∑ l ∈ Finset.range J, survivalProduct a l * f l := by
  have h1 : ρ * (1 - survivalProduct a J)
      ≤ ∑ l ∈ Finset.range J, survivalProduct a l * f l := by
    rw [← survivalProduct_telescope, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    calc ρ * (survivalProduct a l * a l)
        = survivalProduct a l * (ρ * a l) := by ring
      _ ≤ survivalProduct a l * f l :=
          mul_le_mul_of_nonneg_left (hshare l) (hS l)
  have h2 : survivalProduct a J ≤ Real.exp (-A) := by
    rcases (hS J).eq_or_lt with h | h
    · rw [← h]
      exact (Real.exp_pos _).le
    · have hlog : Real.log (survivalProduct a J) ≤ -A := by linarith
      calc survivalProduct a J
          = Real.exp (Real.log (survivalProduct a J)) :=
            (Real.exp_log h).symm
        _ ≤ Real.exp (-A) := Real.exp_le_exp.2 hlog
  calc ρ * (1 - Real.exp (-A)) ≤ ρ * (1 - survivalProduct a J) := by
        apply mul_le_mul_of_nonneg_left _ hρ
        linarith
    _ ≤ _ := h1

/-- `lem:supp-executed-proposal-floor` (boxed
`eq:supp-executed-proposal-floor`): on a probability space, let
`N l` be the event of no launch in bins `< l` (`N 0 = univ`,
decreasing), `P l ⊆ N l \ N (l+1)` the event of a predictor-marked
first launch in bin `l`, and `𝒢` the certified-output event.  If the
conditional launch probabilities satisfy
`μ(N l \ N (l+1)) = a l · μ(N l)` and `μ(P l) = f l · μ(N l)`, the
conditional execution floor `μ(𝒢 ∩ P l) ≥ q_* μ(P l)` holds, the
launch share `f l ≥ ρ_* a l`, `-log S_J ≥ A_* > 0`, `0 < ρ_* ≤ 1`
and `q_* > 0`, then `p(𝒢) ≥ q_* ρ_* (1 - e^{-A_*})`. -/
theorem executed_proposal_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ℕ)
    (N P : ℕ → Set Ω) (G : Set Ω)
    (hN : ∀ l, MeasurableSet (N l)) (hP : ∀ l, MeasurableSet (P l))
    (hG : MeasurableSet G)
    (hN0 : N 0 = Set.univ) (hNsucc : ∀ l, N (l + 1) ⊆ N l)
    (hPN : ∀ l, P l ⊆ N l \ N (l + 1))
    (a f : ℕ → ℝ) (ρ A q : ℝ)
    (ha : ∀ l, (μ (N l \ N (l + 1))).toReal = a l * (μ (N l)).toReal)
    (hf : ∀ l, (μ (P l)).toReal = f l * (μ (N l)).toReal)
    (hq : ∀ l, q * (μ (P l)).toReal ≤ (μ (G ∩ P l)).toReal)
    (hshare : ∀ l, ρ * a l ≤ f l)
    (hA : A ≤ -Real.log (survivalProduct a J)) (_hApos : 0 < A)
    (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1) (hqpos : 0 < q) :
    q * ρ * (1 - Real.exp (-A)) ≤ (μ G).toReal := by
  -- the no-launch survival is the measure of `N l`
  have hS : ∀ l, (μ (N l)).toReal = survivalProduct a l := by
    intro l
    induction l with
    | zero => simp [hN0, survivalProduct]
    | succ n ih =>
        have hdiff : μ (N n \ N (n + 1)) = μ (N n) - μ (N (n + 1)) :=
          measure_sdiff (hNsucc n) (hN (n + 1)).nullMeasurableSet
            (measure_ne_top μ _)
        have hle : μ (N (n + 1)) ≤ μ (N n) := measure_mono (hNsucc n)
        have h1 := ha n
        rw [hdiff, ENNReal.toReal_sub_of_le hle (measure_ne_top μ _), ih]
          at h1
        have hstep : survivalProduct a (n + 1)
            = survivalProduct a n * (1 - a n) := by
          simp [survivalProduct, Finset.prod_range_succ]
        rw [hstep]
        linarith
  -- the predictor-marked first-launch events are pairwise disjoint
  have hanti : Antitone N := antitone_nat_of_succ_le hNsucc
  have hdisjP : ∀ i j, i < j → Disjoint (P i) (P j) := by
    intro i j hij
    have h1 : P i ⊆ N i \ N (i + 1) := hPN i
    have h2 : P j ⊆ N (i + 1) :=
      (hPN j).trans (Set.sdiff_subset.trans (hanti (Nat.succ_le_of_lt hij)))
    exact Set.disjoint_sdiff_left.mono h1 h2
  have hdisj : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint
      (fun l => G ∩ P l) := by
    intro i _ j _ hij
    show Disjoint (G ∩ P i) (G ∩ P j)
    rcases lt_or_gt_of_ne hij with h | h
    · exact (hdisjP i j h).mono Set.inter_subset_right Set.inter_subset_right
    · exact ((hdisjP j i h).mono Set.inter_subset_right
        Set.inter_subset_right).symm
  have hsum : ∑ l ∈ Finset.range J, μ (G ∩ P l) ≤ μ G := by
    rw [← measure_biUnion_finset hdisj (fun l _ => hG.inter (hP l))]
    exact measure_mono (Set.iUnion₂_subset fun l _ => Set.inter_subset_left)
  have hsumR : ∑ l ∈ Finset.range J, (μ (G ∩ P l)).toReal ≤ (μ G).toReal := by
    rw [← ENNReal.toReal_sum (fun l _ => measure_ne_top μ _)]
    exact ENNReal.toReal_mono (measure_ne_top μ _) hsum
  -- assemble
  have hcore := proposal_floor_arith a f J ρ A
    (fun l => by rw [← hS]; exact ENNReal.toReal_nonneg) hshare hA hρ.le
  have hmid : q * ∑ l ∈ Finset.range J, survivalProduct a l * f l
      ≤ ∑ l ∈ Finset.range J, (μ (G ∩ P l)).toReal := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    calc q * (survivalProduct a l * f l) = q * (μ (P l)).toReal := by
          rw [hf, hS]
          ring
      _ ≤ _ := hq l
  calc q * ρ * (1 - Real.exp (-A))
      = q * (ρ * (1 - Real.exp (-A))) := by ring
    _ ≤ q * ∑ l ∈ Finset.range J, survivalProduct a l * f l :=
        mul_le_mul_of_nonneg_left hcore hqpos.le
    _ ≤ _ := hmid
    _ ≤ _ := hsumR

end RenewalGeometry
