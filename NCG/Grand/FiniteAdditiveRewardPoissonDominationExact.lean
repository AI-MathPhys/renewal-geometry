/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCPathLikelihoodExact
import NCG.Grand.PoissonExponentialTightnessExact

/-!
# Poisson domination of finite-state additive rewards

For a resolved finite-state jump path, a bounded state reward contributes at
most its uniform bound times the elapsed time, while a bounded jump reward
contributes at most its uniform bound times the jump count.  This is the
deterministic bridge from Poisson jump-count tails to exponential tightness
of the additive functional in the finite Feynman--Kac/LDP compiler.
-/

open scoped BigOperators

noncomputable section

namespace NCG.FiniteAdditiveRewardPoissonDomination

open NCG.DrivenProcess.FinitePath

variable {S : Type*}

/-- A bounded state-plus-jump reward is controlled by elapsed time and the
number of jumps along every path with nonnegative holding times. -/
theorem abs_additiveReward_le_duration_add_jumpCount
    (v : S → ℝ) (g : S → S → ℝ) (V G terminalHold : ℝ)
    (x : S) (path : List (Jump S))
    (hV : ∀ u, |v u| ≤ V) (hG : ∀ u w, |g u w| ≤ G)
    (hterminal : 0 ≤ terminalHold)
    (hholds : ∀ step ∈ path, 0 ≤ step.1) :
    |additiveReward v g terminalHold x path| ≤
      V * duration terminalHold path + G * path.length := by
  induction path generalizing x with
  | nil =>
      simp only [additiveReward, duration, List.length_nil, Nat.cast_zero,
        mul_zero, add_zero]
      rw [abs_mul, abs_of_nonneg hterminal]
      have hv := hV x
      nlinarith
  | cons step rest ih =>
      rcases step with ⟨hold, y⟩
      have hhold : 0 ≤ hold := hholds (hold, y) (List.mem_cons_self)
      have hrest : ∀ step ∈ rest, 0 ≤ step.1 := by
        intro step hstep
        exact hholds step (List.mem_cons_of_mem _ hstep)
      have hi := ih y hrest
      have hvhold : |hold * v x| ≤ hold * V := by
        rw [abs_mul, abs_of_nonneg hhold]
        exact mul_le_mul_of_nonneg_left (hV x) hhold
      have htri :
          |hold * v x + g x y + additiveReward v g terminalHold y rest| ≤
            |hold * v x| + |g x y| +
              |additiveReward v g terminalHold y rest| := by
        calc
          |hold * v x + g x y + additiveReward v g terminalHold y rest| ≤
              |hold * v x + g x y| +
                |additiveReward v g terminalHold y rest| := abs_add_le _ _
          _ ≤ (|hold * v x| + |g x y|) +
                |additiveReward v g terminalHold y rest| := by
            gcongr
            exact abs_add_le _ _
      simp only [additiveReward, duration, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      calc
        |hold * v x + g x y + additiveReward v g terminalHold y rest| ≤
            |hold * v x| + |g x y| +
              |additiveReward v g terminalHold y rest| := htri
        _ ≤ hold * V + G +
              (V * duration terminalHold rest + G * rest.length) := by
            have hgxy := hG x y
            nlinarith
        _ = V * (hold + duration terminalHold rest) +
              G * (rest.length + 1) := by ring

/-- Fixed-horizon form of the pathwise reward bound. -/
theorem abs_additiveReward_le_time_add_jumpCount
    (v : S → ℝ) (g : S → S → ℝ) (V G T terminalHold : ℝ)
    (x : S) (path : List (Jump S))
    (hV : ∀ u, |v u| ≤ V) (hG : ∀ u w, |g u w| ≤ G)
    (hterminal : 0 ≤ terminalHold)
    (hholds : ∀ step ∈ path, 0 ≤ step.1)
    (hduration : duration terminalHold path = T) :
    |additiveReward v g terminalHold x path| ≤
      V * T + G * path.length := by
  simpa [hduration] using
    abs_additiveReward_le_duration_add_jumpCount
      v g V G terminalHold x path hV hG hterminal hholds

/-- Any reward excursion beyond its deterministic state contribution forces
a proportionally large jump count. -/
theorem jumpCount_large_of_additiveReward_large
    (v : S → ℝ) (g : S → S → ℝ) (V G M T terminalHold : ℝ)
    (x : S) (path : List (Jump S))
    (hV : ∀ u, |v u| ≤ V) (hG : ∀ u w, |g u w| ≤ G)
    (hterminal : 0 ≤ terminalHold)
    (hholds : ∀ step ∈ path, 0 ≤ step.1)
    (hduration : duration terminalHold path = T)
    (hGpos : 0 < G)
    (hlarge : M * T < |additiveReward v g terminalHold x path|) :
    (M - V) * T / G < (path.length : ℝ) := by
  have hbound := abs_additiveReward_le_time_add_jumpCount
    v g V G T terminalHold x path hV hG hterminal hholds hduration
  apply (div_lt_iff₀ hGpos).2
  nlinarith

end NCG.FiniteAdditiveRewardPoissonDomination
