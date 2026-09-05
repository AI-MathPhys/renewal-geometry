/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFeynmanKacPathMomentExact

/-!
# Jump-count domination of the actual finite-horizon Feynman--Kac observable

These bounds concern the measurable infinite-path carrier itself, including
its final partial holding interval. Probabilistic jump-count estimates are
still needed to deduce integrability.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NCG.FiniteHorizonFeynmanKacBound

open FiniteCTMCPathCarrierMeasurability FiniteCTMCPathEvaluationMeasurability
open FiniteCTMCAdditiveRewardMeasurability FiniteCTMCFeynmanKacPathMoment
open NonexplosiveFiniteStatePath

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The actual reward is bounded by elapsed time and the occupied jump index. -/
theorem abs_finiteHorizonAdditiveReward_le
    (v : S → ℝ) (g : S → S → ℝ) (V G T : ℝ)
    (hV : ∀ x, |v x| ≤ V) (hG : ∀ x y, |g x y| ≤ G)
    (z : AdmissibleJumpSequence (S := S)) (hT : 0 ≤ T) :
    |finiteHorizonAdditiveReward v g T z| ≤
      V * T + G * (admissibleJumpIndex z T : ℝ) := by
  let n := admissibleJumpIndex z T
  have hn : cumulativeJumpTime z.1 n ≤ T :=
    ((admissibleJumpIndex_eq_iff z hT n).mp rfl).1
  have hhold (i : ℕ) : 0 ≤ physicalHold z.1 i := (z.2.1 i).le
  have hterm (i : ℕ) :
      |physicalHold z.1 i * v (z.1 i).2 + g (z.1 i).2 (z.1 (i+1)).2| ≤
        physicalHold z.1 i * V + G := by
    calc
      _ ≤ |physicalHold z.1 i * v (z.1 i).2| + |g (z.1 i).2 (z.1 (i+1)).2| := abs_add_le _ _
      _ ≤ physicalHold z.1 i * V + G := by
        rw [abs_mul, abs_of_nonneg (hhold i)]
        exact add_le_add (mul_le_mul_of_nonneg_left (hV _) (hhold i)) (hG _ _)
  have hres : |(T - cumulativeJumpTime z.1 n) * v (z.1 n).2| ≤
      (T - cumulativeJumpTime z.1 n) * V := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hn)]
    exact mul_le_mul_of_nonneg_left (hV _) (sub_nonneg.mpr hn)
  change |fixedJumpCountAdditiveReward v g T n z| ≤ V * T + G * (n : ℝ)
  unfold fixedJumpCountAdditiveReward
  calc
    _ ≤ (∑ i ∈ range n, |physicalHold z.1 i * v (z.1 i).2 +
          g (z.1 i).2 (z.1 (i+1)).2|) +
          |(T - cumulativeJumpTime z.1 n) * v (z.1 n).2| :=
      (abs_add_le _ _).trans (add_le_add (abs_sum_le_sum_abs _ _) (le_refl _))
    _ ≤ (∑ i ∈ range n, (physicalHold z.1 i * V + G)) +
          (T - cumulativeJumpTime z.1 n) * V :=
      add_le_add (Finset.sum_le_sum fun i _ => hterm i) hres
    _ = V * T + G * (n : ℝ) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, cumulativeJumpTime, cumulativeHold]
      ring

/-- Exponential domination by the actual random jump count. -/
theorem norm_feynmanKacIntegrand_le
    (v : S → ℝ) (g : S → S → ℝ) (k V G M T : ℝ) (f : S → ℝ)
    (hV : ∀ x, |v x| ≤ V) (hG : ∀ x y, |g x y| ≤ G)
    (hf : ∀ x, |f x| ≤ M)
    (z : AdmissibleJumpSequence (S := S)) (hT : 0 ≤ T) :
    ‖feynmanKacIntegrand v g k T f z‖ ≤
      Real.exp (|k| * (V * T + G * (admissibleJumpIndex z T : ℝ))) * M := by
  have hr := abs_finiteHorizonAdditiveReward_le v g V G T hV hG z hT
  have hk : k * finiteHorizonAdditiveReward v g T z ≤
      |k| * (V * T + G * (admissibleJumpIndex z T : ℝ)) := by
    calc
      _ ≤ |k * finiteHorizonAdditiveReward v g T z| := le_abs_self _
      _ = |k| * |finiteHorizonAdditiveReward v g T z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (abs_nonneg k)
  simp only [feynmanKacIntegrand, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr hk) (hf _) (abs_nonneg _)
    (Real.exp_pos _).le

end

end NCG.FiniteHorizonFeynmanKacBound
