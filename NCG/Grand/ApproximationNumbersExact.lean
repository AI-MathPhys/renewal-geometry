/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FeedbackTail

/-!
# Approximation numbers and the dimension-three decay law

Machinery for `thm:feedback-Hankel-Weyl`: the approximation numbers
`a_n(T) = inf { ‖T - F‖ : rank F < n }` of a bounded operator, the basic estimate
`a_{r+1}(T) ≤ ‖T - F‖` for `rank F ≤ r`, and the calibrated `n^{-2/3}` decay law obtained from
a rank budget `rank F_R ≤ C_W (1 + R^{3/2})` with truncation error `K / (2R)`.
-/

open Filter Topology

namespace NCG
namespace ApproximationNumbers

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The `n`-th approximation number `a_n(T) = inf { ‖T - F‖ : rank F < n }`. -/
noncomputable def approxNumber (T : X →L[ℝ] Y) (n : ℕ) : ℝ :=
  sInf {r | ∃ F : X →L[ℝ] Y, Module.finrank ℝ (LinearMap.range F.toLinearMap) < n ∧ r = ‖T - F‖}

theorem approxNumber_nonneg (T : X →L[ℝ] Y) (n : ℕ) : 0 ≤ approxNumber T n := by
  unfold approxNumber
  rcases Set.eq_empty_or_nonempty
    {r | ∃ F : X →L[ℝ] Y, Module.finrank ℝ (LinearMap.range F.toLinearMap) < n ∧ r = ‖T - F‖}
    with h | h
  · rw [h, Real.sInf_empty]
  · exact le_csInf h (by rintro _ ⟨F, -, rfl⟩; exact norm_nonneg _)

/-- **Finite-rank approximation bound**: `a_{r+1}(T) ≤ ‖T - F‖` whenever `rank F ≤ r`. -/
theorem approxNumber_le_of_rank_le (T F : X →L[ℝ] Y) {r : ℕ}
    (hF : Module.finrank ℝ (LinearMap.range F.toLinearMap) ≤ r) :
    approxNumber T (r + 1) ≤ ‖T - F‖ := by
  unfold approxNumber
  refine csInf_le ⟨0, ?_⟩ ⟨F, Nat.lt_succ_of_le hF, rfl⟩
  rintro _ ⟨G, -, rfl⟩
  exact norm_nonneg _

/-- Approximation numbers are monotone decreasing in `n ≥ 1`. -/
theorem approxNumber_antitone (T : X →L[ℝ] Y) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    approxNumber T n ≤ approxNumber T m := by
  unfold approxNumber
  have hne : ({r | ∃ F : X →L[ℝ] Y, Module.finrank ℝ (LinearMap.range F.toLinearMap) < m ∧
      r = ‖T - F‖} : Set ℝ).Nonempty := by
    refine ⟨‖T - 0‖, 0, ?_, rfl⟩
    rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, finrank_bot]
    exact hm
  refine csInf_le_csInf ⟨0, ?_⟩ hne ?_
  · rintro _ ⟨G, -, rfl⟩
    exact norm_nonneg _
  · rintro _ ⟨G, hG, rfl⟩
    exact ⟨G, lt_of_lt_of_le hG hmn, rfl⟩

/-- **The dimension-three decay law.** If every truncation energy `R > 0` provides a finite-rank
approximant `F_R` with `rank F_R ≤ C_W R^{3/2}` and `‖T - F_R‖ ≤ K / (2R)`, then for every `n ≥ 1`
`a_{n+1}(T) ≤ C_fb n^{-2/3}` with `C_fb = K C_W^{2/3} / 2`. -/
theorem approxNumber_le_decay (T : X →L[ℝ] Y) {K CW : ℝ} (hK : 0 < K) (hCW : 0 < CW)
    (F : ℝ → X →L[ℝ] Y)
    (hrank : ∀ R : ℝ, 0 < R →
      (Module.finrank ℝ (LinearMap.range (F R).toLinearMap) : ℝ) ≤ CW * R ^ ((3 : ℝ) / 2))
    (herr : ∀ R : ℝ, 0 < R → ‖T - F R‖ ≤ K / (2 * R)) (n : ℕ) (hn : 0 < n) :
    approxNumber T (n + 1) ≤ (K * CW ^ ((2 : ℝ) / 3) / 2) * (n : ℝ) ^ (-((2 : ℝ) / 3)) := by
  obtain ⟨hcal, hlaw⟩ := feedback_hankel_weyl K CW hK hCW n hn
  set R : ℝ := ((n : ℝ) / CW) ^ ((2 : ℝ) / 3) with hR
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hRpos : 0 < R := Real.rpow_pos_of_pos (div_pos hn0 hCW) _
  -- the rank budget is exhausted exactly at the calibrated energy
  have hrankn : Module.finrank ℝ (LinearMap.range (F R).toLinearMap) ≤ n := by
    have h := hrank R hRpos
    rw [hcal] at h
    exact_mod_cast h
  calc approxNumber T (n + 1) ≤ ‖T - F R‖ := approxNumber_le_of_rank_le T (F R) hrankn
    _ ≤ K / (2 * R) := herr R hRpos
    _ = (K * CW ^ ((2 : ℝ) / 3) / 2) * (n : ℝ) ^ (-((2 : ℝ) / 3)) := hlaw

end ApproximationNumbers
end NCG
