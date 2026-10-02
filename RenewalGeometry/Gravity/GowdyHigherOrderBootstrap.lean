/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.GridFaaDiBrunoBootstrap
import RenewalGeometry.Gravity.GowdyHigherOrderStateError

/-!
# The Gowdy `C^r_ℓ` state error under the smallness bootstrap
  (`prop:supp-gowdy-residual-control`, bootstrap branch of `eq:supp-gowdy-state-error`;
  emergent-spacetime supplement)

`GowdyFrameSolution.state_error_bootstrap`: for a smooth solution and a chart radius
`R ≥ chartRadius` there are a near-identity branch radius `ρ_*`, a smallness threshold `ε_*`,
`ℓ₀ > 0`, an envelope radius `R_env` and `C` such that every numerical history of Gowdy split steps
whose implicit stages are `ρ_*`-near-identity, with initial `C^r_ℓ` error `ε₀ ≤ ε_*` and
`√𝓕_h ≤ ε_*`, stays in the `C^r_ℓ` envelope `GowdyEnvR r t₀ R R_env` on the whole interval and
obeys `‖X_n - 𝖲_ℓX_*(t_n)‖_{r,∞,ℓ} ≤ C (ε₀ + h² + √𝓕_h)` — no envelope hypothesis.  The proof
is the continuation argument `SmoothSetup.global_error_bootstrap`.
-/

open Set Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GowdyStaggered

noncomputable section

open GridFaaDiBruno CharStability

namespace GowdyFrameSolution

variable {t₀ t₁ : ℝ} (sol : GowdyFrameSolution t₀ t₁)

/-- **`eq:supp-gowdy-state-error` for every `r` under the smallness bootstrap.** -/
theorem state_error_bootstrap (hs : sol.IsSmooth) (h0 : 0 < t₀) (r : ℕ) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) :
    ∃ ρs εs ℓ₀ Renv C : ℝ, 0 < ρs ∧ 0 < εs ∧ 0 < ℓ₀ ∧ 0 ≤ C ∧
      ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ →
      ∀ X A B : ℕ → GridState N,
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          (∀ j, ‖((A n).site j).toVec - ((X n).site j).toVec‖ ≤ ρs) ∧
          (∀ j, ‖((B n).site j).toVec -
            ((transport (2 * Real.pi / N) (A n)).site j).toVec‖ ≤ ρs)) →
        PeriodicGridResidual.crNorm r (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) ≤ εs →
        Real.sqrt (PeriodicGridResidual.residualFlux r (2 * Real.pi / N) (2 * Real.pi / N)
          (fun k => errArr (X (k + 1)) (B k)) n₀) ≤ εs →
        (∀ n < n₀, GowdyEnvR r t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) ∧
        ∀ n ≤ n₀, PeriodicGridResidual.crNorm r (2 * Real.pi / N)
            (errArr (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N)))) ≤
          C * (PeriodicGridResidual.crNorm r (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) +
            (2 * Real.pi / N) ^ 2 +
            Real.sqrt (PeriodicGridResidual.residualFlux r (2 * Real.pi / N) (2 * Real.pi / N)
              (fun k => errArr (X (k + 1)) (B k)) n)) := by
  obtain ⟨p, S, hp0, hp1, hpm, -, hc, hK, hZ, hl⟩ :=
    sol.exists_gowdySmoothSetup hs h0 (3 + r) hR 0
  obtain ⟨ρs, εs, ℓ₁, C, hρs, hεs, hℓ₁, hC, hb⟩ := S.global_error_bootstrap r (by omega)
  set T := max (t₁ - t₀) 0
  have hT0 : 0 ≤ T := le_max_right _ _
  set κ := 1 + 2 ^ r * Real.sqrt (2 * T)
  have hκ : 1 ≤ κ := by
    have : 0 ≤ 2 ^ r * Real.sqrt (2 * T) := by positivity
    linarith
  refine ⟨ρs, εs / (2 * κ), min ℓ₁ 2, max p.R (Params.envR r p), C * κ, hρs,
    div_pos hεs (by positivity), lt_min hℓ₁ two_pos, mul_nonneg hC (by positivity), ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ X A B hst he0 hF
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hℓ2 : ℓ ≤ 2 := hN.trans (min_le_right _ _)
  have hsamp : ∀ τ, sampleGrid S.Z S.lam N τ = toCG (sol.sample N τ) := fun τ => by
    rw [hZ, hl, sol.sample_toCG]
  -- the residual budget
  have hbud : ∀ n ≤ n₀, ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ
      (errArr (X (i + 1)) (B i)) ≤ 2 ^ r * Real.sqrt (2 * T) *
        Real.sqrt (PeriodicGridResidual.residualFlux r ℓ ℓ (fun k => errArr (X (k + 1)) (B k)) n) := by
    intro n hn
    refine (PeriodicGridResidual.sum_crNorm_le_sqrt_residualFlux hℓpos hℓ2 r _ n).trans ?_
    have hnl : (n : ℝ) * ℓ ≤ T := by
      have : (n : ℝ) ≤ n₀ := by exact_mod_cast hn
      have : (n : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right this hℓpos.le
      exact (by linarith : (n : ℝ) * ℓ ≤ t₁ - t₀).trans (le_max_left _ _)
    have : Real.sqrt (2 * n * ℓ) ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt (by nlinarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity))
      (Real.sqrt_nonneg _)
  have hsmall : PeriodicGridResidual.crNorm r ℓ (CharData.errA (toCG (X 0)) (sampleGrid S.Z S.lam N τ₀)) +
      ∑ i ∈ range n₀, PeriodicGridResidual.crNorm r ℓ (CharData.errA (toCG (X (i + 1))) (toCG (B i))) ≤
        εs := by
    rw [hsamp, errA_toCG]
    simp only [errA_toCG]
    have h1 := hbud n₀ le_rfl
    have h2 : 2 ^ r * Real.sqrt (2 * T) * Real.sqrt (PeriodicGridResidual.residualFlux r ℓ ℓ
        (fun k => errArr (X (k + 1)) (B k)) n₀) ≤ 2 ^ r * Real.sqrt (2 * T) * (εs / (2 * κ)) :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    have h3 : εs / (2 * κ) + 2 ^ r * Real.sqrt (2 * T) * (εs / (2 * κ)) ≤ εs := by
      have : εs / (2 * κ) + 2 ^ r * Real.sqrt (2 * T) * (εs / (2 * κ)) = εs / 2 := by
        simp only [κ]; field_simp
      linarith
    linarith
  have hst' : ∀ n < n₀, S.c.IsSplit ℓ (toCG (X n)) (toCG (A n)) (toCG (B n)) ∧
      (∀ j, ‖(toCG (A n)).site j - (toCG (X n)).site j‖ ≤ ρs) ∧
      (∀ j, ‖(toCG (B n)).site j - (S.c.transport ℓ (toCG (A n))).site j‖ ≤ ρs) := by
    intro n hn
    rw [hc, ← toCG_transport]
    exact ⟨toCG_isSplit (hst n hn).1, (hst n hn).2.1, (hst n hn).2.2⟩
  obtain ⟨henv, hbd⟩ := hb N (hN.trans (min_le_left _ _)) τ₀ n₀ (by rw [hp0]; exact hτ₀)
    (by rw [hp1]; exact hn₀) (fun n => toCG (X n)) (fun n => toCG (A n)) (fun n => toCG (B n))
    hst' hsmall
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have := henv n hn
    rw [hc, hK] at this
    exact this
  · have h := hbd n hn
    rw [hsamp, hsamp, errA_toCG, errA_toCG] at h
    simp only [errA_toCG] at h
    refine h.trans ?_
    set e0 := PeriodicGridResidual.crNorm r ℓ (errArr (X 0) (sol.sample N τ₀))
    set F := Real.sqrt (PeriodicGridResidual.residualFlux r ℓ ℓ
      (fun k => errArr (X (k + 1)) (B k)) n)
    have he0 : 0 ≤ e0 := PeriodicGridResidual.crNorm_nonneg _ _ _
    have hF0 : 0 ≤ F := Real.sqrt_nonneg _
    have h1 := hbud n hn
    have hk : 0 ≤ 2 ^ r * Real.sqrt (2 * T) := by positivity
    have key : e0 + ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errArr (X (i + 1)) (B i)) +
        ℓ ^ 2 ≤ κ * (e0 + ℓ ^ 2 + F) := by
      simp only [κ]
      nlinarith [mul_nonneg hk he0, mul_nonneg hk (sq_nonneg ℓ)]
    calc C * (e0 + ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errArr (X (i + 1)) (B i)) +
          ℓ ^ 2) ≤ C * (κ * (e0 + ℓ ^ 2 + F)) := mul_le_mul_of_nonneg_left key hC
      _ = C * κ * (e0 + ℓ ^ 2 + F) := by ring

end GowdyFrameSolution

/-! ### Non-vacuity of the bootstrap hypotheses -/

/-- The trivial solution samples to the spatially constant states. -/
theorem zeroFrameSolution_sample (t₀ t₁ : ℝ) (N : ℕ) (τ : ℝ) :
    (zeroFrameSolution t₀ t₁).sample N τ = constGrid N τ := by
  simp only [GowdyFrameSolution.sample, constGrid, zeroFrameSolution, GowdyFrameSolution.Z,
    GowdyFrameSolution.fr]
  congr 1
  · funext j
    simp only [LocalState.ofVec]
    congr 1
    funext i; fin_cases i <;> simp

/-- **Non-vacuity of the bootstrap hypotheses** of `state_error_bootstrap`: the spatially
constant split steps of the trivial solution have stage increments `ℓ/2` (hence are
`ρ_*`-near-identity as soon as `ℓ ≤ 2ρ_*`), zero initial error and zero residuals. -/
theorem constGrid_bootstrap_data (t₀ t₁ : ℝ) (N : ℕ) [NeZero N] (τ σ : ℝ) (j : ZMod N) (r : ℕ)
    (ℓ : ℝ) :
    ‖((constGrid N (τ + σ)).site j).toVec - ((constGrid N τ).site j).toVec‖ = |σ| ∧
      ((transport ℓ (constGrid N τ)).site j).toVec = ((constGrid N τ).site j).toVec ∧
      PeriodicGridResidual.crNorm r ℓ
        (errArr (constGrid N τ) ((zeroFrameSolution t₀ t₁).sample N τ)) = 0 := by
  refine ⟨?_, by rw [transport_constGrid], ?_⟩
  · have e : ((constGrid N (τ + σ)).site j).toVec - ((constGrid N τ).site j).toVec =
        ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), σ) := by
      simp [constGrid, LocalState.toVec]
    rw [e, norm_zero_frame]
  · rw [zeroFrameSolution_sample]
    have e : errArr (constGrid N τ) (constGrid N τ) = 0 := by
      funext j; simp [errArr]
    rw [e]
    have hz : ∀ k : ℕ, (PeriodicGridResidual.fwdDiff ℓ)^[k] (0 : ZMod N → StateVec × ℝ) = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih]; exact fwdDiff_const ℓ 0
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun k _ => by rw [hz]; simp
    · exact PeriodicGridResidual.crNorm_nonneg _ _ _

end

end RenewalGeometry.GowdyStaggered
