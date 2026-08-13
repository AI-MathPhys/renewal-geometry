/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Source leakage: persistence, splitting, or escape
  (`thm:source-leakage-limit-alternative`,
  Gran-Tensor manuscript)

* `source_leakage_limit_alternative`: for normalized
  source-leakage vectors `y_n` converging weakly to `y`:
  (i) the boxed splitting identity
      `‖y_n - y‖² → 1 - ‖y‖²`;
  (ii) the weak limit stays in the unit ball (`‖y‖ ≤ 1`);
  (iii) persistence: `‖y‖ = 1` forces strong convergence;
  (iv) escape: `y = 0` gives `‖y_n - y‖² → 1`.

Hence the missing source persists strongly, splits into a
persistent and an escaping component, or escapes every
compact source head.  The subsequence extraction
(Banach–Alaoglu on the transported ball) is the manuscript's
weak-compactness step before these identities.
-/

open scoped InnerProductSpace

namespace NCG

/-- Sequential Banach--Alaoglu plus Fréchet--Riesz: every normalized
sequence in a separable complex Hilbert space has a weakly convergent
subsequence. -/
theorem exists_weakly_convergent_subsequence_of_normalized
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (y : ℕ → H) (hunit : ∀ n, ‖y n‖ = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ yl : H, ∀ z : H,
      Filter.Tendsto (fun n => inner ℂ z (y (φ n)))
        Filter.atTop (nhds (inner ℂ z yl)) := by
  let F : ℕ → WeakDual ℂ H := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (y n))
  let ball : Set (WeakDual ℂ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) 1
  have hmem : ∀ n, F n ∈ ball := by
    intro n
    change WeakDual.toStrongDual (F n) ∈
      Metric.closedBall (0 : StrongDual ℂ H) 1
    rw [Metric.mem_closedBall, dist_zero_right,
      show WeakDual.toStrongDual (F n) = InnerProductSpace.toDual ℂ H (y n) by
        apply ContinuousLinearMap.ext
        intro z
        rfl,
      (InnerProductSpace.toDual ℂ H).norm_map, hunit]
  have hseq : IsSeqCompact ball :=
    WeakDual.isSeqCompact_closedBall ℂ H 0 1
  obtain ⟨flim, hflimMem, φ, hφ, ht⟩ := hseq.subseq_of_frequently_in
    (Filter.Eventually.of_forall hmem).frequently
  let yl : H := (InnerProductSpace.toDual ℂ H).symm
    (WeakDual.toStrongDual flim)
  refine ⟨φ, hφ, yl, fun z => ?_⟩
  have heval := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp ht) z
  have heval0 : Filter.Tendsto
      (fun n => inner ℂ (y (φ n)) z) Filter.atTop
      (nhds (inner ℂ yl z)) := by
    convert heval using 1
    · funext n
      rfl
    · congr 1
      change inner ℂ yl z = (WeakDual.toStrongDual flim) z
      simpa [yl] using
        (InnerProductSpace.toDual_symm_apply
          (x := z) (y := WeakDual.toStrongDual flim))
  have heval' := (Complex.continuous_conj.tendsto _).comp heval0
  convert heval' using 1
  · funext n
    exact (inner_conj_symm z (y (φ n))).symm
  · congr 1
    exact (inner_conj_symm z yl).symm

/-- `thm:source-leakage-limit-alternative`. -/
theorem source_leakage_limit_alternative {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (y : ℕ → H) (yl : H) (hunit : ∀ n, ‖y n‖ = 1)
    (hweak : ∀ z : H,
      Filter.Tendsto (fun n => ⟪z, y n⟫_ℂ)
        Filter.atTop (nhds ⟪z, yl⟫_ℂ)) :
    -- (i) the boxed splitting identity
    Filter.Tendsto (fun n => ‖y n - yl‖ ^ 2)
      Filter.atTop (nhds (1 - ‖yl‖ ^ 2))
    -- (ii) the weak limit stays in the unit ball
    ∧ ‖yl‖ ≤ 1
    -- (iii) persistence
    ∧ (‖yl‖ = 1 →
        Filter.Tendsto (fun n => ‖y n - yl‖)
          Filter.atTop (nhds 0))
    -- (iv) escape
    ∧ (yl = 0 →
        Filter.Tendsto (fun n => ‖y n - yl‖ ^ 2)
          Filter.atTop (nhds 1)) := by
  -- the real part of the pairing converges
  have hre : Filter.Tendsto
      (fun n => (⟪yl, y n⟫_ℂ).re) Filter.atTop
      (nhds ((⟪yl, yl⟫_ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp (hweak yl)
  have hself : (⟪yl, yl⟫_ℂ).re = ‖yl‖ ^ 2 := by
    rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
  -- the splitting identity
  have hmain : Filter.Tendsto (fun n => ‖y n - yl‖ ^ 2)
      Filter.atTop (nhds (1 - ‖yl‖ ^ 2)) := by
    have hexp : ∀ n, ‖y n - yl‖ ^ 2
        = 1 - 2 * (⟪yl, y n⟫_ℂ).re + ‖yl‖ ^ 2 := by
      intro n
      rw [norm_sub_sq (𝕜 := ℂ), hunit, one_pow]
      congr 2
      simpa using inner_re_symm (𝕜 := ℂ) (y n) yl
    have ht : Filter.Tendsto
        (fun n => 1 - 2 * (⟪yl, y n⟫_ℂ).re + ‖yl‖ ^ 2)
        Filter.atTop
        (nhds (1 - 2 * ‖yl‖ ^ 2 + ‖yl‖ ^ 2)) := by
      apply Filter.Tendsto.add_const
      apply Filter.Tendsto.const_sub
      rw [← hself]
      exact hre.const_mul 2
    have heq : 1 - 2 * ‖yl‖ ^ 2 + ‖yl‖ ^ 2
        = 1 - ‖yl‖ ^ 2 := by ring
    rw [heq] at ht
    exact ht.congr (fun n => (hexp n).symm)
  -- the weak limit is in the unit ball
  have hball : ‖yl‖ ≤ 1 := by
    have hbnd : ∀ n, (⟪yl, y n⟫_ℂ).re ≤ ‖yl‖ := by
      intro n
      calc (⟪yl, y n⟫_ℂ).re ≤ ‖(⟪yl, y n⟫_ℂ)‖ :=
            Complex.re_le_norm _
        _ ≤ ‖yl‖ * ‖y n‖ := norm_inner_le_norm _ _
        _ = ‖yl‖ := by rw [hunit, mul_one]
    have hlim : ‖yl‖ ^ 2 ≤ ‖yl‖ := by
      rw [← hself]
      exact le_of_tendsto hre
        (Filter.Eventually.of_forall hbnd)
    nlinarith [norm_nonneg yl]
  refine ⟨hmain, hball, ?_, ?_⟩
  · intro h1
    have h0 : Filter.Tendsto (fun n => ‖y n - yl‖ ^ 2)
        Filter.atTop (nhds 0) := by
      have := hmain
      rw [h1] at this
      simpa using this
    have hs : Filter.Tendsto
        (fun n => Real.sqrt (‖y n - yl‖ ^ 2))
        Filter.atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto _).comp h0
    rw [Real.sqrt_zero] at hs
    exact hs.congr (fun n => by
      rw [Real.sqrt_sq (norm_nonneg _)])
  · intro h0
    subst h0
    simpa using hmain

/-- Full manuscript theorem including the weak-subsequence extraction and the
Pythagorean persistence/splitting/escape alternative. -/
theorem source_leakage_subsequence_alternative
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (y : ℕ → H) (hunit : ∀ n, ‖y n‖ = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ yl : H,
      Filter.Tendsto (fun n => ‖y (φ n) - yl‖ ^ 2)
        Filter.atTop (nhds (1 - ‖yl‖ ^ 2))
      ∧ ‖yl‖ ≤ 1
      ∧ (‖yl‖ = 1 →
          Filter.Tendsto (fun n => ‖y (φ n) - yl‖)
            Filter.atTop (nhds 0))
      ∧ (yl = 0 →
          Filter.Tendsto (fun n => ‖y (φ n) - yl‖ ^ 2)
            Filter.atTop (nhds 1)) := by
  obtain ⟨φ, hφ, yl, hweak⟩ :=
    exists_weakly_convergent_subsequence_of_normalized y hunit
  refine ⟨φ, hφ, yl, ?_⟩
  exact source_leakage_limit_alternative (fun n => y (φ n)) yl
    (fun n => hunit (φ n)) hweak

end NCG
