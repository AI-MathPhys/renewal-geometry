/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Growth suppression at fixed expansion history
  (`thm:growth-sign-consistency`, GR_emergence)

The minimal-closure growth equation is equivalent to the
positive-kernel Volterra equation
`D(t) = g(t) + ∫ₐᵗ K(t,s)·A(s)·D(s) ds` with `K ≥ 0`, free datum
`g ≥ D_i > 0`, and matter coefficient `A ≥ 0`.  Comparison of the
exchange model (`A_Q ≤ A₀`, by comoving matter depletion) with the
noninteracting reference at fixed expansion history:

* `volterra_grönwall_zero` — a nonnegative continuous function
  dominated by `C·∫ₐᵗ m` vanishes (factorial iteration);
* `volterra_positive` — solutions with positive free datum stay
  strictly positive (first-crossing argument);
* `volterra_comparison` — `D_Q ≤ D₀` for `A_Q ≤ A₀` (the boxed
  `(fσ₈)_Q ≤ (fσ₈)₀` inequality at fixed `H` after the derivative
  identity);
* `growth_rate_comparison` — the integral-form derivative ordering
  `0 ≤ Ḋ_Q ≤ Ḋ₀`, hence `(fσ₈)_Q ≤ (fσ₈)₀`.

The reduction of the ODE to the Volterra form and the depletion
input `ρ_m^Q ≤ ρ_m^0` (`thm:comoving-matter-depletion`) are the
declared inputs.
-/

namespace NCG

open intervalIntegral

/-- Iterated Grönwall bound: a nonnegative continuous function on
`[a,b]` satisfying `m(t) ≤ C·∫ₐᵗ m` vanishes identically. -/
theorem volterra_gronwall_zero {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    {m : ℝ → ℝ} (hm : Continuous m)
    (hpos : ∀ t ∈ Set.Icc a b, 0 ≤ m t)
    (hineq : ∀ t ∈ Set.Icc a b, m t ≤ C * ∫ s in a..t, m s) :
    ∀ t ∈ Set.Icc a b, m t = 0 := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hm.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM a ⟨le_refl a, hab⟩)
  -- the factorial iteration
  have hiter : ∀ n : ℕ, ∀ t ∈ Set.Icc a b,
      m t ≤ M * (C ^ n * (t - a) ^ n / n.factorial) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have := hM t ht
      rw [Real.norm_eq_abs, abs_le] at this
      simpa using this.2
    | succ k ih =>
      intro t ht
      have hbound : ∀ s ∈ Set.Icc a t, m s
          ≤ M * (C ^ k * (s - a) ^ k / k.factorial) := by
        intro s hs
        exact ih s ⟨hs.1, le_trans hs.2 ht.2⟩
      have hint : (∫ s in a..t, m s)
          ≤ ∫ s in a..t, M * (C ^ k * (s - a) ^ k / k.factorial) := by
        apply intervalIntegral.integral_mono_on ht.1
          (hm.intervalIntegrable a t)
        · apply Continuous.intervalIntegrable
          continuity
        · exact hbound
      have heval : (∫ s in a..t, M * (C ^ k * (s - a) ^ k / k.factorial))
          = M * (C ^ k * (t - a) ^ (k + 1)
              / ((k + 1) * k.factorial)) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [show (fun s : ℝ => C ^ k * (s - a) ^ k / k.factorial)
          = fun s : ℝ => C ^ k / k.factorial * (s - a) ^ k from by
            funext s
            ring]
        rw [intervalIntegral.integral_const_mul]
        rw [show (fun s : ℝ => (s - a) ^ k)
          = fun s : ℝ => (fun u : ℝ => u ^ k) (s - a) from rfl]
        rw [intervalIntegral.integral_comp_sub_right
          (fun u : ℝ => u ^ k) a, sub_self, integral_pow]
        field_simp
        ring
      calc m t ≤ C * ∫ s in a..t, m s := hineq t ht
      _ ≤ C * ∫ s in a..t, M * (C ^ k * (s - a) ^ k / k.factorial) := by
            apply mul_le_mul_of_nonneg_left hint hC
      _ = M * (C ^ (k + 1) * (t - a) ^ (k + 1) / (k + 1).factorial) := by
            rw [heval, Nat.factorial_succ]
            push_cast
            ring
  -- pass to the limit
  intro t ht
  have hlim : Filter.Tendsto
      (fun n : ℕ => M * (C ^ n * (t - a) ^ n / n.factorial))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto
        (fun n : ℕ => (C * (t - a)) ^ n / n.factorial)
        Filter.atTop (nhds 0) :=
      FloorSemiring.tendsto_pow_div_factorial_atTop (C * (t - a))
    have h2 : (fun n : ℕ => M * (C ^ n * (t - a) ^ n / n.factorial))
        = fun n : ℕ => M * ((C * (t - a)) ^ n / n.factorial) := by
      funext n
      rw [mul_pow]
    rw [h2, show (0 : ℝ) = M * 0 from (mul_zero M).symm]
    exact h1.const_mul M
  have hub : m t ≤ 0 :=
    ge_of_tendsto hlim
      (Filter.Eventually.of_forall fun n => (hiter n t ht))
  exact le_antisymm hub (hpos t ht)

/-- Positivity of positive-kernel Volterra solutions: with free datum
`g ≥ Di > 0` and nonnegative kernel coefficient, the solution stays
strictly positive (first-crossing argument). -/
theorem volterra_positive {a b Di : ℝ} (_hab : a ≤ b) (hDi : 0 < Di)
    {g D : ℝ → ℝ} {q : ℝ → ℝ → ℝ} (hD : Continuous D)
    (hg : ∀ t ∈ Set.Icc a b, Di ≤ g t)
    (hq : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a t, 0 ≤ q t s)
    (heq : ∀ t ∈ Set.Icc a b,
      D t = g t + ∫ s in a..t, q t s * D s) :
    ∀ t ∈ Set.Icc a b, 0 < D t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t0, ht0, hneg⟩ := hcon
  -- the crossing set is closed and nonempty
  set S : Set ℝ := {t ∈ Set.Icc a b | D t ≤ 0} with hS
  have hSne : S.Nonempty := ⟨t0, ht0, hneg⟩
  have hSclosed : IsClosed S :=
    IsClosed.inter isClosed_Icc (isClosed_le hD continuous_const)
  have hSbdd : BddBelow S :=
    ⟨a, fun x hx => hx.1.1⟩
  set T : ℝ := sInf S with hT
  have hTS : T ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hTIcc : T ∈ Set.Icc a b := hTS.1
  -- everything strictly before `T` is positive
  have hbefore : ∀ s ∈ Set.Icc a T, s ≠ T → 0 < D s := by
    intro s hs hne
    by_contra hcon2
    rw [not_lt] at hcon2
    have hsS : s ∈ S := ⟨⟨hs.1, le_trans hs.2 hTIcc.2⟩, hcon2⟩
    have := csInf_le hSbdd hsS
    have hlt : s < T := lt_of_le_of_ne hs.2 hne
    rw [← hT] at this
    linarith
  -- hence `D ≥ 0` on `[a, T]` (continuity at the endpoint)
  have hnonneg : ∀ s ∈ Set.Icc a T, 0 ≤ D s := by
    intro s hs
    by_cases hne : s = T
    · rw [hne]
      by_contra hDT
      rw [not_le] at hDT
      -- `D < 0` at `T` but `D ≥ 0` just before: contradiction with
      -- the integral identity handled below; directly: use that the
      -- crossing value is a limit of positives when `a < T`, and at
      -- `T = a` the identity gives `D a = g a > 0`.
      rcases eq_or_lt_of_le hTIcc.1 with haT | haT
      · have hDa := heq T hTIcc
        rw [← haT] at hDa
        rw [intervalIntegral.integral_same, add_zero] at hDa
        have hga := hg T hTIcc
        rw [← haT] at hga hDT
        linarith
      · -- `D(T) < 0` yet `D > 0` on `[a,T)`: continuity forces
        -- `D(T) ≥ 0`
        have hlim : Filter.Tendsto D (nhdsWithin T (Set.Iio T))
            (nhds (D T)) :=
          (hD.tendsto T).mono_left nhdsWithin_le_nhds
        have hev : ∀ᶠ s in nhdsWithin T (Set.Iio T), 0 ≤ D s := by
          filter_upwards [Ioo_mem_nhdsLT haT] with s hs
          exact (hbefore s ⟨hs.1.le, hs.2.le⟩ (ne_of_lt hs.2)).le
        have := ge_of_tendsto hlim hev
        linarith
    · exact (hbefore s hs hne).le
  -- the Volterra identity at the crossing time
  have hDT := heq T hTIcc
  have hint : 0 ≤ ∫ s in a..T, q T s * D s := by
    apply intervalIntegral.integral_nonneg hTIcc.1
    intro s hs
    exact mul_nonneg (hq T hTIcc s hs) (hnonneg s hs)
  have := hg T hTIcc
  have hDTpos : 0 < D T := by
    rw [hDT]
    linarith
  exact absurd hTS.2 (not_le.mpr hDTpos)

/-- `thm:growth-sign-consistency` (core comparison): at fixed
expansion history, the depleted matter coefficient (`k_Q ≤ k₀`,
from comoving matter depletion) produces a smaller strictly positive
growing mode: `0 < D_Q ≤ D₀` on `[a,b]`. -/
theorem volterra_comparison {a b C Di : ℝ} (hab : a ≤ b)
    (hDi : 0 < Di) (hC : 0 ≤ C)
    {g D0 DQ : ℝ → ℝ} {k0 kQ : ℝ → ℝ → ℝ}
    (hD0 : Continuous D0) (hDQ : Continuous DQ)
    (hk0c : ∀ t, Continuous fun s => k0 t s)
    (hkQc : ∀ t, Continuous fun s => kQ t s)
    (hg : ∀ t ∈ Set.Icc a b, Di ≤ g t)
    (hkQ0 : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a t, 0 ≤ kQ t s)
    (hle : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a t, kQ t s ≤ k0 t s)
    (hCb : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a t, kQ t s ≤ C)
    (heq0 : ∀ t ∈ Set.Icc a b,
      D0 t = g t + ∫ s in a..t, k0 t s * D0 s)
    (heqQ : ∀ t ∈ Set.Icc a b,
      DQ t = g t + ∫ s in a..t, kQ t s * DQ s) :
    ∀ t ∈ Set.Icc a b, 0 < DQ t ∧ DQ t ≤ D0 t := by
  have hQpos := volterra_positive hab hDi hDQ hg hkQ0 heqQ
  have h0pos := volterra_positive hab hDi hD0 hg
    (fun t ht s hs => le_trans (hkQ0 t ht s hs) (hle t ht s hs)) heq0
  -- the negative-part envelope of the difference
  set m : ℝ → ℝ := fun t => max (DQ t - D0 t) 0 with hm
  have hmc : Continuous m := (hDQ.sub hD0).max continuous_const
  have hm0 : ∀ t ∈ Set.Icc a b, 0 ≤ m t := fun t _ => le_max_right _ _
  have hmineq : ∀ t ∈ Set.Icc a b, m t ≤ C * ∫ s in a..t, m s := by
    intro t ht
    have hintm0 : 0 ≤ ∫ s in a..t, m s := by
      apply intervalIntegral.integral_nonneg ht.1
      intro s hs
      exact le_max_right _ _
    have hi1 : IntervalIntegrable
        (fun s => -((k0 t s - kQ t s) * D0 s))
        MeasureTheory.volume a t :=
      Continuous.intervalIntegrable
        (by exact (((hk0c t).sub (hkQc t)).mul hD0).neg) a t
    have hi2 : IntervalIntegrable
        (fun s => kQ t s * (DQ s - D0 s)) MeasureTheory.volume a t :=
      Continuous.intervalIntegrable
        (by exact (hkQc t).mul (hDQ.sub hD0)) a t
    have hi3 : IntervalIntegrable (fun s => kQ t s * DQ s)
        MeasureTheory.volume a t :=
      Continuous.intervalIntegrable (by exact (hkQc t).mul hDQ) a t
    have hi4 : IntervalIntegrable (fun s => k0 t s * D0 s)
        MeasureTheory.volume a t :=
      Continuous.intervalIntegrable (by exact (hk0c t).mul hD0) a t
    have hi5 : IntervalIntegrable (fun s => C * m s)
        MeasureTheory.volume a t :=
      Continuous.intervalIntegrable
        (by exact continuous_const.mul hmc) a t
    have hdiff : DQ t - D0 t
        = -(∫ s in a..t, (k0 t s - kQ t s) * D0 s)
          + ∫ s in a..t, kQ t s * (DQ s - D0 s) := by
      rw [heq0 t ht, heqQ t ht]
      rw [← intervalIntegral.integral_neg,
        ← intervalIntegral.integral_add hi1 hi2]
      have hsub : g t + (∫ s in a..t, kQ t s * DQ s)
            - (g t + ∫ s in a..t, k0 t s * D0 s)
          = (∫ s in a..t, kQ t s * DQ s)
            - ∫ s in a..t, k0 t s * D0 s := by
        ring
      rw [hsub, ← intervalIntegral.integral_sub hi3 hi4]
      apply intervalIntegral.integral_congr
      intro s _
      ring
    have hfirst : 0 ≤ ∫ s in a..t, (k0 t s - kQ t s) * D0 s := by
      apply intervalIntegral.integral_nonneg ht.1
      intro s hs
      apply mul_nonneg (by linarith [hle t ht s hs])
      exact (h0pos s ⟨hs.1, le_trans hs.2 ht.2⟩).le
    have hsecond : (∫ s in a..t, kQ t s * (DQ s - D0 s))
        ≤ ∫ s in a..t, C * m s := by
      apply intervalIntegral.integral_mono_on ht.1 hi2 hi5
      intro s hs
      calc kQ t s * (DQ s - D0 s)
          ≤ kQ t s * m s := by
            apply mul_le_mul_of_nonneg_left (le_max_left _ _)
              (hkQ0 t ht s hs)
      _ ≤ C * m s := by
            apply mul_le_mul_of_nonneg_right (hCb t ht s hs)
              (le_max_right _ _)
    have hchain : DQ t - D0 t ≤ C * ∫ s in a..t, m s := by
      rw [hdiff, intervalIntegral.integral_const_mul] at *
      linarith [hfirst, hsecond]
    apply max_le hchain
    exact mul_nonneg hC hintm0
  have hzero := volterra_gronwall_zero hab hC hmc hm0 hmineq
  intro t ht
  refine ⟨hQpos t ht, ?_⟩
  have := hzero t ht
  have hle' : DQ t - D0 t ≤ m t := le_max_left _ _
  rw [this] at hle'
  linarith

/-- `thm:growth-sign-consistency` (rate ordering): the integral-form
growth rate `Ḋ = M⁻¹(t)·[c + ∫ₐᵗ M·A·D]` inherits the ordering, so
`0 ≤ Ḋ_Q ≤ Ḋ₀` and hence `(fσ₈)_Q ≤ (fσ₈)₀` at fixed expansion
history after positive normalization. -/
theorem growth_rate_comparison {a b c : ℝ} (hc : 0 ≤ c)
    {Minv : ℝ → ℝ} {F0 FQ : ℝ → ℝ}
    (hMinv : ∀ t ∈ Set.Icc a b, 0 < Minv t)
    (hFQ0 : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a t, 0 ≤ FQ s)
    (hord : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a t, FQ s ≤ F0 s)
    (hFQc : Continuous FQ) (hF0c : Continuous F0) :
    ∀ t ∈ Set.Icc a b,
      0 ≤ Minv t * (c + ∫ s in a..t, FQ s)
        ∧ Minv t * (c + ∫ s in a..t, FQ s)
            ≤ Minv t * (c + ∫ s in a..t, F0 s) := by
  intro t ht
  have hintQ : 0 ≤ ∫ s in a..t, FQ s := by
    apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact hFQ0 t ht s hs
  have hmono : (∫ s in a..t, FQ s) ≤ ∫ s in a..t, F0 s := by
    apply intervalIntegral.integral_mono_on ht.1
      (hFQc.intervalIntegrable a t) (hF0c.intervalIntegrable a t)
    intro s hs
    exact hord t ht s hs
  constructor
  · apply mul_nonneg (hMinv t ht).le
    linarith
  · apply mul_le_mul_of_nonneg_left _ (hMinv t ht).le
    linarith

end NCG
