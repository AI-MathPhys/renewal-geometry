/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Lyapunov quadratic forms and exponential growth for nearly constant linear ODEs

Let `A` be a bounded operator on a real Hilbert space `E` such that `‖exp (-T • A)‖ ≤ 1/2` for
some `T > 0` (this holds, by Gelfand's formula, for every real matrix whose complex spectrum lies
in the open right half-plane; see `RenewalGeometry/Analysis/MatrixSpectralDecay.lean`).  The
finite-horizon Lyapunov Gramian
`W = ∫₀ᵀ exp(-rA)* exp(-rA) dr` satisfies

* `⟪W v, w⟫ = ∫₀ᵀ ⟪e^{-rA} v, e^{-rA} w⟫ dr` (`lyapunovGramian_inner`), so `W` is symmetric
  and positive definite (`lyapunovGramian_inner_self_ge`);
* the finite-horizon **Lyapunov identity**
  `2 ⟪W v, A v⟫ = ‖v‖² - ‖e^{-TA} v‖²` (`two_mul_lyapunovGramian_inner_apply`), hence the
  strict **Lyapunov inequality** `2 ⟪W v, A v⟫ ≥ (3/4) ‖v‖²`.

Consequently (`lyapunov_exponential_growth`) there are `ε, c, μ > 0` such that every solution
of a time-dependent linear system `v' = N(s) v` on `[0, S]` with `‖N(s) - A‖ ≤ ε` satisfies the
two-sided exponential estimate
`c e^{μ s} ‖v(0)‖ ≤ ‖v(s)‖ ≤ e^{(‖A‖+ε) s} ‖v(0)‖`.

The scalar comparison lemmas used here (`le_exp_mul_of_hasDerivWithinAt`,
`exp_mul_le_of_hasDerivWithinAt`: `f' ≥ κ f ⇒ f(s) ≥ e^{κ s} f(0)` and its upper twin) are
also exported.

This is the rapid Lyapunov-growth input of `prop:supp-exact-normal-growth` and
`thm:main-exact-residence` (emergent-spacetime manuscript).
-/

open Set Filter MeasureTheory intervalIntegral
open scoped Topology RealInnerProductSpace

namespace RenewalGeometry

namespace LyapunovGrowth

/-! ### Scalar comparison lemmas -/

/-- **Exponential lower comparison.**  If `f' ≥ κ f` on `[0, S]` (derivatives within the
interval), then `e^{κ s} f(0) ≤ f(s)` on `[0, S]`. -/
theorem le_exp_mul_of_hasDerivWithinAt {f f' : ℝ → ℝ} {κ S : ℝ}
    (hf : ∀ s ∈ Icc 0 S, HasDerivWithinAt f (f' s) (Icc 0 S) s)
    (hineq : ∀ s ∈ Icc 0 S, κ * f s ≤ f' s) :
    ∀ s ∈ Icc 0 S, Real.exp (κ * s) * f 0 ≤ f s := by
  set g : ℝ → ℝ := fun s => Real.exp (-(κ * s)) * f s
  have hg : ∀ s ∈ Icc 0 S, HasDerivWithinAt g
      (Real.exp (-(κ * s)) * (-κ) * f s + Real.exp (-(κ * s)) * f' s) (Icc 0 S) s := by
    intro s hs
    have h1 : HasDerivWithinAt (fun s => Real.exp (-(κ * s))) (Real.exp (-(κ * s)) * (-κ))
        (Icc 0 S) s := by
      have := ((hasDerivAt_id s).const_mul κ).neg.exp
      simpa using this.hasDerivWithinAt
    exact h1.mul (hf s hs)
  have hmono : MonotoneOn g (Icc 0 S) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s =>
      Real.exp (-(κ * s)) * (-κ) * f s + Real.exp (-(κ * s)) * f' s) (convex_Icc 0 S) ?_ ?_ ?_
    · exact fun s hs => (hg s hs).continuousWithinAt
    · intro s hs
      exact (hg s (interior_subset hs)).mono interior_subset
    · intro s hs
      have hs' := interior_subset hs
      have := hineq s hs'
      have hpos := Real.exp_pos (-(κ * s))
      nlinarith
  intro s hs
  have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hs.1.trans hs.2⟩
  have := hmono h0 hs hs.1
  simp only [g, mul_zero, neg_zero, Real.exp_zero, one_mul] at this
  have hpos := Real.exp_pos (κ * s)
  have : Real.exp (κ * s) * f 0 ≤ Real.exp (κ * s) * (Real.exp (-(κ * s)) * f s) :=
    mul_le_mul_of_nonneg_left this hpos.le
  rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this

/-- **Exponential upper comparison.**  If `f' ≤ κ f` on `[0, S]`, then
`f(s) ≤ e^{κ s} f(0)` on `[0, S]`. -/
theorem exp_mul_le_of_hasDerivWithinAt {f f' : ℝ → ℝ} {κ S : ℝ}
    (hf : ∀ s ∈ Icc 0 S, HasDerivWithinAt f (f' s) (Icc 0 S) s)
    (hineq : ∀ s ∈ Icc 0 S, f' s ≤ κ * f s) :
    ∀ s ∈ Icc 0 S, f s ≤ Real.exp (κ * s) * f 0 := by
  have := le_exp_mul_of_hasDerivWithinAt (f := fun s => -f s) (f' := fun s => -f' s) (κ := κ)
    (fun s hs => (hf s hs).neg) (fun s hs => by have := hineq s hs; linarith)
  intro s hs
  have := this s hs
  linarith

/-! ### The finite-horizon Lyapunov Gramian -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The propagator `r ↦ exp (-r • A)`. -/
noncomputable def backProp (A : E →L[ℝ] E) (r : ℝ) : E →L[ℝ] E :=
  NormedSpace.exp ((-r) • A)

theorem hasDerivAt_backProp (A : E →L[ℝ] E) (r : ℝ) :
    HasDerivAt (backProp A) (-(backProp A r * A)) r := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (-r)
  have h2 := h.scomp r (hasDerivAt_neg r)
  have h3 : HasDerivAt (backProp A) ((-1 : ℝ) • (NormedSpace.exp ((-r) • A) * A)) r := h2
  convert h3 using 1
  simp [backProp]

theorem continuous_backProp (A : E →L[ℝ] E) : Continuous (backProp A) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_backProp A r).continuousAt

theorem backProp_zero (A : E →L[ℝ] E) : backProp A 0 = 1 := by
  simp [backProp]

/-- `exp (r • A) * exp (-r • A) = 1`. -/
theorem exp_smul_mul_backProp (A : E →L[ℝ] E) (r : ℝ) :
    NormedSpace.exp (r • A) * backProp A r = 1 := by
  have hrad := NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)
  rw [backProp, ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl A).smul_left r).smul_right (-r))
    (hrad.symm ▸ edist_lt_top _ _) (hrad.symm ▸ edist_lt_top _ _)]
  simp [NormedSpace.exp_zero]

/-- The finite-horizon **Lyapunov Gramian** `W = ∫₀ᵀ exp(-rA)* exp(-rA) dr`. -/
noncomputable def lyapunovGramian (A : E →L[ℝ] E) (T : ℝ) : E →L[ℝ] E :=
  ∫ r in (0 : ℝ)..T, ContinuousLinearMap.adjoint (backProp A r) ∘L backProp A r

theorem continuous_gramianIntegrand (A : E →L[ℝ] E) :
    Continuous fun r => ContinuousLinearMap.adjoint (backProp A r) ∘L backProp A r := by
  have h1 : Continuous fun r => ContinuousLinearMap.adjoint (backProp A r) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).continuous.comp
      (continuous_backProp A)
  exact h1.clm_comp (continuous_backProp A)

/-- `⟪W v, w⟫ = ∫₀ᵀ ⟪e^{-rA} v, e^{-rA} w⟫ dr`. -/
theorem lyapunovGramian_inner (A : E →L[ℝ] E) (T : ℝ) (v w : E) :
    ⟪lyapunovGramian A T v, w⟫ = ∫ r in (0 : ℝ)..T, ⟪backProp A r v, backProp A r w⟫ := by
  have hint : IntervalIntegrable
      (fun r => ContinuousLinearMap.adjoint (backProp A r) ∘L backProp A r) volume 0 T :=
    (continuous_gramianIntegrand A).intervalIntegrable 0 T
  rw [lyapunovGramian, ContinuousLinearMap.intervalIntegral_apply hint]
  have hint2 : IntervalIntegrable
      (fun r => (ContinuousLinearMap.adjoint (backProp A r) ∘L backProp A r) v) volume 0 T :=
    ((continuous_gramianIntegrand A).clm_apply continuous_const).intervalIntegrable 0 T
  have key : ⟪∫ r in (0 : ℝ)..T,
      (ContinuousLinearMap.adjoint (backProp A r) ∘L backProp A r) v, w⟫ =
      ∫ r in (0 : ℝ)..T, ⟪(ContinuousLinearMap.adjoint (backProp A r) ∘L backProp A r) v, w⟫ := by
    have := (innerSL ℝ w).intervalIntegral_comp_comm hint2
    simp only [innerSL_apply_apply] at this
    rw [real_inner_comm, ← this]
    congr 1
    funext r
    exact real_inner_comm _ _
  rw [key]
  congr 1
  funext r
  simp [ContinuousLinearMap.adjoint_inner_left]

theorem lyapunovGramian_symm (A : E →L[ℝ] E) (T : ℝ) (v w : E) :
    ⟪lyapunovGramian A T v, w⟫ = ⟪v, lyapunovGramian A T w⟫ := by
  rw [lyapunovGramian_inner, real_inner_comm, lyapunovGramian_inner]
  congr 1
  funext r
  exact real_inner_comm _ _

/-- **Finite-horizon Lyapunov identity**: `2 ⟪W v, A v⟫ = ‖v‖² - ‖e^{-TA} v‖²`. -/
theorem two_mul_lyapunovGramian_inner_apply (A : E →L[ℝ] E) (T : ℝ) (v : E) :
    2 * ⟪lyapunovGramian A T v, A v⟫ = ‖v‖ ^ 2 - ‖backProp A T v‖ ^ 2 := by
  rw [lyapunovGramian_inner]
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) T, HasDerivAt (fun r => ‖backProp A r v‖ ^ 2)
      (-(2 * ⟪backProp A r v, backProp A r (A v)⟫)) r := by
    intro r _
    have h1 : HasDerivAt (fun r => backProp A r v) ((-(backProp A r * A)) v) r := by
      simpa using (hasDerivAt_backProp A r).clm_apply (hasDerivAt_const r v)
    have h2 := h1.norm_sq
    convert h2 using 1
    simp [inner_neg_right]
  have hcont : Continuous fun r => -(2 * ⟪backProp A r v, backProp A r (A v)⟫) := by
    have h1 : Continuous fun r => backProp A r v := (continuous_backProp A).clm_apply
      continuous_const
    have h2 : Continuous fun r => backProp A r (A v) := (continuous_backProp A).clm_apply
      continuous_const
    exact ((h1.inner h2).const_mul 2).neg
  have hftc := integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hftc
  simp only [backProp_zero] at hftc
  rw [show (1 : E →L[ℝ] E) v = v from rfl] at hftc
  linarith

/-- The Gramian is bounded below: `⟪W v, v⟫ ≥ m ‖v‖²` for some `m > 0` (for `T > 0`). -/
theorem lyapunovGramian_inner_self_ge (A : E →L[ℝ] E) {T : ℝ} (hT : 0 < T) :
    ∃ m > 0, ∀ v : E, m * ‖v‖ ^ 2 ≤ ⟪lyapunovGramian A T v, v⟫ := by
  -- bound on the forward propagator over `[0, T]`
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    ((continuous_iff_continuousAt.2 fun r =>
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) A r).continuousAt :
      Continuous fun r : ℝ => NormedSpace.exp (r • A)).continuousOn)
  set K' := max K 1
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨T / K' ^ 2, by positivity, fun v => ?_⟩
  rw [lyapunovGramian_inner]
  have hlow : ∀ r ∈ Icc (0 : ℝ) T, ‖v‖ ^ 2 / K' ^ 2 ≤ ⟪backProp A r v, backProp A r v⟫ := by
    intro r hr
    have hv : v = NormedSpace.exp (r • A) (backProp A r v) := by
      rw [← ContinuousLinearMap.mul_apply, exp_smul_mul_backProp]; rfl
    have hle : ‖v‖ ≤ K' * ‖backProp A r v‖ := by
      calc ‖v‖ = ‖NormedSpace.exp (r • A) (backProp A r v)‖ := by rw [← hv]
        _ ≤ ‖NormedSpace.exp (r • A)‖ * ‖backProp A r v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K' * ‖backProp A r v‖ := by
          gcongr
          exact (hK r hr).trans (le_max_left _ _)
    rw [real_inner_self_eq_norm_sq, div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith [norm_nonneg (backProp A r v)]
  have hint : IntervalIntegrable (fun r => ⟪backProp A r v, backProp A r v⟫) volume 0 T := by
    have h1 : Continuous fun r => backProp A r v := (continuous_backProp A).clm_apply
      continuous_const
    exact (h1.inner h1).intervalIntegrable 0 T
  have := intervalIntegral.integral_mono_on hT.le intervalIntegrable_const hint hlow
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
  calc T / K' ^ 2 * ‖v‖ ^ 2 = T * (‖v‖ ^ 2 / K' ^ 2) := by ring
    _ ≤ _ := this

/-! ### Exponential growth -/

/-- **Lyapunov exponential growth.**  Let `A` be a bounded operator on a real Hilbert space with
`‖exp (-T • A)‖ ≤ 1/2` for some `T > 0`.  There are `ε, c, μ > 0` such that every solution of
`v' = N(s) v` on `[0, S]` with `‖N(s) - A‖ ≤ ε` satisfies
`c e^{μ s} ‖v 0‖ ≤ ‖v s‖ ≤ e^{(‖A‖ + ε) s} ‖v 0‖` on `[0, S]`.  The constants depend only on
`A` (and `T`), not on `N`, `v` or `S`. -/
theorem lyapunov_exponential_growth (A : E →L[ℝ] E) {T : ℝ} (hT : 0 < T)
    (hdecay : ‖NormedSpace.exp ((-T) • A)‖ ≤ 1 / 2) :
    ∃ ε > 0, ∃ c > 0, ∃ μ > 0, ∀ (S : ℝ) (v : ℝ → E) (N : ℝ → E →L[ℝ] E),
      (∀ s ∈ Icc 0 S, HasDerivWithinAt v (N s (v s)) (Icc 0 S) s) →
      (∀ s ∈ Icc 0 S, ‖N s - A‖ ≤ ε) →
      ∀ s ∈ Icc 0 S, c * Real.exp (μ * s) * ‖v 0‖ ≤ ‖v s‖ ∧
        ‖v s‖ ≤ Real.exp ((‖A‖ + ε) * s) * ‖v 0‖ := by
  set W := lyapunovGramian A T
  obtain ⟨m, hm, hmW⟩ := lyapunovGramian_inner_self_ge A hT
  set M := ‖W‖ + 1
  have hM : 0 < M := by positivity
  have hWle : ∀ v : E, ⟪W v, v⟫ ≤ M * ‖v‖ ^ 2 := by
    intro v
    calc ⟪W v, v⟫ ≤ ‖W v‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ ‖W‖ * ‖v‖ * ‖v‖ := by gcongr; exact W.le_opNorm v
      _ ≤ M * ‖v‖ ^ 2 := by nlinarith [norm_nonneg v, norm_nonneg W]
  -- the strict Lyapunov inequality
  have hlyap : ∀ v : E, (3 / 4) * ‖v‖ ^ 2 ≤ 2 * ⟪W v, A v⟫ := by
    intro v
    rw [two_mul_lyapunovGramian_inner_apply]
    have : ‖backProp A T v‖ ≤ (1 / 2) * ‖v‖ :=
      ((backProp A T).le_opNorm v).trans (by gcongr; exact hdecay)
    have h0 : 0 ≤ ‖backProp A T v‖ := norm_nonneg _
    nlinarith [norm_nonneg v]
  set ε := 1 / (8 * M)
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, Real.sqrt (m / M), Real.sqrt_pos.2 (div_pos hm hM), 1 / (4 * M),
    by positivity, ?_⟩
  intro S v N hv hN s hs
  have h0S : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hs.1.trans hs.2⟩
  constructor
  · -- lower bound via the Lyapunov form
    have hq : ∀ s ∈ Icc 0 S, HasDerivWithinAt (fun s => ⟪W (v s), v s⟫)
        (⟪W (v s), N s (v s)⟫ + ⟪W (N s (v s)), v s⟫) (Icc 0 S) s := by
      intro s hs
      have h1 : HasDerivWithinAt (fun s => W (v s)) (W (N s (v s))) (Icc 0 S) s :=
        W.hasFDerivAt.comp_hasDerivWithinAt s (hv s hs)
      have := h1.inner ℝ (hv s hs)
      convert this using 1
    have hineq : ∀ s ∈ Icc 0 S, (1 / (2 * M)) * ⟪W (v s), v s⟫ ≤
        ⟪W (v s), N s (v s)⟫ + ⟪W (N s (v s)), v s⟫ := by
      intro s hs
      set x := v s
      have hsym : ⟪W (N s x), x⟫ = ⟪W x, N s x⟫ := by
        rw [lyapunovGramian_symm, real_inner_comm]
      rw [hsym]
      have hsplit : N s x = A x + (N s - A) x := by simp
      have hpert : |⟪W x, (N s - A) x⟫| ≤ M * ε * ‖x‖ ^ 2 := by
        calc |⟪W x, (N s - A) x⟫| ≤ ‖W x‖ * ‖(N s - A) x‖ := abs_real_inner_le_norm _ _
          _ ≤ (‖W‖ * ‖x‖) * (‖N s - A‖ * ‖x‖) := by
              gcongr
              · exact W.le_opNorm x
              · exact (N s - A).le_opNorm x
          _ ≤ (M * ‖x‖) * (ε * ‖x‖) := by
              gcongr
              · linarith
              · exact hN s hs
          _ = M * ε * ‖x‖ ^ 2 := by ring
      have hMε : M * ε = 1 / 8 := by
        simp only [ε]; field_simp
      rw [hsplit, inner_add_right]
      have hl := hlyap x
      have hu := hWle x
      have hp := (abs_le.1 hpert).1
      rw [hMε] at hp
      have : (1 / (2 * M)) * ⟪W x, x⟫ ≤ (1 / 2) * ‖x‖ ^ 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg x]
      nlinarith
    have hgrow := le_exp_mul_of_hasDerivWithinAt hq hineq s hs
    have hlow0 := hWle (v 0)
    have hlows := hmW (v s)
    have hups := hWle (v s)
    -- `m ‖v s‖² ≤ q(s)` and `q(s) ≥ e^{s/(2M)} q(0) ≥ e^{s/(2M)} m ‖v 0‖²`
    have hq0 := hmW (v 0)
    have hkey : m * Real.exp (1 / (2 * M) * s) * ‖v 0‖ ^ 2 ≤ M * ‖v s‖ ^ 2 := by
      have e1 : 0 < Real.exp (1 / (2 * M) * s) := Real.exp_pos _
      nlinarith
    have hsq : (Real.sqrt (m / M) * Real.exp (1 / (4 * M) * s) * ‖v 0‖) ^ 2 ≤ ‖v s‖ ^ 2 := by
      have hexp : Real.exp (1 / (4 * M) * s) ^ 2 = Real.exp (1 / (2 * M) * s) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp; ring
      rw [mul_pow, mul_pow, Real.sq_sqrt (div_pos hm hM).le, hexp]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hM]
      linarith
    have hnn : 0 ≤ Real.sqrt (m / M) * Real.exp (1 / (4 * M) * s) * ‖v 0‖ := by positivity
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
  · -- upper bound via `‖v‖²`
    have hp : ∀ s ∈ Icc 0 S, HasDerivWithinAt (fun s => ‖v s‖ ^ 2)
        (2 * ⟪v s, N s (v s)⟫) (Icc 0 S) s := fun s hs => (hv s hs).norm_sq
    have hineq : ∀ s ∈ Icc 0 S, 2 * ⟪v s, N s (v s)⟫ ≤ (2 * (‖A‖ + ε)) * ‖v s‖ ^ 2 := by
      intro s hs
      have hNn : ‖N s‖ ≤ ‖A‖ + ε := by
        calc ‖N s‖ = ‖A + (N s - A)‖ := by congr 1; abel
          _ ≤ ‖A‖ + ‖N s - A‖ := norm_add_le _ _
          _ ≤ ‖A‖ + ε := by gcongr; exact hN s hs
      have := real_inner_le_norm (v s) (N s (v s))
      have h2 : ‖N s (v s)‖ ≤ (‖A‖ + ε) * ‖v s‖ :=
        ((N s).le_opNorm _).trans (by gcongr)
      nlinarith [norm_nonneg (v s)]
    have hup := exp_mul_le_of_hasDerivWithinAt hp hineq s hs
    have hexp : Real.exp ((‖A‖ + ε) * s) ^ 2 = Real.exp (2 * (‖A‖ + ε) * s) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsq : ‖v s‖ ^ 2 ≤ (Real.exp ((‖A‖ + ε) * s) * ‖v 0‖) ^ 2 := by
      rw [mul_pow, hexp]; exact hup
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

end LyapunovGrowth

end RenewalGeometry
