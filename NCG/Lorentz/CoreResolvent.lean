/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Common-core strong-resolvent criterion and propagator convergence

`lem:app-core-resolvent` of the flagship manuscript, in two parts.

**Strong resolvent convergence** (`strong_resolvent_of_core`): let
`Rₙ, R` be the resolvents `(Aₙ − z)⁻¹, (A − z)⁻¹` at a fixed nonreal
`z`, encoded by exactly the facts the manuscript proof consumes:

* a uniform bound `‖Rₙ‖ ≤ M` (for self-adjoint `Aₙ` one may take
  `M = |Im z|⁻¹`);
* the left-inverse identities `Rₙ (Aₙ − z) u = u` and
  `R (A − z) u = u` on a common core `C`;
* density of `(A − z) '' C` (for a self-adjoint `A` with core `C`
  this is surjectivity of `A − z` plus graph-density of `C`);
* the core convergence `Aₙ u → A u` on `C`.

Then `Rₙ y → R y` for **every** `y` — the ε/3 argument of the
manuscript: approximate `y` by `(A − z) u`, use the left-inverse
identity on the core and the uniform resolvent bound.  The statement
is phrased for `T = A − z`, `Tₙ = Aₙ − z` directly, over real scalars
(a ℂ-linear resolvent restricts to an ℝ-linear one, so the real
statement is the stronger one).

**Propagator convergence** (`duhamel_propagator_bound`,
`propagator_tendsto`): write `G = −iA` and `Gₙ = −iAₙ` for the skew
generators.  The discrete renewal Hamiltonians are bounded
finite-difference operators, so each `Gₙ` is a bounded operator whose
isometric one-parameter group `Uₙ` is operator-norm differentiable
with `Uₙ' = Gₙ ∘ Uₙ`; the limit evolution `U` need only be
differentiable along the orbit of the vector `u` with generator
values `G(U(s)u)`.  The Duhamel identity

`U(t)u − Uₙ(t)u = ∫₀ᵗ (d/ds) [Uₙ(t−s) U(s) u] ds`

gives `‖U(t)u − Uₙ(t)u‖ ≤ ∫₀ᵀ ‖G(U(s)u) − Gₙ(U(s)u)‖ ds` uniformly
for `t ∈ [0, T]`, and dominated convergence sends the right side to
zero.  This proves the compact-interval propagator clause of
`lem:app-core-resolvent` by the invariant-core Duhamel route; the
`C₀` functional-calculus clause needs an unbounded spectral theorem
that Mathlib does not yet provide and remains a noted step.  Negative
times follow by applying the result to the time-reversed evolutions
`t ↦ U(−t)`, whose skew generators are `−G, −Gₙ`.
-/

namespace NCG

open Filter intervalIntegral

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-! ## Strong resolvent convergence from a common core -/

/-- **`lem:app-core-resolvent` (strong-resolvent clause)**: uniform
resolvent bounds, left inverses on a common core, density of the
core image, and core convergence force strong convergence of the
resolvents on the whole space. -/
theorem strong_resolvent_of_core
    (C : Set H) (R : H →L[ℝ] H) (Rn : ℕ → H →L[ℝ] H)
    (T : H → H) (Tn : ℕ → H → H) {M : ℝ}
    (hM : ∀ n, ‖Rn n‖ ≤ M)
    (hRn_inv : ∀ n, ∀ u ∈ C, Rn n (Tn n u) = u)
    (hR_inv : ∀ u ∈ C, R (T u) = u)
    (hdense : Dense (T '' C))
    (hconv : ∀ u ∈ C,
      Tendsto (fun n => Tn n u) atTop (nhds (T u))) :
    ∀ y : H, Tendsto (fun n => Rn n y) atTop (nhds (R y)) := by
  intro y
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- approximate `y` from the image of the core
  set K : ℝ := M + ‖R‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  have hδpos : 0 < ε / (2 * K) := by positivity
  obtain ⟨z, hzmem, hzdist⟩ :=
    Metric.mem_closure_iff.mp (hdense y) _ hδpos
  obtain ⟨u, huC, rfl⟩ := hzmem
  have hyu : ‖y - T u‖ < ε / (2 * K) := by
    rw [← dist_eq_norm]
    exact hzdist
  -- tail index for the core convergence
  have hM1 : (0:ℝ) < M + 1 := by positivity
  have htail : ∀ᶠ n in atTop,
      ‖T u - Tn n u‖ < ε / (2 * (M + 1)) := by
    have h := (hconv u huC)
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h (ε / (2 * (M + 1))) (by positivity)
    exact eventually_atTop.mpr ⟨N, fun n hn => by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hN n hn⟩
  rw [← eventually_atTop]
  filter_upwards [htail] with n hn
  -- the ε/3 decomposition through the core representative
  have hdecomp : Rn n y - R y
      = Rn n (y - T u) + Rn n (T u - Tn n u) + (R (T u) - R y) := by
    have h1 : Rn n (T u - Tn n u)
        = Rn n (T u) - u := by
      rw [map_sub, hRn_inv n u huC]
    rw [h1, map_sub, hR_inv u huC]
    abel
  have hb1 : ‖Rn n (y - T u)‖ ≤ M * ‖y - T u‖ :=
    le_trans ((Rn n).le_opNorm _)
      (mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _))
  have hb2 : ‖Rn n (T u - Tn n u)‖ ≤ M * ‖T u - Tn n u‖ :=
    le_trans ((Rn n).le_opNorm _)
      (mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _))
  have hb3 : ‖R (T u) - R y‖ ≤ ‖R‖ * ‖y - T u‖ := by
    rw [← map_sub, norm_sub_rev y (T u)]
    exact R.le_opNorm _
  rw [dist_eq_norm, hdecomp]
  have hchain : ‖Rn n (y - T u) + Rn n (T u - Tn n u)
        + (R (T u) - R y)‖
      ≤ M * ‖y - T u‖ + M * ‖T u - Tn n u‖ + ‖R‖ * ‖y - T u‖ := by
    calc ‖Rn n (y - T u) + Rn n (T u - Tn n u) + (R (T u) - R y)‖
        ≤ ‖Rn n (y - T u) + Rn n (T u - Tn n u)‖
          + ‖R (T u) - R y‖ := norm_add_le _ _
      _ ≤ ‖Rn n (y - T u)‖ + ‖Rn n (T u - Tn n u)‖
          + ‖R (T u) - R y‖ := by
          have := norm_add_le (Rn n (y - T u)) (Rn n (T u - Tn n u))
          linarith
      _ ≤ M * ‖y - T u‖ + M * ‖T u - Tn n u‖ + ‖R‖ * ‖y - T u‖ := by
          linarith
  -- assemble the numeric bound
  have hRnn : (0:ℝ) ≤ ‖R‖ := norm_nonneg _
  have hstep1 : (M + ‖R‖) * ‖y - T u‖ < K * (ε / (2 * K)) := by
    have hcoef : M + ‖R‖ < K := by rw [hK]; linarith
    have hyu0 : 0 ≤ ‖y - T u‖ := norm_nonneg _
    by_cases hy0 : ‖y - T u‖ = 0
    · rw [hy0, mul_zero]
      positivity
    · calc (M + ‖R‖) * ‖y - T u‖
          ≤ K * ‖y - T u‖ :=
            mul_le_mul_of_nonneg_right hcoef.le hyu0
        _ < K * (ε / (2 * K)) :=
            mul_lt_mul_of_pos_left hyu hKpos
  have hstep2 : M * ‖T u - Tn n u‖ < (M + 1) * (ε / (2 * (M + 1))) := by
    have h0 : 0 ≤ ‖T u - Tn n u‖ := norm_nonneg _
    calc M * ‖T u - Tn n u‖
        ≤ (M + 1) * ‖T u - Tn n u‖ :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ < (M + 1) * (ε / (2 * (M + 1))) :=
          mul_lt_mul_of_pos_left hn hM1
  have hK2 : K * (ε / (2 * K)) = ε / 2 := by
    field_simp
  have hM2 : (M + 1) * (ε / (2 * (M + 1))) = ε / 2 := by
    field_simp
  rw [hK2] at hstep1
  rw [hM2] at hstep2
  calc ‖Rn n (y - T u) + Rn n (T u - Tn n u) + (R (T u) - R y)‖
      ≤ M * ‖y - T u‖ + M * ‖T u - Tn n u‖ + ‖R‖ * ‖y - T u‖ :=
        hchain
    _ < ε := by linarith

/-! ## Duhamel propagator bound for bounded approximants -/

variable [CompleteSpace H]

/-- **Duhamel bound**: if `Uₙ` is an isometric one-parameter group
with bounded skew generator `Gₙ` (operator-norm derivative
`Uₙ' = Gₙ ∘ Uₙ` and commutation), and `U(s)u` is a differentiable
evolution with generator values `G(U(s)u)` along the orbit of `u`,
then for `0 ≤ t ≤ T`,
`‖U(t)u − Uₙ(t)u‖ ≤ ∫₀ᵀ ‖G(U(s)u) − Gₙ(U(s)u)‖ ds`. -/
theorem duhamel_propagator_bound
    (U : ℝ → H →L[ℝ] H) (Un : ℝ → H →L[ℝ] H) (Gn : H →L[ℝ] H)
    (G : H → H) (u : H) {T : ℝ}
    (hU0 : U 0 u = u) (hUn0 : Un 0 = ContinuousLinearMap.id ℝ H)
    (hUn_iso : ∀ s v, ‖Un s v‖ = ‖v‖)
    (hUn_deriv : ∀ σ, HasDerivAt Un (Gn.comp (Un σ)) σ)
    (hUn_comm : ∀ σ v, Gn (Un σ v) = Un σ (Gn v))
    (hU_deriv : ∀ s, HasDerivAt (fun σ => U σ u) (G (U s u)) s)
    (hGcont : Continuous fun s => G (U s u)) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖U t u - Un t u‖
        ≤ ∫ s in (0:ℝ)..T, ‖G (U s u) - Gn (U s u)‖ := by
  rintro t ⟨ht0, htT⟩
  -- the interpolating curve `g s = Uₙ(t−s) (U(s) u)`
  set g : ℝ → H := fun s => Un (t - s) (U s u) with hg
  have hflip : ∀ s : ℝ,
      HasDerivAt (fun σ : ℝ => Un (t - σ))
        ((-1 : ℝ) • (Gn.comp (Un (t - s)))) s := by
    intro s
    have h1 : HasDerivAt (fun σ : ℝ => t - σ) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    exact HasDerivAt.scomp s (hUn_deriv (t - s)) h1
  -- its derivative collapses to `Uₙ(t−s) ((G − Gₙ) U(s) u)`
  have hgderiv : ∀ s : ℝ, HasDerivAt g
      (Un (t - s) (G (U s u) - Gn (U s u))) s := by
    intro s
    have happ := (hflip s).clm_apply (hU_deriv s)
    have hsimp :
        ((-1 : ℝ) • (Gn.comp (Un (t - s)))) (U s u)
          + Un (t - s) (G (U s u))
        = Un (t - s) (G (U s u) - Gn (U s u)) := by
      simp only [ContinuousLinearMap.comp_apply, neg_smul,
        one_smul, neg_apply, map_sub]
      rw [hUn_comm (t - s) (U s u)]
      abel
    rw [hsimp] at happ
    exact happ
  -- continuity of the orbit and of the derivative
  have hUcont : Continuous fun s => U s u :=
    continuous_iff_continuousAt.mpr
      fun s => (hU_deriv s).differentiableAt.continuousAt
  have hUncont : Continuous fun s : ℝ => Un (t - s) :=
    continuous_iff_continuousAt.mpr
      fun s => (hflip s).differentiableAt.continuousAt
  have hDcont : Continuous fun s =>
      Un (t - s) (G (U s u) - Gn (U s u)) :=
    hUncont.clm_apply (hGcont.sub (Gn.continuous.comp hUcont))
  -- fundamental theorem of calculus on `[0, t]`
  have hFTC : (∫ s in (0:ℝ)..t,
        Un (t - s) (G (U s u) - Gn (U s u)))
      = g t - g 0 :=
    integral_eq_sub_of_hasDerivAt
      (fun s _ => hgderiv s)
      (hDcont.intervalIntegrable 0 t)
  have hgt : g t = U t u := by
    simp [hg, hUn0]
  have hg0 : g 0 = Un t u := by
    simp [hg, hU0]
  -- pointwise norm of the integrand
  have hnorm : ∀ s : ℝ,
      ‖Un (t - s) (G (U s u) - Gn (U s u))‖
      = ‖G (U s u) - Gn (U s u)‖ :=
    fun s => hUn_iso (t - s) _
  -- assemble
  have hbound1 : ‖U t u - Un t u‖
      ≤ ∫ s in (0:ℝ)..t, ‖G (U s u) - Gn (U s u)‖ := by
    rw [← hgt, ← hg0, ← hFTC]
    calc ‖∫ s in (0:ℝ)..t, Un (t - s) (G (U s u) - Gn (U s u))‖
        ≤ ∫ s in (0:ℝ)..t,
            ‖Un (t - s) (G (U s u) - Gn (U s u))‖ :=
          norm_integral_le_integral_norm ht0
      _ = ∫ s in (0:ℝ)..t, ‖G (U s u) - Gn (U s u)‖ := by
          congr 1
          funext s
          exact hnorm s
  refine le_trans hbound1 ?_
  -- extend the integration interval from `[0, t]` to `[0, T]`
  refine integral_mono_interval le_rfl ht0 htT ?_ ?_
  · exact Filter.Eventually.of_forall fun s => norm_nonneg _
  · exact ((hGcont.sub (Gn.continuous.comp hUcont)).norm).intervalIntegrable 0 T

/-- **`lem:app-core-resolvent` (propagator clause)**: with bounded
skew generators converging on the orbit of `u` under a uniform
dominating constant, the discrete propagators converge to the limit
evolution, uniformly for `t` in the compact interval `[0, T]` (the
Duhamel bound is `t`-independent). -/
theorem propagator_tendsto
    (U : ℝ → H →L[ℝ] H) (Un : ℕ → ℝ → H →L[ℝ] H)
    (Gn : ℕ → H →L[ℝ] H) (G : H → H) (u : H) {T : ℝ}
    (hU0 : U 0 u = u)
    (hUn0 : ∀ n, Un n 0 = ContinuousLinearMap.id ℝ H)
    (hUn_iso : ∀ n s v, ‖Un n s v‖ = ‖v‖)
    (hUn_deriv : ∀ n σ, HasDerivAt (Un n)
      ((Gn n).comp (Un n σ)) σ)
    (hUn_comm : ∀ n σ v, Gn n (Un n σ v) = Un n σ (Gn n v))
    (hU_deriv : ∀ s, HasDerivAt (fun σ => U σ u) (G (U s u)) s)
    (hGcont : Continuous fun s => G (U s u))
    (hconv : ∀ s, Tendsto (fun n => Gn n (U s u)) atTop
      (nhds (G (U s u))))
    (hdom : ∃ D : ℝ, ∀ n s, ‖G (U s u) - Gn n (U s u)‖ ≤ D) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      Tendsto (fun n => Un n t u) atTop (nhds (U t u)) := by
  -- the driving integrals tend to zero by dominated convergence
  obtain ⟨D, hD⟩ := hdom
  have hUcont : Continuous fun s => U s u :=
    continuous_iff_continuousAt.mpr
      fun s => (hU_deriv s).differentiableAt.continuousAt
  have hcont : ∀ n, Continuous fun s =>
      ‖G (U s u) - Gn n (U s u)‖ :=
    fun n => (hGcont.sub ((Gn n).continuous.comp hUcont)).norm
  have hint : Tendsto
      (fun n => ∫ s in (0:ℝ)..T, ‖G (U s u) - Gn n (U s u)‖)
      atTop (nhds 0) := by
    have hint2 : Tendsto
        (fun n => ∫ s in (0:ℝ)..T, ‖G (U s u) - Gn n (U s u)‖)
        atTop (nhds (∫ _ in (0:ℝ)..T, (0:ℝ))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun _ => D) ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun n =>
          (hcont n).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun n =>
          MeasureTheory.ae_of_all _ fun s _ => by
            simpa using hD n s
      · exact intervalIntegrable_const
      · refine MeasureTheory.ae_of_all _ fun s _ => ?_
        have h1 : Tendsto (fun n => G (U s u) - Gn n (U s u)) atTop
            (nhds 0) := by
          have h2 := Filter.Tendsto.sub
            (tendsto_const_nhds (x := G (U s u))) (hconv s)
          simpa using h2
        simpa using h1.norm
    simpa using hint2
  -- squeeze through the Duhamel bound
  intro t htmem
  have hbound : ∀ n, ‖U t u - Un n t u‖
      ≤ ∫ s in (0:ℝ)..T, ‖G (U s u) - Gn n (U s u)‖ :=
    fun n => duhamel_propagator_bound U (Un n) (Gn n) G u hU0
      (hUn0 n) (hUn_iso n) (hUn_deriv n) (hUn_comm n)
      hU_deriv hGcont t htmem
  have hnormconv : Tendsto
      (fun n => ‖U t u - Un n t u‖) atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _) hbound hint
  have h2 : Tendsto (fun n => U t u - Un n t u) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormconv
  have h3 := Filter.Tendsto.sub
    (tendsto_const_nhds (x := U t u)) h2
  simpa using h3

end NCG
