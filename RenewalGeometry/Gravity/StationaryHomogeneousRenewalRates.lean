/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.RelationalDeSitterBranch

/-!
# Flat and de Sitter rates are the stationary homogeneous renewal solutions
  (`cor:main-derived-desitter-rates`, `eq:main-stationary-homogeneous-solutions`,
  `eq:desitter-regulator-main`; emergent-spacetime manuscript)

`thm:main-homogeneous-friedmann` shows that stationarity of the renewal-rate
action `eq:main-renewal-rate-action` in the two positive renewal variables is
equivalent to the vacuum Friedmann system `3 𝓗² = Λ`, `D_τ 𝓗 = 0` with
`𝓗 = a' / (N a)`.  This file takes that output as the hypothesis
(`IsStationaryHomogeneousSolution`; only the constraint `3 𝓗² = Λ` is
needed, the second equation follows from it) and classifies the positive
connected solutions:

* `Λ > 0` (`stationary_scale_factor_desitter`): with `H₀ = √(Λ/3)` and the
  renewal time `τ` (`τ' = N`), every solution is
  `a = a(t₀) exp (σ H₀ (τ - τ(t₀)))` with `σ ∈ {1, -1}`
  (`eq:main-stationary-homogeneous-solutions`); the renewal variables are
  `ϱ = a³`, `κ = N²/a²` (`renewalDensity`, `renewalConductance`).
* proper-time gauge `N = 1` on the expanding branch
  (`desitter_regulator_rates`): the root rate `κ/(8h²)` and vertex mass
  `ϱ h³` of `eq:main-general-homogeneous-rates` are exactly
  `a₀⁻² e^{-2H₀(t-t₀)}/(8h²)` and `a₀³ e^{3H₀(t-t₀)} h³`
  (`eq:desitter-regulator-main`); at `a₀ = 1`, `t₀ = 0` these are
  `RelationalDeSitterBranch.rootRate` / `vertexMass`
  (`desitter_regulator_rates_eq_branch`).
* `Λ = 0` (`stationary_scale_factor_flat`): `a` is constant.
* `Λ < 0` (`stationary_solution_empty_of_neg`): no positive solution exists
  (the solution set is empty).

Scoped hypotheses made explicit: the time set `s` is open and connected,
`a` and `N` are positive and differentiable there with continuous
derivative data (`a'`, `N` continuous on `s`), as the manuscript's smooth
homogeneous ansatz implicitly assumes.
-/

open scoped BigOperators

namespace RenewalGeometry

/-- Renewal density `ϱ = a³` of `eq:main-isotropic-renewal-map`. -/
def renewalDensity (a : ℝ → ℝ) (t : ℝ) : ℝ := a t ^ 3

/-- Renewal conductance `κ = N²/a²` of `eq:main-isotropic-renewal-map`. -/
noncomputable def renewalConductance (a N : ℝ → ℝ) (t : ℝ) : ℝ :=
  N t ^ 2 / a t ^ 2

/-- Root rate `k_{α,h} = κ/(8h²)` of `eq:main-general-homogeneous-rates`. -/
noncomputable def homogeneousRootRate (κ : ℝ → ℝ) (h t : ℝ) : ℝ :=
  κ t / (8 * h ^ 2)

/-- Vertex mass `m_h = ϱ h³` of `eq:main-general-homogeneous-rates`. -/
def homogeneousVertexMass (ϱ : ℝ → ℝ) (h t : ℝ) : ℝ := ϱ t * h ^ 3

/-- A positive connected stationary solution of the homogeneous renewal
action on the open connected time set `s`: scale factor `a` with derivative
`a'`, lapse `N`, renewal time `τ` with `τ' = N`, and the Friedmann
constraint `3 𝓗² = Λ`, `𝓗 = a'/(N a)` (the stationarity output of
`thm:main-homogeneous-friedmann`, `eq:main-vacuum-friedmann`). -/
structure IsStationaryHomogeneousSolution (Λ : ℝ) (s : Set ℝ)
    (a a' N τ : ℝ → ℝ) : Prop where
  isOpen : IsOpen s
  isPreconnected : IsPreconnected s
  a_pos : ∀ t ∈ s, 0 < a t
  N_pos : ∀ t ∈ s, 0 < N t
  hasDerivAt_a : ∀ t ∈ s, HasDerivAt a (a' t) t
  hasDerivAt_τ : ∀ t ∈ s, HasDerivAt τ (N t) t
  continuousOn_a' : ContinuousOn a' s
  continuousOn_N : ContinuousOn N s
  friedmann : ∀ t ∈ s, 3 * (a' t / (N t * a t)) ^ 2 = Λ

namespace IsStationaryHomogeneousSolution

variable {Λ : ℝ} {s : Set ℝ} {a a' N τ : ℝ → ℝ}

theorem continuousOn_a (h : IsStationaryHomogeneousSolution Λ s a a' N τ) :
    ContinuousOn a s := fun t ht =>
  (h.hasDerivAt_a t ht).continuousAt.continuousWithinAt

/-- The Hubble rate `𝓗 = a'/(N a)` is continuous on `s`. -/
theorem continuousOn_hubble
    (h : IsStationaryHomogeneousSolution Λ s a a' N τ) :
    ContinuousOn (fun t => a' t / (N t * a t)) s := by
  refine h.continuousOn_a'.div (h.continuousOn_N.mul h.continuousOn_a) ?_
  intro t ht
  exact (mul_pos (h.N_pos t ht) (h.a_pos t ht)).ne'

/-- On a connected time set the Hubble rate has a constant sign:
`𝓗 = σ H₀` with `σ ∈ {1, -1}` and `H₀ = √(Λ/3)`. -/
theorem hubble_eq_sign (h : IsStationaryHomogeneousSolution Λ s a a' N τ)
    (hΛ : 0 < Λ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ t ∈ s, a' t / (N t * a t) = σ * Real.sqrt (Λ / 3) := by
  set H₀ : ℝ := Real.sqrt (Λ / 3) with hH₀
  have hH₀pos : 0 < H₀ := Real.sqrt_pos.mpr (by positivity)
  have hsq : Set.EqOn ((fun t => a' t / (N t * a t)) ^ 2)
      ((fun _ => H₀) ^ 2) s := by
    intro t ht
    simp only [Pi.pow_apply]
    have := h.friedmann t ht
    rw [hH₀, Real.sq_sqrt (by positivity)]
    linarith
  rcases h.isPreconnected.eq_or_eq_neg_of_sq_eq h.continuousOn_hubble
      continuousOn_const hsq (fun _ => hH₀pos.ne') with hpos | hneg
  · exact ⟨1, Or.inl rfl, fun t ht => by simpa using hpos ht⟩
  · exact ⟨-1, Or.inr rfl, fun t ht => by
      have := hneg ht
      simp only [Pi.neg_apply] at this
      rw [this]; ring⟩

/-- Integration of a constant Hubble rate: if `a'/(N a) = c` on `s`, then
`a = a(t₀) exp (c (τ - τ(t₀)))` on `s` (integrating factor `a exp(-c τ)`). -/
theorem scale_factor_of_hubble_const
    (h : IsStationaryHomogeneousSolution Λ s a a' N τ) {c : ℝ}
    (hH : ∀ t ∈ s, a' t / (N t * a t) = c) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    ∀ t ∈ s, a t = a t₀ * Real.exp (c * (τ t - τ t₀)) := by
  -- the integrating factor `φ = a · exp (-c τ)` has zero derivative on `s`
  set φ : ℝ → ℝ := fun t => a t * Real.exp (-(c * τ t)) with hφ
  have hφderiv : ∀ t ∈ s, HasDerivAt φ 0 t := by
    intro t ht
    have h1 := h.hasDerivAt_a t ht
    have h2 : HasDerivAt (fun t => Real.exp (-(c * τ t)))
        (Real.exp (-(c * τ t)) * (-(c * N t))) t :=
      ((h.hasDerivAt_τ t ht).const_mul c).neg.exp
    have h3 := h1.mul h2
    have hNa : N t * a t ≠ 0 := (mul_pos (h.N_pos t ht) (h.a_pos t ht)).ne'
    have ha' : a' t = c * (N t * a t) := by
      have := hH t ht
      rw [div_eq_iff hNa] at this
      rw [this]
    have h4 : a' t * Real.exp (-(c * τ t)) +
        a t * (Real.exp (-(c * τ t)) * (-(c * N t))) = 0 := by
      rw [ha']
      ring
    rw [h4] at h3
    exact h3
  have hconst : ∀ t ∈ s, φ t = φ t₀ := by
    intro t ht
    refine h.isOpen.is_const_of_deriv_eq_zero h.isPreconnected
      (fun t ht => (hφderiv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hφderiv t ht).deriv) ht ht₀
  intro t ht
  have hφt := hconst t ht
  simp only [hφ] at hφt
  have hexp : Real.exp (c * (τ t - τ t₀)) =
      Real.exp (-(c * τ t₀)) / Real.exp (-(c * τ t)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp, ← mul_div_assoc, ← hφt]
  field_simp

/-- `eq:main-stationary-homogeneous-solutions` for `Λ > 0`: every positive
connected stationary solution is `a = a(t₀) exp (σ H₀ (τ - τ(t₀)))` with
`σ ∈ {1, -1}` and `H₀ = √(Λ/3)`. -/
theorem stationary_scale_factor_desitter
    (h : IsStationaryHomogeneousSolution Λ s a a' N τ) (hΛ : 0 < Λ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ t ∈ s, a t = a t₀ *
        Real.exp (σ * Real.sqrt (Λ / 3) * (τ t - τ t₀)) := by
  obtain ⟨σ, hσ, hH⟩ := h.hubble_eq_sign hΛ
  exact ⟨σ, hσ, h.scale_factor_of_hubble_const hH ht₀⟩

/-- `Λ = 0`: the scale factor is constant on the connected time set. -/
theorem stationary_scale_factor_flat
    (h : IsStationaryHomogeneousSolution Λ s a a' N τ) (hΛ : Λ = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    ∀ t ∈ s, a t = a t₀ := by
  have ha' : ∀ t ∈ s, a' t = 0 := by
    intro t ht
    have hf := h.friedmann t ht
    rw [hΛ] at hf
    have hNa : N t * a t ≠ 0 := (mul_pos (h.N_pos t ht) (h.a_pos t ht)).ne'
    have hsq : (a' t / (N t * a t)) ^ 2 = 0 := by linarith
    have hq : a' t / (N t * a t) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    rcases div_eq_zero_iff.mp hq with h0 | h0
    · exact h0
    · exact absurd h0 hNa
  intro t ht
  exact h.isOpen.is_const_of_deriv_eq_zero h.isPreconnected
    (fun t ht => (h.hasDerivAt_a t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(h.hasDerivAt_a t ht).deriv, ha' t ht]; rfl) ht ht₀

/-- `Λ < 0`: there is no positive real stationary solution (the time set
of any solution is empty). -/
theorem stationary_solution_empty_of_neg
    (h : IsStationaryHomogeneousSolution Λ s a a' N τ) (hΛ : Λ < 0) :
    s = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  have hf := h.friedmann t ht
  have : 0 ≤ 3 * (a' t / (N t * a t)) ^ 2 := by positivity
  linarith

/-- Proper-time gauge `N = 1` on `s`: the renewal time is the coordinate
time up to a constant, `τ(t) - τ(t₀) = t - t₀`. -/
theorem renewalTime_sub_eq_of_lapse_one
    (h : IsStationaryHomogeneousSolution Λ s a a' N τ)
    (hN : ∀ t ∈ s, N t = 1) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    ∀ t ∈ s, τ t - τ t₀ = t - t₀ := by
  set ψ : ℝ → ℝ := fun t => τ t - t with hψ
  have hψderiv : ∀ t ∈ s, HasDerivAt ψ 0 t := by
    intro t ht
    have := (h.hasDerivAt_τ t ht).sub (hasDerivAt_id t)
    rw [hN t ht, sub_self] at this
    exact this
  intro t ht
  have := h.isOpen.is_const_of_deriv_eq_zero h.isPreconnected
    (fun t ht => (hψderiv t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hψderiv t ht).deriv) ht ht₀
  simp only [hψ] at this
  linarith

/-- `eq:desitter-regulator-main`: in proper-time gauge on the expanding
branch (`σ = 1`), the root rate `κ/(8h²)` and vertex mass `ϱ h³` built from
`κ = N²/a²`, `ϱ = a³` are `a₀⁻² e^{-2H₀(t-t₀)}/(8h²)` and
`a₀³ e^{3H₀(t-t₀)} h³`, with `a₀ = a(t₀)`. -/
theorem desitter_regulator_rates
    (h : IsStationaryHomogeneousSolution Λ s a a' N τ)
    (hN : ∀ t ∈ s, N t = 1) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hexpanding : ∀ t ∈ s,
      a t = a t₀ * Real.exp (Real.sqrt (Λ / 3) * (t - t₀))) (hh : ℝ) :
    ∀ t ∈ s,
      homogeneousRootRate (renewalConductance a N) hh t =
        (a t₀)⁻¹ ^ 2 * Real.exp (-2 * Real.sqrt (Λ / 3) * (t - t₀)) /
          (8 * hh ^ 2) ∧
      homogeneousVertexMass (renewalDensity a) hh t =
        a t₀ ^ 3 * Real.exp (3 * Real.sqrt (Λ / 3) * (t - t₀)) * hh ^ 3 := by
  intro t ht
  set H₀ : ℝ := Real.sqrt (Λ / 3)
  have hat := hexpanding t ht
  have ha₀ : a t₀ ≠ 0 := (h.a_pos t₀ ht₀).ne'
  have hexp2 : Real.exp (-2 * H₀ * (t - t₀)) =
      (Real.exp (H₀ * (t - t₀)))⁻¹ ^ 2 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexp3 : Real.exp (3 * H₀ * (t - t₀)) =
      Real.exp (H₀ * (t - t₀)) ^ 3 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  constructor
  · simp only [homogeneousRootRate, renewalConductance, hN t ht, hat, hexp2]
    field_simp
  · simp only [homogeneousVertexMass, renewalDensity, hat, hexp3]
    ring

/-- The expanding branch (`σ = 1`, Hubble rate `+H₀`) in proper-time
gauge: `a = a₀ exp (H₀ (t - t₀))`. -/
theorem expanding_scale_factor_of_lapse_one
    (h : IsStationaryHomogeneousSolution Λ s a a' N τ)
    (hN : ∀ t ∈ s, N t = 1) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hσ : ∀ t ∈ s, a' t / (N t * a t) = Real.sqrt (Λ / 3)) :
    ∀ t ∈ s, a t = a t₀ * Real.exp (Real.sqrt (Λ / 3) * (t - t₀)) := by
  intro t ht
  rw [h.scale_factor_of_hubble_const hσ ht₀ t ht,
    h.renewalTime_sub_eq_of_lapse_one hN ht₀ t ht]

end IsStationaryHomogeneousSolution

/-- At `a₀ = 1`, `t₀ = 0` the boxed de Sitter rates of
`eq:desitter-regulator-main` are exactly the encoded regulator rates
`RelationalDeSitterBranch.rootRate` and `RelationalDeSitterBranch.vertexMass`. -/
theorem desitter_regulator_rates_eq_branch (H₀ hh t : ℝ) :
    (1 : ℝ)⁻¹ ^ 2 * Real.exp (-2 * H₀ * (t - 0)) / (8 * hh ^ 2) =
        RelationalDeSitterBranch.rootRate H₀ hh t ∧
      (1 : ℝ) ^ 3 * Real.exp (3 * H₀ * (t - 0)) * hh ^ 3 =
        RelationalDeSitterBranch.vertexMass H₀ hh t := by
  simp [RelationalDeSitterBranch.rootRate, RelationalDeSitterBranch.vertexMass]

end RenewalGeometry
