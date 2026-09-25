/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.CurvatureEnergyPropagationExact

/-!
# Finite curvature-energy propagation from initial data
  (`thm:supp-curvature-propagation`, `eq:supp-curvature-energy-differential`;
  emergent-spacetime manuscript, supplement version of
  `thm:main-curvature-propagation`)

At a fixed cutoff the retained curvature coefficients `y_X = (E_X, B_X)` live
in a finite-dimensional real inner-product space `V`, the positive Gram is a
time-dependent symmetric positive form `M(t)`, and the propagation writer
`eq:main-curvature-propagation-writer` is `ẏ = (K + L) y + f` with `M`-skew
principal block `K` (`M K + Kᵀ M = 0`, i.e. `⟪M x, K x⟫ = 0`).  With
`z_X² = ⟪y, M y⟫ = gramEnergy M y ^ 2` and the growth function `a ≥ 0` of
`eq:main-curvature-growth` (encoded by its defining quadratic-form bound
`⟪x, (Ṁ + M L + Lᵀ M) x⟫ ≤ 2 a ⟪x, M x⟫`), this file states the supplement
theorem in its own form:

* `supp_curvature_energy_differential` (`eq:supp-curvature-energy-differential`):
  `z_X²` is differentiable and `½ (d/dt) z_X² ≤ a_X z_X² + z_X ‖f_X‖_{M_X}`;
  the principal term cancels exactly by `M`-skewness and the source term is
  bounded by Cauchy–Schwarz in the positive `M`-Gram;
* `supp_curvature_propagation`: the differential inequality at every time,
  the boxed propagation bound `eq:main-curvature-energy-propagation`
  (integrating factor on `√(z² + ε²)`, `ε ↓ 0`), and — under the stable
  incidence `eq:main-curvature-incidence`, the lapse bound and the uniform
  budgets `eq:main-curvature-budgets` — the derived `L²` curvature bound
  `eq:main-derived-l2-curvature`.

The analytic content is inherited from `CurvatureEnergyPropagationExact`
(`gramEnergySq_deriv_le`, `curvature_energy_propagation`,
`curvature_energy_uniform_bound`, `derived_l2_curvature_bound`); this file
packages it as the supplement statement.  Scoped hypotheses disclosed:
the writer holds for all real times (only `[0, T_*]` is used), `y` and `M`
are differentiable, `f` and `a` continuous; the slice structure of `L²(K)` is
abstracted as in the main-text file (slice norms `ρ(t) ≤ C_I z(t)`, lapse
`0 ≤ N ≤ N_*`, `‖R_X‖_{L²(K)} ≤ √(∫₀^{T_*} N ρ²) + C_ζ`).
-/

open scoped InnerProductSpace
open MeasureTheory intervalIntegral

namespace RenewalGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `z_X² = ⟪y, M y⟫` when the Gram is positive semidefinite. -/
theorem gramEnergy_sq (M : ℝ → V →L[ℝ] V) (y : ℝ → V) (t : ℝ)
    (hpos : 0 ≤ ⟪y t, M t (y t)⟫_ℝ) :
    gramEnergy M y t ^ 2 = ⟪y t, M t (y t)⟫_ℝ :=
  Real.sq_sqrt hpos

/-- `eq:supp-curvature-energy-differential`: for a positive symmetric Gram
`M`, the energy `z_X² = y_Xᵀ M_X y_X` is differentiable in time and, at every
time where the writer `ẏ = (K + L) y + f` holds with `M`-skew `K` and growth
bound `a`, `½ (d/dt) z_X² ≤ a_X z_X² + z_X ‖f_X‖_{M_X}`. -/
theorem supp_curvature_energy_differential {M M' K L : ℝ → V →L[ℝ] V} {y y' f : ℝ → V}
    {a : ℝ → ℝ} {t : ℝ}
    (hM : HasDerivAt M (M' t) t) (hy : HasDerivAt y (y' t) t)
    (hsymm : ∀ x z, ⟪M t x, z⟫_ℝ = ⟪x, M t z⟫_ℝ) (hpos : ∀ s x, 0 ≤ ⟪x, M s x⟫_ℝ)
    (hwriter : y' t = (K t + L t) (y t) + f t)
    (hskew : ∀ x, ⟪M t x, K t x⟫_ℝ = 0)
    (hgrowth : ∀ x, ⟪x, M' t x⟫_ℝ + 2 * ⟪M t x, L t x⟫_ℝ ≤ 2 * a t * ⟪x, M t x⟫_ℝ) :
    DifferentiableAt ℝ (fun s => gramEnergy M y s ^ 2) t ∧
      (1 / 2) * deriv (fun s => gramEnergy M y s ^ 2) t ≤
        a t * gramEnergy M y t ^ 2 + gramEnergy M y t * gramEnergy M f t := by
  have hderiv : HasDerivAt (fun s => gramEnergy M y s ^ 2)
      (⟪y t, M' t (y t)⟫_ℝ + 2 * ⟪M t (y t), y' t⟫_ℝ) t := by
    have h := hasDerivAt_gramEnergySq hM hy hsymm
    have hfun : (fun s => gramEnergy M y s ^ 2) = fun s => ⟪y s, M s (y s)⟫_ℝ := by
      funext s
      exact gramEnergy_sq M y s (hpos s (y s))
    rw [hfun]
    exact h
  refine ⟨hderiv.differentiableAt, ?_⟩
  rw [hderiv.deriv, gramEnergy_sq M y t (hpos t (y t))]
  have hb := gramEnergySq_deriv_le hsymm (hpos t) hwriter hskew hgrowth
  unfold gramEnergy
  linarith

/-- `thm:supp-curvature-propagation`: at a fixed cutoff with
`y_X = (E_X, B_X)`, positive symmetric Gram `M_X`, `M_X`-skew principal block
`K_X`, lower-order block `L_X`, source `f_X` and growth function `a_X ≥ 0`
as in `eq:main-curvature-propagation-writer`–`eq:main-curvature-growth`, with
`z_X² = y_Xᵀ M_X y_X`:

1. `eq:supp-curvature-energy-differential` holds at every time,
   `½ (d/dt) z_X² ≤ a_X z_X² + z_X ‖f_X‖_{M_X}`;
2. `eq:main-curvature-energy-propagation` holds for every `t ≥ 0`,
   `z_X(t) ≤ e^{∫₀ᵗ a_X} [z_X(0) + ∫₀ᵗ e^{-∫₀ˢ a_X} ‖f_X(s)‖_{M_X(s)} ds]`;
3. under the stable incidence `eq:main-curvature-incidence` (slice norms
   `ρ(t) ≤ C_I z_X(t)`, `‖R_X‖_{L²(K)} ≤ √(∫₀^{T_*} N ρ²) + C_ζ`), the lapse
   bound `0 ≤ N ≤ N_*` and the uniform budgets `eq:main-curvature-budgets`
   (`z_X(0) ≤ Z_*`, `∫₀^{T_*} a_X ≤ A_*`, `∫₀^{T_*} ‖f_X‖_{M_X} ≤ F_*`),
   `eq:main-derived-l2-curvature` follows:
   `‖R_X‖_{L²(K)} ≤ C_I √(N_* T_*) e^{A_*} (Z_* + F_*) + C_ζ`. -/
theorem supp_curvature_propagation (M M' K L : ℝ → V →L[ℝ] V) (y y' f : ℝ → V)
    (a : ℝ → ℝ)
    (hM : ∀ t, HasDerivAt M (M' t) t) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hf : Continuous f) (ha : Continuous a) (ha0 : ∀ t, 0 ≤ a t)
    (hsymm : ∀ t x z, ⟪M t x, z⟫_ℝ = ⟪x, M t z⟫_ℝ) (hpos : ∀ t x, 0 ≤ ⟪x, M t x⟫_ℝ)
    (hwriter : ∀ t, y' t = (K t + L t) (y t) + f t)
    (hskew : ∀ t x, ⟪M t x, K t x⟫_ℝ = 0)
    (hgrowth : ∀ t x, ⟪x, M' t x⟫_ℝ + 2 * ⟪M t x, L t x⟫_ℝ ≤ 2 * a t * ⟪x, M t x⟫_ℝ) :
    -- (1) `eq:supp-curvature-energy-differential`
    (∀ t, DifferentiableAt ℝ (fun s => gramEnergy M y s ^ 2) t ∧
      (1 / 2) * deriv (fun s => gramEnergy M y s ^ 2) t ≤
        a t * gramEnergy M y t ^ 2 + gramEnergy M y t * gramEnergy M f t) ∧
    -- (2) `eq:main-curvature-energy-propagation`
    (∀ t, 0 ≤ t →
      gramEnergy M y t ≤ Real.exp (∫ s in (0:ℝ)..t, a s) *
        (gramEnergy M y 0 + ∫ s in (0:ℝ)..t,
          Real.exp (-∫ u in (0:ℝ)..s, a u) * gramEnergy M f s)) ∧
    -- (3) `eq:main-derived-l2-curvature` under incidence, lapse and budgets
    (∀ (ρ N : ℝ → ℝ) (T Z A F Nstar CI Cζ RL2 : ℝ),
      0 ≤ T → 0 ≤ CI →
      gramEnergy M y 0 ≤ Z → (∫ s in (0:ℝ)..T, a s) ≤ A →
      (∫ s in (0:ℝ)..T, gramEnergy M f s) ≤ F →
      (∀ t ∈ Set.Icc 0 T, 0 ≤ ρ t ∧ ρ t ≤ CI * gramEnergy M y t) →
      (∀ t ∈ Set.Icc 0 T, 0 ≤ N t ∧ N t ≤ Nstar) →
      IntervalIntegrable (fun t => N t * ρ t ^ 2) volume 0 T →
      RL2 ≤ Real.sqrt (∫ t in (0:ℝ)..T, N t * ρ t ^ 2) + Cζ →
      RL2 ≤ CI * Real.sqrt (Nstar * T) * Real.exp A * (Z + F) + Cζ) := by
  refine ⟨fun t => supp_curvature_energy_differential (hM t) (hy t) (hsymm t) hpos
    (hwriter t) (hskew t) (hgrowth t), fun t ht => ?_, ?_⟩
  · exact curvature_energy_propagation M M' K L y y' f a hM hy hf ha ha0 hsymm hpos
      hwriter hskew hgrowth ht
  · intro ρ N T Z A F Nstar CI Cζ RL2 hT hCI hZ hA hF hρ hN hint hR
    have hunif := curvature_energy_uniform_bound M M' K L y y' f a hM hy hf ha ha0 hsymm
      hpos hwriter hskew hgrowth hT hZ hA hF
    have hZ0 : 0 ≤ gramEnergy M y 0 := Real.sqrt_nonneg _
    have hF0 : 0 ≤ ∫ s in (0:ℝ)..T, gramEnergy M f s :=
      intervalIntegral.integral_nonneg hT fun s _ => Real.sqrt_nonneg _
    have hB : 0 ≤ Real.exp A * (Z + F) := by
      have : 0 ≤ Z + F := by linarith
      positivity
    have := derived_l2_curvature_bound (gramEnergy M y) ρ N hT hCI hB hunif
      (fun t _ => Real.sqrt_nonneg _) hρ hN hint hR
    linarith [this]

end RenewalGeometry
