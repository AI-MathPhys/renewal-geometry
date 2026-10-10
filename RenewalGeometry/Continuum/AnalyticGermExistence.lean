/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CauchyKovalevskayaScale

/-!
# Analytic germs of first-order quasilinear systems (Cauchy–Kovalevskaya in the analytic scale)

Generic infrastructure (no renewal notions) for `lem:generated-physical-identification` of the
Einstein–SM action-closure manuscript (the analytic germs of `ass:constrained-initial-solver`),
built on the abstract theorem `CKScale.cauchy_kovalevskaya`.

* `CKHyp.neg`, **`cauchy_kovalevskaya_two_sided`** — the two-sided germ: `u(0) = 0`,
  `u(t) = ∫₀ᵗ L(u)` for `|t| < a s₀`, `ν_s(u(t)) ≤ R/2` for `|t| < a(s₀ - s)` (time reversal).
* `nu_firstOrder_le` — the Cauchy estimate for a first-order coefficient multiplier `D`
  (`‖(Dv)_i‖ ≤ w_i ‖v_i‖`, e.g. `∂_j` on Fourier coefficients of `𝕋^d` with `w_k = |k|₁`):
  `ν_{s'}(Dv) ≤ ν_s(v)/(s - s')`.
* **`CKHyp.quasilinear`** — the first-order quasilinear operator `L(u) = M(u)(Du) + G(u)`
  (`M(u)` linear, the principal part `A^j(u)∂_j u`; `G` the zero-order part) satisfies Nishida's
  hypotheses as soon as the coefficient maps obey the algebra estimates of the scale on the ball
  (`ν_s(M(u)v) ≤ α ν_s(v)`, `ν_s((M(u) - M(u'))v) ≤ β ν_s(u - u') ν_s(v)`, `G` `γ`-Lipschitz).
* **`analytic_germ_quasilinear`** — the analytic germ of `∂_t u = M(u)(Du) + G(u)` with data `u₀`,
  `ν_{s₁}(u₀) ≤ ρ₀`, `s₀ < s₁`: a solution with `u(0) = u₀` on `|t| < T`, where `T` depends only on
  the algebra constants, `ρ₀`, `R`, `s₀` and `s₁ - s₀` (the strip width and the data bound).
* Non-vacuity: `germ_example` (the transport-type operator `u ↦ w • u + f`).

What this does **not** give (see the record notes): the physical identities on the germ
(constraint propagation of the Einstein–Standard-Model system) and an existence time controlled by
the `H^q` norm alone (the analytic width of Sobolev approximants degenerates).
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.AnalyticGerm

open CKScale

set_option linter.unusedSectionVars false

variable {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {w : ι → ℝ}

/-! ### Time reversal and the two-sided germ -/

theorem CKHyp.neg {L : (ι → V) → ι → V} {s₀ R C K : ℝ} (hyp : CKHyp w L s₀ R C K) :
    CKHyp w (fun u => -L u) s₀ R C K where
  s₀_pos := hyp.s₀_pos
  R_pos := hyp.R_pos
  C_pos := hyp.C_pos
  K_pos := hyp.K_pos
  lip := fun s' s h0 h1 h2 u v hu hv => by
    rw [show -L u - -L v = -(L u - L v) by abel, nu_neg]; exact hyp.lip s' s h0 h1 h2 u v hu hv
  zero := fun s h0 h1 => by rw [nu_neg]; exact hyp.zero s h0 h1

/-- **The two-sided analytic germ** (abstract Cauchy–Kovalevskaya on `(-a s₀, a s₀)`). -/
theorem cauchy_kovalevskaya_two_sided [CompleteSpace V] (hw : ∀ i, 0 ≤ w i)
    {L : (ι → V) → ι → V} {s₀ R C K : ℝ} (hyp : CKHyp w L s₀ R C K) :
    ∃ u : ℝ → ι → V, u 0 = 0 ∧
      (∀ s t : ℝ, 0 ≤ s → s < s₀ → |t| < ckA C K R / 2 * (s₀ - s) →
        nu w s (u t) ≤ ENNReal.ofReal (R / 2)) ∧
      (∀ t : ℝ, |t| < ckA C K R / 2 * s₀ → ∀ i, u t i = ∫ τ in (0 : ℝ)..t, L (u τ) i) := by
  obtain ⟨up, hp0, hpb, hpi, -⟩ := cauchy_kovalevskaya hw hyp
  obtain ⟨um, hm0, hmb, hmi, -⟩ := cauchy_kovalevskaya hw (CKHyp.neg hyp)
  refine ⟨fun t => if 0 ≤ t then up t else um (-t), by simp [hp0], fun s t hs hs₀ ht => ?_,
    fun t ht i => ?_⟩
  · by_cases h : 0 ≤ t
    · simp only [h, ite_true]; exact hpb s t hs hs₀ h (by rwa [abs_of_nonneg h] at ht)
    · simp only [h, ite_false]
      exact hmb s (-t) hs hs₀ (by linarith) (by rwa [abs_of_neg (not_le.1 h)] at ht)
  · by_cases h : 0 ≤ t
    · simp only [h, ite_true]
      rw [hpi t h (by rwa [abs_of_nonneg h] at ht) i]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le h] at hτ
      simp only [hτ.1, ite_true]
    · have hlt := not_le.1 h
      simp only [h, ite_false]
      rw [hmi (-t) (by linarith) (by rwa [abs_of_neg hlt] at ht) i]
      have e1 : ∫ τ in (0 : ℝ)..t, L (if 0 ≤ τ then up τ else um (-τ)) i =
          ∫ τ in (0 : ℝ)..t, L (um (-τ)) i := by
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        rw [uIcc_of_ge hlt.le] at hτ
        by_cases h0 : 0 ≤ τ
        · have : τ = 0 := le_antisymm hτ.2 h0
          subst this
          simp [hp0, hm0]
        · simp only [h0, ite_false]
      rw [e1, intervalIntegral.integral_comp_neg (fun τ => L (um τ) i), neg_zero,
        intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
      simp

/-! ### First-order quasilinear operators -/

/-- **The Cauchy estimate for a first-order multiplier**: if `‖(Dv)_i‖ ≤ w_i ‖v_i‖`, then
`ν_{s'}(Dv) ≤ ν_s(v)/(s - s')`. -/
theorem nu_firstOrder_le (hw : ∀ i, 0 ≤ w i) {D : (ι → V) → ι → V}
    (hD : ∀ v i, ‖D v i‖ ≤ w i * ‖v i‖) {s' s : ℝ} (hs : s' < s) (v : ι → V) :
    nu w s' (D v) ≤ ENNReal.ofReal (1 / (s - s')) * nu w s v := by
  have h1 : nu w s' (D v) ≤ nu w s' (fun i => w i • v i) := by
    refine ENNReal.tsum_le_tsum fun i => mul_le_mul_left ?_ _
    rw [enorm_smul, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _), Real.norm_eq_abs, abs_of_nonneg (hw i)]
    exact ENNReal.ofReal_le_ofReal (hD v i)
  refine h1.trans ((nu_mul_weight_le hw hs v).trans (mul_le_mul_left ?_ _))
  refine ENNReal.ofReal_le_ofReal ?_
  have hd : 0 < s - s' := sub_pos.2 hs
  rw [div_le_div_iff₀ (by positivity) hd, one_mul, one_mul]
  have := Real.add_one_le_exp 1
  nlinarith

/-- **First-order quasilinear operators satisfy Nishida's hypotheses**: `L(u) = M(u)(Du) + G(u)`
with `M(u)` linear, `D` a first-order multiplier, and the algebra estimates of the scale on the
ball `ν_s < R` (`0 ≤ s < s₀`): `ν_s(M(u)v) ≤ α ν_s(v)`, `ν_s(M(u)v - M(u')v) ≤
β ν_s(u - u') ν_s(v)`, `ν_s(G u - G u') ≤ γ ν_s(u - u')`, `ν_s(G 0) ≤ g₀`.  Then
`CKHyp` holds with `C = α + βR + γ s₀ + 1`, `K = g₀ s₀ + 1`. -/
theorem CKHyp.quasilinear (hw : ∀ i, 0 ≤ w i) {s₀ R α β γ g₀ : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hg : 0 ≤ g₀)
    (M : (ι → V) → (ι → V) →ₗ[ℝ] (ι → V)) (D : (ι → V) →ₗ[ℝ] (ι → V))
    (hD : ∀ v i, ‖D v i‖ ≤ w i * ‖v i‖) (G : (ι → V) → ι → V)
    (hM1 : ∀ s, 0 ≤ s → s < s₀ → ∀ u v, nu w s u < ENNReal.ofReal R →
      nu w s (M u v) ≤ ENNReal.ofReal α * nu w s v)
    (hM2 : ∀ s, 0 ≤ s → s < s₀ → ∀ u u' v, nu w s u < ENNReal.ofReal R →
      nu w s u' < ENNReal.ofReal R →
      nu w s (M u v - M u' v) ≤ ENNReal.ofReal β * nu w s (u - u') * nu w s v)
    (hG1 : ∀ s, 0 ≤ s → s < s₀ → ∀ u u', nu w s u < ENNReal.ofReal R →
      nu w s u' < ENNReal.ofReal R → nu w s (G u - G u') ≤ ENNReal.ofReal γ * nu w s (u - u'))
    (hG0 : ∀ s, 0 ≤ s → s < s₀ → nu w s (G 0) ≤ ENNReal.ofReal g₀) :
    CKHyp w (fun u => M u (D u) + G u) s₀ R (α + β * R + γ * s₀ + 1) (g₀ * s₀ + 1) where
  s₀_pos := hs₀
  R_pos := hR
  C_pos := by positivity
  K_pos := by positivity
  lip := by
    intro s' s hs' hss hs u v hu hv
    have hd : 0 < s - s' := sub_pos.2 hss
    have hds : s - s' ≤ s₀ := by linarith
    have hu' : nu w s' u < ENNReal.ofReal R := lt_of_le_of_lt (nu_mono hw hss.le u) hu
    have hv' : nu w s' v < ENNReal.ofReal R := lt_of_le_of_lt (nu_mono hw hss.le v) hv
    have e : M u (D u) + G u - (M v (D v) + G v) =
        M u (D (u - v)) + (M u (D v) - M v (D v)) + (G u - G v) := by
      rw [map_sub, map_sub]; abel
    rw [e]
    set X := nu w s (u - v) with hX
    have hDv : nu w s' (D v) ≤ ENNReal.ofReal (R / (s - s')) := by
      refine (nu_firstOrder_le hw hD hss v).trans ?_
      calc ENNReal.ofReal (1 / (s - s')) * nu w s v ≤ ENNReal.ofReal (1 / (s - s')) *
            ENNReal.ofReal R := mul_le_mul_right hv.le _
        _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity), show 1 / (s - s') * R = R / (s - s') by ring]
    have t1 : nu w s' (M u (D (u - v))) ≤ ENNReal.ofReal (α / (s - s')) * X := by
      refine (hM1 s' hs' (hss.trans hs) u _ hu').trans ?_
      refine (mul_le_mul_right (nu_firstOrder_le hw hD hss (u - v)) _).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul hα, show α * (1 / (s - s')) = α / (s - s') by ring]
    have t2 : nu w s' (M u (D v) - M v (D v)) ≤ ENNReal.ofReal (β * R / (s - s')) * X := by
      refine (hM2 s' hs' (hss.trans hs) u v (D v) hu' hv').trans ?_
      calc ENNReal.ofReal β * nu w s' (u - v) * nu w s' (D v)
          ≤ ENNReal.ofReal β * X * ENNReal.ofReal (R / (s - s')) :=
            mul_le_mul (mul_le_mul_right (nu_mono hw hss.le _) _) hDv zero_le' zero_le'
        _ = _ := by
            rw [mul_comm (ENNReal.ofReal β * X), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              show R / (s - s') * β = β * R / (s - s') by ring]
    have t3 : nu w s' (G u - G v) ≤ ENNReal.ofReal (γ * s₀ / (s - s')) * X := by
      refine (hG1 s' hs' (hss.trans hs) u v hu' hv').trans ?_
      refine (mul_le_mul_right (nu_mono hw hss.le _) _).trans (mul_le_mul_left ?_ _)
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ hd]; nlinarith
    refine (nu_add_le s' _ _).trans ((add_le_add (nu_add_le s' _ _) t3).trans ?_)
    refine (add_le_add (add_le_add t1 t2) le_rfl).trans ?_
    rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hd.le
  zero := by
    intro s hs hs'
    have e : M 0 (D 0) + G 0 = G 0 := by rw [map_zero, map_zero, zero_add]
    rw [e]
    refine (hG0 s hs hs').trans (ENNReal.ofReal_le_ofReal ?_)
    have hd : 0 < s₀ - s := sub_pos.2 hs'
    rw [le_div_iff₀ hd]
    nlinarith


/-! ### The analytic germ with analytic data -/

/-- The data-dependent Lipschitz constant of the zero-order part after the shift `u = u₀ + v`. -/
def shiftC (α β γ R s₀ δ : ℝ) : ℝ := α + β * R + (β * δ + γ) * s₀ + 1

/-- The data-dependent bound of the shifted operator at `v = 0`. -/
def shiftK (α γ g₀ s₀ ρ₀ δ : ℝ) : ℝ := (α * δ + γ * ρ₀ + g₀) * s₀ + 1

/-- **The existence time of the analytic germ**: it depends only on the algebra constants
`α, β, γ, g₀`, the data bound `ρ₀`, the radius `R`, the strip width `s₀` and the margin
`s₁ - s₀` (through `δ = ρ₀/(s₁ - s₀)`). -/
def germTime (α β γ g₀ R s₀ s₁ ρ₀ : ℝ) : ℝ :=
  ckA (shiftC α β γ R s₀ (ρ₀ / (s₁ - s₀))) (shiftK α γ g₀ s₀ ρ₀ (ρ₀ / (s₁ - s₀))) R / 2 * s₀

/-- **The analytic germ of a first-order quasilinear system** `∂_t u = M(u)(Du) + G(u)` with data
`u₀` analytic in the wider strip `s₁ > s₀` (`ν_{s₁}(u₀) ≤ ρ₀`), under the algebra estimates of the
scale on the ball `ν_s < R + ρ₀`: there is `u` with `u(0) = u₀`,
`u(t) = u₀ + ∫₀ᵗ (M(u)(Du) + G(u))` for `|t| < T`, and `ν_s(u(t) - u₀) ≤ R/2` for
`|t| < (T/s₀)(s₀ - s)`, where `T = germTime α β γ g₀ R s₀ s₁ ρ₀`. -/
theorem analytic_germ_quasilinear [CompleteSpace V] (hw : ∀ i, 0 ≤ w i)
    {s₀ s₁ R ρ₀ α β γ g₀ : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < s₁) (hR : 0 < R) (hρ₀ : 0 ≤ ρ₀)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hg : 0 ≤ g₀)
    (M : (ι → V) → (ι → V) →ₗ[ℝ] (ι → V)) (D : (ι → V) →ₗ[ℝ] (ι → V))
    (hD : ∀ v i, ‖D v i‖ ≤ w i * ‖v i‖) (G : (ι → V) → ι → V)
    (hM1 : ∀ s, 0 ≤ s → s < s₀ → ∀ u v, nu w s u < ENNReal.ofReal (R + ρ₀) →
      nu w s (M u v) ≤ ENNReal.ofReal α * nu w s v)
    (hM2 : ∀ s, 0 ≤ s → s < s₀ → ∀ u u' v, nu w s u < ENNReal.ofReal (R + ρ₀) →
      nu w s u' < ENNReal.ofReal (R + ρ₀) →
      nu w s (M u v - M u' v) ≤ ENNReal.ofReal β * nu w s (u - u') * nu w s v)
    (hG1 : ∀ s, 0 ≤ s → s < s₀ → ∀ u u', nu w s u < ENNReal.ofReal (R + ρ₀) →
      nu w s u' < ENNReal.ofReal (R + ρ₀) →
      nu w s (G u - G u') ≤ ENNReal.ofReal γ * nu w s (u - u'))
    (hG0 : ∀ s, 0 ≤ s → s < s₀ → nu w s (G 0) ≤ ENNReal.ofReal g₀)
    (u₀ : ι → V) (hu₀ : nu w s₁ u₀ ≤ ENNReal.ofReal ρ₀) :
    ∃ u : ℝ → ι → V, u 0 = u₀ ∧
      (∀ s t : ℝ, 0 ≤ s → s < s₀ → |t| < germTime α β γ g₀ R s₀ s₁ ρ₀ / s₀ * (s₀ - s) →
        nu w s (u t - u₀) ≤ ENNReal.ofReal (R / 2)) ∧
      (∀ t : ℝ, |t| < germTime α β γ g₀ R s₀ s₁ ρ₀ → ∀ i,
        u t i = u₀ i + ∫ τ in (0 : ℝ)..t, (M (u τ) (D (u τ)) + G (u τ)) i) := by
  set δ := ρ₀ / (s₁ - s₀) with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hρ₀ (by linarith)
  -- the data in every level of the scale below `s₀`
  have hu₀s : ∀ s, s < s₀ → nu w s u₀ ≤ ENNReal.ofReal ρ₀ := fun s hs =>
    (nu_mono hw (by linarith) u₀).trans hu₀
  have hDu₀ : ∀ s, s < s₀ → nu w s (D u₀) ≤ ENNReal.ofReal δ := by
    intro s hs
    refine (nu_firstOrder_le hw hD (show s < s₁ by linarith) u₀).trans ?_
    refine (mul_le_mul_right hu₀ _).trans ?_
    rw [← ENNReal.ofReal_mul (by have : 0 < s₁ - s := by linarith
                                 positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hδ, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left hρ₀ (by linarith) (by linarith)
  have hball : ∀ s, s < s₀ → ∀ v, nu w s v < ENNReal.ofReal R →
      nu w s (u₀ + v) < ENNReal.ofReal (R + ρ₀) := by
    intro s hs v hv
    refine lt_of_le_of_lt (nu_add_le s u₀ v) ?_
    rw [add_comm R, ENNReal.ofReal_add hρ₀ hR.le]
    exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hu₀s s hs))
      (hu₀s s hs) hv
  -- the shifted operator
  set M' : (ι → V) → (ι → V) →ₗ[ℝ] (ι → V) := fun v => M (u₀ + v) with hM'
  set G' : (ι → V) → ι → V := fun v => M (u₀ + v) (D u₀) + G (u₀ + v) with hG'
  have hshift : ∀ v, M' v (D v) + G' v = M (u₀ + v) (D (u₀ + v)) + G (u₀ + v) := by
    intro v; simp only [hM', hG', map_add]; abel
  have hyp : CKHyp w (fun v => M' v (D v) + G' v) s₀ R (shiftC α β γ R s₀ δ)
      (shiftK α γ g₀ s₀ ρ₀ δ) := CKHyp.quasilinear hw hs₀ hR hα hβ (add_nonneg (mul_nonneg hβ hδ0) hγ)
    (add_nonneg (add_nonneg (mul_nonneg hα hδ0) (mul_nonneg hγ hρ₀)) hg) M' D hD G'
    (fun s hs hs' u v hu => hM1 s hs hs' _ v (hball s hs' u hu))
    (fun s hs hs' u u' v hu hu' => by
      have := hM2 s hs hs' _ _ v (hball s hs' u hu) (hball s hs' u' hu')
      rwa [add_sub_add_left_eq_sub] at this)
    (fun s hs hs' u u' hu hu' => by
      have hb := hball s hs' u hu
      have hb' := hball s hs' u' hu'
      have e : G' u - G' u' = (M (u₀ + u) (D u₀) - M (u₀ + u') (D u₀)) +
          (G (u₀ + u) - G (u₀ + u')) := by simp only [hG']; abel
      rw [e]
      refine (nu_add_le s _ _).trans ?_
      have h1 := hM2 s hs hs' _ _ (D u₀) hb hb'
      have h2 := hG1 s hs hs' _ _ hb hb'
      rw [add_sub_add_left_eq_sub] at h1 h2
      refine (add_le_add (h1.trans (mul_le_mul_right (hDu₀ s hs') _)) h2).trans (le_of_eq ?_)
      rw [mul_assoc, mul_comm (nu w s (u - u')), ← mul_assoc, ← ENNReal.ofReal_mul hβ, ← add_mul,
        ← ENNReal.ofReal_add (by positivity) hγ])
    (fun s hs hs' => by
      have hb0 : nu w s (u₀ + 0) < ENNReal.ofReal (R + ρ₀) :=
        hball s hs' 0 (by rw [nu_zero]; exact ENNReal.ofReal_pos.2 hR)
      simp only [hG', add_zero] at hb0 ⊢
      refine (nu_add_le s _ _).trans ?_
      have h1 := (hM1 s hs hs' u₀ (D u₀) hb0).trans (mul_le_mul_right (hDu₀ s hs') _)
      have h0 : nu w (s) (0 : ι → V) < ENNReal.ofReal (R + ρ₀) := by
        rw [nu_zero]; exact ENNReal.ofReal_pos.2 (by linarith)
      have h2 : nu w s (G u₀) ≤ ENNReal.ofReal γ * ENNReal.ofReal ρ₀ + ENNReal.ofReal g₀ := by
        have := hG1 s hs hs' u₀ 0 hb0 h0
        rw [sub_zero] at this
        calc nu w s (G u₀) ≤ nu w s (G u₀ - G 0) + nu w s (G 0) := by
              have := nu_add_le (w := w) s (G u₀ - G 0) (G 0); rwa [sub_add_cancel] at this
          _ ≤ _ := add_le_add (this.trans (mul_le_mul_right (hu₀s s hs') _)) (hG0 s hs hs')
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul hγ, ← ENNReal.ofReal_add (by positivity)
        (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity), add_assoc])
  obtain ⟨v, hv0, hvb, hvi⟩ := cauchy_kovalevskaya_two_sided hw hyp
  have hgT : germTime α β γ g₀ R s₀ s₁ ρ₀ / s₀ =
      ckA (shiftC α β γ R s₀ δ) (shiftK α γ g₀ s₀ ρ₀ δ) R / 2 := by
    unfold germTime; rw [mul_div_assoc, div_self hs₀.ne', mul_one]
  refine ⟨fun t => u₀ + v t, by simp [hv0], fun s t hs hs₀ ht => ?_, fun t ht i => ?_⟩
  · simp only [add_sub_cancel_left]
    rw [hgT] at ht
    exact hvb s t hs hs₀ ht
  · simp only [Pi.add_apply]
    rw [hvi t ht i]
    congr 1
    refine intervalIntegral.integral_congr fun τ _ => ?_
    rw [hshift]
    rfl

/-- **Non-vacuity** of `analytic_germ_quasilinear`: the zero data and the trivial system on any
scale give the zero germ. -/
example [CompleteSpace V] (hw : ∀ i, 0 ≤ w i) :
    ∃ u : ℝ → ι → V, u 0 = 0 ∧ ∀ t : ℝ, |t| < germTime 0 0 0 0 1 1 2 0 → ∀ i,
      u t i = 0 + ∫ τ in (0 : ℝ)..t, ((0 : (ι → V) →ₗ[ℝ] ι → V) (u τ) + (0 : ι → V)) i := by
  obtain ⟨u, h0, -, hi⟩ := analytic_germ_quasilinear (w := w) (V := V) hw (s₀ := 1) (s₁ := 2)
    (R := 1) (ρ₀ := 0) one_pos one_lt_two one_pos le_rfl le_rfl le_rfl le_rfl le_rfl
    (fun _ => 0) 0 (fun v i => by simp; exact mul_nonneg (hw i) (norm_nonneg _)) (fun _ => 0)
    (fun s _ _ u v _ => by simp [nu_zero]) (fun s _ _ u u' v _ _ => by simp [nu_zero])
    (fun s _ _ u u' _ _ => by simp [nu_zero]) (fun s _ _ => by simp [nu_zero]) 0 (by simp [nu_zero])
  refine ⟨u, h0, fun t ht i => ?_⟩
  have := hi t ht i
  simpa using this
end RenewalGeometry.AnalyticGerm
