/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.StationaryHomogeneousRenewalRates

/-!
# Vacuum Friedmann equations in renewal coordinates
  (`thm:main-homogeneous-friedmann`, `eq:main-renewal-rate-action`,
  `eq:main-renewal-euler`, `eq:main-vacuum-friedmann`;
  `cor:main-derived-desitter-rates`; emergent-spacetime manuscript)

The reduced homogeneous action `eq:main-homogeneous-action-an` has Lagrangian
`L[a,N] = -6 a a'^2 / N - 2 Λ N a^3` (`homogeneousLagrangian`).  Under the
isotropic renewal map `eq:main-isotropic-renewal-map`
(`ϱ = a^3`, `κ = N^2 / a^2`, so `a = ϱ^{1/3}`, `N = ϱ^{1/3} κ^{1/2}`) it
becomes the boxed renewal-rate Lagrangian
`-(2 ϱ'^2)/(3 ϱ^{4/3} √κ) - 2 Λ ϱ^{4/3} √κ` (`renewalRateLagrangian`,
`renewalRateLagrangian_eq_homogeneous`).

With `u = log κ`, `v = log ϱ` the Lagrangian is `logRenewalLagrangian`, and the
Euler expressions `E_u = ∂L/∂u - d/dt ∂L/∂u'`, `E_v = ∂L/∂v - d/dt ∂L/∂v'`
(`eulerU`, `eulerV`; partial derivatives are Mathlib `deriv`s of the
one-variable sections, the time derivative of the momentum is again `deriv`)
are shown to equal the boxed `eq:main-renewal-euler`
`E_u = N a^3 (3 𝓗^2 - Λ)`,
`E_v = N a^3 [4 D_τ 𝓗 + (8/3)(3 𝓗^2 - Λ)]` with `𝓗 = a'/(N a)` and
`D_τ = N⁻¹ d/dt` (`eulerU_eq`, `eulerV_eq`).  Consequently stationarity in
the two renewal variables is equivalent to the vacuum Friedmann system
`3 𝓗^2 = Λ`, `D_τ 𝓗 = 0` (`renewal_stationary_iff_friedmann`,
`eq:main-vacuum-friedmann`).

The Euler expressions are the standard Euler–Lagrange expressions; the
identification `δS = ∫ (E_u δu + E_v δv) dt` for endpoint-fixed variations is
the usual integration by parts of the pointwise first-variation identity
`firstVariation_integrand_eq` (whose exact term `d/dt (p_v δv)` integrates to
zero under `δv(t₀) = δv(t₁) = 0`, `momentum_boundary_term_integral_eq_zero`).

Finally, `cor:main-derived-desitter-rates` is discharged from the theorem:
`IsStationaryRenewalSolution` is a positive connected stationary solution of
the renewal-rate action in the literal sense `E_u = E_v = 0` (with
`u = log (N^2/a^2)`, `v = log a^3`); it implies the Friedmann-constraint
interface `IsStationaryHomogeneousSolution` of
`Gravity/StationaryHomogeneousRenewalRates.lean`
(`IsStationaryRenewalSolution.toStationaryHomogeneousSolution`), hence the
flat / de Sitter profile classification and the boxed regulator rates
(`derived_desitter_rates`).

Scoped hypotheses made explicit: the paths are pointwise differentiable
(`u`, `v` once and `v'` once at the evaluation time) for the Euler expression
formulas; for the corollary, the time set is open and connected, `a`, `N`
positive, `a`, `τ` differentiable with continuous derivative data, exactly as
in the manuscript's smooth homogeneous ansatz.
-/

open scoped BigOperators

namespace RenewalGeometry

/-! ### Lagrangians -/

/-- Reduced homogeneous Lagrangian `-6 a a'^2 / N - 2 Λ N a^3` of
`eq:main-homogeneous-action-an`. -/
noncomputable def homogeneousLagrangian (Λ a a' N : ℝ) : ℝ :=
  -(6 * a * a' ^ 2 / N) - 2 * Λ * N * a ^ 3

/-- Boxed renewal-rate Lagrangian
`-(2 ϱ'^2)/(3 ϱ^{4/3} √κ) - 2 Λ ϱ^{4/3} √κ` of `eq:main-renewal-rate-action`. -/
noncomputable def renewalRateLagrangian (Λ κ ϱ ϱ' : ℝ) : ℝ :=
  -(2 * ϱ' ^ 2 / (3 * ϱ ^ ((4 : ℝ) / 3) * Real.sqrt κ)) -
    2 * Λ * ϱ ^ ((4 : ℝ) / 3) * Real.sqrt κ

/-- `eq:main-renewal-rate-action`: under `ϱ = a^3`, `κ = N^2/a^2`
(so `ϱ' = 3 a^2 a'`) the renewal-rate Lagrangian is the reduced homogeneous
Lagrangian of `eq:main-homogeneous-action-an`. -/
theorem renewalRateLagrangian_eq_homogeneous (Λ a a' N : ℝ) (ha : 0 < a)
    (hN : 0 < N) :
    renewalRateLagrangian Λ (N ^ 2 / a ^ 2) (a ^ 3) (3 * a ^ 2 * a') =
      homogeneousLagrangian Λ a a' N := by
  have h1 : (a ^ 3 : ℝ) ^ ((4 : ℝ) / 3) = a ^ 4 := by
    rw [← Real.rpow_natCast a 3, ← Real.rpow_mul ha.le,
      show ((3 : ℕ) : ℝ) * ((4 : ℝ) / 3) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have h2 : Real.sqrt (N ^ 2 / a ^ 2) = N / a := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hN.le, Real.sqrt_sq ha.le]
  rw [renewalRateLagrangian, homogeneousLagrangian, h1, h2]
  field_simp
  ring

/-- The renewal-rate Lagrangian in the logarithmic variables `u = log κ`,
`v = log ϱ` (so `ϱ' = e^v v'`); it does not depend on `u'`. -/
noncomputable def logRenewalLagrangian (Λ u u' v v' : ℝ) : ℝ :=
  renewalRateLagrangian Λ (Real.exp u) (Real.exp v) (Real.exp v * v')

theorem exp_four_thirds (v : ℝ) :
    Real.exp (4 * v / 3) = Real.exp (v / 3) ^ 4 := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem exp_two_thirds_sub_half (u v : ℝ) :
    Real.exp (2 * v / 3 - u / 2) = Real.exp (v / 3) ^ 2 / Real.exp (u / 2) := by
  rw [Real.exp_sub, ← Real.exp_nat_mul]; congr 2; push_cast; ring

theorem exp_four_thirds_add_half (u v : ℝ) :
    Real.exp (4 * v / 3 + u / 2) = Real.exp (v / 3) ^ 4 * Real.exp (u / 2) := by
  rw [Real.exp_add, exp_four_thirds]

theorem exp_half_add_third (u v : ℝ) :
    Real.exp (u / 2 + v / 3) = Real.exp (u / 2) * Real.exp (v / 3) := Real.exp_add _ _

/-- Explicit form of the logarithmic Lagrangian:
`L = -(2/3) e^{2v/3 - u/2} v'^2 - 2 Λ e^{4v/3 + u/2}`. -/
theorem logRenewalLagrangian_eq (Λ u u' v v' : ℝ) :
    logRenewalLagrangian Λ u u' v v' =
      -(2 / 3) * Real.exp (2 * v / 3 - u / 2) * v' ^ 2 -
        2 * Λ * Real.exp (4 * v / 3 + u / 2) := by
  unfold logRenewalLagrangian renewalRateLagrangian
  have h1 : Real.exp v ^ ((4 : ℝ) / 3) = Real.exp (4 * v / 3) := by
    rw [← Real.exp_mul]; ring_nf
  have h2 : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos u).le (Real.exp_pos _).le,
      ← Real.exp_add]
    ring_nf
  have hv : Real.exp v = Real.exp (v / 3) ^ 3 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h1, h2, exp_four_thirds, exp_two_thirds_sub_half, exp_four_thirds_add_half, hv]
  have he : 0 < Real.exp (v / 3) := Real.exp_pos _
  have hf : 0 < Real.exp (u / 2) := Real.exp_pos _
  field_simp

/-! ### Euler expressions -/

/-- Euler expression `E_u = ∂L/∂u - d/dt ∂L/∂u'` of the logarithmic
renewal-rate Lagrangian along the path `(u, u', v, v')`. -/
noncomputable def eulerU (Λ : ℝ) (u u' v v' : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun x => logRenewalLagrangian Λ x (u' t) (v t) (v' t)) (u t) -
    deriv (fun s => deriv (fun y => logRenewalLagrangian Λ (u s) y (v s) (v' s)) (u' s)) t

/-- Euler expression `E_v = ∂L/∂v - d/dt ∂L/∂v'` of the logarithmic
renewal-rate Lagrangian along the path `(u, u', v, v')`. -/
noncomputable def eulerV (Λ : ℝ) (u u' v v' : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun x => logRenewalLagrangian Λ (u t) (u' t) x (v' t)) (v t) -
    deriv (fun s => deriv (fun y => logRenewalLagrangian Λ (u s) (u' s) (v s) y) (v' s)) t

/-- Scale factor `a = ϱ^{1/3} = e^{v/3}` of `eq:main-isotropic-renewal-map`. -/
noncomputable def renewalScaleFactor (v : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (v t / 3)

/-- Lapse `N = ϱ^{1/3} κ^{1/2} = e^{u/2 + v/3}` of `eq:main-isotropic-renewal-map`. -/
noncomputable def renewalLapse (u v : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (u t / 2 + v t / 3)

/-- Time derivative `a' = e^{v/3} v'/3` of the scale factor. -/
noncomputable def renewalScaleFactorDeriv (v v' : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (v t / 3) * v' t / 3

/-- Hubble rate `𝓗 = a'/(N a)`. -/
noncomputable def hubbleRate (a a' N : ℝ → ℝ) (t : ℝ) : ℝ := a' t / (N t * a t)

/-- Proper-time derivative `D_τ f = N⁻¹ df/dt`. -/
noncomputable def properTimeDeriv (N f : ℝ → ℝ) (t : ℝ) : ℝ := (N t)⁻¹ * deriv f t

theorem hasDerivAt_renewalScaleFactor {v v' : ℝ → ℝ} {t : ℝ}
    (hv : HasDerivAt v (v' t) t) :
    HasDerivAt (renewalScaleFactor v) (renewalScaleFactorDeriv v v' t) t := by
  have := (hv.div_const 3).exp
  unfold renewalScaleFactor renewalScaleFactorDeriv
  exact this.congr_deriv (by ring)

/-- The Hubble rate of the renewal variables is `v'/(3N)`. -/
theorem hubbleRate_renewal_eq (u v v' : ℝ → ℝ) :
    hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v') (renewalLapse u v) =
      fun t => v' t / (3 * renewalLapse u v t) := by
  funext t
  unfold hubbleRate renewalScaleFactor renewalScaleFactorDeriv renewalLapse
  have := Real.exp_pos (v t / 3)
  have := Real.exp_pos (u t / 2 + v t / 3)
  field_simp

/-- Partial derivative `∂L/∂u = (1/3) e^{2v/3 - u/2} v'^2 - Λ e^{4v/3 + u/2}`. -/
theorem hasDerivAt_logRenewalLagrangian_u (Λ u u' v v' : ℝ) :
    HasDerivAt (fun x => logRenewalLagrangian Λ x u' v v')
      (1 / 3 * Real.exp (2 * v / 3 - u / 2) * v' ^ 2 -
        Λ * Real.exp (4 * v / 3 + u / 2)) u := by
  have hfun : (fun x => logRenewalLagrangian Λ x u' v v') = fun x =>
      -(2 / 3) * Real.exp (2 * v / 3 - x / 2) * v' ^ 2 -
        2 * Λ * Real.exp (4 * v / 3 + x / 2) :=
    funext fun x => logRenewalLagrangian_eq Λ x u' v v'
  rw [hfun]
  have h1 : HasDerivAt (fun x : ℝ => 2 * v / 3 - x / 2) (0 - 1 / 2) u :=
    (hasDerivAt_const u _).sub ((hasDerivAt_id u).div_const 2)
  have h2 : HasDerivAt (fun x : ℝ => 4 * v / 3 + x / 2) (0 + 1 / 2) u :=
    (hasDerivAt_const u _).add ((hasDerivAt_id u).div_const 2)
  have := ((h1.exp.const_mul (-(2 / 3))).mul_const (v' ^ 2)).sub
    (h2.exp.const_mul (2 * Λ))
  exact this.congr_deriv (by ring)

/-- The Lagrangian does not depend on `u'`: `∂L/∂u' = 0`. -/
theorem hasDerivAt_logRenewalLagrangian_u' (Λ u u' v v' : ℝ) :
    HasDerivAt (fun y => logRenewalLagrangian Λ u y v v') 0 u' := by
  have hfun : (fun y => logRenewalLagrangian Λ u y v v') = fun _ =>
      -(2 / 3) * Real.exp (2 * v / 3 - u / 2) * v' ^ 2 -
        2 * Λ * Real.exp (4 * v / 3 + u / 2) :=
    funext fun y => logRenewalLagrangian_eq Λ u y v v'
  rw [hfun]
  exact hasDerivAt_const _ _

/-- Partial derivative `∂L/∂v = -(4/9) e^{2v/3 - u/2} v'^2 - (8/3) Λ e^{4v/3 + u/2}`. -/
theorem hasDerivAt_logRenewalLagrangian_v (Λ u u' v v' : ℝ) :
    HasDerivAt (fun x => logRenewalLagrangian Λ u u' x v')
      (-(4 / 9) * Real.exp (2 * v / 3 - u / 2) * v' ^ 2 -
        8 / 3 * Λ * Real.exp (4 * v / 3 + u / 2)) v := by
  have hfun : (fun x => logRenewalLagrangian Λ u u' x v') = fun x =>
      -(2 / 3) * Real.exp (2 * x / 3 - u / 2) * v' ^ 2 -
        2 * Λ * Real.exp (4 * x / 3 + u / 2) :=
    funext fun x => logRenewalLagrangian_eq Λ u u' x v'
  rw [hfun]
  have h1 : HasDerivAt (fun x : ℝ => 2 * x / 3 - u / 2) (2 * 1 / 3 - 0) v :=
    (((hasDerivAt_id v).const_mul 2).div_const 3).sub (hasDerivAt_const v _)
  have h2 : HasDerivAt (fun x : ℝ => 4 * x / 3 + u / 2) (4 * 1 / 3 + 0) v :=
    (((hasDerivAt_id v).const_mul 4).div_const 3).add (hasDerivAt_const v _)
  have := ((h1.exp.const_mul (-(2 / 3))).mul_const (v' ^ 2)).sub
    (h2.exp.const_mul (2 * Λ))
  exact this.congr_deriv (by ring)

/-- Momentum `∂L/∂v' = -(4/3) e^{2v/3 - u/2} v'`. -/
theorem hasDerivAt_logRenewalLagrangian_v' (Λ u u' v v' : ℝ) :
    HasDerivAt (fun y => logRenewalLagrangian Λ u u' v y)
      (-(4 / 3) * Real.exp (2 * v / 3 - u / 2) * v') v' := by
  have hfun : (fun y => logRenewalLagrangian Λ u u' v y) = fun y =>
      -(2 / 3) * Real.exp (2 * v / 3 - u / 2) * y ^ 2 -
        2 * Λ * Real.exp (4 * v / 3 + u / 2) :=
    funext fun y => logRenewalLagrangian_eq Λ u u' v y
  rw [hfun]
  have := ((hasDerivAt_pow 2 v').const_mul
    (-(2 / 3) * Real.exp (2 * v / 3 - u / 2))).sub
    (hasDerivAt_const v' (2 * Λ * Real.exp (4 * v / 3 + u / 2)))
  exact this.congr_deriv (by push_cast; ring)

/-- The `v'`-momentum along a path. -/
noncomputable def renewalMomentumV (Λ : ℝ) (u v v' : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(4 / 3) * Real.exp (2 * v s / 3 - u s / 2) * v' s

theorem momentumV_eq (Λ : ℝ) (u u' v v' : ℝ → ℝ) :
    (fun s => deriv (fun y => logRenewalLagrangian Λ (u s) (u' s) (v s) y) (v' s)) =
      renewalMomentumV Λ u v v' := by
  funext s
  exact (hasDerivAt_logRenewalLagrangian_v' Λ (u s) (u' s) (v s) (v' s)).deriv

theorem momentumU_eq (Λ : ℝ) (u u' v v' : ℝ → ℝ) :
    (fun s => deriv (fun y => logRenewalLagrangian Λ (u s) y (v s) (v' s)) (u' s)) =
      fun _ => 0 := by
  funext s
  exact (hasDerivAt_logRenewalLagrangian_u' Λ (u s) (u' s) (v s) (v' s)).deriv

theorem hasDerivAt_renewalMomentumV (Λ : ℝ) {u u' v v' v'' : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (u' t) t) (hv : HasDerivAt v (v' t) t)
    (hv' : HasDerivAt v' (v'' t) t) :
    HasDerivAt (renewalMomentumV Λ u v v')
      (-(4 / 3) * (Real.exp (2 * v t / 3 - u t / 2) * (2 * v' t / 3 - u' t / 2) * v' t +
        Real.exp (2 * v t / 3 - u t / 2) * v'' t)) t := by
  have h1 : HasDerivAt (fun s => 2 * v s / 3 - u s / 2) (2 * v' t / 3 - u' t / 2) t :=
    ((hv.const_mul 2).div_const 3).sub (hu.div_const 2)
  have := (h1.exp.const_mul (-(4 / 3))).mul hv'
  unfold renewalMomentumV
  exact this.congr_deriv (by ring)

/-- `eq:main-renewal-euler`, first box: `E_u = N a^3 (3 𝓗^2 - Λ)` (no
differentiability is needed, since `L` does not depend on `u'`). -/
theorem eulerU_eq (Λ : ℝ) (u u' v v' : ℝ → ℝ) (t : ℝ) :
    eulerU Λ u u' v v' t =
      renewalLapse u v t * renewalScaleFactor v t ^ 3 *
        (3 * hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
          (renewalLapse u v) t ^ 2 - Λ) := by
  unfold eulerU
  rw [momentumU_eq, deriv_const, (hasDerivAt_logRenewalLagrangian_u Λ (u t) (u' t) (v t)
    (v' t)).deriv]
  simp only [hubbleRate_renewal_eq]
  unfold renewalLapse renewalScaleFactor
  simp only [exp_two_thirds_sub_half, exp_four_thirds_add_half, exp_half_add_third]
  have he : 0 < Real.exp (v t / 3) := Real.exp_pos _
  have hf : 0 < Real.exp (u t / 2) := Real.exp_pos _
  field_simp
  ring

/-- `eq:main-renewal-euler`, second box:
`E_v = N a^3 [4 D_τ 𝓗 + (8/3)(3 𝓗^2 - Λ)]`. -/
theorem eulerV_eq (Λ : ℝ) {u u' v v' v'' : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (u' t) t) (hv : HasDerivAt v (v' t) t)
    (hv' : HasDerivAt v' (v'' t) t) :
    eulerV Λ u u' v v' t =
      renewalLapse u v t * renewalScaleFactor v t ^ 3 *
        (4 * properTimeDeriv (renewalLapse u v)
            (hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
              (renewalLapse u v)) t +
          8 / 3 * (3 * hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
            (renewalLapse u v) t ^ 2 - Λ)) := by
  unfold eulerV properTimeDeriv
  rw [momentumV_eq, (hasDerivAt_renewalMomentumV Λ hu hv hv').deriv,
    (hasDerivAt_logRenewalLagrangian_v Λ (u t) (u' t) (v t) (v' t)).deriv]
  simp only [hubbleRate_renewal_eq]
  -- derivative of the Hubble rate `v'/(3N)`
  have hN : HasDerivAt (renewalLapse u v)
      (Real.exp (u t / 2 + v t / 3) * (u' t / 2 + v' t / 3)) t := by
    have := ((hu.div_const 2).add (hv.div_const 3)).exp
    unfold renewalLapse
    exact this
  have hH : HasDerivAt (fun s => v' s / (3 * renewalLapse u v s))
      ((v'' t * (3 * renewalLapse u v t) -
        v' t * (3 * (Real.exp (u t / 2 + v t / 3) * (u' t / 2 + v' t / 3)))) /
        (3 * renewalLapse u v t) ^ 2) t := by
    refine hv'.div (hN.const_mul 3) ?_
    unfold renewalLapse
    positivity
  rw [hH.deriv]
  unfold renewalLapse renewalScaleFactor
  simp only [exp_two_thirds_sub_half, exp_four_thirds_add_half, exp_half_add_third]
  have he : 0 < Real.exp (v t / 3) := Real.exp_pos _
  have hf : 0 < Real.exp (u t / 2) := Real.exp_pos _
  field_simp
  ring

/-- `eq:main-vacuum-friedmann`: stationarity of the renewal-rate action in
the two independent positive renewal variables (`E_u = E_v = 0`) is
equivalent to `3 𝓗^2 = Λ` and `D_τ 𝓗 = 0`. -/
theorem renewal_stationary_iff_friedmann (Λ : ℝ) {u u' v v' v'' : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (u' t) t) (hv : HasDerivAt v (v' t) t)
    (hv' : HasDerivAt v' (v'' t) t) :
    (eulerU Λ u u' v v' t = 0 ∧ eulerV Λ u u' v v' t = 0) ↔
      (3 * hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
          (renewalLapse u v) t ^ 2 = Λ ∧
        properTimeDeriv (renewalLapse u v)
          (hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
            (renewalLapse u v)) t = 0) := by
  rw [eulerU_eq, eulerV_eq Λ hu hv hv']
  have hpos : 0 < renewalLapse u v t * renewalScaleFactor v t ^ 3 := by
    unfold renewalLapse renewalScaleFactor; positivity
  set H := hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v')
    (renewalLapse u v) t
  set D := properTimeDeriv (renewalLapse u v)
    (hubbleRate (renewalScaleFactor v) (renewalScaleFactorDeriv v v') (renewalLapse u v)) t
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : 3 * H ^ 2 - Λ = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hpos.ne'
      · exact h
    refine ⟨by linarith, ?_⟩
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hpos.ne'
    · rw [h1'] at h; linarith
  · rintro ⟨h1, h2⟩
    have h1' : 3 * H ^ 2 - Λ = 0 := by linarith
    exact ⟨by rw [h1', mul_zero], by rw [h1', h2]; ring⟩

/-! ### First-variation identity -/

/-- Pointwise first-variation identity: the derivative of the Lagrangian along
the direction `(δu, δu', δv, δv')` equals `E_u δu + E_v δv + d/dt (p_v δv)`,
where `p_v = ∂L/∂v'` is the momentum.  Integrated over `[t₀, t₁]` with
`δv(t₀) = δv(t₁) = 0` the exact term drops, giving
`δS = ∫ (E_u δu + E_v δv)`. -/
theorem firstVariation_integrand_eq (Λ : ℝ) {u u' v v' v'' δu δu' δv δv' : ℝ → ℝ}
    {t : ℝ} (hu : HasDerivAt u (u' t) t) (hv : HasDerivAt v (v' t) t)
    (hv' : HasDerivAt v' (v'' t) t) (hδv : HasDerivAt δv (δv' t) t) :
    HasDerivAt (fun ε : ℝ => logRenewalLagrangian Λ (u t + ε * δu t) (u' t + ε * δu' t)
        (v t + ε * δv t) (v' t + ε * δv' t))
      (eulerU Λ u u' v v' t * δu t + eulerV Λ u u' v v' t * δv t +
        deriv (fun s => renewalMomentumV Λ u v v' s * δv s) t) 0 := by
  -- the exact term
  have hp := (hasDerivAt_renewalMomentumV Λ hu hv hv').mul hδv
  rw [show deriv (fun s => renewalMomentumV Λ u v v' s * δv s) t = _ from hp.deriv]
  unfold eulerU eulerV
  rw [momentumU_eq, momentumV_eq, deriv_const, (hasDerivAt_renewalMomentumV Λ hu hv hv').deriv,
    (hasDerivAt_logRenewalLagrangian_u Λ (u t) (u' t) (v t) (v' t)).deriv,
    (hasDerivAt_logRenewalLagrangian_v Λ (u t) (u' t) (v t) (v' t)).deriv]
  simp_rw [logRenewalLagrangian_eq]
  have h1 : HasDerivAt (fun ε : ℝ => 2 * (v t + ε * δv t) / 3 - (u t + ε * δu t) / 2)
      (2 * (0 + 1 * δv t) / 3 - (0 + 1 * δu t) / 2) 0 :=
    ((((hasDerivAt_const (0:ℝ) (v t)).add ((hasDerivAt_id (0:ℝ)).mul_const (δv t))).const_mul
      2).div_const 3).sub
      (((hasDerivAt_const (0:ℝ) (u t)).add ((hasDerivAt_id (0:ℝ)).mul_const (δu t))).div_const 2)
  have h2 : HasDerivAt (fun ε : ℝ => 4 * (v t + ε * δv t) / 3 + (u t + ε * δu t) / 2)
      (4 * (0 + 1 * δv t) / 3 + (0 + 1 * δu t) / 2) 0 :=
    ((((hasDerivAt_const (0:ℝ) (v t)).add ((hasDerivAt_id (0:ℝ)).mul_const (δv t))).const_mul
      4).div_const 3).add
      (((hasDerivAt_const (0:ℝ) (u t)).add ((hasDerivAt_id (0:ℝ)).mul_const (δu t))).div_const 2)
  have h3 : HasDerivAt (fun ε : ℝ => (v' t + ε * δv' t) ^ 2)
      (2 * (v' t + 0 * δv' t) ^ 1 * (0 + 1 * δv' t)) 0 :=
    ((hasDerivAt_const (0:ℝ) (v' t)).add ((hasDerivAt_id (0:ℝ)).mul_const (δv' t))).pow 2
  have := ((h1.exp.const_mul (-(2 / 3))).mul h3).sub (h2.exp.const_mul (2 * Λ))
  refine this.congr_deriv ?_
  simp only [renewalMomentumV, zero_mul, zero_add, one_mul, add_zero, pow_one]
  ring

/-- The exact term of the first variation integrates to zero over `[t₀, t₁]`
when the variation `δv` vanishes at the endpoints. -/
theorem momentum_boundary_term_integral_eq_zero (Λ : ℝ) {u u' v v' v'' δv δv' : ℝ → ℝ}
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hu : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt u (u' t) t)
    (hv : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt v (v' t) t)
    (hv' : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt v' (v'' t) t)
    (hδv : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt δv (δv' t) t)
    (hint : IntervalIntegrable (fun s => deriv (fun s => renewalMomentumV Λ u v v' s * δv s) s)
      MeasureTheory.volume t₀ t₁)
    (h₀ : δv t₀ = 0) (h₁ : δv t₁ = 0) :
    ∫ s in t₀..t₁, deriv (fun s => renewalMomentumV Λ u v v' s * δv s) s = 0 := by
  have hderiv : ∀ t ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun s => renewalMomentumV Λ u v v' s * δv s)
        (deriv (fun s => renewalMomentumV Λ u v v' s * δv s) t) t := by
    intro t ht
    exact ((hasDerivAt_renewalMomentumV Λ (hu t ht) (hv t ht) (hv' t ht)).mul
      (hδv t ht)).differentiableAt.hasDerivAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [h₀, h₁]

/-! ### The de Sitter corollary discharged from the theorem -/

/-- `u = log κ = log (N^2/a^2)` along a path. -/
noncomputable def logConductance (a N : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (N t ^ 2 / a t ^ 2)

/-- `v = log ϱ = log a^3` along a path. -/
noncomputable def logDensity (a : ℝ → ℝ) (t : ℝ) : ℝ := Real.log (a t ^ 3)

theorem renewalLapse_log (a N : ℝ → ℝ) {t : ℝ} (ha : 0 < a t) (hN : 0 < N t) :
    renewalLapse (logConductance a N) (logDensity a) t = N t := by
  unfold renewalLapse logConductance logDensity
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    show (((2 : ℕ) : ℝ) * Real.log (N t) - ((2 : ℕ) : ℝ) * Real.log (a t)) / 2 +
      ((3 : ℕ) : ℝ) * Real.log (a t) / 3 = Real.log (N t) by push_cast; ring,
    Real.exp_log hN]

theorem renewalScaleFactor_log (a : ℝ → ℝ) {t : ℝ} (ha : 0 < a t) :
    renewalScaleFactor (logDensity a) t = a t := by
  unfold renewalScaleFactor logDensity
  rw [Real.log_pow, show ((3 : ℕ) : ℝ) * Real.log (a t) / 3 = Real.log (a t) by push_cast; ring,
    Real.exp_log ha]

theorem deriv_logDensity (a a' : ℝ → ℝ) {t : ℝ} (ha : 0 < a t)
    (hda : HasDerivAt a (a' t) t) :
    deriv (logDensity a) t = 3 * a' t / a t := by
  have : HasDerivAt (logDensity a) (3 * a t ^ 2 * a' t / a t ^ 3) t := by
    have h := (hda.pow 3).log (by simp only [Pi.pow_apply]; positivity)
    unfold logDensity
    refine h.congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast
    ring
  rw [this.deriv]
  field_simp

/-- A positive connected stationary solution of the renewal-rate action
`eq:main-renewal-rate-action` on the open connected time set `s`: scale
factor `a` with derivative `a'`, lapse `N`, renewal time `τ` with `τ' = N`,
and stationarity `E_u = E_v = 0` of the renewal-rate action in the two
positive renewal variables `u = log (N^2/a^2)`, `v = log a^3`
(the hypothesis of `cor:main-derived-desitter-rates`). -/
structure IsStationaryRenewalSolution (Λ : ℝ) (s : Set ℝ)
    (a a' N τ : ℝ → ℝ) : Prop where
  isOpen : IsOpen s
  isPreconnected : IsPreconnected s
  a_pos : ∀ t ∈ s, 0 < a t
  N_pos : ∀ t ∈ s, 0 < N t
  hasDerivAt_a : ∀ t ∈ s, HasDerivAt a (a' t) t
  hasDerivAt_τ : ∀ t ∈ s, HasDerivAt τ (N t) t
  continuousOn_a' : ContinuousOn a' s
  continuousOn_N : ContinuousOn N s
  stationary : ∀ t ∈ s,
    eulerU Λ (logConductance a N) (deriv (logConductance a N)) (logDensity a)
      (deriv (logDensity a)) t = 0 ∧
    eulerV Λ (logConductance a N) (deriv (logConductance a N)) (logDensity a)
      (deriv (logDensity a)) t = 0

namespace IsStationaryRenewalSolution

variable {Λ : ℝ} {s : Set ℝ} {a a' N τ : ℝ → ℝ}

/-- The lapse Euler equation `E_u = 0` is the Friedmann constraint
`3 𝓗^2 = Λ` with `𝓗 = a'/(N a)`. -/
theorem friedmann (h : IsStationaryRenewalSolution Λ s a a' N τ) :
    ∀ t ∈ s, 3 * (a' t / (N t * a t)) ^ 2 = Λ := by
  intro t ht
  have hE := (h.stationary t ht).1
  rw [eulerU_eq, hubbleRate_renewal_eq] at hE
  simp only at hE
  rw [renewalLapse_log a N (h.a_pos t ht) (h.N_pos t ht),
    renewalScaleFactor_log a (h.a_pos t ht),
    deriv_logDensity a a' (h.a_pos t ht) (h.hasDerivAt_a t ht)] at hE
  have hpos : 0 < N t * a t ^ 3 := by
    have := h.a_pos t ht; have := h.N_pos t ht; positivity
  have hE' : 3 * (3 * a' t / a t / (3 * N t)) ^ 2 - Λ = 0 := by
    rcases mul_eq_zero.mp hE with h0 | h0
    · exact absurd h0 hpos.ne'
    · exact h0
  have hq : 3 * a' t / a t / (3 * N t) = a' t / (N t * a t) := by
    have := h.a_pos t ht; have := h.N_pos t ht
    field_simp
  rw [hq] at hE'
  linarith

/-- Every stationary renewal solution is a Friedmann-constraint solution in
the sense of `Gravity/StationaryHomogeneousRenewalRates.lean`. -/
theorem toStationaryHomogeneousSolution
    (h : IsStationaryRenewalSolution Λ s a a' N τ) :
    IsStationaryHomogeneousSolution Λ s a a' N τ where
  isOpen := h.isOpen
  isPreconnected := h.isPreconnected
  a_pos := h.a_pos
  N_pos := h.N_pos
  hasDerivAt_a := h.hasDerivAt_a
  hasDerivAt_τ := h.hasDerivAt_τ
  continuousOn_a' := h.continuousOn_a'
  continuousOn_N := h.continuousOn_N
  friedmann := h.friedmann

/-- `cor:main-derived-desitter-rates`, discharged from
`thm:main-homogeneous-friedmann`: for `Λ > 0` every positive connected
stationary solution of the renewal-rate action is
`a = a(t₀) exp (σ H₀ (τ - τ(t₀)))`, `σ ∈ {1, -1}`, `H₀ = √(Λ/3)`
(`eq:main-stationary-homogeneous-solutions`), and in proper-time gauge
`N = 1` on the expanding branch the boxed regulator rates
`eq:desitter-regulator-main` hold; for `Λ = 0` the scale factor is constant,
and for `Λ < 0` there is no positive solution. -/
theorem derived_desitter_rates (h : IsStationaryRenewalSolution Λ s a a' N τ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    (0 < Λ → ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ t ∈ s, a t = a t₀ * Real.exp (σ * Real.sqrt (Λ / 3) * (τ t - τ t₀))) ∧
    (0 < Λ → (∀ t ∈ s, N t = 1) →
      (∀ t ∈ s, a' t / (N t * a t) = Real.sqrt (Λ / 3)) → ∀ (hh : ℝ), ∀ t ∈ s,
      homogeneousRootRate (renewalConductance a N) hh t =
        (a t₀)⁻¹ ^ 2 * Real.exp (-2 * Real.sqrt (Λ / 3) * (t - t₀)) / (8 * hh ^ 2) ∧
      homogeneousVertexMass (renewalDensity a) hh t =
        a t₀ ^ 3 * Real.exp (3 * Real.sqrt (Λ / 3) * (t - t₀)) * hh ^ 3) ∧
    (Λ = 0 → ∀ t ∈ s, a t = a t₀) ∧
    (Λ < 0 → s = ∅) := by
  have h' := h.toStationaryHomogeneousSolution
  refine ⟨fun hΛ => h'.stationary_scale_factor_desitter hΛ ht₀, ?_,
    fun hΛ => h'.stationary_scale_factor_flat hΛ ht₀,
    fun hΛ => h'.stationary_solution_empty_of_neg hΛ⟩
  intro _ hN hσ hh
  exact h'.desitter_regulator_rates hN ht₀ (h'.expanding_scale_factor_of_lapse_one hN ht₀ hσ) hh

end IsStationaryRenewalSolution

end RenewalGeometry
