/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.CoordinateCurvature

/-!
# A nonvacuum Einstein–Higgs comparison family (`prop:homogeneous`, Einstein–SM
action closure)

The homogeneous ansatz `g = -dt² + a(t)² δ`, `H = φ(t) h₀/√2`, `A = 0`, `Ψ = Ψ̄ = 0`
(**`eq:homogeneous-fields`**) with `U(φ) = λ_H (φ²/2 - v_H²)²`.

* `homogeneousField`, `exists_local_solution`: the system **`eq:homogeneous-ODE`**
  `ȧ = aℋ`, `φ̇ = π`, `π̇ = -3ℋπ - U'(φ)`, `ℋ̇ = -(κ/2)π²` has, for every initial
  datum with `a₀ > 0`, a `C^∞` local solution on an open interval around `0` with `a > 0`
  (Picard–Lindelöf and the `C^n` bootstrap of Mathlib; positivity of `a` by continuity);
* `friedmann_constraint_propagates`: the Friedmann residual
  `3ℋ² - Λ - κ(π²/2 + U(φ))` has zero derivative along solutions, so the initial
  constraint **`eq:Friedmann-initial`** persists;
* `einstein_equations_of_constraint`: on the flat FLRW jet
  (`Gravity/CoordinateCurvature.lean`) with `ȧ = aℋ`, `ä = a(ℋ² + ℋ̇)`, `ℋ̇ = -(κ/2)π²`
  and the constraint, every component of `G_{μν} + Λ g_{μν} = κ T^H_{μν}` holds, where
  `T^H` is the Higgs stress **`eq:H-stress`** evaluated on the ansatz
  (`homogeneousHiggsStress`: `ρ = π²/2 + U`, `p = π²/2 - U`);
* `einstein_equations_along_solution`: the same along the local solution at every time;
* `higgs_euler_along_solution`, `covariant_higgs_euler_along_solution`: the Higgs Euler
  equation `φ̈ + 3(ȧ/a)φ̇ + U'(φ) = 0`, also in the covariant form `□φ - U'(φ) = 0` with
  the FLRW d'Alembertian `□φ = g^{μν}(∂_μ∂_νφ - Γ^λ_{μν}∂_λφ)` on the jet
  (`flrwBoxHomogeneous_eq`);
* `gauge_current_re_vanishes`: the abstract reason the gauge current vanishes — for a
  skew-adjoint generator `T` and a real relative coefficient,
  `Re ⟪π h₀, T(φ h₀)⟫ = 0`;
* `backreaction_of_pi_ne_zero`: `π₀ ≠ 0` gives `ℋ̇(0) < 0`.

What is *not* formalised: the fermionic equations (satisfied by zero spinors) and the
final sampling sentence (`prop:smooth-sampling`); the Einstein and Higgs equations are
stated on the component jets of `Gravity/CoordinateCurvature.lean`.
-/

open Set Filter Topology Finset
open scoped ContDiff

namespace RenewalGeometry.HomogeneousEinsteinHiggs

/-! ### The Higgs potential -/

/-- `U(φ) = λ_H (φ²/2 - v_H²)²`. -/
noncomputable def higgsPotential (lamH vH φ : ℝ) : ℝ := lamH * (φ ^ 2 / 2 - vH ^ 2) ^ 2

/-- `U'(φ) = 2 λ_H φ (φ²/2 - v_H²)`. -/
noncomputable def higgsPotentialDeriv (lamH vH φ : ℝ) : ℝ := 2 * lamH * φ * (φ ^ 2 / 2 - vH ^ 2)

theorem hasDerivAt_higgsPotential (lamH vH φ : ℝ) :
    HasDerivAt (higgsPotential lamH vH) (higgsPotentialDeriv lamH vH φ) φ := by
  unfold higgsPotential higgsPotentialDeriv
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2 - vH ^ 2) (2 * φ / 2) φ := by
    have := ((hasDerivAt_pow 2 φ).div_const 2).sub_const (vH ^ 2)
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => lamH * ((x ^ 2 / 2 - vH ^ 2) * (x ^ 2 / 2 - vH ^ 2)))
      (lamH * ((2 * φ / 2) * (φ ^ 2 / 2 - vH ^ 2) + (φ ^ 2 / 2 - vH ^ 2) * (2 * φ / 2))) φ :=
    (h1.mul h1).const_mul lamH
  have heq : (fun x : ℝ => lamH * (x ^ 2 / 2 - vH ^ 2) ^ 2)
      = fun x : ℝ => lamH * ((x ^ 2 / 2 - vH ^ 2) * (x ^ 2 / 2 - vH ^ 2)) := by
    funext x; ring
  rw [heq]
  refine h2.congr_deriv ?_
  ring

/-! ### The homogeneous ODE system -/

/-- The vector field of `eq:homogeneous-ODE` on the state `(a, φ, π, ℋ)`. -/
noncomputable def homogeneousField (κ lamH vH : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 0 * x 3, x 2, -3 * x 3 * x 2 - higgsPotentialDeriv lamH vH (x 1), -(κ / 2) * x 2 ^ 2]

theorem contDiff_homogeneousField (κ lamH vH : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (homogeneousField κ lamH vH) := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp [homogeneousField, higgsPotentialDeriv] <;> fun_prop

/-- A solution of `eq:homogeneous-ODE` on a set of times. -/
structure IsSolution (κ lamH vH : ℝ) (a φ π ℋ : ℝ → ℝ) (s : Set ℝ) : Prop where
  a_deriv : ∀ t ∈ s, HasDerivAt a (a t * ℋ t) t
  φ_deriv : ∀ t ∈ s, HasDerivAt φ (π t) t
  π_deriv : ∀ t ∈ s, HasDerivAt π (-3 * ℋ t * π t - higgsPotentialDeriv lamH vH (φ t)) t
  ℋ_deriv : ∀ t ∈ s, HasDerivAt ℋ (-(κ / 2) * π t ^ 2) t

/-- **`prop:homogeneous`, local existence.**  For every initial datum with `a₀ > 0`
there is a `C^∞` local solution of `eq:homogeneous-ODE` on an open interval around `0`
with `a > 0`. -/
theorem exists_local_solution (κ lamH vH a₀ φ₀ π₀ H₀ : ℝ) (ha₀ : 0 < a₀) :
    ∃ (ε : ℝ) (_ : 0 < ε) (a φ π ℋ : ℝ → ℝ),
      a 0 = a₀ ∧ φ 0 = φ₀ ∧ π 0 = π₀ ∧ ℋ 0 = H₀ ∧
      IsSolution κ lamH vH a φ π ℋ (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, 0 < a t) ∧
      ContDiffOn ℝ ∞ a (Ioo (-ε) ε) ∧ ContDiffOn ℝ ∞ φ (Ioo (-ε) ε) ∧
      ContDiffOn ℝ ∞ π (Ioo (-ε) ε) ∧ ContDiffOn ℝ ∞ ℋ (Ioo (-ε) ε) := by
  set x₀ : Fin 4 → ℝ := ![a₀, φ₀, π₀, H₀] with hx₀
  have hf : ContDiffAt ℝ 1 (homogeneousField κ lamH vH) x₀ :=
    (contDiff_homogeneousField κ lamH vH 1).contDiffAt
  obtain ⟨α, hα0, ε₁, hε₁, hα⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  simp only [zero_sub, zero_add] at hα
  -- positivity of `a` near `0`
  have hcont : ContinuousAt (fun t => α t 0) 0 := by
    have := (hα 0 ⟨by linarith, hε₁⟩).continuousAt
    exact (continuous_apply 0).continuousAt.comp this
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < α t 0 := by
    have h0 : 0 < α 0 0 := by rw [hα0]; simpa [hx₀] using ha₀
    exact hcont.eventually (lt_mem_nhds h0)
  obtain ⟨δ, hδ, hδpos⟩ := Metric.eventually_nhds_iff.1 hpos
  -- smoothness on a closed subinterval
  set ε₂ : ℝ := min ε₁ δ / 2 with hε₂
  have hε₂pos : 0 < ε₂ := by positivity
  have hε₂ε₁ : ε₂ < ε₁ := by
    have : min ε₁ δ ≤ ε₁ := min_le_left _ _
    linarith
  have hε₂δ : ε₂ < δ := by
    have : min ε₁ δ ≤ δ := min_le_right _ _
    linarith
  have hIcc : Icc (-ε₂) ε₂ ⊆ Ioo (-ε₁) ε₁ := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsmooth : ContDiffOn ℝ ∞ α (Icc (-ε₂) ε₂) := by
    refine ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun _ x => homogeneousField κ lamH vH x) (u := univ) ?_ ?_ (mapsTo_univ _ _)
    · exact ((contDiff_homogeneousField κ lamH vH _).comp contDiff_snd).contDiffOn
    · intro t ht
      exact (hα t (hIcc ht)).hasDerivWithinAt
  refine ⟨ε₂, hε₂pos, fun t => α t 0, fun t => α t 1, fun t => α t 2, fun t => α t 3,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show α 0 0 = a₀
    rw [hα0]; simp [hx₀]
  · show α 0 1 = φ₀
    rw [hα0]; simp [hx₀]
  · show α 0 2 = π₀
    rw [hα0]; simp [hx₀]
  · show α 0 3 = H₀
    rw [hα0]; simp [hx₀]
  · have hIoo : Ioo (-ε₂) ε₂ ⊆ Ioo (-ε₁) ε₁ := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · have := hasDerivAt_pi.1 (hα t (hIoo ht)) 0
      simpa [homogeneousField] using this
    · have := hasDerivAt_pi.1 (hα t (hIoo ht)) 1
      simpa [homogeneousField] using this
    · have := hasDerivAt_pi.1 (hα t (hIoo ht)) 2
      simpa [homogeneousField] using this
    · have := hasDerivAt_pi.1 (hα t (hIoo ht)) 3
      simpa [homogeneousField] using this
  · intro t ht
    apply hδpos
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · exact ((contDiffOn_pi.1 hsmooth) 0).mono Ioo_subset_Icc_self
  · exact ((contDiffOn_pi.1 hsmooth) 1).mono Ioo_subset_Icc_self
  · exact ((contDiffOn_pi.1 hsmooth) 2).mono Ioo_subset_Icc_self
  · exact ((contDiffOn_pi.1 hsmooth) 3).mono Ioo_subset_Icc_self

/-! ### Constraint propagation -/

/-- The Friedmann residual `3ℋ² - Λ - κ(π²/2 + U(φ))`. -/
noncomputable def friedmannResidual (Λ κ lamH vH : ℝ) (φ π ℋ : ℝ → ℝ) (t : ℝ) : ℝ :=
  3 * ℋ t ^ 2 - Λ - κ * (π t ^ 2 / 2 + higgsPotential lamH vH (φ t))

/-- Along a solution the Friedmann residual has zero derivative. -/
theorem hasDerivAt_friedmannResidual {κ lamH vH : ℝ} {a φ π ℋ : ℝ → ℝ} {s : Set ℝ}
    (sol : IsSolution κ lamH vH a φ π ℋ s) (Λ : ℝ) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (friedmannResidual Λ κ lamH vH φ π ℋ) 0 t := by
  have hH := (sol.ℋ_deriv t ht).pow 2
  have hπ := (sol.π_deriv t ht).pow 2
  have hU := (hasDerivAt_higgsPotential lamH vH (φ t)).comp t (sol.φ_deriv t ht)
  have h := ((hH.const_mul 3).sub_const Λ).sub (((hπ.div_const 2).add hU).const_mul κ)
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, Function.comp_def]
  ring

/-- **Constraint propagation (`eq:Friedmann-initial`).**  If the Friedmann constraint
holds at `t = 0`, it holds on the whole interval of a solution. -/
theorem friedmann_constraint_propagates {κ lamH vH ε : ℝ} {a φ π ℋ : ℝ → ℝ} (hε : 0 < ε)
    (sol : IsSolution κ lamH vH a φ π ℋ (Ioo (-ε) ε)) (Λ : ℝ)
    (h0 : 3 * ℋ 0 ^ 2 = Λ + κ * (π 0 ^ 2 / 2 + higgsPotential lamH vH (φ 0))) :
    ∀ t ∈ Ioo (-ε) ε, 3 * ℋ t ^ 2 = Λ + κ * (π t ^ 2 / 2 + higgsPotential lamH vH (φ t)) := by
  intro t ht
  have h0' : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := friedmannResidual Λ κ lamH vH φ π ℋ) (f' := fun _ => (0 : ℝ)) (C := 0)
    (s := Ioo (-ε) ε)
    (fun x hx => (hasDerivAt_friedmannResidual sol Λ hx).hasDerivWithinAt)
    (fun x _ => by simp) (convex_Ioo _ _) h0' ht
  simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at hbound
  have hres0 : friedmannResidual Λ κ lamH vH φ π ℋ 0 = 0 := by
    unfold friedmannResidual; linarith
  rw [hres0] at hbound
  unfold friedmannResidual at hbound
  linarith

/-! ### The Einstein equations on the flat FLRW jet -/

/-- The Einstein tensor `G_{μν} = R_{μν} - ½ g_{μν} R` of the flat FLRW jet. -/
noncomputable def flrwEinstein (a adot addot : ℝ) (i j : Fin 4) : ℝ :=
  ricci (flrwGamma a adot) (flrwdGamma a adot addot) i j
    - 1 / 2 * flrwG a i j *
      scalarCurv (flrwGinv a) (flrwGamma a adot) (flrwdGamma a adot addot)

/-- The Higgs stress `eq:H-stress` on the ansatz `H = φ h₀/√2`, `A = 0`:
`T_{μν} = ∂_μφ ∂_νφ - g_{μν}(-π²/2 + U(φ))` with `∂φ = (π, 0, 0, 0)`, i.e.
`T_{00} = π²/2 + U = ρ`, `T_{ij} = a²(π²/2 - U) δ_{ij} = p a² δ_{ij}`. -/
noncomputable def homogeneousHiggsStress (lamH vH a φ π : ℝ) (i j : Fin 4) : ℝ :=
  (if i = 0 then π else 0) * (if j = 0 then π else 0)
    - flrwG a i j * (-(π ^ 2) / 2 + higgsPotential lamH vH φ)

theorem homogeneousHiggsStress_00 (lamH vH a φ π : ℝ) :
    homogeneousHiggsStress lamH vH a φ π 0 0 = π ^ 2 / 2 + higgsPotential lamH vH φ := by
  simp [homogeneousHiggsStress, flrwG]; ring

theorem homogeneousHiggsStress_spatial (lamH vH a φ π : ℝ) (i : Fin 4) (hi : i ≠ 0) :
    homogeneousHiggsStress lamH vH a φ π i i = (π ^ 2 / 2 - higgsPotential lamH vH φ) * a ^ 2 := by
  simp [homogeneousHiggsStress, flrwG, hi]; ring

/-- **`prop:homogeneous`, Einstein equations.**  With `ȧ = aℋ`, `ä = a(ℋ² + ℋ̇)`,
`ℋ̇ = -(κ/2)π²` and the Friedmann constraint, every component of
`G_{μν} + Λ g_{μν} = κ T^H_{μν}` holds on the flat FLRW jet. -/
theorem einstein_equations_of_constraint {a : ℝ} (ha : a ≠ 0)
    (Λ κ lamH vH φ π ℋ Hdot : ℝ)
    (hcon : 3 * ℋ ^ 2 = Λ + κ * (π ^ 2 / 2 + higgsPotential lamH vH φ))
    (hHdot : Hdot = -(κ / 2) * π ^ 2) :
    ∀ i j : Fin 4,
      flrwEinstein a (a * ℋ) (a * (ℋ ^ 2 + Hdot)) i j + Λ * flrwG a i j
        = κ * homogeneousHiggsStress lamH vH a φ π i j := by
  obtain ⟨h00, hdiag, hoff⟩ := flrw_ricci_diag ha (a * ℋ) (a * (ℋ ^ 2 + Hdot))
  have hR := flrw_scalar ha (a * ℋ) (a * (ℋ ^ 2 + Hdot))
  have e1 : a * (ℋ ^ 2 + Hdot) / a = ℋ ^ 2 + Hdot := mul_div_cancel_left₀ _ ha
  have e2 : (a * ℋ) ^ 2 / a ^ 2 = ℋ ^ 2 := by
    rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 ha)]
  have e3 : 3 * (a * (ℋ ^ 2 + Hdot)) / a = 3 * (ℋ ^ 2 + Hdot) := by
    rw [mul_div_assoc, e1]
  rw [e1, e2] at hR
  rw [e3] at h00
  intro i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = 0
    · subst hi
      unfold flrwEinstein
      rw [h00, hR, homogeneousHiggsStress_00]
      simp only [flrwG, eq_self_iff_true, ite_true]
      linear_combination hcon
    · unfold flrwEinstein
      rw [hdiag i hi, hR, homogeneousHiggsStress_spatial lamH vH a φ π i hi]
      simp only [flrwG, hi, eq_self_iff_true, ite_true, ite_false]
      subst hHdot
      linear_combination (-(a ^ 2)) * hcon
  · unfold flrwEinstein
    rw [hoff i j hij]
    simp [flrwG, homogeneousHiggsStress, hij]
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', rfl⟩ <;> simp_all

/-- **`prop:homogeneous`, Einstein equations along the solution.**  Along any solution
of `eq:homogeneous-ODE` satisfying the Friedmann constraint at `t = 0` and with `a ≠ 0`,
the scale factor has first and second derivatives `ȧ = aℋ`, `ä = a(ℋ² + ℋ̇)`, and the
Einstein equations `G + Λg = κ T^H` hold at every time. -/
theorem einstein_equations_along_solution {κ lamH vH ε : ℝ} {a φ π ℋ : ℝ → ℝ} (hε : 0 < ε)
    (sol : IsSolution κ lamH vH a φ π ℋ (Ioo (-ε) ε)) (ha : ∀ t ∈ Ioo (-ε) ε, a t ≠ 0)
    (Λ : ℝ) (h0 : 3 * ℋ 0 ^ 2 = Λ + κ * (π 0 ^ 2 / 2 + higgsPotential lamH vH (φ 0))) :
    ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (a t * ℋ t) t ∧
      HasDerivAt (fun t => a t * ℋ t) (a t * (ℋ t ^ 2 + -(κ / 2) * π t ^ 2)) t ∧
      ∀ i j : Fin 4,
        flrwEinstein (a t) (a t * ℋ t) (a t * (ℋ t ^ 2 + -(κ / 2) * π t ^ 2)) i j
            + Λ * flrwG (a t) i j
          = κ * homogeneousHiggsStress lamH vH (a t) (φ t) (π t) i j := by
  intro t ht
  refine ⟨sol.a_deriv t ht, ?_, ?_⟩
  · have h := (sol.a_deriv t ht).mul (sol.ℋ_deriv t ht)
    refine h.congr_deriv ?_
    ring
  · exact einstein_equations_of_constraint (ha t ht) Λ κ lamH vH (φ t) (π t) (ℋ t) _
      (friedmann_constraint_propagates hε sol Λ h0 t ht) rfl

/-- **Higgs Euler equation on the ansatz.**  Along a solution with `a ≠ 0`,
`φ̈ + 3(ȧ/a)φ̇ + U'(φ) = 0` in the form `π̇ = -3(ȧ/a)π - U'(φ)`, `ȧ = aℋ`. -/
theorem higgs_euler_along_solution {κ lamH vH : ℝ} {a φ π ℋ : ℝ → ℝ} {s : Set ℝ}
    (sol : IsSolution κ lamH vH a φ π ℋ s) {t : ℝ} (ht : t ∈ s) (ha : a t ≠ 0) :
    HasDerivAt φ (π t) t ∧
    HasDerivAt π (-3 * (a t * ℋ t / a t) * π t - higgsPotentialDeriv lamH vH (φ t)) t := by
  refine ⟨sol.φ_deriv t ht, ?_⟩
  have h := sol.π_deriv t ht
  rw [mul_div_cancel_left₀ _ ha]
  exact h

/-- The covariant d'Alembertian of a homogeneous scalar on the flat FLRW jet:
`□φ = g^{μν}(∂_μ∂_νφ - Γ^λ_{μν} ∂_λφ)` with `∂φ = (π, 0, 0, 0)` and
`∂∂φ = diag(π̇, 0, 0, 0)`. -/
noncomputable def flrwBoxHomogeneous (a adot π πdot : ℝ) : ℝ :=
  ∑ μ, ∑ ν, flrwGinv a μ ν *
    ((if μ = 0 ∧ ν = 0 then πdot else 0)
      - ∑ l, flrwGamma a adot l μ ν * (if l = 0 then π else 0))

/-- `□φ = -(φ̈ + 3(ȧ/a)φ̇)` on flat FLRW. -/
theorem flrwBoxHomogeneous_eq {a : ℝ} (ha : a ≠ 0) (adot π πdot : ℝ) :
    flrwBoxHomogeneous a adot π πdot = -(πdot + 3 * (adot / a) * π) := by
  unfold flrwBoxHomogeneous flrwGinv flrwGamma
  simp [Fin.sum_univ_four]
  field_simp
  ring

/-- **Covariant Higgs Euler equation on the ansatz.**  Along a solution with `a ≠ 0`,
the scalar equation `□φ - U'(φ) = 0` holds with `□` the FLRW d'Alembertian evaluated on
the jet `(φ̇, φ̈) = (π, π̇)`, `π̇ = -3ℋπ - U'(φ)`, `ȧ = aℋ`. -/
theorem covariant_higgs_euler_along_solution {κ lamH vH : ℝ} {a φ π ℋ : ℝ → ℝ}
    {s : Set ℝ} (sol : IsSolution κ lamH vH a φ π ℋ s) {t : ℝ} (ht : t ∈ s)
    (ha : a t ≠ 0) :
    HasDerivAt π (-3 * ℋ t * π t - higgsPotentialDeriv lamH vH (φ t)) t ∧
    flrwBoxHomogeneous (a t) (a t * ℋ t) (π t)
        (-3 * ℋ t * π t - higgsPotentialDeriv lamH vH (φ t))
      - higgsPotentialDeriv lamH vH (φ t) = 0 := by
  refine ⟨sol.π_deriv t ht, ?_⟩
  rw [flrwBoxHomogeneous_eq ha, mul_div_cancel_left₀ _ ha]
  ring

/-- **Vanishing gauge current, abstract form.**  For a skew-adjoint generator `T` and a
real relative coefficient between `H = φ h₀/√2` and `Ḣ = π h₀/√2`, the real part of the
current pairing `⟪π h₀, T(φ h₀)⟫` vanishes. -/
theorem gauge_current_re_vanishes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : ∀ x y, inner ℂ (T x) y = -inner ℂ x (T y)) (h₀ : E) (φ π : ℝ) :
    (inner ℂ ((π : ℂ) • h₀) (T ((φ : ℂ) • h₀))).re = 0 := by
  have hskew : inner ℂ h₀ (T h₀) = -(starRingEnd ℂ) (inner ℂ h₀ (T h₀)) := by
    have h1 := hT h₀ h₀
    rw [← inner_conj_symm (T h₀) h₀] at h1
    rw [h1, neg_neg]
  have hre : (inner ℂ h₀ (T h₀)).re = 0 := by
    have := congrArg Complex.re hskew
    simp only [Complex.neg_re, Complex.conj_re] at this
    linarith
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul, hre, mul_zero]

/-- **Backreaction.**  With `π₀ ≠ 0` the Hubble rate is strictly decreasing at `t = 0`
(`ℋ̇(0) = -(κ/2)π₀² < 0`), so the family is not a relabelled vacuum metric. -/
theorem backreaction_of_pi_ne_zero {κ lamH vH : ℝ} {a φ π ℋ : ℝ → ℝ} {s : Set ℝ}
    (sol : IsSolution κ lamH vH a φ π ℋ s) (hκ : 0 < κ) (h0 : (0 : ℝ) ∈ s) (hπ : π 0 ≠ 0) :
    HasDerivAt ℋ (-(κ / 2) * π 0 ^ 2) 0 ∧ -(κ / 2) * π 0 ^ 2 < 0 := by
  refine ⟨sol.ℋ_deriv 0 h0, ?_⟩
  have : 0 < π 0 ^ 2 := by positivity
  nlinarith

end RenewalGeometry.HomogeneousEinsteinHiggs
