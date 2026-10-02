/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyActionTestDensity
import RenewalGeometry.Analysis.RectangleIntegrationByParts

/-!
# The areal lift of a Gowdy solution is critical for the unreduced action
  (`eq:supp-gowdy-adm-density`–`eq:supp-gowdy-areal-lift`, `thm:main-gowdy-regulator` (G4);
  emergent-spacetime supplement)

For a smooth solution `X_*` of the frame system `eq:supp-gowdy-frame-system` with the coordinate
constraints `eq:supp-gowdy-coordinate-constraints` (`HermiteReadout.GowdySmoothReference`), the
areal lift `R = t, λ, P, Q, N = 1, β = 0` (`eq:supp-gowdy-areal-lift`) is a critical point of the
unreduced action `∫∫ 𝓛_G` (density `eq:supp-gowdy-adm-density`, `-2NR''` replaced by `2N'R'`),
with the lapse and shift varied independently **before** the areal-gauge restriction:

* `arealLift`: the six fields of the lift; `contJet_arealLift`: its first jet is an areal-gauge
  jet (`liftJet`).
* `fluxT`, `fluxΘ`: the time and space fluxes `F = -t e δR - δλ/2 + t a δP + t e^P c δQ`,
  `G = t f δR + 2 δβ - t b δP - t e^P d δQ` (`e = (a²+b²+c²+d²)/2`, `f = ab + cd`).
* `liftVariation_eq_divergence` (**the six Euler–Lagrange identities**): on the slab, the first
  variation density of the lift in the direction of an arbitrary `C¹` test equals
  `∂_t F + ∂_θ G`.  Coefficientwise this is: lapse `λ_t/2 - t e = 0` (`eq_lam`); shift
  `λ_θ/2 - t f = 0` (`constraint_lam`, with the constant `β_θ`-coefficient `2`); `λ`:
  `∂_t(-1/2) = 0`; area `R`: `(a²+c²-b²-d²)/2 = ∂_t(-te) + ∂_θ(tf)` (the stress identity
  `e_t - f_θ = -(a²+c²)/t` from the frame equations); `P`: `t(c² - d²) = ∂_t(ta) - ∂_θ(tb)`
  (`eq_a`, `eq_P`, `constraint_P`); `Q`: `0 = ∂_t(t e^P c) - ∂_θ(t e^P d)` (`eq_c`, `eq_Q`,
  `constraint_Q`).
* `continuumFirstVariation_arealLift_eq_zero` (**criticality**): for every `C¹` test, `2π`-periodic
  in `θ` and vanishing on the time edges `t = α, β` of a subslab `[α, β] ⊆ [t₀, t₁]`,
  `δS_*[lift; φ] = 0` (integration by parts, `RectangleIntegrationByParts`).
-/

open Set Finset
open scoped BigOperators ContDiff

namespace RenewalGeometry.GowdyStaggered.ActionTest

noncomputable section

/-! ### Partial derivatives along coordinate lines -/

theorem hasDerivAt_dT {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : DifferentiableAt ℝ F p) :
    HasDerivAt (fun t => F (t, p.2)) (dT F p) p.1 := by
  have hl : HasDerivAt (fun t : ℝ => (t, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const _ _)
  exact hF.hasFDerivAt.comp_hasDerivAt p.1 hl

theorem hasDerivAt_dΘ {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : DifferentiableAt ℝ F p) :
    HasDerivAt (fun θ => F (p.1, θ)) (dΘ F p) p.2 := by
  have hl : HasDerivAt (fun θ : ℝ => (p.1, θ)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id p.2)
  exact hF.hasFDerivAt.comp_hasDerivAt p.2 hl

theorem dT_eq_of_hasDerivAt {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : DifferentiableAt ℝ F p) {D : ℝ}
    (h : HasDerivAt (fun t => F (t, p.2)) D p.1) : dT F p = D :=
  (hasDerivAt_dT hF).unique h

theorem dΘ_eq_of_hasDerivAt {F : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hF : DifferentiableAt ℝ F p) {D : ℝ}
    (h : HasDerivAt (fun θ => F (p.1, θ)) D p.2) : dΘ F p = D :=
  (hasDerivAt_dΘ hF).unique h

theorem dT_fst (p : ℝ × ℝ) : dT (fun q : ℝ × ℝ => q.1) p = 1 := by
  simp [dT, fderiv_fst]

theorem dΘ_fst (p : ℝ × ℝ) : dΘ (fun q : ℝ × ℝ => q.1) p = 0 := by
  simp [dΘ, fderiv_fst]

theorem dT_const (c : ℝ) (p : ℝ × ℝ) : dT (fun _ : ℝ × ℝ => c) p = 0 := by
  simp [dT]

theorem dΘ_const (c : ℝ) (p : ℝ × ℝ) : dΘ (fun _ : ℝ × ℝ => c) p = 0 := by
  simp [dΘ]

/-! ### The areal lift -/

variable {t₀ t₁ : ℝ}

open HermiteReadout

/-- **The areal lift** `eq:supp-gowdy-areal-lift` of a smooth reference: `R = t`, `λ`, `P`, `Q`,
lapse `N = 1`, shift `β = 0`. -/
def arealLift (sol : GowdySmoothReference t₀ t₁) : Fin 6 → ℝ × ℝ → ℝ :=
  ![fun p => p.1, sol.lam, sol.P, sol.Q, fun _ => 1, fun _ => 0]

theorem contJet_arealLift (sol : GowdySmoothReference t₀ t₁) (p : ℝ × ℝ) :
    contJet (arealLift sol) p = liftJet p.1 (sol.lam p) (sol.P p) (sol.Q p) (dT sol.lam p)
      (dΘ sol.lam p) (dT sol.P p) (dΘ sol.P p) (dT sol.Q p) (dΘ sol.Q p) := by
  ext k <;> fin_cases k <;> simp [contJet, arealLift, liftJet, dT_fst, dΘ_fst, dT_const, dΘ_const]

theorem contDiff_arealLift (sol : GowdySmoothReference t₀ t₁) (k : Fin 6) :
    ContDiff ℝ ∞ (arealLift sol k) := by
  fin_cases k
  · exact contDiff_fst
  · exact sol.smoothInf_lam
  · exact sol.smoothInf_P
  · exact sol.smoothInf_Q
  · exact contDiff_const
  · exact contDiff_const

/-! ### The fluxes -/

/-- The energy density `e = (a² + b² + c² + d²)/2`. -/
def energyDens (sol : GowdySmoothReference t₀ t₁) (p : ℝ × ℝ) : ℝ :=
  (sol.a p ^ 2 + sol.b p ^ 2 + sol.c p ^ 2 + sol.d p ^ 2) / 2

/-- The momentum density `f = ab + cd`. -/
def momDens (sol : GowdySmoothReference t₀ t₁) (p : ℝ × ℝ) : ℝ :=
  sol.a p * sol.b p + sol.c p * sol.d p

/-- The time flux `F = -t e δR - δλ/2 + t a δP + t e^P c δQ` of the first variation. -/
def fluxT (sol : GowdySmoothReference t₀ t₁) (φ : Fin 6 → ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -(p.1 * energyDens sol p) * φ 0 p - φ 1 p / 2 + p.1 * sol.a p * φ 2 p +
    p.1 * Real.exp (sol.P p) * sol.c p * φ 3 p

/-- The space flux `G = t f δR + 2 δβ - t b δP - t e^P d δQ` of the first variation. -/
def fluxΘ (sol : GowdySmoothReference t₀ t₁) (φ : Fin 6 → ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * momDens sol p * φ 0 p + 2 * φ 5 p - p.1 * sol.b p * φ 2 p -
    p.1 * Real.exp (sol.P p) * sol.d p * φ 3 p

theorem contDiff_fluxT (sol : GowdySmoothReference t₀ t₁) {φ : Fin 6 → ℝ × ℝ → ℝ} {m : ℕ}
    (hφ : ∀ k, ContDiff ℝ m (φ k)) : ContDiff ℝ m (fluxT sol φ) := by
  have ha : ContDiff ℝ m sol.a := sol.smoothInf_a.of_le (by exact_mod_cast le_top)
  have hb : ContDiff ℝ m sol.b := sol.smoothInf_b.of_le (by exact_mod_cast le_top)
  have hc : ContDiff ℝ m sol.c := sol.smoothInf_c.of_le (by exact_mod_cast le_top)
  have hd : ContDiff ℝ m sol.d := sol.smoothInf_d.of_le (by exact_mod_cast le_top)
  have hP : ContDiff ℝ m sol.P := sol.smoothInf_P.of_le (by exact_mod_cast le_top)
  unfold fluxT energyDens
  have := hφ 0; have := hφ 1; have := hφ 2; have := hφ 3
  fun_prop

theorem contDiff_fluxΘ (sol : GowdySmoothReference t₀ t₁) {φ : Fin 6 → ℝ × ℝ → ℝ} {m : ℕ}
    (hφ : ∀ k, ContDiff ℝ m (φ k)) : ContDiff ℝ m (fluxΘ sol φ) := by
  have ha : ContDiff ℝ m sol.a := sol.smoothInf_a.of_le (by exact_mod_cast le_top)
  have hb : ContDiff ℝ m sol.b := sol.smoothInf_b.of_le (by exact_mod_cast le_top)
  have hc : ContDiff ℝ m sol.c := sol.smoothInf_c.of_le (by exact_mod_cast le_top)
  have hd : ContDiff ℝ m sol.d := sol.smoothInf_d.of_le (by exact_mod_cast le_top)
  have hP : ContDiff ℝ m sol.P := sol.smoothInf_P.of_le (by exact_mod_cast le_top)
  unfold fluxΘ momDens
  have := hφ 0; have := hφ 5; have := hφ 2; have := hφ 3
  fun_prop

/-! ### The six Euler–Lagrange identities -/

/-- **The Euler–Lagrange identities at the areal lift.**  On the slab `t ∈ [t₀, t₁]`, for every
differentiable test `φ` (all six directions, lapse and shift included), the first-variation
density of the unreduced action at the areal lift equals the divergence `∂_t F + ∂_θ G` of the
fluxes `fluxT`, `fluxΘ`.  The proof uses exactly: the frame equations `eq_a, eq_b, eq_c, eq_d`
(through the stress identity), `eq_P`, `eq_Q`, `eq_lam` (lapse equation), and the coordinate
constraints `constraint_P`, `constraint_Q`, `constraint_lam` (shift equation). -/
theorem liftVariation_eq_divergence (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀)
    {φ : Fin 6 → ℝ × ℝ → ℝ} (hφ : ∀ k, Differentiable ℝ (φ k)) {p : ℝ × ℝ}
    (hp : p.1 ∈ Icc t₀ t₁) :
    liftVariation p.1 (dT sol.lam p) (dΘ sol.lam p) (sol.P p) (dT sol.P p) (dΘ sol.P p)
        (dT sol.Q p) (dΘ sol.Q p) (contJet φ p) =
      fderiv ℝ (fluxT sol φ) p (1, 0) + fderiv ℝ (fluxΘ sol φ) p (0, 1) := by
  have dA : DifferentiableAt ℝ sol.a p :=
    (sol.smoothInf_a.differentiable (by simp)).differentiableAt
  have dB : DifferentiableAt ℝ sol.b p :=
    (sol.smoothInf_b.differentiable (by simp)).differentiableAt
  have dC : DifferentiableAt ℝ sol.c p :=
    (sol.smoothInf_c.differentiable (by simp)).differentiableAt
  have dD : DifferentiableAt ℝ sol.d p :=
    (sol.smoothInf_d.differentiable (by simp)).differentiableAt
  have dP : DifferentiableAt ℝ sol.P p :=
    (sol.smoothInf_P.differentiable (by simp)).differentiableAt
  have dφ : ∀ k, DifferentiableAt ℝ (φ k) p := fun k => (hφ k) p
  have hdiffT : DifferentiableAt ℝ (fluxT sol φ) p := by
    unfold fluxT energyDens
    have := dφ 0; have := dφ 1; have := dφ 2; have := dφ 3
    fun_prop
  have hdiffΘ : DifferentiableAt ℝ (fluxΘ sol φ) p := by
    unfold fluxΘ momDens
    have := dφ 0; have := dφ 5; have := dφ 2; have := dφ 3
    fun_prop
  -- the time derivative of the time flux
  have ha := hasDerivAt_dT dA
  have hb := hasDerivAt_dT dB
  have hc := hasDerivAt_dT dC
  have hd := hasDerivAt_dT dD
  have hP := hasDerivAt_dT dP
  have hφt := fun k => hasDerivAt_dT (dφ k)
  have he := ((((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)).add (hd.pow 2)).div_const 2
  have hT := (((((hasDerivAt_id' p.1).mul he).neg.mul (hφt 0)).sub ((hφt 1).div_const 2)).add
    (((hasDerivAt_id' p.1).mul ha).mul (hφt 2))).add
    ((((hasDerivAt_id' p.1).mul hP.exp).mul hc).mul (hφt 3))
  have eT := dT_eq_of_hasDerivAt hdiffT (hT.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      simp only [fluxT, energyDens, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.sub_apply, Pi.div_apply]))
  -- the space derivative of the space flux
  have ha' := hasDerivAt_dΘ dA
  have hb' := hasDerivAt_dΘ dB
  have hc' := hasDerivAt_dΘ dC
  have hd' := hasDerivAt_dΘ dD
  have hP' := hasDerivAt_dΘ dP
  have hφθ := fun k => hasDerivAt_dΘ (dφ k)
  have hf := (ha'.mul hb').add (hc'.mul hd')
  have hG := (((((hf.const_mul p.1).mul (hφθ 0)).add ((hφθ 5).const_mul 2)).sub
    ((hb'.const_mul p.1).mul (hφθ 2))).sub
    (((hP'.exp.const_mul p.1).mul hd').mul (hφθ 3)))
  have eΘ := dΘ_eq_of_hasDerivAt hdiffΘ (hG.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun θ => by
      simp only [fluxΘ, momDens, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.sub_apply, Pi.div_apply]))
  change _ = dT (fluxT sol φ) p + dΘ (fluxΘ sol φ) p
  rw [eT, eΘ]
  -- the equations at `p`
  have Ea := sol.eq_a p hp
  have Eb := sol.eq_b p hp
  have Ec := sol.eq_c p hp
  have Ed := sol.eq_d p hp
  have EP := sol.eq_P p hp
  have EQ := sol.eq_Q p hp
  have El := sol.eq_lam p hp
  have CP := sol.constraint_P p hp
  have CQ := sol.constraint_Q p hp
  have Cl := sol.constraint_lam p hp
  have hE : 0 < Real.exp (sol.P p) := Real.exp_pos _
  have hp0 : p.1 ≠ 0 := (lt_of_lt_of_le h0 hp.1).ne'
  have CQ' : dΘ sol.Q p = sol.d p / Real.exp (sol.P p) := by
    rw [← CQ]; field_simp
  have e2 : Real.exp (2 * sol.P p) = Real.exp (sol.P p) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have en : Real.exp (-sol.P p) = (Real.exp (sol.P p))⁻¹ := Real.exp_neg _
  simp only [liftVariation, contJet, Prod.mk.eta, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.neg_apply, Pi.sub_apply, Pi.div_apply, Nat.cast_ofNat]
  rw [El, Cl, EP, CP, EQ, CQ', Ea, Eb, Ec, Ed, e2, en]
  field_simp
  ring

/-! ### Criticality of the areal lift -/

theorem eval_two_pi {F : ℝ × ℝ → ℝ} (hF : ∀ p : ℝ × ℝ, F (p.1, p.2 + 2 * Real.pi) = F p)
    (t : ℝ) : F (t, 2 * Real.pi) = F (t, 0) := by
  simpa using hF (t, 0)

/-- **The areal lift is a critical point of the unreduced action** (`eq:supp-gowdy-adm-density`–
`eq:supp-gowdy-areal-lift`): for every `C¹` test `φ` of the six fields (lapse and shift varied
independently, before the areal-gauge restriction), `2π`-periodic in `θ` and vanishing on the
time edges `t = α, β` of a subslab `[α, β] ⊆ [t₀, t₁]`, the continuum first variation vanishes,
`δS_*[lift; φ] = 0`. -/
theorem continuumFirstVariation_arealLift_eq_zero (sol : GowdySmoothReference t₀ t₁)
    (h0 : 0 < t₀) {φ : Fin 6 → ℝ × ℝ → ℝ} (hφ : ∀ k, ContDiff ℝ 1 (φ k))
    (hper : ∀ k (p : ℝ × ℝ), φ k (p.1, p.2 + 2 * Real.pi) = φ k p) {α β : ℝ} (hαβ : α ≤ β)
    (hα : t₀ ≤ α) (hβ : β ≤ t₁) (hφα : ∀ k θ, φ k (α, θ) = 0) (hφβ : ∀ k θ, φ k (β, θ) = 0) :
    continuumFirstVariation (arealLift sol) φ α β = 0 := by
  have hφd : ∀ k, Differentiable ℝ (φ k) := fun k => (hφ k).differentiable one_ne_zero
  rw [continuumFirstVariation_eq α β
    (fun k => (contDiff_arealLift sol k).differentiable (by simp)) hφd
    (fun p => by simp [arealLift])]
  have hcongr : ∫ t in α..β, ∫ θ in (0 : ℝ)..2 * Real.pi,
      admVariation (contJet (arealLift sol) (t, θ)) (contJet φ (t, θ)) =
      ∫ t in α..β, ∫ θ in (0 : ℝ)..2 * Real.pi,
        (fderiv ℝ (fluxT sol φ) (t, θ) (1, 0) + fderiv ℝ (fluxΘ sol φ) (t, θ) (0, 1)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [uIcc_of_le hαβ] at ht
    simp only [contJet_arealLift, admVariation_liftJet]
    exact liftVariation_eq_divergence sol h0 hφd ⟨hα.trans ht.1, ht.2.trans hβ⟩
  rw [hcongr]
  have hφ1 : ∀ k, ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (φ k) := by simpa using hφ
  have hT : ContDiff ℝ 1 (fluxT sol φ) := by simpa using contDiff_fluxT sol hφ1
  have hΘ : ContDiff ℝ 1 (fluxΘ sol φ) := by simpa using contDiff_fluxΘ sol hφ1
  refine RectangleIntegrationByParts.integral2_divergence_eq_zero hT hΘ
    (fun θ => by simp [fluxT, hφα]) (fun θ => by simp [fluxT, hφβ]) (fun t => ?_)
  simp only [fluxΘ, momDens, eval_two_pi sol.periodic_a, eval_two_pi sol.periodic_b,
    eval_two_pi sol.periodic_c, eval_two_pi sol.periodic_d, eval_two_pi sol.periodic_P,
    eval_two_pi (hper 0), eval_two_pi (hper 2), eval_two_pi (hper 3), eval_two_pi (hper 5)]

end

end RenewalGeometry.GowdyStaggered.ActionTest
