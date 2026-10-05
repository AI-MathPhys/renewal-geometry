/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticImplicitFunction
import RenewalGeometry.Action.ExactPhaseCompatibleAnalytic
import RenewalGeometry.Gravity.InitialConstraintLinearRange

/-!
# Stationary elimination, the Legendre transform and the canonical Hamiltonian
  (`eq:supp-exact-legendre`, `eq:supp-exact-H`, `eq:main-action-legendre-map`,
  `eq:main-action-hamiltonian`, `eq:main-action-initial-constraints`,
  `thm:supp-exact-action-provenance` (iii); emergent-spacetime manuscript)

**Generic analytic Legendre transform** (Banach spaces `P` of parameters and `V` of velocities,
momenta in the dual `V →L[ℝ] ℝ`):

* `velMom L x = D_V L(x)`, `velHess L x = D_V(D_V L)(x)`, and the chart hypothesis
  `LegendreChart L x₀`: `L` analytic at `x₀` and the velocity Hessian invertible there ("on the
  Legendre chart the velocity Hessian is nonsingular").
* `exists_legendre_inverse` / `legendreInv_spec`: on a Legendre chart the Legendre map
  `π = D_V L(p, V)` has an analytic local inverse `V_h(p, π)` with `V_h(p₀, π₀) = V₀`
  (`π₀ = D_V L(p₀, V₀)`), and near `((p₀, π₀), V₀)` the solution set of `π = D_V L(p, V)` is
  exactly the graph of `V_h` (local uniqueness).  Proof: the analytic implicit function theorem
  `AnalyticImplicit.analytic_implicit_function` applied to `F((p, π), V) = D_V L(p, V) - π`.
* `legendreHam L x₀ (p, π) = π(V_h) - L(p, V_h)`: `analyticAt_legendreHam` (analytic at
  `(p₀, π₀)`), `hasFDerivAt_legendreHam` and `legendreHam_partials`: near `(p₀, π₀)`,
  `∂_π H = V_h` and `∂_p H = -∂_p L(p, V_h)` (envelope identity).
* Non-vacuity: an `example` with `L(p, v) = v²/2` on `ℝ × ℝ`.

**The canonical ADM coframe and the reduced Lagrangian.**

* `admCoframe E N β` (`e⁰ = N dt`, `eᵃ = E^a_j (dx^j + β^j dt)`; rows internal, columns
  spacetime): `e⁰₀ = N`, `e⁰_j = 0`, `eᵃ_j = E_{aj}`, `eᵃ₀ = Σ_j E_{aj} β^j`.
  `piArr_admCoframe`: `Π_i(e)` does not depend on the lapse and shift; `admCoframe_flat`:
  `admCoframe 1 1 0 = 1`.
* The manuscript does not specify the triad as a function of the spatial metric ("canonical
  ADM coframe"); it is a parameter `triad : (Fin 3 → Fin 3 → ℝ) → (Fin 3 → Fin 3 → ℝ)`
  (e.g. the symmetric square root, `triad(γ)ᵀ triad(γ) = γ`), assumed analytic where needed.
  Metric and velocity fields are `MetF N = Site N → Fin 6 → ℝ` in `Sym₃` coordinates
  `(11, 22, 33, 12, 13, 23)` (`InitialConstraintLinearRange.sym6`, `symMat`); parameters
  `ParF N = MetF N × (Site N → ℝ) × (Site N → Fin 3 → ℝ)` are `(γ, N, β)`.
* `piDot χ triad γ V`: `∂_tΠ_i = D_γ[Π_i(e(γ))](V)`; `hasDerivAt_piArr_coframeField`: it is
  the time derivative of `Π_i` along any metric curve with `γ̇ = V` (any lapse and shift).
* `redLagr χ Λ triad Ast ((γ, N, β), V) = L°(e, ∂_tΠ; 𝒜(e, ∂_tΠ))`: the reduced Lagrangian
  `𝓛°_h(γ, V, N, β)` of `eq:supp-exact-legendre`.  The stationary connection
  `Ast : (e, ∂_tΠ) ↦ 𝒜_h` is a parameter (the stationary connection of
  `ExactStationaryConnection.lean`, assumed analytic at the base point);
  `analyticAt_redLagr`: `𝓛°_h` is analytic when `triad` and `Ast` are and the plaquettes of
  `Ast` lie on the retained branch.

**The canonical Hamiltonian and the initial constraints.**

* `pairH π V = ⟨π, V⟩_h = h³ Σ_x Σ_{ij} π^{ij}(x) V_{ij}(x)` (`h = 1/N`), `pairCov π = ⟨π, ·⟩_h`.
* `legendreVel` (`V_h(γ, π, N, β)`) and `canonicalHamiltonian`
  (`canonicalHamiltonian_eq`: `𝓗_h = ⟨π, V_h⟩_h - 𝓛°_h(γ, V_h, N, β)`,
  `eq:supp-exact-H` = `eq:main-action-hamiltonian`); `canonical_legendre`: on a Legendre chart
  `V_h` is the unique analytic local solution of `D_V 𝓛°_h(γ, V, N, β) = ⟨π, ·⟩_h` and `𝓗_h`
  is analytic; `hasFDerivAt_canonicalHamiltonian`: `D𝓗_h = ⟨·, V_h⟩_h - ∂_{(γ,N,β)}𝓛°_h`.
* `initialConstraint X = (-∇_N 𝓗_h, ∇_β 𝓗_h)|_{N=1, β=0}` (`⟨·,·⟩_h`-gradients,
  `eq:main-action-initial-constraints`), `analyticAt_initialConstraint`, and
  `initialConstraint_eq`: near the base point the rows are `(∇_N 𝓛°_h, -∇_β 𝓛°_h)` evaluated
  at the Legendre velocity `V_h`.

The nonsingularity of the velocity Hessian of `𝓛°_h` is the chart hypothesis of the manuscript
and is carried as a hypothesis (`legendreChart_redLagr`); it is not verified here.
-/

open Filter
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction

section Legendre

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The velocity momentum `D_V L(p, v) = DL(p, v) ∘ inr` (the partial derivative of `L` in the
velocity variable), a covector on `V`. -/
def velMom (L : P × V → ℝ) (x : P × V) : V →L[ℝ] ℝ :=
  fderiv ℝ L x ∘L ContinuousLinearMap.inr ℝ P V

/-- The velocity Hessian `D_V(D_V L)(p, v)`, as a map from velocities to covectors. -/
def velHess (L : P × V → ℝ) (x : P × V) : V →L[ℝ] (V →L[ℝ] ℝ) :=
  fderiv ℝ (fun v => velMom L (x.1, v)) x.2

/-- The Legendre chart hypothesis at `x₀ = (p₀, V₀)`: `L` is analytic at `x₀` and the velocity
Hessian is invertible there (on the Legendre chart the velocity Hessian is nonsingular). -/
def LegendreChart (L : P × V → ℝ) (x₀ : P × V) : Prop :=
  AnalyticAt ℝ L x₀ ∧ (velHess L x₀).IsInvertible

/-- The Legendre residual `F((p, π), V) = D_V L(p, V) - π`, whose zero set is the graph of the
Legendre map `eq:supp-exact-legendre`. -/
def legendreResidual (L : P × V → ℝ) (z : (P × (V →L[ℝ] ℝ)) × V) : V →L[ℝ] ℝ :=
  velMom L (z.1.1, z.2) - z.1.2

/-- The velocity momentum of an analytic Lagrangian is analytic. -/
theorem analyticAt_velMom {L : P × V → ℝ} {x : P × V} (hL : AnalyticAt ℝ L x) :
    AnalyticAt ℝ (velMom L) x := by
  let Φ : ((P × V) →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ V (P × V) ℝ).flip (ContinuousLinearMap.inr ℝ P V)
  have : velMom L = fun y => Φ (fderiv ℝ L y) := rfl
  rw [this]
  exact (Φ.analyticAt _).comp hL.fderiv

/-- The Legendre residual is analytic at `((p₀, D_V L(p₀, V₀)), V₀)`. -/
theorem analyticAt_legendreResidual {L : P × V → ℝ} {x₀ : P × V} (hL : AnalyticAt ℝ L x₀) :
    AnalyticAt ℝ (legendreResidual L) ((x₀.1, velMom L x₀), x₀.2) := by
  have h1 : AnalyticAt ℝ (fun z : (P × (V →L[ℝ] ℝ)) × V => (z.1.1, z.2))
      ((x₀.1, velMom L x₀), x₀.2) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have h2 := (analyticAt_velMom hL).comp_of_eq h1 (by simp)
  exact h2.sub (analyticAt_snd.comp analyticAt_fst)

/-- The velocity derivative of the Legendre residual at the base point is the velocity Hessian. -/
theorem fderiv_legendreResidual_inr {L : P × V → ℝ} {x₀ : P × V} (hL : AnalyticAt ℝ L x₀) :
    fderiv ℝ (legendreResidual L) ((x₀.1, velMom L x₀), x₀.2) ∘L
      ContinuousLinearMap.inr ℝ (P × (V →L[ℝ] ℝ)) V = velHess L x₀ := by
  set z₀ : (P × (V →L[ℝ] ℝ)) × V := ((x₀.1, velMom L x₀), x₀.2)
  have hF := (analyticAt_legendreResidual hL).differentiableAt.hasFDerivAt
  have hin : HasFDerivAt (fun v : V => ((x₀.1, velMom L x₀), v) : V → (P × (V →L[ℝ] ℝ)) × V)
      (ContinuousLinearMap.inr ℝ (P × (V →L[ℝ] ℝ)) V) x₀.2 := by
    exact (hasFDerivAt_const (x₀.1, velMom L x₀) x₀.2).prodMk (hasFDerivAt_id x₀.2)
  have h1 := hF.comp x₀.2 hin
  have hv : AnalyticAt ℝ (fun v : V => velMom L (x₀.1, v)) x₀.2 :=
    (analyticAt_velMom hL).comp_of_eq (analyticAt_const.prod analyticAt_id) (by simp)
  have h2 : HasFDerivAt (fun v : V => legendreResidual L ((x₀.1, velMom L x₀), v))
      (velHess L x₀) x₀.2 := by
    have := hv.differentiableAt.hasFDerivAt.sub_const (velMom L x₀)
    simpa [legendreResidual, velHess] using this
  exact h1.unique h2

/-- **Analytic Legendre inverse** (`eq:supp-exact-legendre`): on a Legendre chart there is an
analytic germ `V_h` at `(p₀, π₀)`, `π₀ = D_V L(p₀, V₀)`, with `V_h(p₀, π₀) = V₀`,
`D_V L(p, V_h(p, π)) = π` near `(p₀, π₀)`, and near `((p₀, π₀), V₀)` the equation
`D_V L(p, V) = π` holds iff `V = V_h(p, π)`. -/
theorem exists_legendre_inverse {L : P × V → ℝ} {x₀ : P × V} (hc : LegendreChart L x₀) :
    ∃ ψ : P × (V →L[ℝ] ℝ) → V, ψ (x₀.1, velMom L x₀) = x₀.2 ∧
      AnalyticAt ℝ ψ (x₀.1, velMom L x₀) ∧
      (∀ᶠ q in 𝓝 (x₀.1, velMom L x₀), velMom L (q.1, ψ q) = q.2) ∧
      (∀ᶠ z in 𝓝 ((x₀.1, velMom L x₀), x₀.2), velMom L (z.1.1, z.2) = z.1.2 ↔ ψ z.1 = z.2) := by
  have hinv : (fderiv ℝ (legendreResidual L) ((x₀.1, velMom L x₀), x₀.2) ∘L
      ContinuousLinearMap.inr ℝ (P × (V →L[ℝ] ℝ)) V).IsInvertible := by
    rw [fderiv_legendreResidual_inr hc.1]; exact hc.2
  obtain ⟨ψ, hψ0, hψ, hsol, huniq, -⟩ :=
    AnalyticImplicit.analytic_implicit_function (analyticAt_legendreResidual hc.1) hinv
  have hz : legendreResidual L ((x₀.1, velMom L x₀), x₀.2) = 0 := by
    simp [legendreResidual]
  refine ⟨ψ, hψ0, hψ, ?_, ?_⟩
  · filter_upwards [hsol] with q hq
    rw [hz, legendreResidual, sub_eq_zero] at hq
    exact hq
  · filter_upwards [huniq] with z hz'
    rw [hz, legendreResidual, sub_eq_zero] at hz'
    exact hz'

open Classical in
/-- The Legendre inverse `V_h` (the germ of `exists_legendre_inverse` on a Legendre chart; the
constant `V₀` off the chart). -/
def legendreInv (L : P × V → ℝ) (x₀ : P × V) : P × (V →L[ℝ] ℝ) → V :=
  if h : LegendreChart L x₀ then Classical.choose (exists_legendre_inverse h) else fun _ => x₀.2

/-- Specification of `legendreInv` on a Legendre chart (see `exists_legendre_inverse`). -/
theorem legendreInv_spec {L : P × V → ℝ} {x₀ : P × V} (hc : LegendreChart L x₀) :
    legendreInv L x₀ (x₀.1, velMom L x₀) = x₀.2 ∧
      AnalyticAt ℝ (legendreInv L x₀) (x₀.1, velMom L x₀) ∧
      (∀ᶠ q in 𝓝 (x₀.1, velMom L x₀), velMom L (q.1, legendreInv L x₀ q) = q.2) ∧
      (∀ᶠ z in 𝓝 ((x₀.1, velMom L x₀), x₀.2),
        velMom L (z.1.1, z.2) = z.1.2 ↔ legendreInv L x₀ z.1 = z.2) := by
  rw [legendreInv, dite_eq_left_of_eq_true (eq_true hc)]
  exact Classical.choose_spec (exists_legendre_inverse hc)

/-- The Legendre transform `H(p, π) = π(V_h(p, π)) - L(p, V_h(p, π))` (`eq:supp-exact-H`). -/
def legendreHam (L : P × V → ℝ) (x₀ : P × V) (q : P × (V →L[ℝ] ℝ)) : ℝ :=
  q.2 (legendreInv L x₀ q) - L (q.1, legendreInv L x₀ q)

/-- **The Legendre transform is analytic** at `(p₀, π₀)` on a Legendre chart. -/
theorem analyticAt_legendreHam {L : P × V → ℝ} {x₀ : P × V} (hc : LegendreChart L x₀) :
    AnalyticAt ℝ (legendreHam L x₀) (x₀.1, velMom L x₀) := by
  obtain ⟨h0, hψ, -, -⟩ := legendreInv_spec hc
  have h1 : AnalyticAt ℝ (fun q : P × (V →L[ℝ] ℝ) => q.2 (legendreInv L x₀ q))
      (x₀.1, velMom L x₀) :=
    ((ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ)).analyticAt_bilinear _).comp
      (analyticAt_snd.prod hψ)
  have h2 : AnalyticAt ℝ (fun q : P × (V →L[ℝ] ℝ) => L (q.1, legendreInv L x₀ q))
      (x₀.1, velMom L x₀) :=
    hc.1.comp_of_eq (analyticAt_fst.prod hψ) (by rw [h0])
  exact h1.sub h2

/-- **Derivative of the Legendre transform**: near `(p₀, π₀)`,
`DH(p, π)(δp, δπ) = δπ(V_h) - DL(p, V_h)(δp, 0)`. -/
theorem hasFDerivAt_legendreHam {L : P × V → ℝ} {x₀ : P × V} (hc : LegendreChart L x₀) :
    ∀ᶠ q in 𝓝 (x₀.1, velMom L x₀), HasFDerivAt (legendreHam L x₀)
      (ContinuousLinearMap.apply ℝ ℝ (legendreInv L x₀ q) ∘L
          ContinuousLinearMap.snd ℝ P (V →L[ℝ] ℝ) -
        fderiv ℝ L (q.1, legendreInv L x₀ q) ∘L ContinuousLinearMap.inl ℝ P V ∘L
          ContinuousLinearMap.fst ℝ P (V →L[ℝ] ℝ)) q := by
  obtain ⟨h0, hψ, hsol, -⟩ := legendreInv_spec hc
  set ψ := legendreInv L x₀
  have hX : AnalyticAt ℝ (fun q : P × (V →L[ℝ] ℝ) => (q.1, ψ q)) (x₀.1, velMom L x₀) :=
    analyticAt_fst.prod hψ
  have hLev : ∀ᶠ q in 𝓝 (x₀.1, velMom L x₀), AnalyticAt ℝ L (q.1, ψ q) := by
    have := hc.1.eventually_analyticAt
    have hx : (fun q : P × (V →L[ℝ] ℝ) => (q.1, ψ q)) (x₀.1, velMom L x₀) = x₀ := by
      simp [h0]
    rw [← hx] at this
    exact hX.continuousAt.eventually this
  filter_upwards [hsol, hψ.eventually_analyticAt, hLev] with q hq hψq hLq
  have hd1 : HasFDerivAt (fun q : P × (V →L[ℝ] ℝ) => q.2 (ψ q))
      (q.2.comp (fderiv ℝ ψ q) + (ContinuousLinearMap.snd ℝ P (V →L[ℝ] ℝ)).flip (ψ q)) q :=
    (hasFDerivAt_snd).clm_apply hψq.differentiableAt.hasFDerivAt
  have hd2 : HasFDerivAt (fun q : P × (V →L[ℝ] ℝ) => L (q.1, ψ q))
      (fderiv ℝ L (q.1, ψ q) ∘L ((ContinuousLinearMap.fst ℝ P (V →L[ℝ] ℝ)).prod
        (fderiv ℝ ψ q))) q :=
    hLq.differentiableAt.hasFDerivAt.comp q
      (hasFDerivAt_fst.prodMk hψq.differentiableAt.hasFDerivAt)
  have hd : HasFDerivAt (legendreHam L x₀) _ q := hd1.sub hd2
  refine hd.congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
  have hsplit : ((δ.1, fderiv ℝ ψ q δ) : P × V) = (δ.1, 0) + (0, fderiv ℝ ψ q δ) := by simp
  have hmom : fderiv ℝ L (q.1, ψ q) (0, fderiv ℝ ψ q δ) = q.2 (fderiv ℝ ψ q δ) := by
    rw [← hq]; rfl
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    add_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.inl_apply]
  rw [hsplit, map_add, hmom]
  ring

/-- **Partial derivatives of the Legendre transform**: near `(p₀, π₀)`, `∂_π H = V_h` (as the
evaluation functional) and `∂_p H = -∂_p L(p, V_h)` (envelope identity). -/
theorem legendreHam_partials {L : P × V → ℝ} {x₀ : P × V} (hc : LegendreChart L x₀) :
    ∀ᶠ q in 𝓝 (x₀.1, velMom L x₀),
      fderiv ℝ (legendreHam L x₀) q ∘L ContinuousLinearMap.inr ℝ P (V →L[ℝ] ℝ) =
          ContinuousLinearMap.apply ℝ ℝ (legendreInv L x₀ q) ∧
        fderiv ℝ (legendreHam L x₀) q ∘L ContinuousLinearMap.inl ℝ P (V →L[ℝ] ℝ) =
          -(fderiv ℝ L (q.1, legendreInv L x₀ q) ∘L ContinuousLinearMap.inl ℝ P V) := by
  filter_upwards [hasFDerivAt_legendreHam hc] with q hq
  rw [hq.fderiv]
  constructor
  · ext φ; simp [Prod.mk_zero_zero]
  · ext δ; simp

/-- Non-vacuity of the Legendre chart hypothesis: `L(p, v) = v²/2` on `ℝ × ℝ` (velocity Hessian
`1`). -/
example : LegendreChart (fun x : ℝ × ℝ => (1 / 2 : ℝ) * (x.2 * x.2)) ((0 : ℝ), (0 : ℝ)) := by
  refine ⟨analyticAt_const.mul (analyticAt_snd.mul analyticAt_snd), ?_⟩
  have hm : velMom (fun x : ℝ × ℝ => (1 / 2 : ℝ) * (x.2 * x.2)) = fun x =>
      x.2 • ContinuousLinearMap.id ℝ ℝ := by
    funext x
    have h : HasFDerivAt (fun x : ℝ × ℝ => (1 / 2 : ℝ) * (x.2 * x.2))
        (x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
      have hs : HasFDerivAt (fun y : ℝ × ℝ => y.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
        hasFDerivAt_snd
      have h0 := (hs.mul hs).const_mul (1 / 2 : ℝ)
      refine h0.congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
      simp
      ring
    rw [velMom, h.fderiv]
    ext
    simp
  have hH : velHess (fun x : ℝ × ℝ => (1 / 2 : ℝ) * (x.2 * x.2)) ((0 : ℝ), (0 : ℝ)) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ ℝ) := by
    rw [velHess, hm]
    exact ((hasFDerivAt_id (0 : ℝ)).smul_const (ContinuousLinearMap.id ℝ ℝ)).fderiv
  rw [hH]
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := ContinuousLinearMap.apply ℝ ℝ 1) ?_ ?_
  · ext; simp
  · ext; simp

end Legendre

/-! ### The canonical ADM coframe -/

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open PalatiniEinsteinAlgebra

/-- **The canonical ADM coframe** `e⁰ = N dt`, `eᵃ = E^a_j(dx^j + β^j dt)` (row `I` internal,
column `μ` spacetime): `e⁰₀ = N`, `e⁰_j = 0`, `eᵃ₀ = Σ_j E_{aj}β^j`, `eᵃ_j = E_{aj}`. -/
def admCoframe (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β : Fin 3 → ℝ) : M4 :=
  Matrix.of fun I μ => Fin.cases (motive := fun _ => ℝ) (Fin.cases (motive := fun _ => ℝ) n
    (fun _ => 0) μ) (fun a => Fin.cases (motive := fun _ => ℝ) (∑ j, E a j * β j)
      (fun j => E a j) μ) I

/-- `e⁰₀ = N`. -/
@[simp] theorem admCoframe_zero_zero (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β : Fin 3 → ℝ) :
    admCoframe E n β 0 0 = n := rfl

/-- `e⁰_j = 0`. -/
@[simp] theorem admCoframe_zero_succ (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β : Fin 3 → ℝ)
    (j : Fin 3) : admCoframe E n β 0 j.succ = 0 := rfl

/-- `eᵃ₀ = Σ_j E_{aj} β^j`. -/
@[simp] theorem admCoframe_succ_zero (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β : Fin 3 → ℝ)
    (a : Fin 3) : admCoframe E n β a.succ 0 = ∑ j, E a j * β j := rfl

/-- `eᵃ_j = E_{aj}`. -/
@[simp] theorem admCoframe_succ_succ (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β : Fin 3 → ℝ)
    (a j : Fin 3) : admCoframe E n β a.succ j.succ = E a j := rfl

/-- The spatial columns `e^I_j` of an ADM coframe (`0` for `I = 0`, `E_{aj}` for `I = a + 1`). -/
def admSpatialCol (E : Fin 3 → Fin 3 → ℝ) (I : Fin 4) (j : Fin 3) : ℝ :=
  Fin.cases (motive := fun _ => ℝ) 0 (fun a => E a j) I

/-- The spatial columns of an ADM coframe do not depend on the lapse and shift. -/
theorem admCoframe_col_succ (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β : Fin 3 → ℝ) (I : Fin 4)
    (j : Fin 3) : admCoframe E n β I j.succ = admSpatialCol E I j := by
  cases I using Fin.cases <;> rfl

set_option maxRecDepth 100000 in
/-- `ε_{0b0d} = 0`. -/
theorem eps4_zero_mid_zero : ∀ b d : Fin 4, eps4 0 b 0 d = 0 := by decide

set_option maxRecDepth 100000 in
/-- `ε_{b00d} = 0`. -/
theorem eps4_mid_zero_zero : ∀ b d : Fin 4, eps4 b 0 0 d = 0 := by decide

/-- `W_{0σ}(e)` involves only the spatial columns of `e`, so for an ADM coframe it does not
depend on the lapse and shift. -/
theorem palCoeff_admCoframe (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β : Fin 3 → ℝ) (σ : Fin 4) :
    palCoeff (admCoframe E n β) 0 σ = palCoeff (admCoframe E 1 0) 0 σ := by
  ext K L
  simp only [palCoeff, Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  cases μ using Fin.cases with
  | zero => simp [epsR, eps4_zero_mid_zero]
  | succ μ =>
    cases ν using Fin.cases with
    | zero => simp [epsR, eps4_mid_zero_zero]
    | succ ν => simp only [admCoframe_col_succ]

/-- **`Π_i` of the canonical ADM coframe does not depend on `(N, β)`**. -/
theorem piArr_admCoframe (χ : ℝ) (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β : Fin 3 → ℝ) (i : Fin 3) :
    piArr χ (admCoframe E n β) i = piArr χ (admCoframe E 1 0) i := by
  rw [piArr, piArr, palCoeff_admCoframe]

/-- **Flat data**: unit triad, unit lapse and zero shift give the unit coframe. -/
theorem admCoframe_flat : admCoframe (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 0 = 1 := by
  ext I μ
  cases I using Fin.cases with
  | zero => cases μ using Fin.cases with
    | zero => exact (Matrix.one_apply_eq (0 : Fin 4)).symm
    | succ j => exact (Matrix.one_apply_ne (Fin.succ_ne_zero j).symm).symm
  | succ a => cases μ using Fin.cases with
    | zero =>
      rw [Matrix.one_apply_ne (Fin.succ_ne_zero a)]
      exact (admCoframe_succ_zero _ _ _ a).trans (by simp)
    | succ j =>
      exact (admCoframe_succ_succ _ _ _ a j).trans (by simp [Matrix.one_apply, Fin.succ_inj])

section AnalyticCoframe

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {q₀ : X}

/-- The ADM coframe depends analytically on `(E, N, β)`. -/
theorem analyticAt_admCoframe_comp {E : X → Fin 3 → Fin 3 → ℝ} {n : X → ℝ} {β : X → Fin 3 → ℝ}
    (hE : AnalyticAt ℝ E q₀) (hn : AnalyticAt ℝ n q₀) (hβ : AnalyticAt ℝ β q₀) :
    AnalyticAt ℝ (fun q => admCoframe (E q) (n q) (β q)) q₀ := by
  refine analyticAt_of_entries fun I μ => ?_
  have hE' : ∀ a j, AnalyticAt ℝ (fun q => E q a j) q₀ := fun a j =>
    analyticAt_pi_apply (analyticAt_pi_apply hE a) j
  have hβ' : ∀ j, AnalyticAt ℝ (fun q => β q j) q₀ := analyticAt_pi_apply hβ
  cases I using Fin.cases with
  | zero => cases μ using Fin.cases with
    | zero => exact hn
    | succ j => exact analyticAt_const
  | succ a => cases μ using Fin.cases with
    | zero =>
      change AnalyticAt ℝ (fun q => ∑ j, E q a j * β q j) q₀
      exact Finset.analyticAt_fun_sum _ fun j _ => (hE' a j).mul (hβ' j)
    | succ j => exact hE' a j

/-- The symmetric `3 × 3` matrix with `Sym₃` coordinates `c` (order `(11, 22, 33, 12, 13, 23)`,
`InitialConstraintLinearRange.sym6`). -/
def symMat (c : Fin 6 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => c (InitialConstraintLinearRange.sym6 i j)

/-- `symMat` is linear, hence analytic. -/
theorem analyticAt_symMat_comp {g : X → Fin 6 → ℝ} (hg : AnalyticAt ℝ g q₀) :
    AnalyticAt ℝ (fun q => symMat (g q)) q₀ :=
  AnalyticAt.pi fun _ => AnalyticAt.pi fun _ => analyticAt_pi_apply hg _

end AnalyticCoframe

/-! ### The reduced Lagrangian -/

/-- The entry `(K, L)` of `Π_i(e)` for the ADM coframe of the metric with `Sym₃` coordinates `g`
(unit lapse, zero shift; by `piArr_admCoframe` the value is the same for all lapses and shifts). -/
def piEntry (χ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ) (i : Fin 3) (K L : Fin 4)
    (g : Fin 6 → ℝ) : ℝ :=
  piArr χ (admCoframe (triad (symMat g)) 1 0) i K L

/-- The entries of `Π_i` of the ADM coframe are analytic in the metric wherever the triad map is. -/
theorem analyticAt_piEntry (χ : ℝ) {triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    {g : Fin 6 → ℝ} (htr : AnalyticAt ℝ triad (symMat g)) (i : Fin 3) (K L : Fin 4) :
    AnalyticAt ℝ (piEntry χ triad i K L) g :=
  analyticAt_entry_comp (analyticAt_piArr_comp χ i (analyticAt_admCoframe_comp
    (htr.comp (analyticAt_symMat_comp analyticAt_id)) analyticAt_const analyticAt_const)) K L

variable {N : ℕ} [NeZero N]

/-- Spatial metric (and metric velocity / momentum) fields in `Sym₃` coordinates. -/
abbrev MetF (N : ℕ) := Site N → Fin 6 → ℝ

/-- Configuration parameters `(γ, N, β)` of the reduced Lagrangian: metric, lapse, shift. -/
abbrev ParF (N : ℕ) := MetF N × (Site N → ℝ) × (Site N → Fin 3 → ℝ)

/-- The canonical ADM coframe field `e(γ, N, β)(x) = admCoframe(triad(γ(x)), N(x), β(x))`. -/
def coframeField (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ) (p : ParF N) :
    Site N → M4 :=
  fun x => admCoframe (triad (symMat (p.1 x))) (p.2.1 x) (p.2.2 x)

/-- The time derivative `∂_tΠ_i(x) = D_γ[Π_i(e(γ(x)))](V(x))` of the electric coefficient arrays
along a metric velocity `γ̇ = V` (`hasDerivAt_piArr_coframeField`). -/
def piDot (χ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ) (γ V : MetF N) :
    Fin 3 → Site N → M4 :=
  fun i x => Matrix.of fun K L => fderiv ℝ (piEntry χ triad i K L) (γ x) (V x)

/-- **The reduced Lagrangian** `𝓛°_h(γ, V, N, β)` of `eq:supp-exact-legendre`: the
phase-compatible Lagrangian at the canonical ADM coframe, with `∂_tΠ` the metric-velocity
derivative, evaluated at the stationary connection `Ast(e, ∂_tΠ)`. -/
def redLagr (χ Λ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ)
    (Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N) (z : ParF N × MetF N) : ℝ :=
  phaseLagr χ Λ (coframeField triad z.1) (piDot χ triad z.1.1 z.2)
    (Ast (coframeField triad z.1, piDot χ triad z.1.1 z.2))

/-- **The reduced Lagrangian is analytic** at `z₀ = ((γ₀, N₀, β₀), V₀)` when the triad map is
analytic at every `γ₀(x)`, the stationary connection map is analytic at `(e₀, ∂_tΠ₀)`, and its
value lies on the retained plaquette branch. -/
theorem analyticAt_redLagr (χ Λ : ℝ) {triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    {Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N} (z₀ : ParF N × MetF N)
    (htr : ∀ x, AnalyticAt ℝ triad (symMat (z₀.1.1 x)))
    (hAst : AnalyticAt ℝ Ast (coframeField triad z₀.1, piDot χ triad z₀.1.1 z₀.2))
    (hbr : PlaqBranch (hN N) (toA (Ast (coframeField triad z₀.1, piDot χ triad z₀.1.1 z₀.2)))) :
    AnalyticAt ℝ (redLagr χ Λ triad Ast) z₀ := by
  have hγ : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => z.1.1 x) z₀ := fun x =>
    analyticAt_pi_apply (analyticAt_fst.comp analyticAt_fst) x
  have hn : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => z.1.2.1 x) z₀ := fun x =>
    analyticAt_pi_apply (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)) x
  have hβ : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => z.1.2.2 x) z₀ := fun x =>
    analyticAt_pi_apply (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)) x
  have hV : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => z.2 x) z₀ := fun x =>
    analyticAt_pi_apply analyticAt_snd x
  have he : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => coframeField triad z.1 x) z₀ :=
    fun x => analyticAt_admCoframe_comp
      ((htr x).comp_of_eq (analyticAt_symMat_comp (hγ x)) rfl) (hn x) (hβ x)
  have hPd : ∀ i x, AnalyticAt ℝ (fun z : ParF N × MetF N => piDot χ triad z.1.1 z.2 i x) z₀ := by
    intro i x
    refine analyticAt_of_entries fun K L => ?_
    have hf : AnalyticAt ℝ (fun z : ParF N × MetF N => fderiv ℝ (piEntry χ triad i K L) (z.1.1 x))
        z₀ := ((analyticAt_piEntry χ (htr x) i K L).fderiv).comp_of_eq (hγ x) rfl
    exact ((ContinuousLinearMap.id ℝ ((Fin 6 → ℝ) →L[ℝ] ℝ)).analyticAt_bilinear _).comp
      (hf.prod (hV x))
  have hE : AnalyticAt ℝ (fun z : ParF N × MetF N => coframeField triad z.1) z₀ :=
    AnalyticAt.pi he
  have hP : AnalyticAt ℝ (fun z : ParF N × MetF N => piDot χ triad z.1.1 z.2) z₀ :=
    AnalyticAt.pi fun i => AnalyticAt.pi fun x => hPd i x
  have hA : AnalyticAt ℝ (fun z : ParF N × MetF N =>
      Ast (coframeField triad z.1, piDot χ triad z.1.1 z.2)) z₀ :=
    hAst.comp_of_eq (hE.prod hP) rfl
  have key : AnalyticAt ℝ (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N =>
      phaseLagr χ Λ q.1 q.2.1 q.2.2) (coframeField triad z₀.1, piDot χ triad z₀.1.1 z₀.2,
        Ast (coframeField triad z₀.1, piDot χ triad z₀.1.1 z₀.2)) :=
    analyticAt_phaseLagr χ Λ _ hbr
  have hG : AnalyticAt ℝ (fun z : ParF N × MetF N => ((coframeField triad z.1,
      piDot χ triad z.1.1 z.2, Ast (coframeField triad z.1, piDot χ triad z.1.1 z.2)) :
        (Site N → M4) × (Fin 3 → Site N → M4) × Conn N)) z₀ :=
    hE.prod (hP.prod hA)
  have hΦ := key.comp_of_eq hG rfl
  exact hΦ

/-! ### The weighted momentum pairing -/

/-- The grid pairing `⟨π, V⟩_h = h³ Σ_x Σ_{ij} π^{ij}(x) V_{ij}(x)` (`h = 1/N`). -/
def pairH (π V : MetF N) : ℝ :=
  hN N ^ 3 * ∑ x, ∑ i, ∑ j, symMat (π x) i j * symMat (V x) i j

/-- The grid pairing as a bilinear map. -/
def pairBil : MetF N →ₗ[ℝ] MetF N →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ pairH
    (fun a b c => by
      simp only [pairH, symMat, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add])
    (fun r a b => by
      simp only [pairH, symMat, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring)
    (fun a b c => by
      simp only [pairH, symMat, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun r a b => by
      simp only [pairH, symMat, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring)

/-- The momentum covector `π ↦ ⟨π, ·⟩_h`. -/
def pairCov : MetF N →L[ℝ] (MetF N →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (MetF N →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (MetF N →L[ℝ] ℝ)).toLinearMap ∘ₗ
      pairBil)

/-- `pairCov π V = ⟨π, V⟩_h`. -/
@[simp] theorem pairCov_apply (π V : MetF N) : pairCov π V = pairH π V := rfl

/-! ### The canonical Hamiltonian -/

/-- The Legendre velocity `V_h(γ, π, N, β)`: the inverse of `π = D_V 𝓛°_h` on the Legendre chart
based at `z₀` (`eq:main-action-legendre-map`). -/
def legendreVel (χ Λ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ)
    (Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N) (z₀ : ParF N × MetF N)
    (p : ParF N) (π : MetF N) : MetF N :=
  legendreInv (redLagr χ Λ triad Ast) z₀ (p, pairCov π)

/-- **The canonical Hamiltonian** `𝓗_h(γ, π, N, β) = ⟨π, V_h⟩_h - 𝓛°_h(γ, V_h, N, β)`
(`eq:supp-exact-H`, `eq:main-action-hamiltonian`). -/
def canonicalHamiltonian (χ Λ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ)
    (Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N) (z₀ : ParF N × MetF N)
    (p : ParF N) (π : MetF N) : ℝ :=
  legendreHam (redLagr χ Λ triad Ast) z₀ (p, pairCov π)

/-- **The displayed Legendre transform** (`eq:main-action-hamiltonian`):
`𝓗_h(γ, π, N, β) = ⟨π, V_h⟩_h - 𝓛°_h(γ, V_h, N, β)`. -/
theorem canonicalHamiltonian_eq (χ Λ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ)
    (Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N) (z₀ : ParF N × MetF N)
    (p : ParF N) (π : MetF N) :
    canonicalHamiltonian χ Λ triad Ast z₀ p π =
      pairH π (legendreVel χ Λ triad Ast z₀ p π) -
        redLagr χ Λ triad Ast (p, legendreVel χ Λ triad Ast z₀ p π) := rfl

/-- The reduced Lagrangian is on a Legendre chart as soon as it is analytic (`analyticAt_redLagr`)
and its velocity Hessian is nonsingular (the chart hypothesis of the manuscript). -/
theorem legendreChart_redLagr (χ Λ : ℝ) {triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    {Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N} (z₀ : ParF N × MetF N)
    (htr : ∀ x, AnalyticAt ℝ triad (symMat (z₀.1.1 x)))
    (hAst : AnalyticAt ℝ Ast (coframeField triad z₀.1, piDot χ triad z₀.1.1 z₀.2))
    (hbr : PlaqBranch (hN N) (toA (Ast (coframeField triad z₀.1, piDot χ triad z₀.1.1 z₀.2))))
    (hHess : (velHess (redLagr χ Λ triad Ast) z₀).IsInvertible) :
    LegendreChart (redLagr χ Λ triad Ast) z₀ :=
  ⟨analyticAt_redLagr χ Λ z₀ htr hAst hbr, hHess⟩

/-- The map `(p, π) ↦ (p, ⟨π, ·⟩_h)` is analytic. -/
theorem analyticAt_momMap (q : ParF N × MetF N) :
    AnalyticAt ℝ (fun q : ParF N × MetF N => (q.1, pairCov q.2)) q :=
  analyticAt_fst.prod (((pairCov (N := N)).analyticAt q.2).comp analyticAt_snd)

/-- **Clause (iii) of `thm:supp-exact-action-provenance`**: on a Legendre chart based at `z₀`, with
`⟨π₀, ·⟩_h = D_V 𝓛°_h(z₀)`, the Legendre velocity `V_h` satisfies `V_h(z₀.1, π₀) = V₀`, is
analytic, solves `D_V 𝓛°_h(γ, V_h, N, β) = ⟨π, ·⟩_h` near `(z₀.1, π₀)`, is the unique local
solution, and the canonical Hamiltonian `𝓗_h` is analytic at `(z₀.1, π₀)`. -/
theorem canonical_legendre (χ Λ : ℝ) {triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    {Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N} {z₀ : ParF N × MetF N}
    (hc : LegendreChart (redLagr χ Λ triad Ast) z₀) {π₀ : MetF N}
    (hπ₀ : pairCov π₀ = velMom (redLagr χ Λ triad Ast) z₀) :
    legendreVel χ Λ triad Ast z₀ z₀.1 π₀ = z₀.2 ∧
      AnalyticAt ℝ (fun q : ParF N × MetF N => legendreVel χ Λ triad Ast z₀ q.1 q.2) (z₀.1, π₀) ∧
      (∀ᶠ q in 𝓝 (z₀.1, π₀), ∀ V, velMom (redLagr χ Λ triad Ast)
        (q.1, legendreVel χ Λ triad Ast z₀ q.1 q.2) V = pairH q.2 V) ∧
      (∀ᶠ w in 𝓝 ((z₀.1, π₀), z₀.2), (∀ V, velMom (redLagr χ Λ triad Ast) (w.1.1, w.2) V =
        pairH w.1.2 V) ↔ legendreVel χ Λ triad Ast z₀ w.1.1 w.1.2 = w.2) ∧
      AnalyticAt ℝ (fun q : ParF N × MetF N => canonicalHamiltonian χ Λ triad Ast z₀ q.1 q.2)
        (z₀.1, π₀) := by
  obtain ⟨h0, hψ, hsol, huniq⟩ := legendreInv_spec hc
  have hm := analyticAt_momMap (z₀.1, π₀)
  have hm0 : (fun q : ParF N × MetF N => (q.1, pairCov q.2)) (z₀.1, π₀) =
      (z₀.1, velMom (redLagr χ Λ triad Ast) z₀) := by simp [hπ₀]
  refine ⟨?_, hψ.comp_of_eq hm hm0, ?_, ?_, (analyticAt_legendreHam hc).comp_of_eq hm hm0⟩
  · change legendreInv _ z₀ (z₀.1, pairCov π₀) = z₀.2
    rw [hπ₀]; exact h0
  · rw [← hm0] at hsol
    filter_upwards [hm.continuousAt.eventually hsol] with q hq V
    change velMom _ (q.1, legendreInv _ z₀ (q.1, pairCov q.2)) V = _
    rw [hq]; rfl
  · have hw : AnalyticAt ℝ (fun w : (ParF N × MetF N) × MetF N => ((w.1.1, pairCov w.1.2), w.2))
        ((z₀.1, π₀), z₀.2) :=
      have h1 : AnalyticAt ℝ (fun w : (ParF N × MetF N) × MetF N => (w.1.1, pairCov w.1.2))
          ((z₀.1, π₀), z₀.2) := hm.comp_of_eq analyticAt_fst rfl
      h1.prod analyticAt_snd
    have hw0 : (fun w : (ParF N × MetF N) × MetF N => ((w.1.1, pairCov w.1.2), w.2))
        ((z₀.1, π₀), z₀.2) = ((z₀.1, velMom (redLagr χ Λ triad Ast) z₀), z₀.2) := by
      simp [hπ₀]
    rw [← hw0] at huniq
    filter_upwards [hw.continuousAt.eventually huniq] with w hw'
    change _ ↔ legendreInv _ z₀ (w.1.1, pairCov w.1.2) = w.2
    rw [← hw']
    constructor
    · intro h; ext V; rw [h]; rfl
    · intro h V; rw [h]; rfl

/-! ### The initial constraint map -/

/-- Reference multipliers `N = 1`, `β = 0`. -/
def refMult (γ : MetF N) : ParF N := (γ, fun _ => 1, fun _ => 0)

/-- The lapse direction `δN = e_x`. -/
def lapseDir (x : Site N) : ParF N × MetF N := ((0, Pi.single x 1, 0), 0)

/-- The shift direction `δβ = e_x ⊗ e_a`. -/
def shiftDir (x : Site N) (a : Fin 3) : ParF N × MetF N :=
  ((0, 0, Pi.single x (Pi.single a 1)), 0)

/-- **The initial constraint map** `𝒞_h(X) = (-∇_N 𝓗_h, ∇_β 𝓗_h)|_{N=1,β=0}`, `X = (γ, π)`
(`eq:main-action-initial-constraints`), with `⟨·,·⟩_h`-gradients `∇_N 𝓗(x) = h⁻³ ∂𝓗/∂N(x)`. -/
def initialConstraint (χ Λ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ)
    (Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N) (z₀ : ParF N × MetF N)
    (X : MetF N × MetF N) : (Site N → ℝ) × (Site N → Fin 3 → ℝ) :=
  (fun x => -((hN N ^ 3)⁻¹ * fderiv ℝ (fun q : ParF N × MetF N =>
      canonicalHamiltonian χ Λ triad Ast z₀ q.1 q.2) (refMult X.1, X.2) (lapseDir x)),
   fun x a => (hN N ^ 3)⁻¹ * fderiv ℝ (fun q : ParF N × MetF N =>
      canonicalHamiltonian χ Λ triad Ast z₀ q.1 q.2) (refMult X.1, X.2) (shiftDir x a))

/-- **The initial constraint map is analytic** at `X₀` when the Legendre chart is based at the
reference multipliers `N = 1`, `β = 0` over `X₀`. -/
theorem analyticAt_initialConstraint (χ Λ : ℝ) {triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    {Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N} {z₀ : ParF N × MetF N}
    (hc : LegendreChart (redLagr χ Λ triad Ast) z₀) (X₀ : MetF N × MetF N)
    (hz : z₀.1 = refMult X₀.1) (hπ₀ : pairCov X₀.2 = velMom (redLagr χ Λ triad Ast) z₀) :
    AnalyticAt ℝ (initialConstraint χ Λ triad Ast z₀) X₀ := by
  have hH := (canonical_legendre χ Λ hc hπ₀).2.2.2.2
  rw [hz] at hH
  have hr : AnalyticAt ℝ (fun X : MetF N × MetF N => (refMult X.1, X.2)) X₀ :=
    (analyticAt_fst.prod analyticAt_const).prod analyticAt_snd
  have hD : AnalyticAt ℝ (fun X : MetF N × MetF N => fderiv ℝ (fun q : ParF N × MetF N =>
      canonicalHamiltonian χ Λ triad Ast z₀ q.1 q.2) (refMult X.1, X.2)) X₀ :=
    hH.fderiv.comp_of_eq hr rfl
  refine AnalyticAt.prod (AnalyticAt.pi fun x => ?_)
    (AnalyticAt.pi fun x => AnalyticAt.pi fun a => ?_)
  · exact (analyticAt_const.mul
      (((ContinuousLinearMap.apply ℝ ℝ (lapseDir x)).analyticAt _).comp hD)).neg
  · exact analyticAt_const.mul
      (((ContinuousLinearMap.apply ℝ ℝ (shiftDir x a)).analyticAt _).comp hD)

/-- **Derivative of the canonical Hamiltonian** near the chart base:
`D𝓗_h(p, π)(δp, δπ) = ⟨δπ, V_h⟩_h - D𝓛°_h(p, V_h)(δp, 0)`. -/
theorem hasFDerivAt_canonicalHamiltonian (χ Λ : ℝ)
    {triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    {Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N} {z₀ : ParF N × MetF N}
    (hc : LegendreChart (redLagr χ Λ triad Ast) z₀) {π₀ : MetF N}
    (hπ₀ : pairCov π₀ = velMom (redLagr χ Λ triad Ast) z₀) :
    ∀ᶠ q in 𝓝 (z₀.1, π₀), HasFDerivAt
      (fun q : ParF N × MetF N => canonicalHamiltonian χ Λ triad Ast z₀ q.1 q.2)
      (ContinuousLinearMap.apply ℝ ℝ (legendreVel χ Λ triad Ast z₀ q.1 q.2) ∘L pairCov ∘L
          ContinuousLinearMap.snd ℝ (ParF N) (MetF N) -
        fderiv ℝ (redLagr χ Λ triad Ast) (q.1, legendreVel χ Λ triad Ast z₀ q.1 q.2) ∘L
          ContinuousLinearMap.inl ℝ (ParF N) (MetF N) ∘L
            ContinuousLinearMap.fst ℝ (ParF N) (MetF N)) q := by
  have hm := analyticAt_momMap (z₀.1, π₀)
  have hm0 : (fun q : ParF N × MetF N => (q.1, pairCov q.2)) (z₀.1, π₀) =
      (z₀.1, velMom (redLagr χ Λ triad Ast) z₀) := by simp [hπ₀]
  have hD := hasFDerivAt_legendreHam hc
  rw [← hm0] at hD
  filter_upwards [hm.continuousAt.eventually hD] with q hq
  have hmq : HasFDerivAt (fun q : ParF N × MetF N => (q.1, pairCov q.2))
      ((ContinuousLinearMap.fst ℝ (ParF N) (MetF N)).prod
        (pairCov ∘L ContinuousLinearMap.snd ℝ (ParF N) (MetF N))) q :=
    hasFDerivAt_fst.prodMk (pairCov.hasFDerivAt.comp q hasFDerivAt_snd)
  have := hq.comp q hmq
  refine this.congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
  simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.inl_apply]
  rfl

/-- **The lapse–shift rows** near the chart base: `𝒞_h(X) = (∇_N 𝓛°_h, -∇_β 𝓛°_h)` at
`(γ, V_h, 1, 0)` (envelope identity). -/
theorem initialConstraint_eq (χ Λ : ℝ) {triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    {Ast : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N} {z₀ : ParF N × MetF N}
    (hc : LegendreChart (redLagr χ Λ triad Ast) z₀) (X₀ : MetF N × MetF N)
    (hz : z₀.1 = refMult X₀.1) (hπ₀ : pairCov X₀.2 = velMom (redLagr χ Λ triad Ast) z₀) :
    ∀ᶠ X in 𝓝 X₀, initialConstraint χ Λ triad Ast z₀ X =
      (fun x => (hN N ^ 3)⁻¹ * fderiv ℝ (redLagr χ Λ triad Ast)
          (refMult X.1, legendreVel χ Λ triad Ast z₀ (refMult X.1) X.2) (lapseDir x),
        fun x a => -((hN N ^ 3)⁻¹ * fderiv ℝ (redLagr χ Λ triad Ast)
          (refMult X.1, legendreVel χ Λ triad Ast z₀ (refMult X.1) X.2) (shiftDir x a))) := by
  have hH := hasFDerivAt_canonicalHamiltonian χ Λ hc hπ₀
  rw [hz] at hH
  have hr : AnalyticAt ℝ (fun X : MetF N × MetF N => (refMult X.1, X.2)) X₀ :=
    (analyticAt_fst.prod analyticAt_const).prod analyticAt_snd
  filter_upwards [hr.continuousAt.eventually hH] with X hX
  rw [initialConstraint, hX.fderiv]
  have h0 : ∀ v : ParF N × MetF N, v.2 = 0 → (pairCov v.2 : MetF N →L[ℝ] ℝ) = 0 := by
    intro v hv; rw [hv, map_zero]
  refine Prod.ext (funext fun x => ?_) (funext fun x => funext fun a => ?_)
  · dsimp only
    simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.inl_apply, h0 (lapseDir x) rfl, zero_apply,
      zero_sub, mul_neg, neg_neg]
    rfl
  · dsimp only
    simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.inl_apply, h0 (shiftDir x a) rfl, zero_apply,
      zero_sub, mul_neg]
    rfl

/-- `piDot` is the time derivative of `Π_i` along the canonical coframe of any metric curve with
`γ̇ = V`, for arbitrary lapse and shift. -/
theorem hasDerivAt_piArr_coframeField (χ : ℝ) {triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    {γ : ℝ → MetF N} {V : MetF N} {t : ℝ} (n : Site N → ℝ) (β : Site N → Fin 3 → ℝ)
    (x : Site N) (i : Fin 3) (K L : Fin 4) (hγ : HasDerivAt γ V t)
    (htr : AnalyticAt ℝ triad (symMat (γ t x))) :
    HasDerivAt (fun s => piArr χ (coframeField triad (γ s, n, β) x) i K L)
      (piDot χ triad (γ t) V i x K L) t := by
  have hfun : (fun s => piArr χ (coframeField triad (γ s, n, β) x) i K L) =
      fun s => piEntry χ triad i K L (γ s x) := by
    funext s
    simp only [coframeField, piEntry]
    rw [piArr_admCoframe]
  rw [hfun]
  have hx : HasDerivAt (fun s => γ s x) (V x) t := hasDerivAt_pi.1 hγ x
  exact (analyticAt_piEntry χ htr i K L).differentiableAt.hasFDerivAt.comp_hasDerivAt t hx

end RenewalGeometry.ExactPhaseAction
