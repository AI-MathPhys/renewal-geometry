/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Analysis.AnalyticImplicitFunction

/-!
# The analytic Legendre transform and its Hamiltonian on Banach spaces

Banach spaces `P` of parameters and `V` of velocities, momenta in the dual `V →L[ℝ] ℝ`:

* `velMom L x = D_V L(x)`, `velHess L x = D_V(D_V L)(x)`, and the chart hypothesis
  `LegendreChart L x₀`: `L` analytic at `x₀` and the velocity Hessian invertible there.
* `exists_legendre_inverse` / `legendreInv_spec`: on a Legendre chart the Legendre map
  `π = D_V L(p, V)` has an analytic local inverse `V_h(p, π)` with `V_h(p₀, π₀) = V₀`, and near
  `((p₀, π₀), V₀)` the solution set of `π = D_V L(p, V)` is exactly the graph of `V_h` (analytic
  implicit function theorem applied to `F((p, π), V) = D_V L(p, V) - π`).
* `legendreHam L x₀ (p, π) = π(V_h) - L(p, V_h)`: `analyticAt_legendreHam`,
  `hasFDerivAt_legendreHam` and `legendreHam_partials` (`∂_π H = V_h`,
  `∂_p H = -∂_p L(p, V_h)`, the envelope identity).
* Non-vacuity: an `example` with `L(p, v) = v²/2` on `ℝ × ℝ`.

Split out of `ExactLegendreHamiltonian` (declaration names unchanged), which applies it to the
reduced ADM Lagrangian.
-/

open Filter
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace MathPhys.ExactPhaseAction

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

end MathPhys.ExactPhaseAction
