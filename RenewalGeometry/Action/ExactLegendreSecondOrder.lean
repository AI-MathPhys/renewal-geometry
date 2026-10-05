/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactLegendreHamiltonian

/-!
# Second-order jet of the analytic Legendre transform
  (`eq:supp-exact-legendre`, `eq:supp-exact-H`; ingredient of
  `thm:supp-exact-action-provenance` (iv), emergent-spacetime manuscript)

For the generic analytic Legendre transform of `ExactLegendreHamiltonian.lean`
(`H(p, π) = π(V_h) - L(p, V_h)` on a Legendre chart based at `x₀ = (p₀, V₀)`,
`π₀ = D_V L(x₀)`):

* `velHess_apply`: the velocity Hessian is the `VV` block of the second derivative,
  `velHess L x₀ u v = D²L(x₀)(0, u)(0, v)`.
* `legendreHam_apply_base`, `fderiv_legendreHam_base`: `H(p₀, π₀) = π₀(V₀) - L(x₀)` and
  `DH(p₀, π₀)(δp, δπ) = δπ(V₀) - DL(x₀)(δp, 0)`.
* **`fderiv_fderiv_legendreHam`** (second-order Legendre formula):
  `D²H(p₀, π₀)(δp, δπ)(δp', δπ') = δπ'(w) - D²L(x₀)(δp, w)(δp', 0)`, where `w` is the (unique)
  velocity with `D²L(x₀)(δp, w)(0, ·) = δπ` — the linearized Legendre map.  For a quadratic
  Lagrangian this is the Legendre transform of the quadratic form.
-/

open Filter
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.QuadJet

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **The velocity Hessian is the `VV` block of the second derivative.** -/
theorem velHess_apply {L : P × V → ℝ} {x₀ : P × V} (hL : AnalyticAt ℝ L x₀) (u v : V) :
    velHess L x₀ u v = fderiv ℝ (fderiv ℝ L) x₀ (0, u) (0, v) := by
  have hD : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) x₀) x₀ :=
    hL.fderiv.differentiableAt.hasFDerivAt
  have hin : HasFDerivAt (fun v : V => ((x₀.1, v) : P × V)) (ContinuousLinearMap.inr ℝ P V) x₀.2 :=
    (hasFDerivAt_const x₀.1 x₀.2).prodMk (hasFDerivAt_id x₀.2)
  have h1 : HasFDerivAt (fun v : V => fderiv ℝ L (x₀.1, v))
      (fderiv ℝ (fderiv ℝ L) x₀ ∘L ContinuousLinearMap.inr ℝ P V) x₀.2 :=
    hD.comp x₀.2 hin
  have h2 : HasFDerivAt (fun v : V => velMom L (x₀.1, v))
      (((ContinuousLinearMap.compL ℝ V (P × V) ℝ).flip (ContinuousLinearMap.inr ℝ P V)) ∘L
        (fderiv ℝ (fderiv ℝ L) x₀ ∘L ContinuousLinearMap.inr ℝ P V)) x₀.2 :=
    (((ContinuousLinearMap.compL ℝ V (P × V) ℝ).flip
      (ContinuousLinearMap.inr ℝ P V)).hasFDerivAt).comp x₀.2 h1
  rw [velHess, h2.fderiv]
  simp

/-- The value of the Legendre transform at the base point. -/
theorem legendreHam_apply_base {L : P × V → ℝ} {x₀ : P × V} (hc : LegendreChart L x₀) :
    legendreHam L x₀ (x₀.1, velMom L x₀) = velMom L x₀ x₀.2 - L x₀ := by
  obtain ⟨h0, -, -, -⟩ := legendreInv_spec hc
  simp [legendreHam, h0]

/-- The first derivative of the Legendre transform at the base point. -/
theorem fderiv_legendreHam_base {L : P × V → ℝ} {x₀ : P × V} (hc : LegendreChart L x₀)
    (δq : P × (V →L[ℝ] ℝ)) :
    fderiv ℝ (legendreHam L x₀) (x₀.1, velMom L x₀) δq = δq.2 x₀.2 - fderiv ℝ L x₀ (δq.1, 0) := by
  obtain ⟨h0, -, -, -⟩ := legendreInv_spec hc
  have h := (hasFDerivAt_legendreHam hc).self_of_nhds
  rw [h.fderiv]
  simp [h0]

/-- **Second-order Legendre formula.**  On a Legendre chart,
`D²H(p₀, π₀)(δp, δπ)(δp', δπ') = δπ'(w) - D²L(x₀)(δp, w)(δp', 0)` for every `w` solving the
linearized Legendre map `D²L(x₀)(δp, w)(0, v) = δπ(v)` (`∀ v`). -/
theorem fderiv_fderiv_legendreHam {L : P × V → ℝ} {x₀ : P × V} (hc : LegendreChart L x₀)
    (δq δq' : P × (V →L[ℝ] ℝ)) (w : V)
    (hw : ∀ v, fderiv ℝ (fderiv ℝ L) x₀ (δq.1, w) (0, v) = δq.2 v) :
    fderiv ℝ (fderiv ℝ (legendreHam L x₀)) (x₀.1, velMom L x₀) δq δq' =
      δq'.2 w - fderiv ℝ (fderiv ℝ L) x₀ (δq.1, w) (δq'.1, 0) := by
  obtain ⟨h0, hψ, hsol, -⟩ := legendreInv_spec hc
  set ψ := legendreInv L x₀ with hψdef
  set q₀ : P × (V →L[ℝ] ℝ) := (x₀.1, velMom L x₀) with hq₀
  set D2 := fderiv ℝ (fderiv ℝ L) x₀ with hD2
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ q₀) q₀ := hψ.differentiableAt.hasFDerivAt
  set Dψ := fderiv ℝ ψ q₀ with hDψ
  have hX : HasFDerivAt (fun q : P × (V →L[ℝ] ℝ) => ((q.1, ψ q) : P × V))
      ((ContinuousLinearMap.fst ℝ P (V →L[ℝ] ℝ)).prod Dψ) q₀ := hasFDerivAt_fst.prodMk hψd
  have hXq₀ : (fun q : P × (V →L[ℝ] ℝ) => ((q.1, ψ q) : P × V)) q₀ = x₀ := by
    show (q₀.1, ψ q₀) = x₀
    rw [h0]
  have hDL : HasFDerivAt (fderiv ℝ L) D2 ((fun q : P × (V →L[ℝ] ℝ) => ((q.1, ψ q) : P × V)) q₀) := by
    rw [hXq₀]; exact hc.1.fderiv.differentiableAt.hasFDerivAt
  have hDLc : HasFDerivAt (fun q : P × (V →L[ℝ] ℝ) => fderiv ℝ L (q.1, ψ q))
      (D2 ∘L (ContinuousLinearMap.fst ℝ P (V →L[ℝ] ℝ)).prod Dψ) q₀ := hDL.comp q₀ hX
  -- evaluations of `q ↦ DL(q.1, ψ q)` at fixed vectors
  have hEval : ∀ y : P × V, HasFDerivAt (fun q : P × (V →L[ℝ] ℝ) => fderiv ℝ L (q.1, ψ q) y)
      ((ContinuousLinearMap.apply ℝ ℝ y) ∘L (D2 ∘L (ContinuousLinearMap.fst ℝ P (V →L[ℝ] ℝ)).prod Dψ))
      q₀ := fun y =>
    HasFDerivAt.comp (g := ⇑(ContinuousLinearMap.apply ℝ ℝ y : ((P × V) →L[ℝ] ℝ) →L[ℝ] ℝ))
      (f := fun q : P × (V →L[ℝ] ℝ) => fderiv ℝ L (q.1, ψ q)) q₀
      (ContinuousLinearMap.hasFDerivAt _) hDLc
  -- the linearized Legendre map: `D²L(x₀)(δp, Dψ δq)(0, ·) = δπ`
  have hmom : ∀ v, D2 (δq.1, Dψ δq) (0, v) = δq.2 v := by
    intro v
    have hEv : (fun q : P × (V →L[ℝ] ℝ) => fderiv ℝ L (q.1, ψ q) (0, v)) =ᶠ[𝓝 q₀]
        fun q => q.2 v := by
      filter_upwards [hsol] with q hq
      have := congrArg (fun T : V →L[ℝ] ℝ => T v) hq
      simpa [velMom] using this
    have hB : HasFDerivAt (fun q : P × (V →L[ℝ] ℝ) => q.2 v)
        ((ContinuousLinearMap.apply ℝ ℝ v) ∘L ContinuousLinearMap.snd ℝ P (V →L[ℝ] ℝ)) q₀ :=
      HasFDerivAt.comp (g := ⇑(ContinuousLinearMap.apply ℝ ℝ v : (V →L[ℝ] ℝ) →L[ℝ] ℝ))
        (f := fun q : P × (V →L[ℝ] ℝ) => q.2) q₀ (ContinuousLinearMap.hasFDerivAt _) hasFDerivAt_snd
    have heq := (hEval (0, v)).unique (hB.congr_of_eventuallyEq hEv)
    have := congrArg (fun T => T δq) heq
    simpa using this
  -- `Dψ δq = w` by injectivity of the velocity Hessian
  have hw' : Dψ δq = w := by
    have hinj : Function.Injective (velHess L x₀) := by
      obtain ⟨e, he⟩ := hc.2
      rw [← he]; exact e.injective
    apply sub_eq_zero.1
    apply hinj
    rw [map_zero]
    ext v
    rw [velHess_apply hc.1]
    have e1 : ((0 : P), Dψ δq - w) = (δq.1, Dψ δq) - (δq.1, w) := by simp
    rw [e1, map_sub]
    simp only [sub_apply, zero_apply]
    rw [hmom v, ← hD2, hw v, sub_self]
  -- reduce to the derivative of a scalar function
  have hHan : AnalyticAt ℝ (legendreHam L x₀) q₀ := analyticAt_legendreHam hc
  have hfd : DifferentiableAt ℝ (fderiv ℝ (legendreHam L x₀)) q₀ := hHan.fderiv.differentiableAt
  have hred : fderiv ℝ (fderiv ℝ (legendreHam L x₀)) q₀ δq δq' =
      fderiv ℝ (fun q => fderiv ℝ (legendreHam L x₀) q δq') q₀ δq := by
    rw [fderiv_clm_apply hfd (differentiableAt_const δq')]
    simp
  rw [hred]
  have hK : (fun q => fderiv ℝ (legendreHam L x₀) q δq') =ᶠ[𝓝 q₀] fun q =>
      δq'.2 (ψ q) - fderiv ℝ L (q.1, ψ q) (δq'.1, 0) := by
    filter_upwards [hasFDerivAt_legendreHam hc] with q hq
    rw [hq.fderiv]
    simp [hψdef]
  rw [hK.fderiv_eq]
  have h1 : HasFDerivAt (fun q : P × (V →L[ℝ] ℝ) => δq'.2 (ψ q)) (δq'.2 ∘L Dψ) q₀ :=
    HasFDerivAt.comp (g := ⇑δq'.2) (f := ψ) q₀ (ContinuousLinearMap.hasFDerivAt _) hψd
  rw [(h1.fun_sub (hEval (δq'.1, 0))).fderiv]
  simp [hw']

end RenewalGeometry.ExactPhaseAction.QuadJet
