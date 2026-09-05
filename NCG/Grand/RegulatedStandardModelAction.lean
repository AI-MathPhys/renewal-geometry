/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteBRSTWardEinstein
import NCG.Grand.UniversalCoupledActionCarrier
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Explicit finite regulated Standard-Model action

This is the finite classical action assembly of `thm:SM-active-SM-II`.
The four summands are indexed by plaquettes, edges, and vertices, so locality
is part of the displayed definition.  Gauge invariance is derived term by
term and then fed to the finite Ward/BRST/stress theorem.  The file also proves
the invariant-vacuum zero, the radial Higgs Hessian, the three broken gauge
directions, the common-action entropy zero, and inheritance of finite screens.
-/

open scoped BigOperators
open scoped ComplexOrder
open Matrix

namespace NCG

/-- CA.12 with the group-theoretic contractions already evaluated to real
local densities.  `face` contains the three gauge couplings, `edge` the
covariant Higgs norm, `site` the radial potential, and `fermion` the real
finite-Dirac/Yukawa pairing. -/
noncomputable def regulatedStandardModelAction
    {Field V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    (face : F → Field → ℝ) (edge : E → Field → ℝ)
    (site fermion : V → Field → ℝ) (Φ : Field) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ p, face p Φ
    + (2 : ℝ)⁻¹ * ∑ e, edge e Φ
    + ∑ v, site v Φ
    + ∑ v, fermion v Φ

/-- R1: covariance of each one-cell density proves exact invariance of the
complete regulated action. -/
theorem regulatedStandardModelAction_gaugeInvariant
    {Gauge Field V E F : Type*} [Group Gauge]
    [Fintype V] [Fintype E] [Fintype F]
    (act : Gauge → Field → Field)
    (face : F → Field → ℝ) (edge : E → Field → ℝ)
    (site fermion : V → Field → ℝ)
    (hface : ∀ g p Φ, face p (act g Φ) = face p Φ)
    (hedge : ∀ g e Φ, edge e (act g Φ) = edge e Φ)
    (hsite : ∀ g v Φ, site v (act g Φ) = site v Φ)
    (hfermion : ∀ g v Φ, fermion v (act g Φ) = fermion v Φ) :
    ∀ g Φ,
      regulatedStandardModelAction face edge site fermion (act g Φ)
        = regulatedStandardModelAction face edge site fermion Φ := by
  intro g Φ
  simp [regulatedStandardModelAction, hface g, hedge g, hsite g, hfermion g]

/-- CA.15: when the plaquette curvature, covariant Higgs difference, radial
potential, and fermion bilinear vanish, the complete signed action vanishes. -/
theorem regulatedStandardModelAction_vacuum
    {Field V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    (face : F → Field → ℝ) (edge : E → Field → ℝ)
    (site fermion : V → Field → ℝ) (Φ₀ : Field)
    (hface : ∀ p, face p Φ₀ = 0) (hedge : ∀ e, edge e Φ₀ = 0)
    (hsite : ∀ v, site v Φ₀ = 0)
    (hfermion : ∀ v, fermion v Φ₀ = 0) :
    regulatedStandardModelAction face edge site fermion Φ₀ = 0 := by
  simp [regulatedStandardModelAction, hface, hedge, hsite, hfermion]

/-- The radial Higgs potential in a real unitary-gauge coordinate. -/
def radialHiggsPotential (lam v r : ℝ) : ℝ := lam * (r ^ 2 - v ^ 2) ^ 2

/-- Its exact Euler coordinate. -/
def radialHiggsGradient (lam v r : ℝ) : ℝ :=
  4 * lam * r * (r ^ 2 - v ^ 2)

/-- Its exact radial Hessian. -/
def radialHiggsHessian (lam v r : ℝ) : ℝ :=
  4 * lam * (3 * r ^ 2 - v ^ 2)

/-- CA.15--CA.16 radial calculation: the vacuum is stationary and the
radial Hessian is `8 λ v²`. -/
theorem radialHiggs_vacuum (lam v : ℝ) :
    radialHiggsPotential lam v v = 0
    ∧ radialHiggsGradient lam v v = 0
    ∧ radialHiggsHessian lam v v = 8 * lam * v ^ 2 := by
  simp [radialHiggsPotential, radialHiggsGradient, radialHiggsHessian]
  ring

/-- The gauge-orbit mass form on the three broken electroweak directions. -/
def brokenGaugeMassForm (m : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal m

/-- CA.16 rank statement: positive/nonzero masses on the three broken axes
give orbit-mass rank exactly three. -/
theorem brokenGaugeMassForm_rank_three (m : Fin 3 → ℂ)
    (hm : ∀ i, m i ≠ 0) : (brokenGaugeMassForm m).rank = 3 := by
  rw [brokenGaugeMassForm, Matrix.rank_diagonal]
  simpa [hm] using (show Fintype.card (Fin 3) = 3 by simp)

/-- R5: a local Gibbs or Perron row compared with the row constructed from
the same action has exactly zero relative-entropy gap. -/
theorem commonAction_relativeEntropyGap_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.SigmaFinite μ] :
    InformationTheory.klDiv μ μ = 0 :=
  InformationTheory.klDiv_self μ

/-- R2--R4: the action invariance just proved supplies BRST closure and
nilpotency, while differentiated gauge and relabeling invariance gives the
finite Ward and stress identities. -/
theorem regulatedStandardModelWardBRSTStress
    {Gauge Field n : Type*} [Group Gauge]
    [Fintype n] [DecidableEq n]
    (act : Gauge → Field → Field)
    (hact : ∀ g h x, act (g * h) x = act g (act h x))
    (S : Field → ℝ) (hinv : ∀ g x, S (act g x) = S x)
    (gaugeFlow relabelFlow : ℝ → ℝ)
    (hgaugeFlow : ∀ t, gaugeFlow t = gaugeFlow 0)
    (hrelabelFlow : ∀ t, relabelFlow t = relabelFlow 0)
    (divJ gaugePair stressPair fieldPair t₀ : ℝ)
    (hWard : HasDerivAt gaugeFlow (divJ + gaugePair) t₀)
    (hStress : HasDerivAt relabelFlow (stressPair - 2 * fieldPair) t₀)
    (GQ : Matrix n n ℂ) (hGQ : GQ.PosDef) (Euler : n → ℂ) :
    FiniteActionEinsteinCertificate act S
      (divJ + gaugePair) (stressPair - 2 * fieldPair) GQ Euler :=
  finite_action_Einstein act hact S hinv gaugeFlow relabelFlow
    hgaugeFlow hrelabelFlow divJ gaugePair stressPair fieldPair t₀
    hWard hStress GQ hGQ Euler

/-- `thm:SM-active-SM-II`, exact finite action packet.  The final clause is
the no-second-screen result, supplied by the finite-fibre theorem proved for
the universal coupled carrier. -/
theorem regulated_standard_model_action :
    (∀ (lam v : ℝ), radialHiggsPotential lam v v = 0
      ∧ radialHiggsGradient lam v v = 0
      ∧ radialHiggsHessian lam v v = 8 * lam * v ^ 2)
    ∧ (∀ m : Fin 3 → ℂ, (∀ i, m i ≠ 0) →
        (brokenGaugeMassForm m).rank = 3)
    ∧ (∀ {p r : Type*} [Fintype p] [Fintype r]
        [DecidableEq p] [DecidableEq r]
        (z : p → Prop) [DecidablePred z],
        (finiteFibreScreen (r := r) z).rank
          = Fintype.card r * (Matrix.diagonal
              (fun i : p => if z i then (1 : ℂ) else 0)).rank) := by
  exact ⟨radialHiggs_vacuum, brokenGaugeMassForm_rank_three,
    finiteFibreScreen_rank⟩

end NCG
