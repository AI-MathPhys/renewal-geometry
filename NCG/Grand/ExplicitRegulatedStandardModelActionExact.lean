/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RegulatedStandardModelAction
import NCG.Grand.StandardModelHiggsStabilizerExact

/-!
# The explicit regulated Standard-Model field and action packet

This removes the opaque-field scope change in the first encoding of
`thm:SM-active-SM-II`.  A configuration now literally contains link gauge
variables, vertex Higgs variables, spinors, and independent dual spinors.
The regulated action has the four CA.12 summands, indexed respectively by
plaquettes, edges, and vertices.  Component covariance proves invariance of
this same action, which is then passed to the finite Ward/BRST/stress theorem.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace NCG

/-- A finite classical Standard-Model configuration on one active carrier. -/
structure RegulatedSMConfiguration
    (V E Gauge Higgs Spinor DualSpinor : Type*) where
  gaugeLink : E → Gauge
  higgs : V → Higgs
  spinor : V → Spinor
  dualSpinor : V → DualSpinor

/-- The literal four-term Euclidean action CA.12.  `faceEnergy` contains the
three invariant gauge-metric coefficients, `edgeEnergy` the companion-Hodge
covariant Higgs norm, `higgsNormSq` the vertex Higgs norm, and
`fermionEnergy` the real finite-Dirac/Yukawa pairing with its independent dual
amplitude. -/
noncomputable def explicitRegulatedStandardModelAction
    {V E F Gauge Higgs Spinor DualSpinor : Type*}
    [Fintype V] [Fintype E] [Fintype F]
    (faceEnergy : F → (E → Gauge) → ℝ)
    (edgeEnergy : E → (E → Gauge) → (V → Higgs) → ℝ)
    (vertexMass : V → ℝ) (higgsNormSq : Higgs → ℝ)
    (lambdaH vacuumNormSq : ℝ)
    (fermionEnergy : V → (E → Gauge) → (V → Higgs) →
      (V → Spinor) → (V → DualSpinor) → ℝ)
    (Phi : RegulatedSMConfiguration V E Gauge Higgs Spinor DualSpinor) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ p, faceEnergy p Phi.gaugeLink
    + (2 : ℝ)⁻¹ * ∑ e, edgeEnergy e Phi.gaugeLink Phi.higgs
    + ∑ v, vertexMass v * lambdaH *
        (higgsNormSq (Phi.higgs v) - vacuumNormSq) ^ 2
    + ∑ v, fermionEnergy v Phi.gaugeLink Phi.higgs
        Phi.spinor Phi.dualSpinor

/-- The one-cell decomposition is definitional and hence gives a
cutoff-independent support radius: every summand is attached to one face,
edge, or vertex. -/
theorem explicitRegulatedStandardModelAction_local_decomposition
    {V E F Gauge Higgs Spinor DualSpinor : Type*}
    [Fintype V] [Fintype E] [Fintype F]
    (faceEnergy : F → (E → Gauge) → ℝ)
    (edgeEnergy : E → (E → Gauge) → (V → Higgs) → ℝ)
    (vertexMass : V → ℝ) (higgsNormSq : Higgs → ℝ)
    (lambdaH vacuumNormSq : ℝ)
    (fermionEnergy : V → (E → Gauge) → (V → Higgs) →
      (V → Spinor) → (V → DualSpinor) → ℝ)
    (Phi : RegulatedSMConfiguration V E Gauge Higgs Spinor DualSpinor) :
    explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
        higgsNormSq lambdaH vacuumNormSq fermionEnergy Phi =
      (2 : ℝ)⁻¹ * ∑ p, faceEnergy p Phi.gaugeLink
      + (2 : ℝ)⁻¹ * ∑ e, edgeEnergy e Phi.gaugeLink Phi.higgs
      + ∑ v, vertexMass v * lambdaH *
          (higgsNormSq (Phi.higgs v) - vacuumNormSq) ^ 2
      + ∑ v, fermionEnergy v Phi.gaugeLink Phi.higgs
          Phi.spinor Phi.dualSpinor := rfl

/-- Gauge covariance of each CA.12 cell proves exact invariance of the action
on the explicit configuration type. -/
theorem explicitRegulatedStandardModelAction_gaugeInvariant
    {V E F Gauge Higgs Spinor DualSpinor : Type*}
    [Fintype V] [Fintype E] [Fintype F]
    (LocalGauge : Type*) [Group LocalGauge]
    (transform : LocalGauge →
      RegulatedSMConfiguration V E Gauge Higgs Spinor DualSpinor →
        RegulatedSMConfiguration V E Gauge Higgs Spinor DualSpinor)
    (faceEnergy : F → (E → Gauge) → ℝ)
    (edgeEnergy : E → (E → Gauge) → (V → Higgs) → ℝ)
    (vertexMass : V → ℝ) (higgsNormSq : Higgs → ℝ)
    (lambdaH vacuumNormSq : ℝ)
    (fermionEnergy : V → (E → Gauge) → (V → Higgs) →
      (V → Spinor) → (V → DualSpinor) → ℝ)
    (hface : ∀ g p Phi, faceEnergy p (transform g Phi).gaugeLink =
      faceEnergy p Phi.gaugeLink)
    (hedge : ∀ g e Phi,
      edgeEnergy e (transform g Phi).gaugeLink (transform g Phi).higgs =
        edgeEnergy e Phi.gaugeLink Phi.higgs)
    (hhiggs : ∀ g v Phi,
      higgsNormSq ((transform g Phi).higgs v) =
        higgsNormSq (Phi.higgs v))
    (hfermion : ∀ g v Phi,
      fermionEnergy v (transform g Phi).gaugeLink (transform g Phi).higgs
          (transform g Phi).spinor (transform g Phi).dualSpinor =
        fermionEnergy v Phi.gaugeLink Phi.higgs Phi.spinor Phi.dualSpinor) :
    ∀ g Phi,
      explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
          higgsNormSq lambdaH vacuumNormSq fermionEnergy (transform g Phi) =
        explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
          higgsNormSq lambdaH vacuumNormSq fermionEnergy Phi := by
  intro g Phi
  simp only [explicitRegulatedStandardModelAction, hface g, hedge g,
    hhiggs g, hfermion g]

/-- The periodic internal configuration is a zero-action vacuum when its
curvature, covariant Higgs difference, radial defect, and fermion field all
vanish. -/
theorem explicitRegulatedStandardModelAction_vacuum
    {V E F Gauge Higgs Spinor DualSpinor : Type*}
    [Fintype V] [Fintype E] [Fintype F]
    (faceEnergy : F → (E → Gauge) → ℝ)
    (edgeEnergy : E → (E → Gauge) → (V → Higgs) → ℝ)
    (vertexMass : V → ℝ) (higgsNormSq : Higgs → ℝ)
    (lambdaH vacuumNormSq : ℝ)
    (fermionEnergy : V → (E → Gauge) → (V → Higgs) →
      (V → Spinor) → (V → DualSpinor) → ℝ)
    (Phi0 : RegulatedSMConfiguration V E Gauge Higgs Spinor DualSpinor)
    (hface : ∀ p, faceEnergy p Phi0.gaugeLink = 0)
    (hedge : ∀ e, edgeEnergy e Phi0.gaugeLink Phi0.higgs = 0)
    (hhiggs : ∀ v, higgsNormSq (Phi0.higgs v) = vacuumNormSq)
    (hfermion : ∀ v, fermionEnergy v Phi0.gaugeLink Phi0.higgs
      Phi0.spinor Phi0.dualSpinor = 0) :
    explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
      higgsNormSq lambdaH vacuumNormSq fermionEnergy Phi0 = 0 := by
  simp [explicitRegulatedStandardModelAction, hface, hedge, hhiggs, hfermion]

/-- **Explicit regulated classical Standard-Model action on the active
carrier (`thm:SM-active-SM-II`).**  This assembles locality, invariance,
Ward/BRST/stress, the periodic vacuum, the Higgs Hessian, the three broken
directions, common-action entropy, and inheritance of finite-fibre screens
for the same CA.12 action. -/
theorem explicit_regulated_standard_model_action_exact
    {V E F Gauge Higgs Spinor DualSpinor n Omega : Type*}
    [Fintype V] [Fintype E] [Fintype F] [Fintype n] [DecidableEq n]
    [MeasurableSpace Omega] [Group Gauge]
    (transform : Gauge →
      RegulatedSMConfiguration V E Gauge Higgs Spinor DualSpinor →
        RegulatedSMConfiguration V E Gauge Higgs Spinor DualSpinor)
    (htransform : ∀ g h Phi, transform (g * h) Phi = transform g (transform h Phi))
    (faceEnergy : F → (E → Gauge) → ℝ)
    (edgeEnergy : E → (E → Gauge) → (V → Higgs) → ℝ)
    (vertexMass : V → ℝ) (higgsNormSq : Higgs → ℝ)
    (lambdaH vacuumNormSq : ℝ)
    (fermionEnergy : V → (E → Gauge) → (V → Higgs) →
      (V → Spinor) → (V → DualSpinor) → ℝ)
    (hface : ∀ g p Phi, faceEnergy p (transform g Phi).gaugeLink =
      faceEnergy p Phi.gaugeLink)
    (hedge : ∀ g e Phi,
      edgeEnergy e (transform g Phi).gaugeLink (transform g Phi).higgs =
        edgeEnergy e Phi.gaugeLink Phi.higgs)
    (hhiggs : ∀ g v Phi,
      higgsNormSq ((transform g Phi).higgs v) = higgsNormSq (Phi.higgs v))
    (hfermion : ∀ g v Phi,
      fermionEnergy v (transform g Phi).gaugeLink (transform g Phi).higgs
          (transform g Phi).spinor (transform g Phi).dualSpinor =
        fermionEnergy v Phi.gaugeLink Phi.higgs Phi.spinor Phi.dualSpinor)
    (Phi0 : RegulatedSMConfiguration V E Gauge Higgs Spinor DualSpinor)
    (hface0 : ∀ p, faceEnergy p Phi0.gaugeLink = 0)
    (hedge0 : ∀ e, edgeEnergy e Phi0.gaugeLink Phi0.higgs = 0)
    (hhiggs0 : ∀ v, higgsNormSq (Phi0.higgs v) = vacuumNormSq)
    (hfermion0 : ∀ v, fermionEnergy v Phi0.gaugeLink Phi0.higgs
      Phi0.spinor Phi0.dualSpinor = 0)
    (gaugeFlow relabelFlow : ℝ → ℝ)
    (hgaugeFlow : ∀ t, gaugeFlow t = gaugeFlow 0)
    (hrelabelFlow : ∀ t, relabelFlow t = relabelFlow 0)
    (divJ gaugePair stressPair fieldPair t0 : ℝ)
    (hWard : HasDerivAt gaugeFlow (divJ + gaugePair) t0)
    (hStress : HasDerivAt relabelFlow (stressPair - 2 * fieldPair) t0)
    (GQ : Matrix n n ℂ) (hGQ : GQ.PosDef) (Euler : n → ℂ)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.SigmaFinite mu] :
    (∀ Phi,
      explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
        higgsNormSq lambdaH vacuumNormSq fermionEnergy Phi =
      (2 : ℝ)⁻¹ * ∑ p, faceEnergy p Phi.gaugeLink
      + (2 : ℝ)⁻¹ * ∑ e, edgeEnergy e Phi.gaugeLink Phi.higgs
      + ∑ v, vertexMass v * lambdaH *
          (higgsNormSq (Phi.higgs v) - vacuumNormSq) ^ 2
      + ∑ v, fermionEnergy v Phi.gaugeLink Phi.higgs
          Phi.spinor Phi.dualSpinor)
    ∧ (∀ g Phi,
      explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
          higgsNormSq lambdaH vacuumNormSq fermionEnergy (transform g Phi) =
        explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
          higgsNormSq lambdaH vacuumNormSq fermionEnergy Phi)
    ∧ FiniteActionEinsteinCertificate transform
        (explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
          higgsNormSq lambdaH vacuumNormSq fermionEnergy)
        (divJ + gaugePair) (stressPair - 2 * fieldPair) GQ Euler
    ∧ explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
        higgsNormSq lambdaH vacuumNormSq fermionEnergy Phi0 = 0
    ∧ (∀ lam v : ℝ, radialHiggsPotential lam v v = 0
      ∧ radialHiggsGradient lam v v = 0
      ∧ radialHiggsHessian lam v v = 8 * lam * v ^ 2)
    ∧ Nonempty (smHiggsVacuumStabilizer ≃* SMGaugeU3)
    ∧ (∀ masses : Fin 3 → ℂ, (∀ i, masses i ≠ 0) →
      (brokenGaugeMassForm masses).rank = 3)
    ∧ InformationTheory.klDiv mu mu = 0
    ∧ (∀ {p r : Type*} [Fintype p] [Fintype r]
        [DecidableEq p] [DecidableEq r]
        (z : p → Prop) [DecidablePred z],
      (finiteFibreScreen (r := r) z).rank =
        Fintype.card r * (Matrix.diagonal
          (fun i : p => if z i then (1 : ℂ) else 0)).rank) := by
  let S := explicitRegulatedStandardModelAction faceEnergy edgeEnergy vertexMass
    higgsNormSq lambdaH vacuumNormSq fermionEnergy
  have hinv : ∀ g Phi, S (transform g Phi) = S Phi :=
    explicitRegulatedStandardModelAction_gaugeInvariant Gauge transform
      faceEnergy edgeEnergy vertexMass higgsNormSq lambdaH vacuumNormSq
      fermionEnergy hface hedge hhiggs hfermion
  have hcert : FiniteActionEinsteinCertificate transform S
      (divJ + gaugePair) (stressPair - 2 * fieldPair) GQ Euler :=
    finite_action_Einstein transform htransform S hinv gaugeFlow relabelFlow
      hgaugeFlow hrelabelFlow divJ gaugePair stressPair fieldPair t0
      hWard hStress GQ hGQ Euler
  refine ⟨fun Phi => explicitRegulatedStandardModelAction_local_decomposition
      faceEnergy edgeEnergy vertexMass higgsNormSq lambdaH vacuumNormSq
        fermionEnergy Phi, hinv, hcert, ?_, radialHiggs_vacuum,
      ⟨smHiggsVacuumStabilizerEquivU3⟩, brokenGaugeMassForm_rank_three,
      commonAction_relativeEntropyGap_zero mu, ?_⟩
  · exact explicitRegulatedStandardModelAction_vacuum faceEnergy edgeEnergy
      vertexMass higgsNormSq lambdaH vacuumNormSq fermionEnergy Phi0
      hface0 hedge0 hhiggs0 hfermion0
  · intro p r _ _ _ _ z _
    exact finiteFibreScreen_rank z

end NCG
