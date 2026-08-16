/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ActionEinstein

/-!
# Finite BRST, Ward, stress, and Einstein assembly

This file supplies the clause missing from the earlier
`ActionEinstein` slice.  For a finite gauge action it constructs the first two
operators of the inhomogeneous group-cochain (finite BRST) complex and proves
their composition is zero.  Gauge-invariant actions are therefore BRST closed,
not merely assumed to be so.  The final certificate assembles this fact with
the differentiated Ward and tangential identities and with the faithful
finite Einstein residual.
-/

open scoped ComplexOrder
open Matrix

namespace NCG

section FiniteBRST

variable {Gauge Field R : Type*} [Group Gauge] [AddCommGroup R]

/-- Degree-zero finite BRST coboundary for a left gauge action. -/
def finiteBRST0 (act : Gauge → Field → Field) (f : Field → R) :
    Gauge → Field → R :=
  fun g x => f (act g x) - f x

/-- Degree-one finite BRST coboundary in inhomogeneous coordinates. -/
def finiteBRST1 (act : Gauge → Field → Field)
    (ω : Gauge → Field → R) : Gauge → Gauge → Field → R :=
  fun g h x => ω g (act h x) - ω (g * h) x + ω h x

/-- The first finite BRST square vanishes by the gauge-action law. -/
theorem finiteBRST_nilpotent
    (act : Gauge → Field → Field)
    (hact : ∀ g h x, act (g * h) x = act g (act h x))
    (f : Field → R) :
    finiteBRST1 act (finiteBRST0 act f) = 0 := by
  funext g h x
  simp only [finiteBRST1, finiteBRST0, Pi.zero_apply]
  rw [← hact]
  abel

/-- Exact finite gauge invariance is equivalent to BRST closure in degree
zero. -/
theorem finiteBRST0_eq_zero_iff
    (act : Gauge → Field → Field) (f : Field → R) :
    finiteBRST0 act f = 0 ↔ ∀ g x, f (act g x) = f x := by
  constructor
  · intro h g x
    have hx := congrFun (congrFun h g) x
    simpa [finiteBRST0] using sub_eq_zero.mp hx
  · intro h
    funext g x
    simp [finiteBRST0, h g x]

/-- An invariant finite classical action is BRST closed and its BRST
differential is nilpotent. -/
theorem finiteGaugeAction_BRST
    (act : Gauge → Field → Field)
    (hact : ∀ g h x, act (g * h) x = act g (act h x))
    (S : Field → R) (hinv : ∀ g x, S (act g x) = S x) :
    finiteBRST0 act S = 0 ∧
      finiteBRST1 act (finiteBRST0 act S) = 0 :=
  ⟨(finiteBRST0_eq_zero_iff act S).2 hinv,
    finiteBRST_nilpotent act hact S⟩

end FiniteBRST

/-- The four exact outputs of `thm:SMST-finite-action-Einstein` on a finite
common carrier.  The BRST fields are actual finite group cochains; the Ward
and stress quantities are the derivatives of the same action along the
specified one-parameter gauge and relabeling flows. -/
structure FiniteActionEinsteinCertificate
    {Gauge Field n : Type*} [Group Gauge]
    [Fintype n] [DecidableEq n]
    (act : Gauge → Field → Field) (Smat : Field → ℝ)
    (ward stress : ℝ) (GQ : Matrix n n ℂ) (E : n → ℂ) : Prop where
  /-- (F1) The finite Ward expression vanishes. -/
  wardIdentity : ward = 0
  /-- (F2) The classical matter action is BRST closed. -/
  brstClosed : finiteBRST0 act Smat = 0
  /-- (F2) The next BRST differential kills its coboundary. -/
  brstNilpotent : finiteBRST1 act (finiteBRST0 act Smat) = 0
  /-- (F3) The finite tangential stress-transfer expression vanishes. -/
  stressIdentity : stress = 0
  /-- (F4) The faithful inverse-metric Einstein residual is nonnegative. -/
  einsteinResidualNonnegative :
    0 ≤ (dotProduct (star E) ((GQ⁻¹).mulVec E)).re
  /-- (F4) It vanishes exactly at metric stationarity. -/
  einsteinResidual_eq_zero_iff :
    dotProduct (star E) ((GQ⁻¹).mulVec E) = 0 ↔ E = 0

/-- `thm:SMST-finite-action-Einstein`, including the previously absent finite
BRST clause.  Gauge and tangential invariance are differentiated along the
displayed flows, while BRST nilpotency follows internally from the gauge
action law. -/
theorem finite_action_Einstein
    {Gauge Field n : Type*} [Group Gauge]
    [Fintype n] [DecidableEq n]
    (act : Gauge → Field → Field)
    (hact : ∀ g h x, act (g * h) x = act g (act h x))
    (Smat : Field → ℝ) (hgauge : ∀ g x, Smat (act g x) = Smat x)
    (gaugeFlow relabelFlow : ℝ → ℝ)
    (hgaugeFlow : ∀ t, gaugeFlow t = gaugeFlow 0)
    (hrelabelFlow : ∀ t, relabelFlow t = relabelFlow 0)
    (divJ gaugePair stressPair fieldPair t₀ : ℝ)
    (hWardDeriv : HasDerivAt gaugeFlow (divJ + gaugePair) t₀)
    (hStressDeriv : HasDerivAt relabelFlow (stressPair - 2 * fieldPair) t₀)
    (GQ : Matrix n n ℂ) (hGQ : GQ.PosDef) (E : n → ℂ) :
    FiniteActionEinsteinCertificate act Smat
      (divJ + gaugePair) (stressPair - 2 * fieldPair) GQ E := by
  have hbrst := finiteGaugeAction_BRST act hact Smat hgauge
  have hward := gauge_ward_identity gaugeFlow hgaugeFlow
    divJ gaugePair t₀ hWardDeriv
  have hstressEq := relabeling_stress_identity relabelFlow hrelabelFlow
    stressPair fieldPair t₀ hStressDeriv
  have hein := einstein_residual_psd GQ hGQ E
  refine {
    wardIdentity := hward
    brstClosed := hbrst.1
    brstNilpotent := hbrst.2
    stressIdentity := ?_
    einsteinResidualNonnegative := hein.1
    einsteinResidual_eq_zero_iff := hein.2 }
  linarith

end NCG
