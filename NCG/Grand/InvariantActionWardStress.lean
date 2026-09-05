/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteBRSTWardEinstein

/-!
# Ward and stress identities from actual invariant-action flows

This file removes the abstract constant-flow premise from the finite
Ward/BRST/stress assembly.  The two real-valued flows are evaluations of one
action along genuine gauge and relabeling orbits.  Their constancy is derived
from the corresponding invariance laws.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace InvariantActionWardStress

variable {Gauge Relabel Field n : Type*}
variable [Group Gauge] [Group Relabel]
variable [Fintype n] [DecidableEq n]

/-- The action evaluated along a one-parameter family of gauge transformations. -/
def gaugeOrbitFlow (gaugeAct : Gauge → Field → Field) (S : Field → ℝ)
    (path : ℝ → Gauge) (Φ : Field) : ℝ → ℝ :=
  fun t => S (gaugeAct (path t) Φ)

/-- The same action evaluated along a one-parameter family of relabelings. -/
def relabelOrbitFlow (relabelAct : Relabel → Field → Field) (S : Field → ℝ)
    (path : ℝ → Relabel) (Φ : Field) : ℝ → ℝ :=
  fun t => S (relabelAct (path t) Φ)

/-- Gauge invariance makes every actual gauge-orbit action flow constant. -/
theorem gaugeOrbitFlow_constant
    (gaugeAct : Gauge → Field → Field) (S : Field → ℝ)
    (hinv : ∀ g Φ, S (gaugeAct g Φ) = S Φ)
    (path : ℝ → Gauge) (Φ : Field) :
    ∀ t, gaugeOrbitFlow gaugeAct S path Φ t =
      gaugeOrbitFlow gaugeAct S path Φ 0 := by
  intro t
  simp only [gaugeOrbitFlow, hinv]

/-- Relabeling invariance makes every actual relabeling-orbit action flow
constant. -/
theorem relabelOrbitFlow_constant
    (relabelAct : Relabel → Field → Field) (S : Field → ℝ)
    (hinv : ∀ r Φ, S (relabelAct r Φ) = S Φ)
    (path : ℝ → Relabel) (Φ : Field) :
    ∀ t, relabelOrbitFlow relabelAct S path Φ t =
      relabelOrbitFlow relabelAct S path Φ 0 := by
  intro t
  simp only [relabelOrbitFlow, hinv]

/-- CA.5--CA.6 on a finite carrier.  Gauge and stress flows are not arbitrary
constant functions: they are the action itself restricted to genuine gauge
and relabeling orbits.  Exact invariance supplies their constancy, while the
two derivative hypotheses identify the corresponding first variations with
the Ward and stress-transfer expressions displayed in the manuscript. -/
theorem certificate_from_invariant_orbit_flows
    (gaugeAct : Gauge → Field → Field)
    (hgaugeAct : ∀ g h Φ, gaugeAct (g * h) Φ = gaugeAct g (gaugeAct h Φ))
    (relabelAct : Relabel → Field → Field)
    (S : Field → ℝ)
    (hgaugeInv : ∀ g Φ, S (gaugeAct g Φ) = S Φ)
    (hrelabelInv : ∀ r Φ, S (relabelAct r Φ) = S Φ)
    (gaugePath : ℝ → Gauge) (relabelPath : ℝ → Relabel) (Φ : Field)
    (ward stress t₀ : ℝ)
    (hWard : HasDerivAt (gaugeOrbitFlow gaugeAct S gaugePath Φ) ward t₀)
    (hStress : HasDerivAt
      (relabelOrbitFlow relabelAct S relabelPath Φ) stress t₀)
    (GQ : Matrix n n ℂ) (hGQ : GQ.PosDef) (Euler : n → ℂ) :
    FiniteActionEinsteinCertificate gaugeAct S ward stress GQ Euler := by
  simpa using (finite_action_Einstein gaugeAct hgaugeAct S hgaugeInv
    (gaugeOrbitFlow gaugeAct S gaugePath Φ)
    (relabelOrbitFlow relabelAct S relabelPath Φ)
    (gaugeOrbitFlow_constant gaugeAct S hgaugeInv gaugePath Φ)
    (relabelOrbitFlow_constant relabelAct S hrelabelInv relabelPath Φ)
    ward 0 stress 0 t₀ (by simpa using hWard) (by simpa using hStress)
    GQ hGQ Euler)

/-- In particular, the Ward expression, BRST differential and its square,
and the tangential stress-transfer expression all vanish. -/
theorem ward_brst_stress_from_invariance
    (gaugeAct : Gauge → Field → Field)
    (hgaugeAct : ∀ g h Φ, gaugeAct (g * h) Φ = gaugeAct g (gaugeAct h Φ))
    (relabelAct : Relabel → Field → Field)
    (S : Field → ℝ)
    (hgaugeInv : ∀ g Φ, S (gaugeAct g Φ) = S Φ)
    (hrelabelInv : ∀ r Φ, S (relabelAct r Φ) = S Φ)
    (gaugePath : ℝ → Gauge) (relabelPath : ℝ → Relabel) (Φ : Field)
    (ward stress t₀ : ℝ)
    (hWard : HasDerivAt (gaugeOrbitFlow gaugeAct S gaugePath Φ) ward t₀)
    (hStress : HasDerivAt
      (relabelOrbitFlow relabelAct S relabelPath Φ) stress t₀) :
    ward = 0 ∧ finiteBRST0 gaugeAct S = 0 ∧
      finiteBRST1 gaugeAct (finiteBRST0 gaugeAct S) = 0 ∧ stress = 0 := by
  have hbrst := finiteGaugeAction_BRST gaugeAct hgaugeAct S hgaugeInv
  have hw : ward = 0 := by
    have hc := gaugeOrbitFlow_constant gaugeAct S hgaugeInv gaugePath Φ
    simpa using (gauge_ward_identity
      (gaugeOrbitFlow gaugeAct S gaugePath Φ) hc ward 0 t₀
      (by simpa using hWard))
  have hs : stress = 0 := by
    have hc := relabelOrbitFlow_constant relabelAct S hrelabelInv relabelPath Φ
    have h := relabeling_stress_identity
      (relabelOrbitFlow relabelAct S relabelPath Φ) hc stress 0 t₀
      (by simpa using hStress)
    linarith
  exact ⟨hw, hbrst.1, hbrst.2, hs⟩

end InvariantActionWardStress
end NCG
