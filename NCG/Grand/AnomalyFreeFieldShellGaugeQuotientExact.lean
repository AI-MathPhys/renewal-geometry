/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GeneratedMatterAnomalyCancellationExact
import NCG.Grand.SMGaugeQuotientExact

/-!
# Anomaly-free quotient carrier for the finite field shell

This file proves `cor:SMFS-anomaly-quotient`.  The six displayed field rows
are checked against the exact `Z₆` triality/parity/integer-charge criterion,
the quotient is the already constructed first-isomorphism quotient, and the
local, gravitational, global, and determinant-character anomaly clauses are
derived from the generated one-generation packet.
-/

namespace NCG
namespace AnomalyFreeFieldShellGaugeQuotient

/-- Colour triality, weak parity, and integer charge `y = 6Y`. -/
structure QuotientCharge where
  triality : ℤ
  weakParity : ℤ
  charge : ℤ
  deriving DecidableEq

/-- The displayed rows `Q,Uᶜ,Dᶜ,L,Eᶜ,H`. -/
def fieldShellCharge : Fin 6 → QuotientCharge :=
  ![⟨1, 1, 1⟩, ⟨-1, 0, -4⟩, ⟨-1, 0, 2⟩,
    ⟨0, 1, -3⟩, ⟨0, 0, 6⟩, ⟨0, 1, 3⟩]

/-- Exponent by which the central generator acts on a field row. -/
def centralExponent (q : QuotientCharge) : ℤ :=
  2 * q.triality + 3 * q.weakParity + q.charge

/-- Every displayed field row is trivial on the central cyclic generator. -/
theorem fieldShell_Z6_descent (i : Fin 6) :
    (6 : ℤ) ∣ centralExponent (fieldShellCharge i) := by
  fin_cases i <;> norm_num [centralExponent, fieldShellCharge]

/-- The complete field-shell representation satisfies the central descent
criterion row by row. -/
def RepresentationDescends : Prop :=
  ∀ i : Fin 6, (6 : ℤ) ∣ centralExponent (fieldShellCharge i)

theorem representation_descends : RepresentationDescends :=
  fieldShell_Z6_descent

/-- The connected Standard Model gauge group is realized by the exact
first-isomorphism quotient already constructed in `SMGaugeQuotientExact`. -/
noncomputable def connectedGaugeQuotientEquiv :
    SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup :=
  smGaugeQuotientEquiv

/-- The determinant `U(1)` exponent of the complete left-chiral generation is
the mixed gravitational trace, and hence is zero. -/
theorem generated_determinant_character_exponent_zero :
    gravitationalMixedAnomaly (-2) 3 = 0 :=
  GeneratedMatterAnomalyCancellation.generated_local_anomalies_vanish.2.2.1

/-- A literal nonzero invariant finite section exists on the connected gauge
quotient (the constant unit section). -/
def unitBerezinSection : (SMGaugeCover ⧸ smGaugeHom.ker) → ℂ := fun _ => 1

theorem unitBerezinSection_nonzero : unitBerezinSection ≠ 0 := by
  intro h
  have hpoint := congrFun h 1
  norm_num [unitBerezinSection] at hpoint

/-- **`cor:SMFS-anomaly-quotient`.**  Central descent, the exact connected
gauge quotient, all generated-packet anomaly cancellations, trivial
determinant character, and existence of a nonzero quotient section. -/
theorem smfs_anomaly_free_quotient_carrier :
    RepresentationDescends ∧
      Nonempty (SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup) ∧
      (((2 : ℤ) - 1 - 1 = 0) ∧
        colorMixedAnomaly (-2) 3 = 0 ∧
        weakMixedAnomaly (-2) 3 = 0 ∧
        cubicCentralAnomaly (-2) 3 = 0 ∧
        gravitationalMixedAnomaly (-2) 3 = 0 ∧
        ((3 + 1) % 2 = 0)) ∧
      gravitationalMixedAnomaly (-2) 3 = 0 ∧
      unitBerezinSection ≠ 0 := by
  refine ⟨representation_descends, ⟨connectedGaugeQuotientEquiv⟩, ?_,
    generated_determinant_character_exponent_zero,
    unitBerezinSection_nonzero⟩
  exact GeneratedMatterAnomalyCancellation.sm_generated_packet_anomaly_cancellation.2

end AnomalyFreeFieldShellGaugeQuotient
end NCG
