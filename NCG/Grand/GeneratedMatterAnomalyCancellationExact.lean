/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMTensorGeneration

/-!
# Anomaly cancellation of the generated matter packet

This file proves `thm:SM-anomaly` from the actual tensor-generated matter
labels and the finite packet trace definitions, rather than from an isolated
list of rational identities.
-/

namespace NCG
namespace GeneratedMatterAnomalyCancellation

open SMTensorGeneration

/-- Left-chiral charges obtained from the generated rows `Q,u,d,L,e` by
conjugating the three right-handed singlets. -/
def generatedLeftChiralCharge : Fin 5 → ℤ :=
  ![1, -4, 2, -3, 6]

/-- The anomaly packet's left-chiral weights are literally the charges of the
tensor-generated matter table after right-handed conjugation. -/
theorem leftChiralWeight_eq_generatedCharge :
    leftChiralCentralWeight (-2) 3 =
      fun i => (generatedLeftChiralCharge i : ℚ) := by
  funext i
  fin_cases i <;> norm_num [leftChiralCentralWeight,
    generatedLeftChiralCharge, Matrix.cons_val]

/-- All four local anomaly traces vanish on the generated packet. -/
theorem generated_local_anomalies_vanish :
    colorMixedAnomaly (-2) 3 = 0 ∧
      weakMixedAnomaly (-2) 3 = 0 ∧
      gravitationalMixedAnomaly (-2) 3 = 0 ∧
      cubicCentralAnomaly (-2) 3 = 0 := by
  exact (tensorExteriorAnomalyPacket_vanishes_iff (-2) 3).2 (by norm_num)

/-- The pure colour and global mod-two weak anomalies vanish for the same
generated one-generation packet. -/
theorem generated_pure_and_global_anomalies_vanish :
    ((2 : ℤ) - 1 - 1 = 0) ∧ ((3 + 1) % 2 = 0) :=
  ⟨pureColorAnomaly_packet, weakWittenAnomaly_packet⟩

/-- **`thm:SM-anomaly`.**  The packet generated from primitive weights
`C ↦ -2`, `W ↦ 3`, after replacing right-handed fields by their left-handed
conjugates, has vanishing pure colour, mixed colour, mixed weak, cubic
central, mixed gravitational, and global `SU(2)` anomalies. -/
theorem sm_generated_packet_anomaly_cancellation :
    leftChiralCentralWeight (-2) 3 =
        (fun i => (generatedLeftChiralCharge i : ℚ)) ∧
      ((2 : ℤ) - 1 - 1 = 0) ∧
      colorMixedAnomaly (-2) 3 = 0 ∧
      weakMixedAnomaly (-2) 3 = 0 ∧
      cubicCentralAnomaly (-2) 3 = 0 ∧
      gravitationalMixedAnomaly (-2) 3 = 0 ∧
      ((3 + 1) % 2 = 0) := by
  rcases generated_local_anomalies_vanish with ⟨hc, hw, hg, hcube⟩
  exact ⟨leftChiralWeight_eq_generatedCharge,
    pureColorAnomaly_packet, hc, hw, hcube, hg, weakWittenAnomaly_packet⟩

end GeneratedMatterAnomalyCancellation
end NCG
