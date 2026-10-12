/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.EinsteinSMGravityFirstOrder
import RenewalGeometry.Continuum.EinsteinSMCompactnessCertificates
import RenewalGeometry.Continuum.EinsteinSMWeakMatterEquations
import MathPhys.FieldTheory.Continuum.EinsteinSMJointDefect
import MathPhys.FieldTheory.Continuum.EinsteinSMVariationContinuity
open MathPhys

/-!
# Non-vacuity of the first-variation continuity statements: the flat regulator

The flat regulator `flatRegulator` (`EinsteinSMCompactnessCertificates`), which converges to the
flat limit in the reduced action topology, satisfies the hypotheses of
`smVariation_dual_tendsto` (`EinsteinSMFermionicContinuity`) and of
`actionVariation_dual_tendsto` (`EinsteinSMGravityFirstOrder`), with the trivial carrier and the
constant physical bank; with constant bosonic fields on a one-point chart it also satisfies the
hypothesis packet of `joint_defect_einstein_weak` (`EinsteinSMJointDefect`).  (Moved out of those
files, unchanged.)
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace RenewalGeometry
namespace EinsteinSM
open MathPhys.EinsteinSM

/-- **Non-vacuity of `smVariation_dual_tendsto`** (and hence of the Dirac sector): the flat
regulator, which converges to the flat limit in the reduced action topology, satisfies all the
hypotheses, with the trivial carrier and the constant physical bank. -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 1 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest (trivialCarrier Unit).left r K,
      |firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) .standardModel
          ((flatRegulator T).fields n).z v.val -
        smLimitVariation (trivialCarrier Unit) physicalBank
          (slabChart t₀ t₁ h0 h01 h1 (T := T)) flatLimit v| ≤ ε * ‖v‖ :=
  smVariation_dual_tendsto (trivialCarrier Unit) h0 h01 h1 hK hr
    (flatRegulator_reducedActionConvergence T _) tendsto_const_nhds tendsto_const_nhds hε

/-- **Non-vacuity**: the flat regulator satisfies the hypotheses of the complete statement. -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {r : ℕ} (hr : 1 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest (trivialCarrier Unit).left r K,
      |(firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) .gravity
            ((flatRegulator T).fields n).z v.val +
          firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) .standardModel
            ((flatRegulator T).fields n).z v.val) -
        (gravLimitVariation (trivialCarrier Unit) physicalBank
            (slabChart t₀ t₁ h0 h01 h1 (T := T)) flatLimit v +
          smLimitVariation (trivialCarrier Unit) physicalBank
            (slabChart t₀ t₁ h0 h01 h1 (T := T)) flatLimit v)| ≤ ε * ‖v‖ :=
  actionVariation_dual_tendsto (trivialCarrier Unit) h0 h01 h1 hK hr
    (flatRegulator_reducedActionConvergence T _) tendsto_const_nhds tendsto_const_nhds hε

section JointDefectExample

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

open BosonicStress QuadraticPacketDefect SignedMeasureWeakCompactness BosonicStressDefect

/-- **Non-vacuity of `joint_defect_einstein_weak`**: the complete hypothesis packet is satisfied by
the Minkowski metric with constant bosonic fields on a one-point chart and the flat regulator
(trivial carrier, physical bank) for the fermionic part. -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {Kc : CylRegion T}
    (hK : ∀ p ∈ Kc.carrier, p.1 ∈ Icc t₀ t₁) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(Unit, ℝ),
      IsYMDefect (Measure.dirac ()) (fun _ => minkField) minkField (fun _ _ => (1 : ℝ))
        (fun _ : Fin 1 => 1) (fun _ _ _ _ _ => (0 : ℝ)) (fun _ _ _ _ => 0) σ SYM := by
  obtain ⟨σ, hσ, SYM, SH, hSYM, -, -⟩ := joint_defect_einstein_weak (V₀ := Measure.dirac ())
    (E := ℝ) (κG := Fin 1) (κ := Fin 1) (trivialCarrier Unit)
    (g := fun _ => minkField) (g₀ := minkField) tendsto_const_nhds (fun _ => minkField_det)
    minkField_det (w := fun _ _ => (1 : ℝ)) (w₀ := fun _ => 1) (fun _ => tendsto_const_nhds)
    (weakL2_const _ (Fp fun _ _ _ _ => (0 : ℝ))) (H := fun _ _ => (1 : ℝ)) (H₀ := fun _ => 1)
    (fun _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => tendsto_const_nhds)
    (C := 1) (fun _ => by
      refine (eLpNorm_le_of_ae_bound (C := 1) (Eventually.of_forall fun _ => by simp)).trans ?_
      simp)
    (weakL2_const _ (Yp fun _ _ _ => (0 : ℝ))) (lam := fun _ => 1) (vH := fun _ => 0)
    tendsto_const_nhds tendsto_const_nhds h0 h01 h1 hK (r := 4) (by norm_num)
    (flatRegulator_weakMatterConvergence T _) tendsto_const_nhds tendsto_const_nhds
    (fun _ _ _ => 0)
  exact ⟨σ, hσ, SYM, SH, hSYM⟩

end JointDefectExample

namespace VarLip
open MathPhys.EinsteinSM.VarLip

set_option synthInstance.maxSize 1024

/-! ### Non-vacuity -/

section NonVacuity

/-- The flat fields lie in the bounded strong-packet class of every slab chart. -/
theorem flat_packetBound {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      PacketBound (slabChart t₀ t₁ h0 h01 h1) {flatCoframe} B ((flatRegulator T).fields 0) :=
  exists_packetBound _ _ fun _ _ => rfl

/-- **Non-vacuity of `variation_continuity`**: all hypotheses are met by the trivial carrier, the
flat coframe set, the physical bank and the flat fields (which lie in the class). -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      PacketBound (slabChart t₀ t₁ h0 h01 h1) {flatCoframe} B ((flatRegulator T).fields 0) ∧
      ∃ CK : ℝ≥0∞, CK ≠ ⊤ ∧ ∀ (b : Sector) (v : CrTest (trivialCarrier Unit).left 4 K),
        ENNReal.ofReal |firstVariation T (trivialCarrier Unit) physicalBank b
            ((flatRegulator T).fields 0).z v.val -
          firstVariation T (trivialCarrier Unit) physicalBank b
            ((flatRegulator T).fields 0).z v.val| ≤
          CK * dK (slabChart t₀ t₁ h0 h01 h1) ((flatRegulator T).fields 0) physicalBank
            ((flatRegulator T).fields 0) physicalBank * ENNReal.ofReal ‖v‖ := by
  obtain ⟨B, hB, hp⟩ := flat_packetBound h0 h01 h1
  obtain ⟨CK, hCK, h⟩ := variation_continuity (trivialCarrier Unit) h0 h01 h1 hK (r := 4)
    (by norm_num) isCompactCoframeSet_flat isCompactBankSet_physical (yukawaLipOn_trivial _) hB
  exact ⟨B, hB, hp, CK, hCK, fun b v => h _ _ _ _ rfl rfl hp hp b v⟩

end NonVacuity

end VarLip

end EinsteinSM
end RenewalGeometry
