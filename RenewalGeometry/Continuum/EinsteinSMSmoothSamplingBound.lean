/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMReducedClosure

/-!
# The stationarity–consistency triangle of `prop:smooth-sampling`

Einstein–Standard-Model action-closure manuscript, `prop:smooth-sampling`, proof: "If `z_*` is
critical, `prop:variation-continuity` gives `ε_h(K) ≤ c_h(K) + C_K d_K(z_h, z_*) = O(h)`."

In the encoding of `def:regulator` (`EinsteinSMRegulatorSequence.lean`) this file proves the
part of that inequality that does not use the (open) Lipschitz estimate of
`prop:variation-continuity`:

* `stationarityDefect_le_consistencyDefect_add`:
  `ε_h(K) ≤ c_h(K) + sup_{‖v‖ ≤ 1} |D𝒮_{θ_h}(z_h)[v]|`
  (triangle inequality through the continuum first variation of the reconstructed fields);
* `stationarityDefect_le_of_critical`: if `z_*` is a critical point of the continuum action with
  bank `θ_*` (`D𝒮_{θ_*}(z_*)[v] = 0` for all tests), then
  `ε_h(K) ≤ c_h(K) + sup_{‖v‖ ≤ 1} |D𝒮_{θ_h}(z_h)[v] - D𝒮_{θ_*}(z_*)[v]|`;
* `stationarityDefect_le_of_rates`: consequently `c_h(K) ≤ C h` and a first-variation continuity
  defect `≤ C' h` give `ε_h(K) ≤ (C + C') h` (`eq:sampling-stationarity`).

The remaining inputs of `prop:smooth-sampling` are the rate `c_h(K) = O(h)`
(`prop:mesh-consistency`)
and the bound of the continuity defect by `C_K d_K(z_h, z_*)` with `d_K(z_h, z_*) = O(h)`
(`prop:variation-continuity` and the strong-packet convergence of `prop:mesh-consistency`); they
enter `stationarityDefect_le_of_rates` as hypotheses.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace RenewalGeometry
namespace EinsteinSM
namespace SmoothSamplingBound

variable {T : ℝ} {Ysec : Type} [Finite Ysec] {FC : FermionCarrier Ysec}

/-- **Triangle through the continuum variation**: `ε_h(K) ≤ c_h(K) + sup_{‖v‖≤1}
|D𝒮_{θ_h}(z_h)[v]|` with `D𝒮 = D𝒮_g + D𝒮_{SM}` the continuum first variation of the
reconstructed fields. -/
theorem stationarityDefect_le_consistencyDefect_add (reg : RegulatorSequence T FC) (n : ℕ)
    (K : CylRegion T) :
    reg.stationarityDefect n K ≤ reg.consistencyDefect n K +
      ⨆ (v : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 v.1 ≤ 1),
        ENNReal.ofReal |firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.1 +
          firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.1| := by
  have := Fintype.ofFinite Ysec
  refine iSup₂_le fun v hv => ?_
  set D := firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.1 +
    firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.1
  set Φ := fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)
  have hb := (reg.defect_bounds n K (v : CrTest FC.left reg.r0 K) hv).1
  have hsup : ENNReal.ofReal |D| ≤
      ⨆ (w : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 w.1 ≤ 1),
        ENNReal.ofReal |firstVariation T FC (reg.bank n) .gravity (reg.fields n).z w.1 +
          firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z w.1| :=
    le_iSup₂ (f := fun (w : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 w.1 ≤ 1) =>
      ENNReal.ofReal |firstVariation T FC (reg.bank n) .gravity (reg.fields n).z w.1 +
        firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z w.1|) v hv
  have htri : |Φ| ≤ |D - Φ| + |D| := by
    have := abs_sub_le Φ D 0
    rw [sub_zero, sub_zero, abs_sub_comm Φ D] at this
    exact this
  calc ENNReal.ofReal |Φ| ≤ ENNReal.ofReal (|D - Φ| + |D|) := ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |D - Φ| + ENNReal.ofReal |D| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add hb hsup

/-- **Critical limits** (`prop:smooth-sampling`, second clause, triangle form): if `z_*` is a
critical point of the continuum action with bank `θ_*`, then
`ε_h(K) ≤ c_h(K) + sup_{‖v‖≤1} |D𝒮_{θ_h}(z_h)[v] - D𝒮_{θ_*}(z_*)[v]|`. -/
theorem stationarityDefect_le_of_critical (reg : RegulatorSequence T FC) (n : ℕ)
    (K : CylRegion T) (θs : CoefficientBank Ysec) (zs : FieldTuple FC.C)
    (hcrit : ∀ v ∈ testSubmodule FC.left K,
      firstVariation T FC θs .gravity zs v + firstVariation T FC θs .standardModel zs v = 0) :
    reg.stationarityDefect n K ≤ reg.consistencyDefect n K +
      ⨆ (v : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 v.1 ≤ 1),
        ENNReal.ofReal |(firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.1 +
          firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.1) -
          (firstVariation T FC θs .gravity zs v.1 +
            firstVariation T FC θs .standardModel zs v.1)| := by
  refine (stationarityDefect_le_consistencyDefect_add reg n K).trans (add_le_add le_rfl ?_)
  refine iSup₂_mono fun v _ => le_of_eq ?_
  rw [hcrit v.1 v.2, sub_zero]

/-- **`eq:sampling-stationarity` from rates**: if `c_h(K) ≤ C h` and the first-variation
continuity defect against a critical `z_*` is `≤ C' h` on the unit ball, then
`ε_h(K) ≤ (C + C') h`. -/
theorem stationarityDefect_le_of_rates (reg : RegulatorSequence T FC) (n : ℕ)
    (K : CylRegion T) (θs : CoefficientBank Ysec) (zs : FieldTuple FC.C)
    (hcrit : ∀ v ∈ testSubmodule FC.left K,
      firstVariation T FC θs .gravity zs v + firstVariation T FC θs .standardModel zs v = 0)
    {C C' : ℝ} (hC : reg.consistencyDefect n K ≤ ENNReal.ofReal (C * reg.cutoff n))
    (hC' : ∀ v : ↥(testSubmodule FC.left K), testNorm reg.r0 v.1 ≤ 1 →
      |(firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.1 +
          firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.1) -
          (firstVariation T FC θs .gravity zs v.1 +
            firstVariation T FC θs .standardModel zs v.1)| ≤ C' * reg.cutoff n)
    (hC0 : 0 ≤ C) (hC'0 : 0 ≤ C') :
    reg.stationarityDefect n K ≤ ENNReal.ofReal ((C + C') * reg.cutoff n) := by
  refine (stationarityDefect_le_of_critical reg n K θs zs hcrit).trans ?_
  have hsup : (⨆ (v : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 v.1 ≤ 1),
        ENNReal.ofReal |(firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.1 +
          firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.1) -
          (firstVariation T FC θs .gravity zs v.1 +
            firstVariation T FC θs .standardModel zs v.1)|) ≤
      ENNReal.ofReal (C' * reg.cutoff n) :=
    iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal (hC' v hv)
  have hh := (reg.cutoff_pos n).le
  calc _ ≤ ENNReal.ofReal (C * reg.cutoff n) + ENNReal.ofReal (C' * reg.cutoff n) :=
        add_le_add hC hsup
    _ = ENNReal.ofReal ((C + C') * reg.cutoff n) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end SmoothSamplingBound
end EinsteinSM
end RenewalGeometry
