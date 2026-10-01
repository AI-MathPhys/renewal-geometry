/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniformly integrable critical curvature energy
  (`def:critical-curvature-ui`, Einstein–SM action closure)

Setting.  The compact chart is a set `K` in a measure space `(α, μ)` with
`μ = vol_0` the comparison volume; the family of reconstructed connections is
indexed by `ι` and its curvatures are `Fc h : α → V`, with values in a normed
space `V` whose norm is the fibre norm `|·|_r` (the `r`-contracted norm of the
Lie-algebra-valued two-form).

* `criticalCurvatureSmallSetEnergy μ K Fc δ` —
  `sup_h sup_{E ⊆ K measurable, vol_0(E) ≤ δ} ∫_E |F_{A_h}|_r² dV_0`
  (as an `ℝ≥0∞`-valued lower integral, so no integrability is presupposed);
* `CriticalCurvatureUI μ K Fc` — `eq:critical-curvature-ui`: this quantity
  tends to `0` as `δ ↓ 0`;
* `criticalCurvatureUI_iff` — the equivalent `ε`–`δ` form;
* `criticalCurvatureUI_gauge_invariant` — "this property is internal-gauge
  invariant": a fibrewise norm-preserving action (for instance the adjoint
  action of a unitary gauge transformation on the curvature, which preserves
  the Frobenius norm by `frobSq_conj_of_mul` of
  `Algebra/SeriesLogUnitConjugation.lean`) leaves the small-set energies and
  hence the property unchanged.
-/

namespace RenewalGeometry

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

section CriticalCurvatureUI

variable {α : Type*} [MeasurableSpace α] {ι : Type*} {V : Type*} [NormedAddCommGroup V]

/-- `sup_h sup_{E ⊆ K measurable, vol_0(E) ≤ δ} ∫_E |F_{A_h}|_r² dV_0`
(the quantity inside the limit of `eq:critical-curvature-ui`). -/
def criticalCurvatureSmallSetEnergy (μ : Measure α) (K : Set α) (Fc : ι → α → V)
    (δ : ℝ) : ℝ≥0∞ :=
  ⨆ h, ⨆ E : Set α, ⨆ (_ : MeasurableSet E ∧ E ⊆ K ∧ μ E ≤ ENNReal.ofReal δ),
    ∫⁻ x in E, ‖Fc h x‖ₑ ^ 2 ∂μ

/-- `def:critical-curvature-ui`, `eq:critical-curvature-ui`: a family of
reconstructed connections has uniformly integrable critical curvature energy on
the compact chart `K` if the small-set curvature energies tend to zero as
`δ ↓ 0`. -/
def CriticalCurvatureUI (μ : Measure α) (K : Set α) (Fc : ι → α → V) : Prop :=
  Tendsto (criticalCurvatureSmallSetEnergy μ K Fc) (𝓝[>] 0) (𝓝 0)

/-- `def:critical-curvature-ui` in `ε`–`δ` form: for every `ε > 0` there is
`δ > 0` such that every measurable `E ⊆ K` with `vol_0(E) ≤ δ` carries curvature
energy at most `ε`, uniformly in `h`. -/
theorem criticalCurvatureUI_iff (μ : Measure α) (K : Set α) (Fc : ι → α → V) :
    CriticalCurvatureUI μ K Fc ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h (E : Set α), MeasurableSet E → E ⊆ K →
        μ E ≤ ENNReal.ofReal δ → ∫⁻ x in E, ‖Fc h x‖ₑ ^ 2 ∂μ ≤ ε := by
  unfold CriticalCurvatureUI
  rw [ENNReal.tendsto_nhds_zero]
  constructor
  · intro H ε hε
    obtain ⟨δ, hδle, hδpos⟩ := ((H ε hε).and self_mem_nhdsWithin).exists
    refine ⟨δ, hδpos, fun h E hE hEK hμE => le_trans ?_ hδle⟩
    unfold criticalCurvatureSmallSetEnergy
    exact le_iSup_of_le h (le_iSup_of_le E (le_iSup_of_le ⟨hE, hEK, hμE⟩ le_rfl))
  · intro H ε hε
    obtain ⟨δ, hδpos, hδ⟩ := H ε hε
    filter_upwards [Ioo_mem_nhdsGT hδpos] with δ' hδ'
    unfold criticalCurvatureSmallSetEnergy
    refine iSup_le fun h => iSup_le fun E => iSup_le fun hE => ?_
    exact hδ h E hE.1 hE.2.1
      (le_trans hE.2.2 (ENNReal.ofReal_le_ofReal hδ'.2.le))

/-- The small-set curvature energies only depend on the fibre norms. -/
theorem criticalCurvatureSmallSetEnergy_congr_norm (μ : Measure α) (K : Set α)
    {W : Type*} [NormedAddCommGroup W] (Fc : ι → α → V) (Gc : ι → α → W)
    (hFG : ∀ h x, ‖Gc h x‖ = ‖Fc h x‖) (δ : ℝ) :
    criticalCurvatureSmallSetEnergy μ K Gc δ = criticalCurvatureSmallSetEnergy μ K Fc δ := by
  have he : ∀ h x, ‖Gc h x‖ₑ = ‖Fc h x‖ₑ := by
    intro h x
    rw [← ofReal_norm, ← ofReal_norm, hFG]
  unfold criticalCurvatureSmallSetEnergy
  simp_rw [he]

/-- `def:critical-curvature-ui`, last sentence: the property is
internal-gauge invariant.  If the gauge transformations act on the curvature
fibres by norm-preserving maps `g h x` (the adjoint action of a unitary gauge
transformation on `|·|_r`), the transformed family has uniformly integrable
critical curvature energy iff the original one does. -/
theorem criticalCurvatureUI_gauge_invariant (μ : Measure α) (K : Set α) (Fc : ι → α → V)
    (g : ι → α → V → V) (hg : ∀ h x v, ‖g h x v‖ = ‖v‖) :
    CriticalCurvatureUI μ K (fun h x => g h x (Fc h x)) ↔ CriticalCurvatureUI μ K Fc := by
  unfold CriticalCurvatureUI
  have : criticalCurvatureSmallSetEnergy μ K (fun h x => g h x (Fc h x)) =
      criticalCurvatureSmallSetEnergy μ K Fc :=
    funext fun δ => criticalCurvatureSmallSetEnergy_congr_norm μ K Fc _
      (fun h x => hg h x (Fc h x)) δ
  rw [this]

end CriticalCurvatureUI

end

end RenewalGeometry
