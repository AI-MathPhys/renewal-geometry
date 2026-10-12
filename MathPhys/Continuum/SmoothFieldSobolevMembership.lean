/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.EinsteinSMFieldSpaces
import MathPhys.Analysis.SobolevOpenSet
import MathPhys.Analysis.SobolevLocalRellich

/-!
# Classical functions are Sobolev on `ℝ⁴`

* `pd_congr`: coordinate partials of germ-equal functions agree.
* `isFiniteMeasure_restrict_of_compact_closure`, `memLp_of_continuousOn_closure`: continuous
  functions on the compact closure of an open set lie in every `L^p` of the set.
* `memW12_of_contDiffOn`: a `C¹` function on a neighbourhood of a compact closure lies in
  `W^{1,2}` with its classical partials as weak partials.

Split out of `MathPhys.Continuum.EinsteinSMFirstVariationContinuity` (which re-exports it);
names are unchanged.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

namespace MathPhys
namespace EinsteinSM

open SobolevOpen (pd MemW12)

theorem pd_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E4 → F} {x : E4}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 4) : pd f i x = pd g i x := by
  unfold pd; rw [h.fderiv_eq]

theorem isFiniteMeasure_restrict_of_compact_closure {Ω : Set E4} (hc : IsCompact (closure Ω)) :
    IsFiniteMeasure (volume.restrict Ω) :=
  isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt hc.measure_lt_top).ne

theorem memLp_of_continuousOn_closure {F : Type*} [NormedAddCommGroup F] {Ω : Set E4}
    (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) {f : E4 → F} (hf : ContinuousOn f (closure Ω))
    (p : ℝ≥0∞) : MemLp f p (volume.restrict Ω) := by
  haveI := isFiniteMeasure_restrict_of_compact_closure hc
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable hΩ.measurableSet) M ?_
  exact (ae_restrict_iff' hΩ.measurableSet).mpr
    (Eventually.of_forall fun x hx => hM x (subset_closure hx))

/-- **Classical functions are Sobolev**: a `C¹` function on an open neighbourhood `U` of the
compact closure of an open `Ω` lies in `W^{1,2}(Ω)`, with its classical partials as weak
partials. -/
theorem memW12_of_contDiffOn {Ω U : Set E4} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hc : IsCompact (closure Ω)) (hΩU : closure Ω ⊆ U) {u : E4 → ℂ} (hu : ContDiffOn ℝ 1 u U) :
    MemW12 Ω u (fun i => pd u i) := by
  obtain ⟨χ, hχ, hχ1, -⟩ := SobolevOpen.exists_cutoff hU hc hΩU
  set w : E4 → ℂ := fun x => ((χ x : ℝ) : ℂ) * u x with hw_def
  have hχc : ContDiff ℝ 1 fun x => ((χ x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hχ.smooth.of_le (by simp))
  have hw : ContDiff ℝ 1 w := by
    refine contDiff_iff_contDiffAt.mpr fun y => ?_
    by_cases hy : y ∈ U
    · exact hχc.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hy))
    · have hy' : y ∉ tsupport χ := fun h => hy (hχ.subset h)
      have h0 : χ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy'
      refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [h0] with x hx
      simp [hw_def, hx]
  have hwu : ∀ x ∈ Ω, w =ᶠ[𝓝 x] u := fun x hx => by
    have := hχ1.filter_mono (nhds_le_nhdsSet (subset_closure hx))
    filter_upwards [this] with y hy
    simp [hw_def, hy]
  have hfd : ContinuousOn (fderiv ℝ u) U := hu.continuousOn_fderiv_of_isOpen hU le_rfl
  refine ⟨memLp_of_continuousOn_closure hΩ hc (hu.continuousOn.mono hΩU) 2, fun i =>
    memLp_of_continuousOn_closure hΩ hc ((hfd.mono hΩU).clm_apply continuousOn_const) 2,
    fun i φ hφ => ?_⟩
  have h := SobolevOpen.hasWeakPartial_of_contDiff Ω hw i φ hφ
  have hφ0 : ∀ x ∉ Ω, φ =ᶠ[𝓝 x] 0 := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hφ.subset h)
  have e1 : ∀ x, ((pd φ i x : ℝ) : ℂ) * u x = ((pd φ i x : ℝ) : ℂ) * w x := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [(hwu x hx).eq_of_nhds]
    · rw [pd_congr (hφ0 x hx) i]
      simp [pd]
  have e2 : ∀ x, ((φ x : ℝ) : ℂ) * pd u i x = ((φ x : ℝ) : ℂ) * pd w i x := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [pd_congr (hwu x hx) i]
    · rw [(hφ0 x hx).eq_of_nhds]
      simp
  simp only [e1, e2]
  exact h

end EinsteinSM
end MathPhys
