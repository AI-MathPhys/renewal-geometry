/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalCurvatureUniformIntegrabilityExact

/-!
# Compact scalar magnitude implies energy uniform integrability
  (`lem:compact-magnitude-ui`, Einstein–SM action closure)

A family that is relatively compact (equivalently, since `L²` is complete,
totally bounded) in `L²` has uniformly integrable squares.

* `compactMagnitude_unifIntegrable` — a totally bounded family in `Lp V 2 μ`
  is `UnifIntegrable` with exponent `2`: choose a finite `L²` net (of radius
  `ε/2`), apply `MeasureTheory.unifIntegrable_finite` to the finitely many net
  elements (absolute continuity of the integral), and use the triangle
  inequality `‖1_E f‖₂ ≤ ‖f - f_j‖₂ + ‖1_E f_j‖₂` (the norm form of the
  manuscript's `∫_E|f|² ≤ 2‖f-f_j‖₂² + 2∫_E|f_j|²`);
* `compactMagnitude_ui` — `eq:compact-magnitude-ui` on the region `K`:
  for a totally bounded family in `L²(K)` (i.e. `Lp V 2 (μ.restrict K)`),
  `lim_{|E|↓0} sup_f ∫_E |f|² = 0`, stated as
  `CriticalCurvatureUI μ K (fun i => F i)` of
  `Continuum/CriticalCurvatureUniformIntegrabilityExact.lean`
  (measurable `E ⊆ K`, lower-integral form);
* `compactMagnitude_ui_of_isCompact_closure` — the same under the literal
  hypothesis "relatively compact in `L²(K)`" (`IsCompact (closure (range F))`).

The hypothesis that `K` has finite measure is not needed and is not assumed.
-/

namespace RenewalGeometry

open MeasureTheory Set
open scoped ENNReal

section CompactMagnitudeUI

variable {α : Type*} [MeasurableSpace α] {ι : Type*} {V : Type*} [NormedAddCommGroup V]

/-- `lem:compact-magnitude-ui`, `L²` form: a totally bounded (equivalently,
relatively compact) family in `L²(μ)` is uniformly integrable with exponent `2`. -/
theorem compactMagnitude_unifIntegrable {μ : Measure α} (F : ι → Lp V 2 μ)
    (hF : TotallyBounded (Set.range F)) : UnifIntegrable (fun i => ⇑(F i)) 2 μ := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨t, ht, hcover⟩ :=
    EMetric.totallyBounded_iff.1 hF (ENNReal.ofReal (ε / 2)) (by simpa using hε2)
  have : Finite t := ht.to_subtype
  obtain ⟨δ, hδ, hδ'⟩ := unifIntegrable_finite (ι := t) (μ := μ) (p := 2) (by norm_num)
    (by simp) (f := fun g : t => ⇑(g : Lp V 2 μ)) (fun g => Lp.memLp _) hε2
  refine ⟨δ, hδ, fun i s hs hμs => ?_⟩
  obtain ⟨g, hgt, hig⟩ := mem_iUnion₂.1 (hcover (mem_range_self i))
  have h1 : eLpNorm (s.indicator (⇑(F i) - ⇑g)) 2 μ ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_indicator_le _).trans ?_
    rw [← Lp.edist_def]
    exact le_of_lt hig
  have h2 := hδ' ⟨g, hgt⟩ s hs hμs
  have hsplit : s.indicator (⇑(F i)) = s.indicator (⇑(F i) - ⇑g) + s.indicator ⇑g := by
    rw [← indicator_add']
    simp
  calc eLpNorm (s.indicator (F i)) 2 μ
      = eLpNorm (s.indicator (⇑(F i) - ⇑g) + s.indicator ⇑g) 2 μ := by rw [hsplit]
    _ ≤ eLpNorm (s.indicator (⇑(F i) - ⇑g)) 2 μ + eLpNorm (s.indicator ⇑g) 2 μ :=
        eLpNorm_add_le
          (((Lp.aestronglyMeasurable (F i)).sub (Lp.aestronglyMeasurable g)).indicator hs)
          ((Lp.aestronglyMeasurable g).indicator hs) (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε2.le hε2.le]
        ring_nf

/-- The small-set energy `∫_E |f|²` of an `L²(K)` element, for measurable
`E ⊆ K`, is the square of the `L²(K)` norm of `1_E f`. -/
theorem compactMagnitude_setLIntegral_eq {μ : Measure α} {K E : Set α} (hE : MeasurableSet E)
    (hEK : E ⊆ K) (f : α → V) :
    ∫⁻ x in E, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm (E.indicator f) 2 (μ.restrict K) ^ 2 := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hE, Measure.restrict_restrict hE,
    inter_eq_left.2 hEK]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ.restrict E)
    (p := (2 : NNReal)) (by norm_num)
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [h]

/-- `lem:compact-magnitude-ui`, `eq:compact-magnitude-ui`: if a family is totally
bounded (equivalently relatively compact) in `L²(K)`, then
`lim_{|E|↓0} sup_f ∫_E |f|² = 0`. -/
theorem compactMagnitude_ui (μ : Measure α) (K : Set α) (F : ι → Lp V 2 (μ.restrict K))
    (hF : TotallyBounded (Set.range F)) : CriticalCurvatureUI μ K (fun i => ⇑(F i)) := by
  rw [criticalCurvatureUI_iff]
  intro ε hε
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr1
  have hη : 0 < Real.sqrt r := Real.sqrt_pos.2 hrpos
  obtain ⟨δ, hδ, hδ'⟩ := compactMagnitude_unifIntegrable F hF hη
  refine ⟨δ, hδ, fun i E hE hEK hμE => ?_⟩
  have hμE' : μ.restrict K E ≤ ENNReal.ofReal δ := by
    rw [Measure.restrict_apply hE, inter_eq_left.2 hEK]
    exact hμE
  have h := hδ' i E hE hμE'
  rw [compactMagnitude_setLIntegral_eq hE hEK]
  calc eLpNorm (E.indicator (F i)) 2 (μ.restrict K) ^ 2
      ≤ ENNReal.ofReal (Real.sqrt r) ^ 2 := pow_le_pow_left₀ (zero_le) h 2
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr0]
    _ ≤ ε := hr2.le

/-- `lem:compact-magnitude-ui` with the literal hypothesis "relatively compact in
`L²(K)`". -/
theorem compactMagnitude_ui_of_isCompact_closure (μ : Measure α) (K : Set α)
    (F : ι → Lp V 2 (μ.restrict K)) (hF : IsCompact (closure (Set.range F))) :
    CriticalCurvatureUI μ K (fun i => ⇑(F i)) :=
  compactMagnitude_ui μ K F (hF.totallyBounded.subset subset_closure)

end CompactMagnitudeUI

end RenewalGeometry
