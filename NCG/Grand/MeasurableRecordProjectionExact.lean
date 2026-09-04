/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

/-!
# Actual L2 projection onto a retained measurable record sector

Selection is multiplication by the indicator of the retained event. It is
a contractive continuous linear idempotent whose fixed space consists
exactly of vectors vanishing outside that event. Gauge-invariant selection
commutes with the actual measure-preserving pullback.
-/

open MeasureTheory Filter Set

namespace NCG.MeasurableRecordProjection

noncomputable section

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) (S : Set X) (hS : MeasurableSet S)

def select (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).indicator hS).toLp (S.indicator f)

theorem select_ae (f : Lp ℂ 2 μ) : select μ S hS f =ᵐ[μ] S.indicator f :=
  MemLp.coeFn_toLp _

theorem select_add (f g : Lp ℂ 2 μ) :
    select μ S hS (f + g) = select μ S hS f + select μ S hS g := by
  apply Lp.ext
  filter_upwards [select_ae μ S hS (f + g), select_ae μ S hS f, select_ae μ S hS g,
    Lp.coeFn_add f g, Lp.coeFn_add (select μ S hS f) (select μ S hS g)]
    with x hfg hf hg hsum hout
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx] at hfg hf hg
    simp only [Pi.add_apply] at hsum hout
    rw [hfg, hsum, hout, hf, hg]
  · simp only [Set.indicator_of_notMem hx] at hfg hf hg
    simp only [Pi.add_apply] at hout
    rw [hfg, hout, hf, hg, zero_add]

theorem select_smul (c : ℂ) (f : Lp ℂ 2 μ) :
    select μ S hS (c • f) = c • select μ S hS f := by
  apply Lp.ext
  filter_upwards [select_ae μ S hS (c • f), select_ae μ S hS f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (select μ S hS f)] with x hcf hf hsm hout
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx] at hcf hf
    simp only [Pi.smul_apply] at hsm hout
    rw [hcf, hsm, hout, hf]
  · simp only [Set.indicator_of_notMem hx] at hcf hf
    simp only [Pi.smul_apply] at hout
    rw [hcf, hout, hf, smul_zero]

theorem norm_select_le (f : Lp ℂ 2 μ) : ‖select μ S hS f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [select_ae μ S hS f] with x hx
  rw [hx]
  by_cases hs : x ∈ S <;> simp [hs]

def selection : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := select μ S hS
      map_add' := select_add μ S hS
      map_smul' := select_smul μ S hS }
    1 (fun f => by simpa using norm_select_le μ S hS f)

theorem select_eq_self_iff (f : Lp ℂ 2 μ) :
    select μ S hS f = f ↔ ∀ᵐ x ∂μ, x ∉ S → f x = 0 := by
  constructor
  · intro heq
    have ha := select_ae μ S hS f
    rw [heq] at ha
    filter_upwards [ha] with x hx hs
    simpa only [Set.indicator_of_notMem hs] using hx
  · intro ha
    apply Lp.ext
    filter_upwards [select_ae μ S hS f, ha] with x hx hz
    rw [hx]
    by_cases hs : x ∈ S
    · exact Set.indicator_of_mem hs f
    · rw [Set.indicator_of_notMem hs, hz hs]

theorem select_idempotent (f : Lp ℂ 2 μ) :
    select μ S hS (select μ S hS f) = select μ S hS f := by
  apply (select_eq_self_iff μ S hS _).mpr
  filter_upwards [select_ae μ S hS f] with x hx hs
  simpa only [Set.indicator_of_notMem hs] using hx

theorem select_commutes_pullback (T : X → X) (hT : MeasurePreserving T μ μ)
    (hinvariant : ∀ x, T x ∈ S ↔ x ∈ S) (f : Lp ℂ 2 μ) :
    select μ S hS (Lp.compMeasurePreserving T hT f) =
      Lp.compMeasurePreserving T hT (select μ S hS f) := by
  apply Lp.ext
  filter_upwards [select_ae μ S hS (Lp.compMeasurePreserving T hT f),
    Lp.coeFn_compMeasurePreserving f hT,
    Lp.coeFn_compMeasurePreserving (select μ S hS f) hT,
    hT.quasiMeasurePreserving.ae_eq_comp (select_ae μ S hS f)] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h2 h3 h4
  by_cases hx : x ∈ S
  · have htx := (hinvariant x).mpr hx
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem htx] at h1 h4
    rw [h1, h2, h3, h4]
  · have htx : T x ∉ S := fun h => hx ((hinvariant x).mp h)
    simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem htx] at h1 h4
    rw [h1, h3, h4]

end

end NCG.MeasurableRecordProjection
