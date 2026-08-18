/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventRangeShiftTransport

/-!
# Transport of real-parameter resolvent ranges between shifts

This specializes source transport to real resolvent parameters on either real or complex
Hilbert spaces.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- Real-parameter version of the resolvent source-transform identity. -/
theorem realResolvent_apply_sourceTransform
    (T : ℝ → E →L[K] E)
    (hres : ∀ a b,
      T a - T b = (((b - a : ℝ) : K)) • ((T a).comp (T b)))
    (a b : ℝ) (x : E) :
    T a (x + (((a - b : ℝ) : K)) • T b x) = T b x := by
  have hid := DFunLike.congr_fun (hres a b) x
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] at hid
  rw [map_add, map_smul]
  apply sub_eq_zero.mp
  calc
    (T a x + (((a - b : ℝ) : K)) • T a (T b x)) - T b x =
        (T a x - T b x) + (((a - b : ℝ) : K)) • T a (T b x) := by abel
    _ = (((b - a : ℝ) : K)) • T a (T b x) +
          (((a - b : ℝ) : K)) • T a (T b x) := by rw [hid]
    _ = 0 := by rw [← add_smul]; norm_num

/-- All real shifts of a resolvent family on an `RCLike` Hilbert space have the same range. -/
theorem range_realResolvent_eq_of_secondResolventIdentity
    (T : ℝ → E →L[K] E)
    (hres : ∀ a b,
      T a - T b = (((b - a : ℝ) : K)) • ((T a).comp (T b)))
    (a b : ℝ) :
    Set.range (T a) = Set.range (T b) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨x + (((b - a : ℝ) : K)) • T a x, ?_⟩
    exact realResolvent_apply_sourceTransform T hres b a x
  · rintro y ⟨x, rfl⟩
    refine ⟨x + (((a - b : ℝ) : K)) • T b x, ?_⟩
    exact realResolvent_apply_sourceTransform T hres a b x

/-- A varying real-shift energy core can be transported to any fixed real shift, also for a
complex Hilbert space. -/
theorem fixedRealShift_energyCore_of_varyingShift_energyCore
    {Y : Type w} [TopologicalSpace Y]
    (q : E → Y) (T : ℝ → E →L[K] E)
    (hres : ∀ a b,
      T a - T b = (((b - a : ℝ) : K)) • ((T a).comp (T b)))
    (shift : ℕ → ℝ)
    (hcore : ∀ x : E, ∃ source : ℕ → E,
      Tendsto (fun n ↦ T (shift n) (source n)) atTop (nhds x) ∧
        Tendsto (fun n ↦ q (T (shift n) (source n))) atTop (nhds (q x)))
    (a : ℝ) :
    ∀ x : E, ∃ source : ℕ → E,
      Tendsto (fun n ↦ T a (source n)) atTop (nhds x) ∧
        Tendsto (fun n ↦ q (T a (source n))) atTop (nhds (q x)) := by
  intro x
  obtain ⟨source, hvec, henergy⟩ := hcore x
  let fixedSource : ℕ → E := fun n ↦
    source n + (((a - shift n : ℝ) : K)) • T (shift n) (source n)
  have hfixed : ∀ n, T a (fixedSource n) = T (shift n) (source n) := by
    intro n
    exact realResolvent_apply_sourceTransform T hres a (shift n) (source n)
  refine ⟨fixedSource, ?_, ?_⟩
  · exact hvec.congr' (Eventually.of_forall fun n ↦ (hfixed n).symm)
  · exact henergy.congr' (Eventually.of_forall fun n ↦ congrArg q (hfixed n).symm)

end NCG.VaryingHilbert
