/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventShiftPropagation

/-!
# Transport of resolvent ranges and energy cores between shifts

The second resolvent identity gives an explicit change of source which leaves the resolvent
image unchanged.  Consequently all resolvent shifts have exactly the same range, and an
energy core assembled using varying shifts can be transported to any fixed shift.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- The source transform associated with the second resolvent identity.  Applying the
`a`-resolvent to this transformed source gives exactly the original `b`-resolvent image. -/
theorem resolvent_apply_sourceTransform
    (T : K → E →L[K] E)
    (hres : ∀ a b,
      T a - T b = (b - a) • ((T a).comp (T b)))
    (a b : K) (x : E) :
    T a (x + (a - b) • T b x) = T b x := by
  have hid := DFunLike.congr_fun (hres a b) x
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] at hid
  rw [map_add, map_smul]
  apply sub_eq_zero.mp
  calc
    (T a x + (a - b) • T a (T b x)) - T b x =
        (T a x - T b x) + (a - b) • T a (T b x) := by abel
    _ = (b - a) • T a (T b x) + (a - b) • T a (T b x) := by rw [hid]
    _ = 0 := by rw [← add_smul]; simp

/-- Every pair of shifts of a family satisfying the second resolvent identity have the same
range. -/
theorem range_resolvent_eq_of_secondResolventIdentity
    (T : K → E →L[K] E)
    (hres : ∀ a b,
      T a - T b = (b - a) • ((T a).comp (T b)))
    (a b : K) :
    Set.range (T a) = Set.range (T b) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨x + (b - a) • T a x, ?_⟩
    exact resolvent_apply_sourceTransform T hres b a x
  · rintro y ⟨x, rfl⟩
    refine ⟨x + (a - b) • T b x, ?_⟩
    exact resolvent_apply_sourceTransform T hres a b x

/-- Transport a sequence of resolvent images at varying shifts to a fixed shift without
changing a single image. -/
theorem exists_fixedShift_sources_of_varyingShift_sources
    (T : K → E →L[K] E)
    (hres : ∀ a b,
      T a - T b = (b - a) • ((T a).comp (T b)))
    (a : K) (shift : ℕ → K) (source : ℕ → E) :
    ∃ fixedSource : ℕ → E, ∀ n,
      T a (fixedSource n) = T (shift n) (source n) := by
  refine ⟨fun n ↦ source n + (a - shift n) • T (shift n) (source n), ?_⟩
  intro n
  exact resolvent_apply_sourceTransform T hres a (shift n) (source n)

/-- A varying-shift energy core is automatically an energy core for every fixed resolvent
shift.  The statement is generic in the topology of the energy values. -/
theorem fixedShift_energyCore_of_varyingShift_energyCore
    {Y : Type w} [TopologicalSpace Y]
    (q : E → Y) (T : K → E →L[K] E)
    (hres : ∀ a b,
      T a - T b = (b - a) • ((T a).comp (T b)))
    (shift : ℕ → K)
    (hcore : ∀ x : E, ∃ source : ℕ → E,
      Tendsto (fun n ↦ T (shift n) (source n)) atTop (𝓝 x) ∧
        Tendsto (fun n ↦ q (T (shift n) (source n))) atTop (𝓝 (q x)))
    (a : K) :
    ∀ x : E, ∃ source : ℕ → E,
      Tendsto (fun n ↦ T a (source n)) atTop (𝓝 x) ∧
        Tendsto (fun n ↦ q (T a (source n))) atTop (𝓝 (q x)) := by
  intro x
  obtain ⟨source, hvec, henergy⟩ := hcore x
  obtain ⟨fixedSource, hfixed⟩ :=
    exists_fixedShift_sources_of_varyingShift_sources T hres a shift source
  refine ⟨fixedSource, ?_, ?_⟩
  · exact hvec.congr' (Eventually.of_forall fun n ↦ (hfixed n).symm)
  · exact henergy.congr' (Eventually.of_forall fun n ↦ congrArg q (hfixed n).symm)

end NCG.VaryingHilbert
