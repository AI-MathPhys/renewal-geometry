/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Almost-sure one-step events for Ionescu--Tulcea trajectories

This file extracts a reusable consequence of the Ionescu--Tulcea joint-law
identity.  If every value of a transition kernel assigns mass one to a
measurable set, then the corresponding next coordinate of the infinite
trajectory belongs to that set almost surely.
-/

open MeasureTheory ProbabilityTheory Set Preorder
open ProbabilityTheory.Kernel

noncomputable section

namespace NCG.TrajectoryKernelAlmostSureEvent

set_option linter.style.haveILetI false

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]
  {κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))}
  [∀ n, IsMarkovKernel (κ n)]

/-- Exact probability-one transfer from a one-step kernel to the next
coordinate of its Ionescu--Tulcea trajectory. -/
theorem trajMeasure_next_mem_eq_one
    (n : ℕ) (A : Set (X (n + 1))) (hA : MeasurableSet A)
    (hκ : ∀ x, κ n x A = 1) :
    trajMeasure μ₀ κ {z | z (n + 1) ∈ A} = 1 := by
  let joint : (Π i, X i) →
      (Π i : Finset.Iic n, X i) × X (n + 1) :=
    fun z => (frestrictLe n z, z (n + 1))
  have hjoint :
      (trajMeasure μ₀ κ).map (frestrictLe n) ⊗ₘ κ n =
        (trajMeasure μ₀ κ).map joint := by
    simpa [joint] using
      (map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (μ₀ := μ₀) (κ := κ) (a := n))
  have hpreimage : joint ⁻¹' (Set.univ ×ˢ A) = {z | z (n + 1) ∈ A} := by
    ext z
    simp [joint]
  letI : IsProbabilityMeasure
      ((trajMeasure μ₀ κ).map (frestrictLe n)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  calc
    trajMeasure μ₀ κ {z | z (n + 1) ∈ A} =
        (trajMeasure μ₀ κ).map joint (Set.univ ×ˢ A) := by
      rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod hA), hpreimage]
    _ = ((trajMeasure μ₀ κ).map (frestrictLe n) ⊗ₘ κ n)
        (Set.univ ×ˢ A) := by rw [hjoint]
    _ = ∫⁻ x in Set.univ, κ n x A ∂
        (trajMeasure μ₀ κ).map (frestrictLe n) := by
      rw [Measure.compProd_apply_prod MeasurableSet.univ hA]
    _ = 1 := by
      simp_rw [hκ]
      simp

end NCG.TrajectoryKernelAlmostSureEvent
