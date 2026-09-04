/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Transporting all finite trajectory laws from one-step compatibility

A measurable reset/shift of prefixes that intertwines each concrete one-step
kernel intertwines every iterated prefix law. This is the finite-prefix
induction needed to identify a homogeneous Markov restart, and does not
assume equality of the iterated laws as a hypothesis.
-/

open MeasureTheory ProbabilityTheory
open Preorder
open ProbabilityTheory.Kernel

namespace NCG.TrajectoryPrefixTransport

variable {X Y : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]

/-- Equality of every finite initial-segment marginal determines a finite
measure on the full countable trajectory space. -/
theorem measure_eq_of_prefix_marginals (μ ν : Measure (Π n, X n)) [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (frestrictLe n) = ν.map (frestrictLe n)) : μ = ν := by
  let P := fun I : Finset ℕ => ν.map I.restrict
  letI : ∀ I, IsFiniteMeasure (P I) := fun I => by dsimp [P]; infer_instance
  have hP : IsProjectiveMeasureFamily P := by
    intro I J hJI
    dsimp [P]
    rw [Measure.map_map (by fun_prop) (by fun_prop), Finset.restrict₂_comp_restrict hJI]
  have hν : IsProjectiveLimit ν P := fun _ => rfl
  have hμ : IsProjectiveLimit μ P := (isProjectiveLimit_nat_iff hP μ).mpr h
  exact hμ.unique hν

/-- The same finite-prefix criterion applies pointwise to genuine finite
trajectory kernels. -/
theorem kernel_eq_of_prefix_marginals {A : Type*} [MeasurableSpace A]
    (K M : Kernel A (Π n, X n)) [IsFiniteKernel M]
    (h : ∀ n, K.map (frestrictLe n) = M.map (frestrictLe n)) : K = M := by
  ext a : 1
  apply measure_eq_of_prefix_marginals
  intro n
  simpa only [Kernel.map_apply _ (measurable_frestrictLe n)] using
    congrArg (fun Q : Kernel A (Π i : Finset.Iic n, X i) => Q a) (h n)

variable (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
variable (η : (n : ℕ) → Kernel (Π i : Finset.Iic n, Y i) (Y (n + 1)))
variable (a : ℕ)
variable (F : (n : ℕ) → (Π i : Finset.Iic (a + n), X i) → (Π i : Finset.Iic n, Y i))
variable (hF : ∀ n, Measurable (F n))

set_option backward.isDefEq.respectTransparency false in
/-- One-step kernel compatibility propagates to every finite prefix. -/
theorem map_partialTraj_eq_of_step_compatibility
    (hstep : ∀ n,
      (partialTraj κ (a + n) (a + (n + 1))).map (F (n + 1)) =
        partialTraj η n (n + 1) ∘ₖ Kernel.deterministic (F n) (hF n))
    (n : ℕ) :
    (partialTraj κ a (a + n)).map (F n) =
      partialTraj η 0 n ∘ₖ Kernel.deterministic (F 0) (hF 0) := by
  induction n with
  | zero => simp [hF 0]
  | succ n ih =>
    change (partialTraj κ a (a + n + 1)).map (F (n + 1)) =
      partialTraj η 0 (n + 1) ∘ₖ Kernel.deterministic (F 0) (hF 0)
    have hrec := partialTraj_succ_eq_comp (κ := κ) (Nat.le_add_right a n)
    have hs : (partialTraj κ (a + n) (a + n + 1)).map (F (n + 1)) =
        partialTraj η n (n + 1) ∘ₖ Kernel.deterministic (F n) (hF n) := hstep n
    rw [hrec, map_comp, hs,
      Kernel.comp_assoc, deterministic_comp_eq_map (hF n), ih,
      ← Kernel.comp_assoc,
      partialTraj_comp_partialTraj (κ := η) (Nat.zero_le n) (Nat.le_succ n)]

end NCG.TrajectoryPrefixTransport
