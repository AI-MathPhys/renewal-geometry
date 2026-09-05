/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RealMoscoResolventConvergence

/-!
# Semibounded Mosco convergence and shifted resolvents

A form with lower bound `-c` becomes nonnegative after adding `c * ‖x‖²`.  Its resolvent
objective at a parameter `lam > c` is exactly the objective of the shifted form at the positive
parameter `lam - c`.  This file packages that reduction together with the varying-Hilbert
Mosco-to-resolvent theorem.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E]

/-- Add a common quadratic lower-bound correction to a real-valued form. -/
def semiboundedShift (q : E → ℝ) (c : ℝ) (x : E) : ℝ :=
  q x + c * ‖x‖ ^ 2

/-- Shifting the form by `c` and the resolvent parameter by `-c` leaves the objective unchanged. -/
@[simp]
theorem resolventObjective_semiboundedShift
    [InnerProductSpace K E]
    (q : E → ℝ) (c lam : ℝ) (f x : E) :
    resolventObjective (K := K) (semiboundedShift q c) (lam - c) f x =
      resolventObjective (K := K) q lam f x := by
  simp only [resolventObjective, semiboundedShift]
  ring

namespace System

universe w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- The forward semibounded Mosco theorem.  Mosco convergence is imposed on the nonnegative
shifted forms, while the displayed operators minimize the original objectives at `lam > c`.
The quadratic-shift identity reduces the claim to the positive-parameter theorem. -/
theorem strongOperatorConverges_resolvents_of_semibounded_realMosco_minimizers
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) (c : ℝ)
    (hmosco : J.RealMoscoConverges
      (fun n ↦ semiboundedShift (q n) c) (semiboundedShift qlim c))
    (lam : ℝ) (hlam : c < lam)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hqconvex : ∀ n, ConvexOn ℝ univ (semiboundedShift (q n) c))
    (hqlimConvex : ConvexOn ℝ univ (semiboundedShift qlim c))
    (hq0 : ∀ n, q n 0 = 0)
    (hqLower : ∀ n (z : Hn n), -c * ‖z‖ ^ 2 ≤ q n z)
    (hstageMin : ∀ n (f z : Hn n),
      resolventObjective (K := K) (q n) lam f (Tn n f) ≤
        resolventObjective (K := K) (q n) lam f z)
    (hlimitMin : ∀ (f z : H),
      resolventObjective (K := K) qlim lam f (T f) ≤
        resolventObjective (K := K) qlim lam f z) :
    J.StrongOperatorConverges J Tn T := by
  apply strongOperatorConverges_resolvents_of_realMosco_minimizers J
    (fun n ↦ semiboundedShift (q n) c) (semiboundedShift qlim c)
    hmosco (lam - c) (sub_pos.mpr hlam) Tn T hqconvex hqlimConvex
  · intro n
    simp [semiboundedShift, hq0 n]
  · intro n z
    dsimp [semiboundedShift]
    linarith [hqLower n z]
  · intro n f z
    simpa using hstageMin n f z
  · intro f z
    simpa using hlimitMin f z

end System

end NCG.VaryingHilbert
