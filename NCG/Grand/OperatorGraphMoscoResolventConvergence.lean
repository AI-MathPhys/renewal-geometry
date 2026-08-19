/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExtendedENNRealMoscoResolventConvergenceFromConvexity
import NCG.Grand.ENNRealOperatorGraphResolventMinimizer

/-!
# Resolvent convergence of Mosco-convergent operator graphs

Weak Euler equations for squared operator-graph energies give finite-energy ranges and exact
variational minimizers.  Since graph energies are automatically convex, cofinal Mosco
convergence therefore implies strong resolvent convergence at every positive shift.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z z'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ K H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
  [NormedSpace ℝ F] [IsScalarTower ℝ K F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ K (Fn n)]

/-- Cofinal Mosco convergence and weak graph resolvent equations imply strong operator
convergence of the resolvents at every positive real shift. -/
theorem operatorGraphMosco_strongResolvents_allPositive
    (J : System (K := K) (H := H) (Hn := Hn))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (D : Submodule K H) (A : D →ₗ[K] F)
    (Rn : ℝ → ∀ n, Hn n →L[K] Hn n) (R : ℝ → H →L[K] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn lam n f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f)) :
    ∀ lam, 0 < lam → J.StrongOperatorConverges J (Rn lam) (R lam) := by
  intro lam hlam
  let qn : (n : ℕ) → Hn n → ℝ≥0∞ :=
    fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n)
  let q : H → ℝ≥0∞ := ennrealOperatorGraphEnergy D A
  apply J.strongOperatorConverges_resolvents_of_extendedCofinalMosco_minimizers
    qn q (by simpa [qn, q] using hmosco) lam hlam (Rn lam) (R lam)
  · intro n
    simp [qn]
  · intro n f
    simpa [qn] using (hstageEquation lam hlam n f).mem
  · intro f
    simpa [q] using (hlimitEquation lam hlam f).mem
  · intro n
    simpa [qn] using convexOn_ennrealOperatorGraphEnergy (Dn n) (An n)
  · simpa [q] using convexOn_ennrealOperatorGraphEnergy D A
  · intro n f z hz
    apply operatorGraph_resolventObjective_minimizer
      (Dn n) (An n) lam hlam.le f (Rn lam n f)
        (hstageEquation lam hlam n f) z
    simpa [qn] using hz
  · intro f z hz
    apply operatorGraph_resolventObjective_minimizer
      D A lam hlam.le f (R lam f) (hlimitEquation lam hlam f) z
    simpa [q] using hz

end NCG.VaryingHilbert.System
