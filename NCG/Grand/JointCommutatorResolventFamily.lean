/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorResolvent

/-!
# All-shift families of finite joint-commutator resolvents

The graph-Mosco compilers take a resolvent family defined at every real shift
and require its equation only at positive shifts.  This module packages the
canonical positive inverse and uses zero outside the positive half-line,
providing exactly that interface for a changing finite cutoff family.
-/

noncomputable section

namespace NCG

universe u

/-- The canonical finite joint-commutator resolvent, extended by zero at
nonpositive shifts. -/
noncomputable def jointCommutatorResolventAllShifts
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) :
    EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  if hlam : 0 < lam then jointCommutatorResolvent c lam hlam else 0

/-- At every positive shift, the all-shift package satisfies the exact weak
graph-resolvent equation. -/
theorem jointCommutatorResolventAllShifts_resolventEquation
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) (hlam : 0 < lam)
    (f : EuclideanSpace ℂ (n × n)) :
    NCG.VaryingHilbert.OperatorGraphResolventEquation
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (n × n)))
      (NCG.VaryingHilbert.boundedOperatorGraphMap (jointCommutatorCLM c))
      lam f (jointCommutatorResolventAllShifts c lam f) := by
  rw [jointCommutatorResolventAllShifts, dif_pos hlam]
  exact jointCommutatorResolvent_resolventEquation c lam hlam f

/-- The canonical resolvent family for a changing sequence of finite
joint-commutator cutoffs. -/
noncomputable def jointCommutatorResolventFamily
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (lam : ℝ) (cutoff : ℕ) :
    EuclideanSpace ℂ (d cutoff × d cutoff) →L[ℂ]
      EuclideanSpace ℂ (d cutoff × d cutoff) :=
  jointCommutatorResolventAllShifts (c cutoff) lam

/-- The changing-cutoff canonical resolvent family satisfies the stagewise
weak graph equations at every positive shift. -/
theorem jointCommutatorResolventFamily_resolventEquation
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (lam : ℝ) (hlam : 0 < lam) (cutoff : ℕ)
    (f : EuclideanSpace ℂ (d cutoff × d cutoff)) :
    NCG.VaryingHilbert.OperatorGraphResolventEquation
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
      (NCG.VaryingHilbert.boundedOperatorGraphMap
        (jointCommutatorCLM (c cutoff)))
      lam f (jointCommutatorResolventFamily c lam cutoff f) := by
  exact jointCommutatorResolventAllShifts_resolventEquation
    (c cutoff) lam hlam f

end NCG
