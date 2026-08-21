/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusFourierInterpolation
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Filter.Finite

/-!
# Stabilization of centered finite-torus frequencies

Every fixed integer frequency is eventually its own centered representative
modulo `N + 1`.  For finitely many coordinates, the stabilization holds
simultaneously.  This is the changing-cutoff bridge from fixed continuum
Fourier boxes to finite `ZMod` frequencies.
-/

open Filter

namespace NCG

/-- A fixed integer is eventually unchanged by taking its centered residue
modulo `N + 1`. -/
theorem eventually_valMinAbs_intCast_eq (a : ℤ) :
    ∀ᶠ N : ℕ in atTop,
      ((a : ZMod (N + 1)).valMinAbs = a) := by
  filter_upwards [eventually_gt_atTop (2 * a.natAbs)] with N hN
  cases a with
  | ofNat m =>
      change 2 * m < N at hN
      apply (ZMod.valMinAbs_spec _ _).2
      refine ⟨rfl, ?_, ?_⟩
      · change -(N + 1 : ℤ) < (m : ℤ) * 2
        omega
      · change (m : ℤ) * 2 ≤ (N + 1 : ℤ)
        omega
  | negSucc m =>
      change 2 * (m + 1) < N at hN
      apply (ZMod.valMinAbs_spec _ _).2
      refine ⟨rfl, ?_, ?_⟩
      · change -(N + 1 : ℤ) < (-((m : ℤ) + 1)) * 2
        omega
      · change (-((m : ℤ) + 1)) * 2 ≤ (N + 1 : ℤ)
        omega
/-- A fixed multidimensional integer frequency is eventually unchanged
coordinatewise by centered reduction modulo `N + 1`. -/
theorem eventually_finiteTorusCenteredFrequency_intCast_eq
    {d : Type*} [Fintype d] [DecidableEq d] (k : d → ℤ) :
    ∀ᶠ N : ℕ in atTop,
      finiteTorusCenteredFrequency
          (N := N + 1) (fun j => (k j : ZMod (N + 1))) = k := by
  have hcoord (j : d) :
      ∀ᶠ N : ℕ in atTop,
        (((k j : ℤ) : ZMod (N + 1)).valMinAbs = k j) :=
    eventually_valMinAbs_intCast_eq (k j)
  have hall := (eventually_all).2 hcoord
  filter_upwards [hall] with N hN
  funext j
  exact hN j

/-- Every mode in a fixed finite continuum Fourier box is eventually
represented by its own centered finite-torus residue, simultaneously. -/
theorem eventually_forall_mem_finiteBox_centeredFrequency_intCast_eq
    {d : Type*} [Fintype d] [DecidableEq d]
    (s : Finset (d → ℤ)) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ s,
      finiteTorusCenteredFrequency
          (N := N + 1) (fun j => (k j : ZMod (N + 1))) = k := by
  rw [eventually_all_finset]
  intro k _
  exact eventually_finiteTorusCenteredFrequency_intCast_eq k

end NCG
