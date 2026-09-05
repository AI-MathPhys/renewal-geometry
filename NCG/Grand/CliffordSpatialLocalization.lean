/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FinalPanels2

/-!
# Spatial localization of the Clifford occurrence

This module completes `cor:SMST-Clifford-spatial-route`.  The numerical lower
bound is `spatial_route_bound`; the results below supply the previously missing
tetrahedral-covariance clause at the matrix level.
-/

open Matrix

namespace NCG

/-- Unitary conjugation preserves the trace of a finite matrix. -/
theorem trace_eq_of_unitary_conjugate {n : Type*} [Fintype n]
    [DecidableEq n] (A B U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (hconj : B = U * A * Uᴴ) : B.trace = A.trace := by
  rw [hconj, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- A transitive tetrahedral covariance action makes the three spatial block
traces, and therefore their occurrence masses, equal. -/
theorem tetrahedral_covariance_spatial_mass
    {G n : Type*} [Fintype n] [DecidableEq n]
    (act : G → Fin 3 → Fin 3)
    (htrans : ∀ i j : Fin 3, ∃ g, act g i = j)
    (U : G → Matrix n n ℂ) (hU : ∀ g, (U g)ᴴ * U g = 1)
    (block : Fin 3 → Matrix n n ℂ)
    (hcov : ∀ g i, block (act g i) = U g * block i * (U g)ᴴ) :
    ∀ i j, (block i).trace.re = (block j).trace.re := by
  intro i j
  obtain ⟨g, hg⟩ := htrans i j
  have ht : (block (act g i)).trace = (block i).trace :=
    trace_eq_of_unitary_conjugate (block i) (block (act g i)) (U g)
      (hU g) (hcov g i)
  rw [hg] at ht
  exact congrArg Complex.re ht.symm

/-- Exact corollary bundle: the spatial lower bound together with equality of
the three spatial masses under tetrahedral covariance. -/
theorem clifford_spatial_localization
    {G n : Type*} [Fintype n] [DecidableEq n]
    (pt ps : ℝ) (hpt : pt ≤ 1) (hps : 0 ≤ ps)
    (act : G → Fin 3 → Fin 3)
    (htrans : ∀ i j : Fin 3, ∃ g, act g i = j)
    (U : G → Matrix n n ℂ) (hU : ∀ g, (U g)ᴴ * U g = 1)
    (block : Fin 3 → Matrix n n ℂ)
    (hcov : ∀ g i, block (act g i) = U g * block i * (U g)ᴴ) :
    ps ≥ max 0 ((4 * ((pt + 3 * ps) / 4) - 1) / 3)
      ∧ ∀ i j, (block i).trace.re = (block j).trace.re :=
  ⟨spatial_route_bound pt ps hpt hps,
    tetrahedral_covariance_spatial_mass act htrans U hU block hcov⟩

end NCG
