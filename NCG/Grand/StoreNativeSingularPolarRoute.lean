/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SingularPolarData

/-!
# Singular Moore--Penrose polar route for the Store generator
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- (R4) Singular Moore--Penrose polar data for the Store route.  In
particular, the normalized route is exactly `B * Pd`, its initial support is
`UᴴU`, and it is a partial isometry even when `BᴴB` is singular. -/
theorem storeRoute_singularPolarSupport {e : ℕ}
    (B : Matrix (Fin e) (Fin e) ℂ) :
    ∃ (U P Pd : Matrix (Fin e) (Fin e) ℂ),
      P.PosSemidef ∧ P * P = Bᴴ * B ∧
      U = B * Pd ∧ B = U * P ∧
      U * (Uᴴ * U) = U ∧
      P * Pd = Uᴴ * U ∧ Pd * P = Uᴴ * U := by
  obtain ⟨U, P, Pd, hP, hBUP, hP2, hpartial, hPPd, hPdP, _⟩ :=
    exists_singular_polar_data B
  have hUBPd : U = B * Pd := by
    calc
      U = U * (Uᴴ * U) := hpartial.symm
      _ = U * (P * Pd) := by rw [hPPd]
      _ = (U * P) * Pd := by simp only [Matrix.mul_assoc]
      _ = B * Pd := by rw [← hBUP]
  exact ⟨U, P, Pd, hP, hP2, hUBPd, hBUP, hpartial, hPPd, hPdP⟩

end NCG
