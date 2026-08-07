/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cartan closure of the shift sector
  (`thm:SMST-shift-Cartan`, Gran-Tensor manuscript)

* `smst_shift_cartan`: writing the affine torsion of the
  shift sector in frame components as
  `T(ω₀) = D + (ω₀ - W)·E - N·FK`
  (`D` the drift derivative `(∂₀ - L_β)E`, `W` the spatial
  inflow `βʲω_j`, `FK = E^{-T}K` the extrinsic term, `E`
  the invertible spatial frame):
  (a) the boxed canonical Cartan rotation
      `ω₀^C = W + N·FK·E⁻¹ - D·E⁻¹`
      kills the torsion exactly, `T(ω₀^C) = 0`;
  (b) uniqueness: every torsion-free rotation equals
      `ω₀^C`, so the shift sector closes to a unique
      Levi-Civita-compatible Cartan connection.

The identification of `D`, `W`, `FK` with the geometric
drift, inflow, and extrinsic-curvature data of the moving
frame (and the metricity of the resulting connection) is the
manuscript's frame bookkeeping over this unique-solution
core.
-/

open Matrix

namespace NCG

/-- `thm:SMST-shift-Cartan`. -/
theorem smst_shift_cartan {n : Type*} [Fintype n]
    [DecidableEq n] (E D W FK : Matrix n n ℂ) (N : ℂ)
    [Invertible E] :
    -- (a) the boxed canonical rotation kills the torsion
    D + ((W + N • (FK * E⁻¹) - D * E⁻¹) - W) * E - N • FK
      = 0
    -- (b) uniqueness of the torsion-free rotation
    ∧ (∀ ω : Matrix n n ℂ,
        D + (ω - W) * E - N • FK = 0 →
        ω = W + N • (FK * E⁻¹) - D * E⁻¹) := by
  have hEcan : ∀ X : Matrix n n ℂ, X * E⁻¹ * E = X := by
    intro X
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.mul_one]
  constructor
  · have hcoll : (W + N • (FK * E⁻¹) - D * E⁻¹) - W
        = N • (FK * E⁻¹) - D * E⁻¹ := by abel
    rw [hcoll, Matrix.sub_mul, Matrix.smul_mul, hEcan,
      hEcan]
    abel
  · intro ω hω
    have h1 : (ω - W) * E = N • FK - D := by
      rw [eq_sub_iff_add_eq, ← sub_eq_zero]
      calc (ω - W) * E + D - N • FK
          = D + (ω - W) * E - N • FK := by abel
        _ = 0 := hω
    have h2 := congrArg (fun X => X * E⁻¹) h1
    rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul]
      at h2
    rw [sub_eq_iff_eq_add] at h2
    rw [h2]
    abel

end NCG
