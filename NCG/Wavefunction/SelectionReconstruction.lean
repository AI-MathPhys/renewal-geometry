/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Selection–reconstruction duality
  (`prop:selection-reconstruction`, wavefunction)

Both branch selection (conditioning on a stable central sector) and
horizon reconstruction (enlarging the accessible radiation
subalgebra) are governed by one algebraic operation: restriction and
conditioning of record algebras.  The operative identity is the
conditioning tower:

* `conditionalState` — the Lüders/central conditional state
  `ρ_P = PρP / Tr(PρP)`;
* `conditioning_tower` — for nested sectors `W ≤ Z` (i.e.
  `WZ = ZW = W`), conditioning on the coarse sector and then the
  finer one equals conditioning on the finer sector directly:
  enlarging access refines selection consistently, in measurement
  and horizon settings alike.

The identification of measurement selection and horizon
reconstruction as the two readings of this tower is the manuscript's
interpretive framing.
-/

namespace NCG

variable {n : ℕ}

/-- The central/Lüders conditional state `PρP / Tr(PρP)`. -/
noncomputable def conditionalState (P rho : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((P * rho * P).trace)⁻¹ • (P * rho * P)

/-- `prop:selection-reconstruction` (conditioning tower): for nested
record sectors `W ≤ Z`, conditioning through the coarse sector and
then the finer one equals direct conditioning on the finer sector. -/
theorem conditioning_tower (Z W rho : Matrix (Fin n) (Fin n) ℂ)
    (hWZ : W * Z = W) (hZW : Z * W = W)
    (hZ : (Z * rho * Z).trace ≠ 0) :
    conditionalState W (conditionalState Z rho)
      = conditionalState W rho := by
  unfold conditionalState
  have hcollapse : W * (Z * rho * Z) * W = W * rho * W := by
    calc W * (Z * rho * Z) * W = W * Z * rho * (Z * W) := by
          simp only [Matrix.mul_assoc]
    _ = W * rho * W := by rw [hWZ, hZW]
  rw [Matrix.mul_smul, Matrix.smul_mul, hcollapse, Matrix.trace_smul,
    smul_smul]
  congr 1
  rw [smul_eq_mul, mul_inv, inv_inv]
  field_simp

end NCG
