/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The twelve oriented `A₃` roots

`a3Roots` lists the twelve vectors `±eᵢ ± eⱼ` (`i < j`) of the `A₃ ≅ D₃` root system in `ℝ³`
(the nearest-neighbour vectors of the face-centred cubic lattice).

Split out of `RelationalFlatVacuum` (declaration name unchanged).
-/

namespace MathPhys

/-- The twelve oriented `A₃` roots. -/
def a3Roots : Fin 12 → (Fin 3 → ℝ) :=
  ![![1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 0],
    ![1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, -1],
    ![0, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, -1]]

end MathPhys
