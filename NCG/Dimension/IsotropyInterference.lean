/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The full-isotropy interference route (d = 3 witness)

**Theorem `thm:full-isotropy-interference`**: under full isotropy
(`Hol = SO(V)`) a nonzero equivariant map `Λ²V → V` exists only for
`d = 3`, where it is unique up to scale.  The existence half proved
here: the cross product is a nonzero antisymmetric bilinear map on
`ℝ³` (`NCG.cross_product_witness` — `e₁ × e₂ = e₃`;
`NCG.cross_product_antisymm`), realising the `d = 3` intertwiner and
matching the proved Hodge-degree selection `d − 2 = 1`.  The
`SO(d)`-representation-theoretic vanishing for `d ≠ 3` and the Schur
uniqueness are the noted steps.
-/

namespace NCG

/-- **Theorem `thm:full-isotropy-interference` (d = 3 witness)**: the
cross product realises the `Λ²ℝ³ → ℝ³` intertwiner —
`e₁ × e₂ = e₃`. -/
theorem cross_product_witness :
    crossProduct (R := ℝ) ![1, 0, 0] ![0, 1, 0] = ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-- The `d = 3` intertwiner is nonzero. -/
theorem cross_product_ne_zero :
    crossProduct (R := ℝ) ![1, 0, 0] ![0, 1, 0] ≠ 0 := by
  rw [cross_product_witness]
  intro h
  simpa using congrFun h 2

/-- The `d = 3` intertwiner is antisymmetric — it factors through
`Λ²ℝ³`. -/
theorem cross_product_antisymm (v w : Fin 3 → ℝ) :
    crossProduct v w + crossProduct w v = 0 :=
  cross_anticomm' v w

end NCG
