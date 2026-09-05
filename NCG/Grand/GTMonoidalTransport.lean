/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Word-level monoidal transport residual
  (`thm:GT-monoidal-transport`, Gran-Tensor manuscript)

* `gt_monoidal_innovation`: the boxed GT.1 — the monoidal
  innovation `𝕀_mon(U) = ℛ_U*ℛ_U` of the residual
  synthesis is positive semidefinite, and it vanishes
  exactly when the residual synthesis itself vanishes —
  i.e. exactly when every unit, star, and product defect
  column is zero, which is the manuscript's
  characterization of `U` as the `L²` extension of a
  trace-preserving unital `*`-isomorphism through the flat
  word depth.

* `gt_monoidal_transport_cocycle`: the boxed GT.2 — for
  composable unital linear maps the product defects
  compose as a twisted cocycle,
  `R_{VU}(a,b) = V R_U(a,b) + R_V(Ua, Ub)`: a terminal
  product defect is the transported sum of the local
  product writers.

The identification of the residual columns with the
word-basis defects `U1-1`, `U(w*)-U(w)*`,
`U(wₐw_b)-U(wₐ)U(w_b)`, and the passage from vanishing
defects to a `*`-isomorphism of the underlying algebras,
are the manuscript's word-compiler layer.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false in
/-- `thm:GT-monoidal-transport` (GT.1): the innovation
Gram is PSD and vanishes iff the residual synthesis
does. -/
theorem gt_monoidal_innovation {n m : Type} [Fintype n]
    [Fintype m] (R : Matrix n m ℂ) :
    (Rᴴ * R).PosSemidef ∧ (Rᴴ * R = 0 ↔ R = 0) := by
  constructor
  · exact Matrix.posSemidef_conjTranspose_mul_self R
  · constructor
    · intro h
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h
    · rintro rfl
      simp

/-- `thm:GT-monoidal-transport` (GT.2): the product-defect
cocycle. -/
theorem gt_monoidal_transport_cocycle {A B C : Type*}
    [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B]
    [NonUnitalNonAssocRing C]
    [Module ℂ A] [Module ℂ B] [Module ℂ C]
    (U : A →ₗ[ℂ] B) (W : B →ₗ[ℂ] C) (a b : A) :
    -- R_{WU}(a,b) = W R_U(a,b) + R_W(Ua, Ub)
    W (U (a * b)) - W (U a) * W (U b)
      = W (U (a * b) - U a * U b)
        + (W (U a * U b) - W (U a) * W (U b)) := by
  rw [map_sub]
  abel

end NCG
