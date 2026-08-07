/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sealed-provenance cocycle and centered response
  (`thm:sealed-provenance-cocycle`, Gran-Tensor manuscript)

* `sealed_provenance_cocycle`: for sealed (block
  lower-triangular) extensions `T̃ = [[T,0],[H,D]]` on
  `L ⊕ E`:
  (i) the boxed cocycle `H_{vw} = H_v·T_w + D_v·H_w` and
      `D_{vw} = D_v·D_w` — composition of two sealed
      extensions is sealed with exactly these blocks;
  (ii) the table-native centered response
      `K = Y_{vw} - Y_v·T_w` equals the boxed
      `R·D_v·H_w` for every passive Read `R`.

Word-level assembly over `Σ*` is the iteration of the
two-letter identity proved here.
-/

open Matrix

namespace NCG

/-- `thm:sealed-provenance-cocycle`. -/
theorem sealed_provenance_cocycle {l e y : Type*} [Fintype l]
    [Fintype e]
    (Tv Tw : Matrix l l ℂ) (Hv Hw : Matrix e l ℂ)
    (Dv Dw : Matrix e e ℂ) (R : Matrix y e ℂ) :
    -- (i) the sealed cocycle
    fromBlocks Tv 0 Hv Dv * fromBlocks Tw 0 Hw Dw
      = fromBlocks (Tv * Tw) 0 (Hv * Tw + Dv * Hw) (Dv * Dw)
    -- (ii) the centered response is `R·D_v·H_w`
    ∧ R * (Hv * Tw + Dv * Hw) - R * Hv * Tw
        = R * (Dv * Hw) := by
  constructor
  · rw [Matrix.fromBlocks_multiply]
    congr 1 <;> simp
  · rw [Matrix.mul_add]
    simp [Matrix.mul_assoc]

end NCG
