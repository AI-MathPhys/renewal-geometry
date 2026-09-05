/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CoherenceFactorization

/-!
# Marginal canonicality does not determine relative orientation
  (`cth:marginals-no-relative-orientation`,
  Gran-Tensor manuscript)

* `fromBlocks_posSemidef_swap_iff`: block-swap invariance of
  positive semidefiniteness (conjugation by the sum-swap
  permutation).
* `marginals_no_relative_orientation`: for faithful marginal
  Grams `G₁ ≻ 0`, `G₂ ≻ 0`, the positive completions of the
  joint Gram `[[G₁, C₂₁ᴴ],[C₂₁, G₂]]` are precisely the boxed
  family `C₂₁ = √G₂ · K · √G₁` with `K` a contraction
  (`I - KᴴK ⪰ 0`) — a full contraction ball of relative
  orientations survives both canonical marginals.

Rendering disclosed: the manuscript's Moore–Penrose extension
to non-faithful supports is rendered by positive definiteness
(the compressions to the faithful source supports), which is
the manuscript's own support reduction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- Positive semidefiniteness is invariant under the block
swap (conjugation by the sum-swap permutation matrix). -/
theorem fromBlocks_posSemidef_swap_iff {n m : Type*}
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (D : Matrix m m ℂ) :
    (Matrix.fromBlocks A B C D).PosSemidef
      ↔ (Matrix.fromBlocks D C B A).PosSemidef := by
  constructor
  · intro h
    have hs := h.submatrix (Sum.swap : m ⊕ n → n ⊕ m)
    rwa [Matrix.fromBlocks_submatrix_sum_swap_sum_swap] at hs
  · intro h
    have hs := h.submatrix (Sum.swap : n ⊕ m → m ⊕ n)
    rwa [Matrix.fromBlocks_submatrix_sum_swap_sum_swap] at hs

/-- `cth:marginals-no-relative-orientation`. -/
theorem marginals_no_relative_orientation {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {G₁ : Matrix n n ℂ} {G₂ : Matrix m m ℂ}
    (hG₁ : G₁.PosDef) (hG₂ : G₂.PosDef) (C₂₁ : Matrix m n ℂ) :
    (Matrix.fromBlocks G₁ C₂₁ᴴ C₂₁ G₂).PosSemidef
      ↔ ∃ K : Matrix m n ℂ,
          ((1 : Matrix n n ℂ) - Kᴴ * K).PosSemidef
          ∧ C₂₁ = CFC.sqrt G₂ * K * CFC.sqrt G₁ := by
  rw [fromBlocks_posSemidef_swap_iff]
  exact coherence_factorization hG₂ hG₁ C₂₁

end NCG
