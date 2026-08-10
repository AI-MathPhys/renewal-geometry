/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveBlockContractionFactorization

/-!
# Physical two-history coherence

This module states the singular-support contraction factorization in the
upper-right-block orientation used by the Gran-Tensor manuscript.  The
diagonal blocks need only be positive semidefinite; no invertibility or
faithfulness hypothesis is imposed.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false

/-- A positive two-history block has exactly a square-root factorization of
its off-diagonal block by a contraction.  Singular directions are handled by
the polar support construction in `positiveBlock_iff_contractionFactorization`;
the contraction is extended by zero away from the two supports. -/
theorem coherenceFactorization_onSupports {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (X : Matrix (Fin n) (Fin m) ℂ) :
    (Matrix.fromBlocks A X Xᴴ B).PosSemidef ↔
      ∃ C : Matrix (Fin n) (Fin m) ℂ,
        ((1 : Matrix (Fin m) (Fin m) ℂ) - Cᴴ * C).PosSemidef ∧
        X = CFC.sqrt A * C * CFC.sqrt B := by
  rw [fromBlocks_posSemidef_swap_iff]
  exact positiveBlock_iff_contractionFactorization hB hA X

/-- Controlled Choi completions of two positive histories are parameterized
exactly by contractions between their support spaces. -/
theorem physicalTwoHistoryCoherence_parameterization {n m : ℕ}
    (J₀ : Matrix (Fin n) (Fin n) ℂ)
    (J₁ : Matrix (Fin m) (Fin m) ℂ)
    (hJ₀ : J₀.PosSemidef) (hJ₁ : J₁.PosSemidef)
    (X : Matrix (Fin n) (Fin m) ℂ) :
    (Matrix.fromBlocks J₀ X Xᴴ J₁).PosSemidef ↔
      ∃ C : Matrix (Fin n) (Fin m) ℂ,
        ((1 : Matrix (Fin m) (Fin m) ℂ) - Cᴴ * C).PosSemidef ∧
        X = CFC.sqrt J₀ * C * CFC.sqrt J₁ :=
  coherenceFactorization_onSupports hJ₀ hJ₁ X

end NCG
