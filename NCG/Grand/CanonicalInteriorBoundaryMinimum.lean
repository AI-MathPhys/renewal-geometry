/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProtectedObservableRieszPseudoinverseExact

/-!
# Canonical finite interior--boundary minimum

For a positive interior form `L` and a boundary operator `D`, this file
constructs the minimum-norm solution of

`L^{1/2} a + Dᴴ j = s`.

The construction uses the genuine spectral Moore--Penrose inverse of
`A = L + DᴴD`; it remains valid when `A` is singular.  Besides the source
decomposition and energy formula, we prove the full Pythagoras identity for
every competing representation.  This is the reusable variational layer in
`thm:NS-translation-helical-handoff` and the singular Thomson/Riesz records.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace CanonicalInteriorBoundaryMinimum

open GeometricThresholdBank SourceCoercivityInfluence PsdBlockSchur

variable {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- The stacked square-root/interior-boundary synthesis operator. -/
noncomputable def synthesis (L : Matrix n n ℂ) (D : Matrix m n ℂ) :
    Matrix (n ⊕ m) n ℂ :=
  Matrix.fromRows (CFC.sqrt L) D

/-- The positive action `A = L + DᴴD`. -/
def action (L : Matrix n n ℂ) (D : Matrix m n ℂ) : Matrix n n ℂ :=
  L + Dᴴ * D

theorem action_posSemidef (L : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hL : L.PosSemidef) : (action L D).PosSemidef := by
  exact hL.add (Matrix.posSemidef_conjTranspose_mul_self D)

/-- The stacked synthesis has Gram matrix `L + DᴴD`. -/
theorem synthesis_gram (L : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hL : L.PosSemidef) :
    (synthesis L D)ᴴ * synthesis L D = action L D := by
  simp only [synthesis, action,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  rw [sqrt_isHermitian L, sqrt_mul_self_eq L hL]

/-- Canonical stacked minimizer. -/
noncomputable def minimizer (L : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hL : L.PosSemidef) (s : n → ℂ) : (n ⊕ m) → ℂ :=
  synthesis L D *ᵥ (pinv (action_posSemidef L D hL).1 *ᵥ s)

theorem minimizer_apply (L : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hL : L.PosSemidef) (s : n → ℂ) :
    minimizer L D hL s = Sum.elim
      (CFC.sqrt L *ᵥ (pinv (action_posSemidef L D hL).1 *ᵥ s))
      (D *ᵥ (pinv (action_posSemidef L D hL).1 *ᵥ s)) := by
  simp [minimizer, synthesis]

/-- On the supported source range, the canonical pair synthesizes `s`. -/
theorem minimizer_feasible (L : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hL : L.PosSemidef) (s : n → ℂ)
    (hs : action L D *ᵥ
      (pinv (action_posSemidef L D hL).1 *ᵥ s) = s) :
    (synthesis L D)ᴴ *ᵥ minimizer L D hL s = s := by
  rw [minimizer, Matrix.mulVec_mulVec,
    synthesis_gram L D hL, hs]

/-- The canonical energy is the Moore--Penrose quadratic form. -/
theorem minimizer_energy (L : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hL : L.PosSemidef) (s : n → ℂ)
    (hs : action L D *ᵥ
      (pinv (action_posSemidef L D hL).1 *ᵥ s) = s) :
    star (minimizer L D hL s) ⬝ᵥ minimizer L D hL s =
      star s ⬝ᵥ (pinv (action_posSemidef L D hL).1 *ᵥ s) := by
  let A := action L D
  let G := pinv (action_posSemidef L D hL).1
  let x := G *ᵥ s
  let T := synthesis L D
  have hTH : Tᴴ * T = A := synthesis_gram L D hL
  have hGH : G.IsHermitian := pinv_isHermitian (action_posSemidef L D hL).1
  change star (T *ᵥ x) ⬝ᵥ (T *ᵥ x) = star s ⬝ᵥ (G *ᵥ s)
  calc
    star (T *ᵥ x) ⬝ᵥ (T *ᵥ x)
        = star x ⬝ᵥ ((Tᴴ * T) *ᵥ x) := by
          rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
            Matrix.mulVec_mulVec]
    _ = star x ⬝ᵥ s := by rw [hTH, hs]
    _ = star s ⬝ᵥ (G *ᵥ s) := by
      simpa [x] using
        (dotProduct_mulVec_hermitian hGH s s).symm

/-- Every feasible competitor splits orthogonally into the canonical
minimizer plus a vector in the kernel of the synthesis adjoint. -/
theorem feasible_pythagoras (L : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hL : L.PosSemidef) (s : n → ℂ)
    (hs : action L D *ᵥ
      (pinv (action_posSemidef L D hL).1 *ᵥ s) = s)
    (y : (n ⊕ m) → ℂ) (hy : (synthesis L D)ᴴ *ᵥ y = s) :
    star y ⬝ᵥ y =
      star (minimizer L D hL s) ⬝ᵥ minimizer L D hL s +
      star (y - minimizer L D hL s) ⬝ᵥ
        (y - minimizer L D hL s) := by
  let T := synthesis L D
  let y0 := minimizer L D hL s
  let z := y - y0
  have hy0 : Tᴴ *ᵥ y0 = s := minimizer_feasible L D hL s hs
  have hz : Tᴴ *ᵥ z = 0 := by
    change Tᴴ *ᵥ (y - y0) = 0
    rw [Matrix.mulVec_sub, hy, hy0, sub_self]
  have hcross1 : star y0 ⬝ᵥ z = 0 := by
    rw [show y0 = T *ᵥ
        (pinv (action_posSemidef L D hL).1 *ᵥ s) from rfl]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hz, dotProduct_zero]
  have hcross2 : star z ⬝ᵥ y0 = 0 := by
    rw [show y0 = T *ᵥ
        (pinv (action_posSemidef L D hL).1 *ᵥ s) from rfl]
    rw [Matrix.dotProduct_mulVec]
    have hadj : star z ᵥ* T = star (Tᴴ *ᵥ z) := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    rw [hadj, hz, star_zero, zero_dotProduct]
  have hyz : y = y0 + z := by simp [z]
  have hdiff : y - y0 = z := by rw [hyz]; simp
  calc
    star y ⬝ᵥ y = star (y0 + z) ⬝ᵥ (y0 + z) := by rw [hyz]
    _ = star y0 ⬝ᵥ y0 + star y0 ⬝ᵥ z +
        (star z ⬝ᵥ y0 + star z ⬝ᵥ z) := by
          simp only [star_add, add_dotProduct, dotProduct_add]
          ring
    _ = star y0 ⬝ᵥ y0 + star z ⬝ᵥ z := by
          rw [hcross1, hcross2]
          abel
    _ = star (minimizer L D hL s) ⬝ᵥ minimizer L D hL s +
        star (y - minimizer L D hL s) ⬝ᵥ
          (y - minimizer L D hL s) := by rw [hdiff]

/-- The canonical decomposition and the strong attained-minimum statement. -/
theorem canonical_interior_boundary_minimum
    (L : Matrix n n ℂ) (D : Matrix m n ℂ)
    (hL : L.PosSemidef) (s : n → ℂ)
    (hs : action L D *ᵥ
      (pinv (action_posSemidef L D hL).1 *ᵥ s) = s) :
    (synthesis L D)ᴴ *ᵥ minimizer L D hL s = s ∧
    star (minimizer L D hL s) ⬝ᵥ minimizer L D hL s =
      star s ⬝ᵥ (pinv (action_posSemidef L D hL).1 *ᵥ s) ∧
    ∀ y : (n ⊕ m) → ℂ, (synthesis L D)ᴴ *ᵥ y = s →
      star y ⬝ᵥ y =
        star (minimizer L D hL s) ⬝ᵥ minimizer L D hL s +
        star (y - minimizer L D hL s) ⬝ᵥ
          (y - minimizer L D hL s) := by
  exact ⟨minimizer_feasible L D hL s hs,
    minimizer_energy L D hL s hs,
    fun y hy => feasible_pythagoras L D hL s hs y hy⟩

end CanonicalInteriorBoundaryMinimum
end NCG
