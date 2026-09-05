/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Universal moment-exact leakage
  (`thm:universal-moment-leakage`, Gran-Tensor manuscript)

* `universal_moment_leakage`: in the whitened picture
  (`W` an isometry, `WᴴW = 1`, `T` hermitian), the boxed
  leakage form `𝕍 = WᴴT²W − (WᴴTW)²` factors exactly as the
  head-to-tail Gram `𝕍 = (QTW)ᴴ(QTW)` with `Q = I − WWᴴ`;
  hence `𝕍 ⪰ 0`, `rank 𝕍 = rank (QTW)` (the dimension of the
  new Krylov component), and `𝕍 = 0` exactly when the finite
  head is `T`-invariant (`QTW = 0`).

Rendering disclosed: the whitening `W = 𝒞(H⁽⁰⁾)^{†/2}` of the
controllability map is the declared isometry input (on a
faithful head `H⁽⁰⁾ ≻ 0` it is `𝒞·(√H⁽⁰⁾)⁻¹`, and `WᴴT^kW`
are exactly the boxed whitened moments); the operator-norm
identity `‖𝕍‖ = ‖QTW‖²` is the spectral reading of the proved
Gram factorization.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:universal-moment-leakage`. -/
theorem universal_moment_leakage {h k : Type*} [Fintype h]
    [Fintype k] [DecidableEq h] [DecidableEq k]
    (W : Matrix h k ℂ)
    (T : Matrix h h ℂ) (hW : Wᴴ * W = 1) (hT : Tᴴ = T) :
    -- the boxed Gram factorization of the leakage form
    (Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W)
      = (((1 : Matrix h h ℂ) - W * Wᴴ) * T * W)ᴴ
          * (((1 : Matrix h h ℂ) - W * Wᴴ) * T * W))
    -- positivity of the leakage
    ∧ (Wᴴ * (T * T) * W
        - (Wᴴ * T * W) * (Wᴴ * T * W)).PosSemidef
    -- rank identification with the new Krylov component
    ∧ (Wᴴ * (T * T) * W
        - (Wᴴ * T * W) * (Wᴴ * T * W)).rank
      = (((1 : Matrix h h ℂ) - W * Wᴴ) * T * W).rank
    -- exact vanishing at head invariance
    ∧ (Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W) = 0
        ↔ ((1 : Matrix h h ℂ) - W * Wᴴ) * T * W = 0) := by
  have hW' : ∀ Y : Matrix k k ℂ,
      Wᴴ * (W * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  have hQH : ((1 : Matrix h h ℂ) - W * Wᴴ)ᴴ
      = (1 : Matrix h h ℂ) - W * Wᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hkey : Wᴴ * (T * T) * W
        - (Wᴴ * T * W) * (Wᴴ * T * W)
      = (((1 : Matrix h h ℂ) - W * Wᴴ) * T * W)ᴴ
          * (((1 : Matrix h h ℂ) - W * Wᴴ) * T * W) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hQH, hT]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, hW']
    abel
  refine ⟨hkey, ?_, ?_, ?_⟩
  · rw [hkey]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [hkey]
    exact Matrix.rank_conjTranspose_mul_self _
  · rw [hkey]
    exact Matrix.conjTranspose_mul_self_eq_zero

end NCG
