/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar
import NCG.Grand.GramHelpers

/-!
# Outgoing-energy Pythagoras and the Ward–graph identity
  (`thm:renewal-boundary-Ward-graph`, Gran-Tensor manuscript)

* `renewal_boundary_ward_graph`: for the current/outgoing
  renewal-boundary panel `G = SᴴS ≻ 0`, `C = SᴴY`,
  `H₂ = YᴴY`, with `R = G^{-1/2}` (the inverse CFC square
  root), `K̂ = R·C·R`, `B = R·H₂·R`:
  (i) the boxed leakage factorization
      `Λ := B - K̂ᴴK̂ = LᴴL` with
      `L = (I - P)·Y·R`, `P = S·R·R·Sᴴ` the source-head
      projection — hence `Λ ⪰ 0` and
      `B = K̂ᴴK̂ + Λ`, `I - K̂ᴴK̂ = (I - B) + Λ`;
  (ii) the Ward form is the exact squared residual
      `𝔚(W) = (Y - SW)ᴴ(Y - SW)`;
  (iii) the boxed normalized decomposition
      `R·𝔚(W)·R = Λ + (K̂ - Ŵ)ᴴ(K̂ - Ŵ)`,
      `Ŵ = G^{1/2}·W·G^{-1/2}`;
  (iv) `𝔚(W) = 0 ↔ Y = SW`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:renewal-boundary-Ward-graph`. -/
theorem renewal_boundary_ward_graph {H E : Type*}
    [Fintype H] [Fintype E] [DecidableEq H] [DecidableEq E]
    (S Y : Matrix H E ℂ) (hG : (Sᴴ * S).PosDef)
    (W Rp R : Matrix E E ℂ)
    (hRp : Rp = CFC.sqrt (Sᴴ * S)) (hR : R = Rp⁻¹) :
    -- (i) the leakage factorization `Λ = LᴴL ⪰ 0`
    (R * (Yᴴ * Y) * R
        - (R * (Sᴴ * Y) * R)ᴴ * (R * (Sᴴ * Y) * R)
      = ((1 - S * R * (R * Sᴴ)) * (Y * R))ᴴ
        * ((1 - S * R * (R * Sᴴ)) * (Y * R)))
    ∧ (R * (Yᴴ * Y) * R
        - (R * (Sᴴ * Y) * R)ᴴ
          * (R * (Sᴴ * Y) * R)).PosSemidef
    -- (ii) the Ward form is the exact squared residual
    ∧ (Yᴴ * Y - (Sᴴ * Y)ᴴ * W - Wᴴ * (Sᴴ * Y)
          + Wᴴ * (Sᴴ * S) * W
        = (Y - S * W)ᴴ * (Y - S * W))
    -- (iii) the normalized Ward decomposition
    ∧ (R * ((Y - S * W)ᴴ * (Y - S * W)) * R
        = (R * (Yᴴ * Y) * R
            - (R * (Sᴴ * Y) * R)ᴴ * (R * (Sᴴ * Y) * R))
          + (R * (Sᴴ * Y) * R - Rp * W * R)ᴴ
            * (R * (Sᴴ * Y) * R - Rp * W * R))
    -- (iv) exact-zero characterization
    ∧ ((Y - S * W)ᴴ * (Y - S * W) = 0 ↔ Y = S * W) := by
  have hGpsd := hG.posSemidef
  have hRp2 : Rp * Rp = Sᴴ * S := by
    rw [hRp]
    exact sqrt_mul_self_eq _ hGpsd
  have hRpH : Rpᴴ = Rp := by
    rw [hRp]
    exact sqrt_isHermitian _
  have hRpu : IsUnit Rp := by
    rw [hRp]
    exact sqrt_isUnit hG
  haveI := hRpu.invertible
  have hRRp : R * Rp = 1 := by
    rw [hR]
    exact Matrix.inv_mul_of_invertible Rp
  have hRpR : Rp * R = 1 := by
    rw [hR]
    exact Matrix.mul_inv_of_invertible Rp
  have hRH : Rᴴ = R := by
    rw [hR, Matrix.conjTranspose_nonsing_inv, hRpH]
  have hSS : Sᴴ * S = Rp * Rp := hRp2.symm
  have hi : R * (Yᴴ * Y) * R
      - (R * (Sᴴ * Y) * R)ᴴ * (R * (Sᴴ * Y) * R)
      = ((1 - S * R * (R * Sᴴ)) * (Y * R))ᴴ
        * ((1 - S * R * (R * Sᴴ)) * (Y * R)) := by
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hRH, Matrix.conjTranspose_conjTranspose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    simp only [Matrix.mul_assoc, hSS, gram_swap hSS,
      cancel_left hRRp, cancel_left hRpR, hRRp, hRpR,
      Matrix.mul_one, Matrix.one_mul]
    abel
  have hii : (Yᴴ * Y - (Sᴴ * Y)ᴴ * W - Wᴴ * (Sᴴ * Y)
      + Wᴴ * (Sᴴ * S) * W)
      = (Y - S * W)ᴴ * (Y - S * W) := by
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    abel
  refine ⟨hi, ?_, hii, ?_, ?_⟩
  · rw [hi]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, hRH, hRpH,
      Matrix.sub_mul, Matrix.mul_sub]
    simp only [Matrix.mul_assoc, hSS, gram_swap hSS,
      cancel_left hRRp, cancel_left hRpR, hRRp, hRpR,
      Matrix.mul_one, Matrix.one_mul]
    abel
  · constructor
    · intro h0
      have h := Matrix.conjTranspose_mul_self_eq_zero.mp h0
      exact sub_eq_zero.mp h
    · intro h
      rw [h, sub_self, Matrix.conjTranspose_zero,
        Matrix.zero_mul]

end NCG
