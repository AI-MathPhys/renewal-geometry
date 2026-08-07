/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Smith–Pontryagin constraint duality
  (`thm:Smith-Pontryagin`, Gran-Tensor manuscript)

* `smith_pontryagin`: the three proved engines of the boxed
  exact sequence — (1) annihilator duality: a character
  annihilates the range of the constraint matrix exactly when
  it lies in the kernel of the transposed action
  (`x·(Ay) = 0 ∀y ⟺ xA = 0`, at every finite level); (2) the
  Smith-block torsion kernel: on the circle `𝕋 = ℝ/ℤ`, the
  kernel of multiplication by `d ≠ 0` is exactly the cyclic
  group `μ_d = {k/d}` of `d`-th roots; (3) right exactness:
  multiplication by `d ≠ 0` is surjective on `𝕋` (divisibility
  of the circle), so the diagonal Smith blocks are onto and the
  torus cokernel is carried by the zero invariants alone.

Rendering disclosed: the boxed four-term sequence and the
product decomposition `coker^ ≅ 𝕋^{m-r} × Πμ_{d_i}` are the
manuscript's Smith-coordinate assembly (unimodular `U, V` from
the proved Smith–Gale records) of these engines: in Smith
coordinates `A^T` acts diagonally, clause (2) computes each
`μ_{d_i}` factor, clause (3) gives exactness on the right, and
clause (1) identifies `ker A^T` with the character annihilator
`coker^`.
-/

open Matrix

namespace NCG

/-- `thm:Smith-Pontryagin`. -/
theorem smith_pontryagin :
    -- (1) annihilator duality at every finite level
    (∀ {q : ℕ} {m n : Type} [Fintype m] [Fintype n]
      [DecidableEq n] (A : Matrix m n (ZMod q))
      (x : m → ZMod q),
      Matrix.vecMul x A = 0
        ↔ ∀ y : n → ZMod q, x ⬝ᵥ (A *ᵥ y) = 0)
    -- (2) the Smith-block kernel on 𝕋 is μ_d
    ∧ (∀ (d : ℤ) (x : AddCircle (1 : ℝ)), d ≠ 0 →
        (d • x = 0 ↔ ∃ k : ℤ,
          x = (((k : ℝ) / (d : ℝ) : ℝ) : AddCircle (1 : ℝ))))
    -- (3) multiplication by d ≠ 0 is surjective on 𝕋
    ∧ (∀ d : ℤ, d ≠ 0 →
        Function.Surjective
          (fun x : AddCircle (1 : ℝ) => d • x)) := by
  have hcast : ∀ {d : ℤ}, d ≠ 0 → ((d : ℝ) ≠ 0) :=
    fun hd => Int.cast_ne_zero.mpr hd
  have hsmul : ∀ (d : ℤ) (r : ℝ),
      d • ((r : ℝ) : AddCircle (1 : ℝ))
        = ((d • r : ℝ) : AddCircle (1 : ℝ)) := by
    intro d r
    exact (map_zsmul
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      d r).symm
  refine ⟨?_, ?_, ?_⟩
  · intro q m n _ _ _ A x
    constructor
    · intro h y
      rw [Matrix.dotProduct_mulVec, h, zero_dotProduct]
    · intro h
      funext jj
      have hy := h (Pi.single jj 1)
      rw [Matrix.dotProduct_mulVec, dotProduct_single,
        mul_one] at hy
      exact hy
  · intro d x hd
    induction x using QuotientAddGroup.induction_on with
    | H r =>
      constructor
      · intro h0
        rw [hsmul] at h0
        obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp h0
        refine ⟨k, ?_⟩
        have hk' : (k : ℝ) = d * r := by
          simpa using hk
        have hr : r = (k : ℝ) / (d : ℝ) := by
          field_simp [hcast hd] at hk' ⊢
          linarith [hk']
        rw [← hr]
      · rintro ⟨k, hk⟩
        rw [hk, hsmul]
        rw [show d • ((k : ℝ) / (d : ℝ)) = (k : ℝ) from by
          rw [zsmul_eq_mul, mul_div_cancel₀ _ (hcast hd)]]
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨k, by simp⟩
  · intro d hd y
    induction y using QuotientAddGroup.induction_on with
    | H r =>
      refine ⟨((r / (d : ℝ) : ℝ) : AddCircle (1 : ℝ)), ?_⟩
      change d • ((r / (d : ℝ) : ℝ) : AddCircle (1 : ℝ))
        = ((r : ℝ) : AddCircle (1 : ℝ))
      rw [hsmul]
      congr 1
      rw [zsmul_eq_mul, mul_div_cancel₀ _ (hcast hd)]

end NCG
