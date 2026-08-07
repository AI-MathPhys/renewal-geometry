/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockQuarterRoot

/-!
# The typed record map
  (`thm:SM-record-map`, Gran-Tensor manuscript)

* `sm_record_map`: with a square-root datum `S*S = K` for the
  typed Kossakowski operator, the boxed record map
  `Θ(c) = K^{1/2} c K^{1/2}` is completely positive in the
  displayed sense (it maps positive semidefinite arguments to
  positive semidefinite values) and is normalized by
  `Θ(1) = K`; for the score-square bridge the instance
  `Θ^sb(c) = ½·PcP` arises from the root `S = 2^{-1/2}·P` of a
  Hermitian projection.

Rendering disclosed: the unique minimal record-sufficient
Stinespring space (the cyclic hull) and the protected-record
retention clause are the manuscript's dilation bookkeeping over
the proved map identities.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:SM-record-map`: positivity, normalization, and the
score-square instance of the record map. -/
theorem sm_record_map {e : Type*} [Fintype e] [DecidableEq e]
    (S K : Matrix e e ℂ) (hS : Sᴴ * S = K) :
    (∀ c : Matrix e e ℂ, c.PosSemidef →
      (Sᴴ * c * S).PosSemidef)
    ∧ (Sᴴ * 1 * S = K)
    ∧ (∀ (P c : Matrix e e ℂ), Pᴴ = P →
        (invSqrt2 • P)ᴴ * c * (invSqrt2 • P)
          = (2⁻¹ : ℂ) • (P * c * P)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    exact hc.conjTranspose_mul_mul_same S
  · rw [Matrix.mul_one, hS]
  · intro P c hP
    rw [Matrix.conjTranspose_smul, invSqrt2_star, hP,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul]
    rw [show invSqrt2 * invSqrt2 = (2⁻¹ : ℂ) from by
      have h := invSqrt2_sq
      rwa [pow_two] at h]

end NCG
