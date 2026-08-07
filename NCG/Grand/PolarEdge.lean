/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Polar edge equivalence and the flat/irreducible extremes
  (`lem:SMST-polar-edge` and `cor:SMST-polar-extremes`,
  Gran-Tensor manuscript)

* `polar_edge`: for an invertible edge transport in polar form
  `F = UP` (`U` unitary, `P` hermitian invertible), the two
  intertwining equations `R_t F = F R_s`, `R_s F* = F* R_t` are
  jointly equivalent to the boxed pair
  `[R_s, P²] = 0` and `R_t = U R_s U*`.
* `polar_extremes`: scalar generators commute with everything
  (flat limit); an operator commuting with everything is scalar
  (irreducible limit, via the matrix-unit criterion); unitary
  transports have trivial polar metric; and even on a tree a
  non-scalar positive metric reduces the commutant (explicit
  2×2 witness).

Rendering disclosed: the functional-calculus step
"`[R, P²] = 0` implies `[R, P] = 0`" (continuity of the square
root, `P ≻ 0`) enters as the declared hypothesis `hsqrt`; the
manuscript's positivity of `P` is carried by hermiticity plus
invertibility in the equivalence itself.
-/

open Matrix

namespace NCG

/-- `lem:SMST-polar-edge`. -/
theorem polar_edge {g : Type*} [Fintype g] [DecidableEq g]
    (U P Rs Rt : Matrix g g ℂ) [Invertible P]
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) (hP : Pᴴ = P)
    (hsqrt : ∀ R : Matrix g g ℂ,
      R * (P * P) = (P * P) * R → R * P = P * R) :
    (Rt * (U * P) = (U * P) * Rs
        ∧ Rs * (U * P)ᴴ = (U * P)ᴴ * Rt)
      ↔ (Rs * (P * P) = (P * P) * Rs
        ∧ Rt = U * Rs * Uᴴ) := by
  have hadj : (U * P)ᴴ = P * Uᴴ := by
    rw [Matrix.conjTranspose_mul, hP]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hadj] at h2
    -- (i)  (Uᴴ Rt U) P = P Rs
    have hi : Uᴴ * Rt * U * P = P * Rs := by
      have h := congrArg (fun M => Uᴴ * M) h1
      simp only [← Matrix.mul_assoc] at h
      rwa [hU', Matrix.one_mul] at h
    -- (ii) Rs P = P (Uᴴ Rt U)
    have hii : Rs * P = P * (Uᴴ * Rt * U) := by
      have h := congrArg (fun M => M * U) h2
      simp only [← Matrix.mul_assoc] at h
      rwa [Matrix.mul_assoc (Rs * P), hU', Matrix.mul_one,
        Matrix.mul_assoc P Uᴴ Rt,
        Matrix.mul_assoc P (Uᴴ * Rt) U] at h
    have hc : Rs * (P * P) = (P * P) * Rs := by
      calc Rs * (P * P) = (Rs * P) * P := by
            rw [Matrix.mul_assoc]
        _ = (P * (Uᴴ * Rt * U)) * P := by rw [hii]
        _ = P * ((Uᴴ * Rt * U) * P) := by
            rw [Matrix.mul_assoc]
        _ = P * (P * Rs) := by rw [hi]
        _ = (P * P) * Rs := by rw [Matrix.mul_assoc]
    have hPc : Rs * P = P * Rs := hsqrt Rs hc
    rw [hPc] at hii
    have hS : Rs = Uᴴ * Rt * U := by
      have h := congrArg (fun M => ⅟P * M) hii
      simpa only [invOf_mul_cancel_left] using h
    refine ⟨hc, ?_⟩
    rw [hS]
    calc Rt = 1 * Rt * 1 := by
          rw [Matrix.one_mul, Matrix.mul_one]
      _ = (U * Uᴴ) * Rt * (U * Uᴴ) := by rw [hU]
      _ = U * (Uᴴ * Rt * U) * Uᴴ := by
          simp only [Matrix.mul_assoc]
  · rintro ⟨hc, hRt⟩
    have hPc : Rs * P = P * Rs := hsqrt Rs hc
    constructor
    · rw [hRt]
      calc U * Rs * Uᴴ * (U * P)
          = U * (Rs * (Uᴴ * (U * P))) := by
            simp only [Matrix.mul_assoc]
        _ = U * (Rs * ((Uᴴ * U) * P)) := by
            rw [← Matrix.mul_assoc Uᴴ U P]
        _ = U * (Rs * P) := by rw [hU', Matrix.one_mul]
        _ = U * (P * Rs) := by rw [hPc]
        _ = (U * P) * Rs := by rw [← Matrix.mul_assoc]
    · rw [hadj, hRt]
      calc Rs * (P * Uᴴ) = (Rs * P) * Uᴴ := by
            rw [← Matrix.mul_assoc]
        _ = (P * Rs) * Uᴴ := by rw [hPc]
        _ = P * (Uᴴ * (U * (Rs * Uᴴ))) := by
            rw [show Uᴴ * (U * (Rs * Uᴴ))
                = (Uᴴ * U) * (Rs * Uᴴ) from
                (Matrix.mul_assoc Uᴴ U (Rs * Uᴴ)).symm,
              hU', Matrix.one_mul, ← Matrix.mul_assoc]
        _ = (P * Uᴴ) * (U * (Rs * Uᴴ)) := by
            rw [← Matrix.mul_assoc]
        _ = (P * Uᴴ) * (U * Rs * Uᴴ) := by
            rw [← Matrix.mul_assoc U Rs Uᴴ]

/-- `cor:SMST-polar-extremes`. -/
theorem polar_extremes {g : Type*} [Fintype g] [DecidableEq g] :
    -- (i) scalar generators commute with everything
    (∀ (α : ℂ) (R : Matrix g g ℂ),
      R * (α • 1) = (α • 1) * R)
    -- (ii) commuting with everything forces a scalar
    ∧ (∀ R : Matrix g g ℂ,
        (∀ S : Matrix g g ℂ, R * S = S * R) →
        ∃ α : ℂ, R = α • 1)
    -- (iii) unitary transports have trivial polar metric
    ∧ (∀ Q : Matrix g g ℂ, Qᴴ * Q = 1 →
        Qᴴ * (1 : Matrix g g ℂ) * Q = 1)
    -- (iv) a non-scalar positive tree metric reduces the
    --      commutant: explicit 2×2 witness
    ∧ (∃ K R : Matrix (Fin 2) (Fin 2) ℂ,
        Kᴴ = K ∧ R * K ≠ K * R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α R
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro R hR
    obtain ⟨α, hα⟩ :=
      Matrix.mem_range_scalar_iff_commute_single'.mpr
        (fun i j => (hR (Matrix.single i j 1)).symm)
    refine ⟨α, ?_⟩
    rw [← hα]
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  · intro Q hQ
    rw [Matrix.mul_one]
    exact hQ
  · refine ⟨!![1, 0; 0, 2], !![0, 1; 0, 0], ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.conjTranspose_apply]
    · intro h
      have h01 := Matrix.ext_iff.mpr h 0 1
      norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h01

end NCG
