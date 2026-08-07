/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Atomic-reset characterization
  (`thm:atomic-reset-characterization`,
  Gran-Tensor manuscript)

* `atomic_reset_characterization`:
  (i) the boxed atomic form `R(X) = ℓ(X)ω` is decoupling:
      any two outputs lie on the ray of `ω`;
  (ii) conversely, a map with one-dimensional output ray is
      atomic: the coefficient is a linear functional
      (constructed from any nonzero coordinate of `ω`);
  (iii) on a matrix algebra every linear functional is a
      unique trace pairing `ℓ(X) = Tr(EX)` — the boxed
      `R(X) = Tr(EX)ω` normal form.

The positivity bookkeeping (a nonzero positive rank-one
map admits a positive factorization after a simultaneous
sign choice; positivity of the Choi operator `Eᵀ ⊗ ω`) is
the manuscript's cone layer over these linear identities.
-/

open Matrix

set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:atomic-reset-characterization`. -/
theorem atomic_reset_characterization {n w : Type*}
    [Fintype n] [DecidableEq n] :
    -- (i) the atomic form is decoupling
    (∀ (ℓ : Matrix n n ℂ →ₗ[ℂ] ℂ) (ω : Matrix w w ℂ)
        (X Y : Matrix n n ℂ), ℓ Y ≠ 0 →
      ∃ c : ℂ, ℓ X • ω = c • (ℓ Y • ω))
    -- (ii) a one-dimensional output ray is atomic
    ∧ (∀ (R : Matrix n n ℂ →ₗ[ℂ] Matrix w w ℂ)
        (ω : Matrix w w ℂ) (i0 j0 : w), ω i0 j0 ≠ 0 →
        (∀ X, ∃ c : ℂ, R X = c • ω) →
        ∃ ℓ : Matrix n n ℂ →ₗ[ℂ] ℂ,
          ∀ X, R X = ℓ X • ω)
    -- (iii) unique trace normal form of the coefficient
    ∧ (∀ ℓ : Matrix n n ℂ →ₗ[ℂ] ℂ,
        ∃! E : Matrix n n ℂ,
          ∀ X, ℓ X = (E * X).trace) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ℓ ω X Y hY
    exact ⟨ℓ X / ℓ Y, by
      rw [smul_smul, div_mul_cancel₀ _ hY]⟩
  · intro R ω i0 j0 hω hray
    refine ⟨{
      toFun := fun X => R X i0 j0 / ω i0 j0
      map_add' := fun X Y => by
        simp only [map_add, Matrix.add_apply]
        ring
      map_smul' := fun c X => by
        simp only [map_smul, Matrix.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        ring }, ?_⟩
    intro X
    obtain ⟨c, hc⟩ := hray X
    have hcoeff : R X i0 j0 = c * ω i0 j0 := by
      rw [hc, Matrix.smul_apply, smul_eq_mul]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [hcoeff, mul_div_cancel_right₀ _ hω]
    exact hc
  · intro ℓ
    have key : ∀ X : Matrix n n ℂ,
        ℓ X = ((Matrix.of fun i j =>
          ℓ (Matrix.single j i 1)) * X).trace := by
      intro X
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      rw [map_sum]
      conv_rhs => rw [Matrix.matrix_eq_sum_single X]
      rw [Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.trace_mul_single]
      have hs : Matrix.single i j (X i j)
          = X i j • Matrix.single i j (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, smul_eq_mul]
      simp only [Matrix.of_apply, op_smul_eq_mul]
      ring
    refine ⟨Matrix.of fun i j => ℓ (Matrix.single j i 1),
      fun X => key X, ?_⟩
    intro E' hE'
    ext i j
    have h1 := hE' (Matrix.single j i (1 : ℂ))
    rw [Matrix.trace_mul_single] at h1
    simp only [MulOpposite.op_one, one_smul] at h1
    simp only [Matrix.of_apply]
    exact h1.symm

end NCG
