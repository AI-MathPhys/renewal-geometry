/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.AtomicReset
import Mathlib.Analysis.Matrix.Order
import NCG.Upstream.PrimitiveWeight

/-!
# Positive functionals on finite matrix algebras

A complex-linear functional which is nonnegative on positive-semidefinite
matrices preserves adjoints.  Consequently its unique trace-pairing
representer is itself positive semidefinite.
-/

open Matrix
open scoped ComplexOrder MatrixOrder ComplexStarModule

namespace NCG

variable {n : ℕ}

open Upstream.PrimitiveWeight

/-- Complex-linear maps on a matrix algebra are determined by their values on
Hermitian matrices. -/
theorem complexLinearMap_ext_of_isHermitian {m : ℕ}
    (F G : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ X, X.IsHermitian → F X = G X) : F = G := by
  apply LinearMap.ext
  intro X
  let A : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) := ℜ X
  let B : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) := ℑ X
  calc
    F X = F (A.val + Complex.I • B.val) := by
      congr 1
      exact (realPart_add_I_smul_imaginaryPart X).symm
    _ = F A.val + Complex.I • F B.val := by rw [map_add, map_smul]
    _ = G A.val + Complex.I • G B.val := by rw [h A.val A.prop, h B.val B.prop]
    _ = G (A.val + Complex.I • B.val) := by rw [map_add, map_smul]
    _ = G X := by rw [realPart_add_I_smul_imaginaryPart X]

/-- A positive functional is real on Hermitian matrices. -/
theorem positiveMatrixFunctional_star_eq_of_isHermitian
    (ℓ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hpos : ∀ X, X.PosSemidef → 0 ≤ ℓ X)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) :
    star (ℓ X) = ℓ X := by
  have hP := hpos (posPart hX) (posPart_posSemidef hX)
  have hQ := hpos (negPart hX) (negPart_posSemidef hX)
  have hPstar : star (ℓ (posPart hX)) = ℓ (posPart hX) := by
    apply Complex.ext
    · simp
    · have hi := (Complex.nonneg_iff.mp hP).2
      change -(ℓ (posPart hX)).im = (ℓ (posPart hX)).im
      linarith
  have hQstar : star (ℓ (negPart hX)) = ℓ (negPart hX) := by
    apply Complex.ext
    · simp
    · have hi := (Complex.nonneg_iff.mp hQ).2
      change -(ℓ (negPart hX)).im = (ℓ (negPart hX)).im
      linarith
  rw [← posPart_sub_negPart hX, map_sub, star_sub, hPstar, hQstar]

/-- A positive complex matrix functional preserves conjugate transpose. -/
theorem positiveMatrixFunctional_map_conjTranspose
    (ℓ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hpos : ∀ X, X.PosSemidef → 0 ≤ ℓ X)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ℓ Xᴴ = star (ℓ X) := by
  let A : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) := ℜ X
  let B : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) := ℑ X
  have hXdecomp : X = (A : Matrix (Fin n) (Fin n) ℂ) +
      Complex.I • (B : Matrix (Fin n) (Fin n) ℂ) :=
    (realPart_add_I_smul_imaginaryPart X).symm
  have hXstar : Xᴴ = (A : Matrix (Fin n) (Fin n) ℂ) -
      Complex.I • (B : Matrix (Fin n) (Fin n) ℂ) := by
    calc
      Xᴴ = ((A : Matrix (Fin n) (Fin n) ℂ) +
          Complex.I • (B : Matrix (Fin n) (Fin n) ℂ))ᴴ :=
        congrArg Matrix.conjTranspose hXdecomp
      _ = (A : Matrix (Fin n) (Fin n) ℂ) -
          Complex.I • (B : Matrix (Fin n) (Fin n) ℂ) := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
          ← Matrix.star_eq_conjTranspose, A.prop,
          ← Matrix.star_eq_conjTranspose, B.prop]
        simp [sub_eq_add_neg]
  have hℓA := positiveMatrixFunctional_star_eq_of_isHermitian ℓ hpos
    (A : Matrix (Fin n) (Fin n) ℂ) A.prop
  have hℓB := positiveMatrixFunctional_star_eq_of_isHermitian ℓ hpos
    (B : Matrix (Fin n) (Fin n) ℂ) B.prop
  calc
    ℓ Xᴴ = ℓ A - Complex.I • ℓ B := by
      rw [hXstar, map_sub]
      congr 1
      exact map_smul ℓ Complex.I (B : Matrix (Fin n) (Fin n) ℂ)
    _ = star (ℓ A + Complex.I • ℓ B) := by
      rw [star_add, star_smul, hℓA, hℓB]
      simp [sub_eq_add_neg]
    _ = star (ℓ X) := by
      congr 1
      rw [hXdecomp, map_add]
      congr 1
      exact (map_smul ℓ Complex.I (B : Matrix (Fin n) (Fin n) ℂ)).symm

/-- The unique trace representer of a positive functional is positive
semidefinite. -/
theorem positiveMatrixFunctional_traceRepresenter_posSemidef
    (ℓ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hpos : ∀ X, X.PosSemidef → 0 ≤ ℓ X)
    (E : Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ X, ℓ X = (E * X).trace) :
    E.PosSemidef := by
  have hHerm : E.IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    rw [Matrix.conjTranspose_apply]
    have hij := hE (Matrix.single i j (1 : ℂ))
    have hji := hE (Matrix.single j i (1 : ℂ))
    rw [Matrix.trace_mul_single] at hij hji
    simp only [MulOpposite.op_one, one_smul] at hij hji
    have hstar := positiveMatrixFunctional_map_conjTranspose ℓ hpos
      (Matrix.single i j (1 : ℂ))
    simp only [Matrix.conjTranspose_single, star_one] at hstar
    rw [← hij, ← hji]
    exact hstar.symm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
  intro x
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.vecMulVec x (star x)
  have hP : P.PosSemidef := posSemidef_vecMulVec_self_star x
  have hp := hpos P hP
  rw [hE P] at hp
  have htrace : (E * P).trace = star x ⬝ᵥ (E *ᵥ x) := by
    simp only [P, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.vecMulVec_apply, dotProduct]
    change (∑ i : Fin n, ∑ j : Fin n,
        E i j * (x j * star (x i))) =
      ∑ i : Fin n, star (x i) * (∑ j : Fin n, E i j * x j)
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rwa [htrace] at hp

/-- Every positive functional has a unique positive-semidefinite trace
representer. -/
theorem positiveMatrixFunctional_existsUnique_traceRepresenter
    (ℓ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hpos : ∀ X, X.PosSemidef → 0 ≤ ℓ X) :
    ∃! E : Matrix (Fin n) (Fin n) ℂ,
      E.PosSemidef ∧ ∀ X, ℓ X = (E * X).trace := by
  obtain ⟨E, hE, huniq⟩ :=
    (atomic_reset_characterization (n := Fin n) (w := Fin 1)).2.2 ℓ
  refine ⟨E, ⟨positiveMatrixFunctional_traceRepresenter_posSemidef
    ℓ hpos E hE, hE⟩, ?_⟩
  intro F hF
  exact huniq F hF.2

end NCG
