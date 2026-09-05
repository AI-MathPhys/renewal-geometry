/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusCovariantFourierSymbol

/-!
# Fourier inversion on finite tori

The product standard characters on `(ZMod N)^d` separate points.  Their
orthogonality gives the exact inversion formula for the unnormalized
finite-torus Fourier transform.
-/

open Finset AddChar

namespace NCG

variable {N : ℕ} [NeZero N]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A nonzero frequency defines a nontrivial product character. -/
theorem finiteTorusAddChar_ne_one {k : d → ZMod N} (hk : k ≠ 0) :
    finiteTorusAddChar k ≠ 1 := by
  intro hchar
  apply hk
  funext j
  apply ZMod.injective_stdAddChar
  calc
    ZMod.stdAddChar (k j) =
        finiteTorusAddChar k (Pi.single j 1) := by
          rw [finiteTorusAddChar_single]
          simp
    _ = (1 : AddChar (d → ZMod N) ℂ) (Pi.single j 1) := by
          rw [hchar]
    _ = ZMod.stdAddChar 0 := by simp

/-- Orthogonality sum for the product characters. -/
theorem sum_finiteTorusAddChar (k : d → ZMod N) :
    ∑ x : d → ZMod N, finiteTorusAddChar k x =
      if k = 0 then (Fintype.card (d → ZMod N) : ℂ) else 0 := by
  split_ifs with hk
  · subst k
    simp [finiteTorusAddChar]
  · exact AddChar.sum_eq_zero_of_ne_one (finiteTorusAddChar_ne_one hk)

/-- Orthogonality is unchanged when the spatial variable is negated. -/
theorem sum_finiteTorusAddChar_neg (k : d → ZMod N) :
    ∑ x : d → ZMod N, finiteTorusAddChar k (-x) =
      if k = 0 then (Fintype.card (d → ZMod N) : ℂ) else 0 := by
  calc
    (∑ x : d → ZMod N, finiteTorusAddChar k (-x)) =
        ∑ x : d → ZMod N, finiteTorusAddChar k x :=
      Fintype.sum_equiv (Equiv.neg (d → ZMod N))
        (fun x : d → ZMod N => finiteTorusAddChar k (-x))
        (fun x : d → ZMod N => finiteTorusAddChar k x)
        (fun x => by simp)
    _ = _ := sum_finiteTorusAddChar k

/-- Multiplication of the two kernels occurring in the iterated transform. -/
theorem finiteTorusAddChar_kernel_mul
    (x k y : d → ZMod N) :
    finiteTorusAddChar x (-k) * finiteTorusAddChar k (-y) =
      finiteTorusAddChar (x + y) (-k) := by
  rw [finiteTorusAddChar_apply, finiteTorusAddChar_apply,
    finiteTorusAddChar_apply, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← map_add_eq_mul]
  congr 1
  simp only [Pi.neg_apply, Pi.add_apply]
  ring

/-- Applying the unnormalized product Fourier transform twice reflects the
input and multiplies it by the cardinality of the finite torus. -/
theorem finiteTorusFourier_fourier
    (Phi : (d → ZMod N) → E) :
    finiteTorusFourier (finiteTorusFourier Phi) =
      fun x => (Fintype.card (d → ZMod N) : ℂ) • Phi (-x) := by
  funext x
  simp only [finiteTorusFourier, smul_sum, ← smul_assoc]
  rw [sum_comm]
  simp only [smul_eq_mul]
  simp_rw [finiteTorusAddChar_kernel_mul]
  simp_rw [← sum_smul]
  simp_rw [sum_finiteTorusAddChar_neg]
  have hzero (y : d → ZMod N) : x + y = 0 ↔ y = -x := by
    rw [add_comm, add_eq_zero_iff_eq_neg]
  simp only [hzero, ite_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]

end NCG
