/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ZModCovariantFourierSymbol

/-!
# Covariant Fourier symbols on finite tori

The product additive character on `(ZMod N)^d` defines the unnormalized
finite-torus Fourier transform.  Translation by an arbitrary torus vector is
diagonal with its character value, constant fibre operators commute with the
transform, and consequently every covariant difference has its exact
operator-valued Fourier symbol.
-/

open Finset AddChar

namespace NCG

variable {N : ℕ} [NeZero N]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Product additive character on the finite torus at frequency `k`. -/
noncomputable def finiteTorusAddChar (k : d → ZMod N) :
    AddChar (d → ZMod N) ℂ where
  toFun x := ∏ j, ZMod.stdAddChar (x j * k j)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, add_mul, map_add_eq_mul, Finset.prod_mul_distrib]

omit [DecidableEq d] in
@[simp]
theorem finiteTorusAddChar_apply (k x : d → ZMod N) :
    finiteTorusAddChar k x = ∏ j, ZMod.stdAddChar (x j * k j) := rfl

/-- The product character evaluated on a coordinate vector. -/
theorem finiteTorusAddChar_single
    (k : d → ZMod N) (j : d) (a : ZMod N) :
    finiteTorusAddChar k (Pi.single j a) =
      ZMod.stdAddChar (a * k j) := by
  classical
  rw [finiteTorusAddChar_apply, Finset.prod_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · simp

/-- Unnormalized Fourier transform on the finite torus. -/
noncomputable def finiteTorusFourier
    (Phi : (d → ZMod N) → E) (k : d → ZMod N) : E :=
  ∑ x, finiteTorusAddChar k (-x) • Phi x

/-- Translation by a torus vector. -/
def finiteTorusShift
    (e : d → ZMod N) (Phi : (d → ZMod N) → E) :
    (d → ZMod N) → E :=
  fun x => Phi (x + e)

/-- Every torus translation is diagonalized by the product Fourier
transform. -/
theorem finiteTorusFourier_shift
    (e : d → ZMod N) (Phi : (d → ZMod N) → E)
    (k : d → ZMod N) :
    finiteTorusFourier (finiteTorusShift e Phi) k =
      finiteTorusAddChar k e • finiteTorusFourier Phi k := by
  unfold finiteTorusFourier finiteTorusShift
  have hreindex :
      (∑ x : d → ZMod N,
        finiteTorusAddChar k (-x) • Phi (x + e)) =
      ∑ y : d → ZMod N,
        finiteTorusAddChar k (-(y - e)) • Phi y := by
    simpa using Fintype.sum_equiv (Equiv.addRight e)
      (fun x : d → ZMod N => finiteTorusAddChar k (-x) • Phi (x + e))
      (fun y : d → ZMod N => finiteTorusAddChar k (-(y - e)) • Phi y)
      (fun x => by simp)
  rw [hreindex, smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have harg : -(y - e) = e + -y := by abel
  rw [harg, map_add_eq_mul, mul_smul]

/-- Coordinate translation has the expected one-dimensional phase. -/
theorem finiteTorusFourier_coordinateShift
    (j : d) (Phi : (d → ZMod N) → E) (k : d → ZMod N) :
    finiteTorusFourier (finiteTorusShift (Pi.single j 1) Phi) k =
      ZMod.stdAddChar (k j) • finiteTorusFourier Phi k := by
  rw [finiteTorusFourier_shift, finiteTorusAddChar_single]
  simp
/-- A constant scalar commutes with the finite-torus Fourier transform. -/
theorem finiteTorusFourier_const_smul
    (c : ℂ) (Phi : (d → ZMod N) → E) (k : d → ZMod N) :
    finiteTorusFourier (fun x => c • Phi x) k =
      c • finiteTorusFourier Phi k := by
  unfold finiteTorusFourier
  rw [smul_sum]
  apply Finset.sum_congr rfl
  simp [smul_smul, mul_comm]


/-- Constant fibre operators commute with the finite-torus Fourier
transform. -/
theorem finiteTorusFourier_clm_apply
    (U : E →L[ℂ] E) (Phi : (d → ZMod N) → E)
    (k : d → ZMod N) :
    finiteTorusFourier (fun x => U (Phi x)) k =
      U (finiteTorusFourier Phi k) := by
  simp only [finiteTorusFourier, map_sum, map_smul]

/-- Covariant coordinate difference on the finite torus. -/
def finiteTorusCovariantDifference
    (j : d) (U : E →L[ℂ] E) (Phi : (d → ZMod N) → E) :
    (d → ZMod N) → E :=
  fun x => Phi (x + Pi.single j 1) - U (Phi x)

/-- Exact operator-valued Fourier symbol of a torus covariant coordinate
difference. -/
theorem finiteTorusFourier_covariantDifference
    (j : d) (U : E →L[ℂ] E) (Phi : (d → ZMod N) → E)
    (k : d → ZMod N) :
    finiteTorusFourier (finiteTorusCovariantDifference j U Phi) k =
      (ZMod.stdAddChar (k j) • (1 : E →L[ℂ] E) - U)
        (finiteTorusFourier Phi k) := by
  unfold finiteTorusCovariantDifference finiteTorusFourier
  simp only [smul_sub]
  rw [sum_sub_distrib]
  change finiteTorusFourier (finiteTorusShift (Pi.single j 1) Phi) k -
      finiteTorusFourier (fun x => U (Phi x)) k = _
  rw [finiteTorusFourier_coordinateShift, finiteTorusFourier_clm_apply]
  change ZMod.stdAddChar (k j) • finiteTorusFourier Phi k -
      U (finiteTorusFourier Phi k) =
    ZMod.stdAddChar (k j) • finiteTorusFourier Phi k -
      U (finiteTorusFourier Phi k)
  rfl

/-- Exact Fourier symbol of a mesh-scaled covariant difference. -/
theorem finiteTorusFourier_scaledCovariantDifference
    (h : ℝ) (j : d) (U : E →L[ℂ] E)
    (Phi : (d → ZMod N) → E) (k : d → ZMod N) :
    finiteTorusFourier
        (fun x => (h⁻¹ : ℂ) • finiteTorusCovariantDifference j U Phi x) k =
      (h⁻¹ : ℂ) •
        ((ZMod.stdAddChar (k j) • (1 : E →L[ℂ] E) - U)
          (finiteTorusFourier Phi k)) := by
  rw [finiteTorusFourier_const_smul,
    finiteTorusFourier_covariantDifference]


end NCG
