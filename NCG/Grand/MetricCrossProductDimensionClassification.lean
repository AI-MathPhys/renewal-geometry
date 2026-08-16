/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CrossProductDimensionDivisibility
import NCG.Grand.ComplexCliffordMatrixBound
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Classification of metric vector cross-product dimensions

This file completes the finite-dimensional Hurwitz obstruction needed by the
Gran--Tensor manuscript.  Quaternionic divisibility gives `4 ∣ d + 1` for
`d ≥ 2`; complexification of the remaining Clifford generators and the
Jordan--Wigner matrix bound exclude every congruent dimension above seven.
-/

open scoped BigOperators

namespace NCG.MetricCrossProduct

/-- The coordinate basis of `ℝ ⊕ ℝᵈ`, indexed by one scalar coordinate and
the `d` imaginary coordinates. -/
noncomputable def compositionBasis (d : ℕ) :
    Module.Basis (Unit ⊕ Fin d) ℝ (CompositionSpace d) :=
  (Module.Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ (Fin d))

/-- Matrix of a real endomorphism, followed by coefficientwise extension to
the complex numbers. -/
noncomputable def complexMatrix {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V] (b : Module.Basis ι ℝ V) :
    Module.End ℝ V →+* Matrix ι ι ℂ :=
  Complex.ofRealHom.mapMatrix.comp
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom

/-- Canonical identification of `Fin m × Bool` with `Fin (2m)`. -/
def cliffordIndexEquiv (m : ℕ) :
    NCG.ComplexCliffordBound.CliffordIndex m ≃ Fin (m * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans
    finProdFinEquiv

/-- Include the first `2m` Clifford coordinates in a `d`-coordinate family. -/
def cliffordCoordinate {m d : ℕ} (hmd : m * 2 ≤ d)
    (i : NCG.ComplexCliffordBound.CliffordIndex m) : Fin d :=
  Fin.castLE hmd (cliffordIndexEquiv m i)

theorem cliffordCoordinate_injective {m d : ℕ} (hmd : m * 2 ≤ d) :
    Function.Injective (cliffordCoordinate hmd) :=
  (Fin.castLE_injective hmd).comp (cliffordIndexEquiv m).injective

/-- The chosen real Clifford generators, multiplied by `i` after
complexification so that their squares become `+1`. -/
noncomputable def complexCliffordGenerator (X : CrossProduct d) (m : ℕ)
    (hmd : m * 2 ≤ d)
    (i : NCG.ComplexCliffordBound.CliffordIndex m) :
    Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ :=
  Complex.I • complexMatrix (compositionBasis d)
    (imaginaryLeft X (coordinateVector (cliffordCoordinate hmd i)))

theorem complexCliffordGenerator_clifford (X : CrossProduct d) (m : ℕ)
    (hmd : m * 2 ≤ d) (i j : NCG.ComplexCliffordBound.CliffordIndex m) :
    complexCliffordGenerator X m hmd i *
        complexCliffordGenerator X m hmd j +
      complexCliffordGenerator X m hmd j *
        complexCliffordGenerator X m hmd i =
      (if i = j then (2 : ℂ) else 0) • 1 := by
  classical
  let b := compositionBasis d
  let Ji := imaginaryLeft X (coordinateVector (cliffordCoordinate hmd i))
  let Jj := imaginaryLeft X (coordinateVector (cliffordCoordinate hmd j))
  let Mi := complexMatrix b Ji
  let Mj := complexMatrix b Jj
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    have hsquare := congrArg (complexMatrix b)
      (coordinate_imaginaryLeft_sq X (cliffordCoordinate hmd i))
    change Complex.I • Mi * (Complex.I • Mi) +
        Complex.I • Mi * (Complex.I • Mi) = (2 : ℂ) • 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, map_mul, map_neg, map_one] at hsquare ⊢
    rw [hsquare]
    module
  · simp only [hij, if_false, zero_smul]
    have hcoord : cliffordCoordinate hmd i ≠ cliffordCoordinate hmd j := by
      exact fun h => hij (cliffordCoordinate_injective hmd h)
    have hanti := congrArg (complexMatrix b)
      (coordinate_imaginaryLeft_anticomm_of_ne X hcoord)
    simp only [map_mul, map_neg] at hanti
    change Mi * Mj = -(Mj * Mi) at hanti
    change Complex.I • Mi * (Complex.I • Mj) +
        Complex.I • Mj * (Complex.I • Mi) = 0
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, map_mul, map_neg] at hanti ⊢
    rw [hanti]
    module

/-- The even Clifford subsystem attached to a cross product obeys the
Jordan--Wigner exponential dimension bound. -/
theorem crossProduct_clifford_bound (X : CrossProduct d) (hd : 1 ≤ d) :
    let m := (d - 1) / 2
    (2 ^ m) ^ 2 ≤ (d + 1) ^ 2 := by
  let m := (d - 1) / 2
  have hmd : m * 2 ≤ d := by
    dsimp only [m]
    omega
  have hbound := NCG.ComplexCliffordBound.matrix_card_bound m
    (complexCliffordGenerator X m hmd)
    (complexCliffordGenerator_clifford X m hmd)
  simpa [Fintype.card_sum, m, add_comm] using hbound

theorem two_mul_add_two_lt_two_pow {m : ℕ} (hm : 5 ≤ m) :
    2 * m + 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ]
      omega

/-- **Hurwitz dimension obstruction for metric vector cross products.** -/
theorem dimension_eq_zero_one_three_or_seven (X : CrossProduct d) :
    d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 7 := by
  by_cases hd : d < 2
  · omega
  · have hd2 : 2 ≤ d := by omega
    have hdiv := four_dvd_dimension_succ X hd2
    have hbound := crossProduct_clifford_bound X (by omega)
    rcases hdiv with ⟨q, hq⟩
    by_cases hd11 : d < 11
    · omega
    · have hm : 5 ≤ (d - 1) / 2 := by omega
      have hexp := two_mul_add_two_lt_two_pow hm
      have hdim : d + 1 = 2 * ((d - 1) / 2) + 2 := by omega
      rw [hdim] at hbound
      nlinarith [sq_nonneg ((2 : ℤ) ^ ((d - 1) / 2) -
        (2 * ((d - 1) / 2) + 2))]

end NCG.MetricCrossProduct
