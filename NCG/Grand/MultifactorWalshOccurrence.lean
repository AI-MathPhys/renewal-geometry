/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TopWalsh

/-!
# Multifactor Walsh occurrence reconstruction

This file completes the general finite-factor branch of
`thm:SM-top-Walsh`.  The sign-cube transform is defined recursively, with
each step explicitly adding the positive branch and the character-weighted
negative branch.  Its factorization theorem therefore applies to arbitrary
finite ordered products in a noncommutative complex algebra.
-/

namespace NCG

open Matrix
open NormedSpace

/-- One factor in an ordered Walsh expansion.  `evenPart` is unchanged by
sign reversal, `oddPart` changes sign, and `selected` records membership in
the Walsh character set. -/
structure WalshFactor (A : Type*) where
  evenPart : A
  oddPart : A
  selected : Bool

/-- The unnormalized Walsh character sum over all sign choices.  The first
summand fixes the current sign to `+`; the second fixes it to `-` and inserts
the current character sign when the factor is selected. -/
def walshCharacterSum {A : Type*} [Ring A] [Algebra ℂ A] :
    A → List (WalshFactor A) → A
  | C, [] => C
  | C, f :: fs =>
      walshCharacterSum (C * (f.evenPart + f.oddPart)) fs +
        (if f.selected then (-1 : ℂ) else 1) •
          walshCharacterSum (C * (f.evenPart - f.oddPart)) fs

/-- The ordered product selected by a Walsh character: choose the odd part
at indices in the character set and the even part elsewhere. -/
def selectedWalshProduct {A : Type*} [Mul A] :
    A → List (WalshFactor A) → A
  | C, [] => C
  | C, f :: fs =>
      selectedWalshProduct
        (C * if f.selected then f.oddPart else f.evenPart) fs

/-- The selected ordered product is additive in its initial row. -/
theorem selectedWalshProduct_add {A : Type*} [Ring A]
    (C D : A) (fs : List (WalshFactor A)) :
    selectedWalshProduct (C + D) fs =
      selectedWalshProduct C fs + selectedWalshProduct D fs := by
  induction fs generalizing C D with
  | nil => rfl
  | cons f fs ih =>
      simp only [selectedWalshProduct]
      rw [add_mul, ih]

/-- The selected ordered product respects complex scaling of its initial row. -/
theorem selectedWalshProduct_smul {A : Type*}
    [Ring A] [Algebra ℂ A] (c : ℂ) (C : A)
    (fs : List (WalshFactor A)) :
    selectedWalshProduct (c • C) fs =
      c • selectedWalshProduct C fs := by
  induction fs generalizing C with
  | nil => rfl
  | cons f fs ih =>
      simp only [selectedWalshProduct]
      rw [smul_mul_assoc, ih]

/-- A zero initial row gives a zero selected product. -/
theorem selectedWalshProduct_zero {A : Type*} [Ring A]
    (fs : List (WalshFactor A)) :
    selectedWalshProduct 0 fs = 0 := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp only [selectedWalshProduct, zero_mul, ih]

private theorem selectedWalshProduct_even_split {A : Type*}
    [Ring A] [Algebra ℂ A] (C e o : A) (fs : List (WalshFactor A)) :
    selectedWalshProduct (C * (e + o)) fs +
        selectedWalshProduct (C * (e - o)) fs =
      (2 : ℂ) • selectedWalshProduct (C * e) fs := by
  rw [← selectedWalshProduct_add]
  have h : C * (e + o) + C * (e - o) = (2 : ℂ) • (C * e) := by
    rw [mul_add, mul_sub]
    module
  rw [h, selectedWalshProduct_smul]

private theorem selectedWalshProduct_odd_split {A : Type*}
    [Ring A] [Algebra ℂ A] (C e o : A) (fs : List (WalshFactor A)) :
    selectedWalshProduct (C * (e + o)) fs -
        selectedWalshProduct (C * (e - o)) fs =
      (2 : ℂ) • selectedWalshProduct (C * o) fs := by
  rw [sub_eq_add_neg]
  rw [← neg_one_smul ℂ (selectedWalshProduct (C * (e - o)) fs)]
  rw [← selectedWalshProduct_smul, ← selectedWalshProduct_add]
  have h : C * (e + o) + (-1 : ℂ) • (C * (e - o)) =
      (2 : ℂ) • (C * o) := by
    rw [mul_add, mul_sub]
    module
  rw [h, selectedWalshProduct_smul]

/-- General finite Walsh factorization.  Summing all `2^m` signed ordered
branches against one character leaves exactly the matching ordered monomial,
with coefficient `2^m`. -/
theorem walshCharacterSum_factorization {A : Type*}
    [Ring A] [Algebra ℂ A] (C : A) (fs : List (WalshFactor A)) :
    walshCharacterSum C fs =
      ((2 : ℂ) ^ fs.length) • selectedWalshProduct C fs := by
  induction fs generalizing C with
  | nil => simp [walshCharacterSum, selectedWalshProduct]
  | cons f fs ih =>
      rw [walshCharacterSum, ih, ih]
      cases hsel : f.selected
      · simp only [hsel, Bool.false_eq_true, ↓reduceIte,
          selectedWalshProduct, List.length_cons, pow_succ, one_smul]
        rw [← smul_add, selectedWalshProduct_even_split, smul_smul]
      · simp only [hsel, ↓reduceIte, selectedWalshProduct,
          List.length_cons, pow_succ, neg_smul, one_smul]
        rw [← sub_eq_add_neg]
        rw [← smul_sub, selectedWalshProduct_odd_split, smul_smul]

/-- Normalized Walsh coefficient.  The manuscript normalization is
`2^{-m/2}`; it is kept as an explicit scalar so the algebraic theorem does not
choose a square-root convention. -/
def normalizedWalshCoefficient {A : Type*} [Ring A] [Algebra ℂ A]
    (normalization : ℂ) (C : A) (fs : List (WalshFactor A)) : A :=
  normalization • walshCharacterSum C fs

/-- The normalized form of the multifactor expansion. -/
theorem normalizedWalshCoefficient_factorization {A : Type*}
    [Ring A] [Algebra ℂ A] (normalization : ℂ)
    (C : A) (fs : List (WalshFactor A)) :
    normalizedWalshCoefficient normalization C fs =
      (normalization * (2 : ℂ) ^ fs.length) •
        selectedWalshProduct C fs := by
  rw [normalizedWalshCoefficient, walshCharacterSum_factorization, smul_smul]

/-! ## Rectangular occurrence rows -/

/-- The Walsh character sum for a rectangular occurrence row `Y ← Q₀` and
square right-acting factors on `Q₀`. -/
def matrixWalshCharacterSum {y n : Type*} [Fintype n]
    (C : Matrix y n ℂ) :
    List (WalshFactor (Matrix n n ℂ)) → Matrix y n ℂ
  | [] => C
  | f :: fs =>
      matrixWalshCharacterSum (C * (f.evenPart + f.oddPart)) fs +
        (if f.selected then (-1 : ℂ) else 1) •
          matrixWalshCharacterSum (C * (f.evenPart - f.oddPart)) fs

/-- The ordered character-selected monomial for a rectangular occurrence row. -/
def matrixSelectedWalshProduct {y n : Type*} [Fintype n]
    (C : Matrix y n ℂ) :
    List (WalshFactor (Matrix n n ℂ)) → Matrix y n ℂ
  | [] => C
  | f :: fs =>
      matrixSelectedWalshProduct
        (C * if f.selected then f.oddPart else f.evenPart) fs

private theorem matrixSelectedWalshProduct_add {y n : Type*} [Fintype n]
    (C D : Matrix y n ℂ) (fs : List (WalshFactor (Matrix n n ℂ))) :
    matrixSelectedWalshProduct (C + D) fs =
      matrixSelectedWalshProduct C fs + matrixSelectedWalshProduct D fs := by
  induction fs generalizing C D with
  | nil => rfl
  | cons f fs ih =>
      simp only [matrixSelectedWalshProduct]
      rw [Matrix.add_mul, ih]

private theorem matrixSelectedWalshProduct_smul {y n : Type*} [Fintype n]
    (c : ℂ) (C : Matrix y n ℂ)
    (fs : List (WalshFactor (Matrix n n ℂ))) :
    matrixSelectedWalshProduct (c • C) fs =
      c • matrixSelectedWalshProduct C fs := by
  induction fs generalizing C with
  | nil => rfl
  | cons f fs ih =>
      simp only [matrixSelectedWalshProduct]
      rw [Matrix.smul_mul, ih]

private theorem matrixSelectedWalshProduct_even_split {y n : Type*} [Fintype n]
    (C : Matrix y n ℂ) (e o : Matrix n n ℂ)
    (fs : List (WalshFactor (Matrix n n ℂ))) :
    matrixSelectedWalshProduct (C * (e + o)) fs +
        matrixSelectedWalshProduct (C * (e - o)) fs =
      (2 : ℂ) • matrixSelectedWalshProduct (C * e) fs := by
  rw [← matrixSelectedWalshProduct_add]
  have h : C * (e + o) + C * (e - o) = (2 : ℂ) • (C * e) := by
    rw [Matrix.mul_add, Matrix.mul_sub]
    module
  rw [h, matrixSelectedWalshProduct_smul]

private theorem matrixSelectedWalshProduct_odd_split {y n : Type*} [Fintype n]
    (C : Matrix y n ℂ) (e o : Matrix n n ℂ)
    (fs : List (WalshFactor (Matrix n n ℂ))) :
    matrixSelectedWalshProduct (C * (e + o)) fs -
        matrixSelectedWalshProduct (C * (e - o)) fs =
      (2 : ℂ) • matrixSelectedWalshProduct (C * o) fs := by
  rw [sub_eq_add_neg,
    ← neg_one_smul ℂ (matrixSelectedWalshProduct (C * (e - o)) fs),
    ← matrixSelectedWalshProduct_smul, ← matrixSelectedWalshProduct_add]
  have h : C * (e + o) + (-1 : ℂ) • (C * (e - o)) =
      (2 : ℂ) • (C * o) := by
    rw [Matrix.mul_add, Matrix.mul_sub]
    module
  rw [h, matrixSelectedWalshProduct_smul]

/-- Full multifactor Walsh factorization for the manuscript's rectangular
common occurrence row. -/
theorem matrixWalshCharacterSum_factorization {y n : Type*} [Fintype n]
    (C : Matrix y n ℂ) (fs : List (WalshFactor (Matrix n n ℂ))) :
    matrixWalshCharacterSum C fs =
      ((2 : ℂ) ^ fs.length) • matrixSelectedWalshProduct C fs := by
  induction fs generalizing C with
  | nil => simp [matrixWalshCharacterSum, matrixSelectedWalshProduct]
  | cons f fs ih =>
      rw [matrixWalshCharacterSum, ih, ih]
      cases hsel : f.selected
      · simp only [hsel, Bool.false_eq_true, ↓reduceIte,
          matrixSelectedWalshProduct, List.length_cons, pow_succ, one_smul]
        rw [← smul_add, matrixSelectedWalshProduct_even_split, smul_smul]
      · simp only [hsel, ↓reduceIte, matrixSelectedWalshProduct,
          List.length_cons, pow_succ, neg_smul, one_smul]
        rw [← sub_eq_add_neg, ← smul_sub,
          matrixSelectedWalshProduct_odd_split, smul_smul]

/-- A nonzero scalar multiple of a common row followed by a unitary ordered
product reconstructs the row and preserves its matrix rank. -/
theorem commonRow_reconstruction_from_unitaryTop {y n : Type*}
    [Fintype n] [DecidableEq n]
    (C : Matrix y n ℂ) (U : Matrix n n ℂ) (α : ℂ)
    (hα : α ≠ 0) (hU : U * Uᴴ = 1) :
    α⁻¹ • ((α • (C * U)) * Uᴴ) = C ∧ (C * U).rank = C.rank := by
  constructor
  · rw [Matrix.smul_mul, Matrix.mul_assoc, hU, Matrix.mul_one,
      smul_smul, inv_mul_cancel₀ hα, one_smul]
  · have hdet : IsUnit U.det := by
      have hd := congrArg Matrix.det hU
      rw [Matrix.det_mul, Matrix.det_one] at hd
      exact isUnit_iff_exists_inv.mpr ⟨(Uᴴ).det, hd⟩
    exact Matrix.rank_mul_eq_left_of_isUnit_det U C hdet

/-- A matrix Walsh factor coming from
`cos θ · I - i sin θ · N`, with the requested character membership. -/
noncomputable def trigonometricWalshFactor {n : Type*}
    [Fintype n] [DecidableEq n] (N : Matrix n n ℂ) (θ : ℝ)
    (selected : Bool) : WalshFactor (Matrix n n ℂ) where
  evenPart := (Real.cos θ : ℂ) • 1
  oddPart := (-(Complex.I * Real.sin θ)) • N
  selected := selected

/-- The trigonometric factor is the actual matrix exponential of a normalized
involution.  This supplies the exponential-to-Walsh bridge used in the
manuscript's definition of every resolved branch. -/
theorem involution_exp_eq_walshRot {n : Type*}
    [Fintype n] [DecidableEq n] (N : Matrix n n ℂ)
    (hN : N * N = 1) (θ : ℝ) :
    NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • N) = walshRot N θ := by
  have hevenPow (k : ℕ) : N ^ (2 * k) = 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.mul_succ, pow_add, ih]
        simpa [pow_two] using hN
  have hoddPow (k : ℕ) : N ^ (2 * k + 1) = N := by
    rw [pow_succ, hevenPow, one_mul]
  have hscalarEven (k : ℕ) :
      (-(Complex.I * (θ : ℂ))) ^ (2 * k) =
        (-1 : ℂ) ^ k * (θ : ℂ) ^ (2 * k) := by
    rw [neg_pow, mul_pow,
      show Complex.I ^ (2 * k) = (Complex.I ^ 2) ^ k by rw [pow_mul],
      Complex.I_sq]
    simp [Even.neg_one_pow (even_two_mul k)]
  have hscalarOdd (k : ℕ) :
      (-(Complex.I * (θ : ℂ))) ^ (2 * k + 1) =
        (-Complex.I) * ((-1 : ℂ) ^ k * (θ : ℂ) ^ (2 * k + 1)) := by
    rw [pow_succ, hscalarEven, pow_succ]
    ring
  have hcos := Complex.hasSum_cos (θ : ℂ)
  have hcosM := hcos.smul_const (1 : Matrix n n ℂ)
  have hsin := (Complex.hasSum_sin (θ : ℂ)).mul_left (-Complex.I)
  have hsinM := hsin.smul_const N
  have heven : HasSum
      (fun k : ℕ => (((2 * k).factorial : ℂ)⁻¹ •
        ((-(Complex.I * (θ : ℂ))) • N) ^ (2 * k)))
      ((Real.cos θ : ℂ) • (1 : Matrix n n ℂ)) := by
    convert hcosM using 1
    · funext k
      ext i j
      rw [smul_pow, hevenPow, hscalarEven]
      simp [div_eq_mul_inv]
      ring
    · simp
  have hodd : HasSum
      (fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹ •
        ((-(Complex.I * (θ : ℂ))) • N) ^ (2 * k + 1)))
      ((-(Complex.I * Real.sin θ)) • N) := by
    convert hsinM using 1
    · funext k
      ext i j
      rw [smul_pow, hoddPow, hscalarOdd]
      simp [div_eq_mul_inv]
      ring
    · simp
  have hsplit : HasSum
      (fun k : ℕ => (k.factorial : ℂ)⁻¹ •
        ((-(Complex.I * (θ : ℂ))) • N) ^ k)
      ((Real.cos θ : ℂ) • (1 : Matrix n n ℂ) +
        (-(Complex.I * Real.sin θ)) • N) :=
    HasSum.even_add_odd heven hodd
  rw [congrFun (exp_eq_tsum ℂ)
    ((-(Complex.I * (θ : ℂ))) • N)]
  simpa [walshRot] using hsplit.tsum_eq

/-- The two sign branches of a trigonometric Walsh factor are exactly the
positive- and negative-angle rotations. -/
theorem trigonometricWalshFactor_branches {n : Type*}
    [Fintype n] [DecidableEq n] (N : Matrix n n ℂ) (θ : ℝ)
    (selected : Bool) :
    (trigonometricWalshFactor N θ selected).evenPart +
        (trigonometricWalshFactor N θ selected).oddPart = walshRot N θ ∧
      (trigonometricWalshFactor N θ selected).evenPart -
        (trigonometricWalshFactor N θ selected).oddPart = walshRot N (-θ) := by
  constructor
  · rfl
  · simp [trigonometricWalshFactor, walshRot, Real.cos_neg, Real.sin_neg]

/-- At quarter dwell, an unselected factor kills the selected monomial because
its even part is zero. -/
theorem selectedWalshProduct_quarterDwell_vanishes {n : Type*}
    [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (pre post : List (WalshFactor (Matrix n n ℂ)))
    (N : Matrix n n ℂ) :
    selectedWalshProduct C
      (pre ++ trigonometricWalshFactor N (Real.pi / 2) false :: post) = 0 := by
  induction pre generalizing C with
  | nil =>
      simp only [List.nil_append, selectedWalshProduct,
        trigonometricWalshFactor, Bool.false_eq_true, ↓reduceIte,
        Real.cos_pi_div_two, Complex.ofReal_zero, zero_smul, mul_zero]
      exact selectedWalshProduct_zero post
  | cons f pre ih =>
      simp only [List.cons_append, selectedWalshProduct]
      exact ih _

/-- The top character at quarter dwell is the ordered product of the normalized
Walsh directions, with one factor `-i` per direction. -/
theorem selectedWalshProduct_top_quarterDwell {n : Type*}
    [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (Ns : List (Matrix n n ℂ)) :
    selectedWalshProduct C
        (Ns.map fun N => trigonometricWalshFactor N (Real.pi / 2) true) =
      Ns.foldl (fun X N => X * ((-Complex.I) • N)) C := by
  induction Ns generalizing C with
  | nil => rfl
  | cons N Ns ih =>
      rw [List.map_cons]
      simp only [selectedWalshProduct, trigonometricWalshFactor,
        Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ofReal_zero,
        Complex.ofReal_one, zero_smul]
      rw [List.foldl_cons]
      simpa [trigonometricWalshFactor, Matrix.mul_smul] using
        ih (C * ((-Complex.I) • N))

/-- The common-row hypothesis is necessary.  Two resolved two-branch packets
can have identical branch effects while their odd Walsh coefficients differ. -/
theorem resolvedEffects_do_not_determine_topWalsh :
    let plus₁ : Matrix (Fin 1) (Fin 1) ℂ := 1
    let minus₁ : Matrix (Fin 1) (Fin 1) ℂ := 1
    let plus₂ : Matrix (Fin 1) (Fin 1) ℂ := 1
    let minus₂ : Matrix (Fin 1) (Fin 1) ℂ := -1
    Matrix.conjTranspose plus₁ * plus₁ = Matrix.conjTranspose plus₂ * plus₂ ∧
      Matrix.conjTranspose minus₁ * minus₁ = Matrix.conjTranspose minus₂ * minus₂ ∧
      plus₁ - minus₁ ≠ plus₂ - minus₂ := by
  dsimp
  constructor
  · simp
  constructor
  · simp
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    norm_num at h00

end NCG
