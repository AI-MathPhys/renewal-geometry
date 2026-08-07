/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Grand-Tensor countermodels
  (`cth:ambient-invisible`, `cth:generation-number`,
   `cth:Schur-fill-in`, `cth:relative-interface-frame`,
   `cth:cohomology-rank-not-determinant`,
   `countertheorem:a-second-scalar-coupling...`,
   `countertheorem:dimension-coincidence...`,
   `prop:opposite-innovation`, Gran-Tensor manuscript)

* `ambient_invisible`: appending an ambient summand with zero
  source (`T ⊕ A`, `S ⊕ 0`) leaves every declared source moment
  `SᴴTⁿS` unchanged — ambient sectors are not data identifiable;
* `generation_number_free`: tensoring by a trivial multiplicity
  space `ℂ^g` leaves every moment in Kronecker-multiplied form
  (`(SᴴTⁿS)⊗I_g`), while the carrier dimension scales by `g` —
  gauge data do not determine generation number;
* `schur_fill_in`: an explicit star system with two boundary–
  interior couplings whose Schur response has all four entries
  nonzero — elimination creates quadratic fill-in;
* `relative_interface_frame`: two gluings with identical
  component data up to a coupling sign (equal component
  responses) and different glued responses — local spectra do
  not determine gluing;
* `cohomology_rank_not_determinant`: two one-arrow complexes
  with equal kernel/cokernel dimensions and different singular-
  value Grams;
* `second_scalar_coupling`: two different couplings produce
  identical normalized branch probabilities — no retained
  discriminator;
* `dimension_coincidence`: two three-dimensional carriers with
  different first moments admit no source-fixing intertwiner —
  dimension coincidence is not cycle–flavour duality;
* `opposite_innovation`: the innovation short supports both a
  small-rank/large-energy and a full-rank/small-energy
  instance — neither objective controls the other.
-/

open Matrix Kronecker

namespace NCG

/-- `cth:ambient-invisible`: the ambient extension
`T' = T ⊕ A`, `S' = S ⊕ 0` has identical declared source
moments at every order. -/
theorem ambient_invisible {m z p : Type*} [Fintype m]
    [Fintype z] [DecidableEq m] [DecidableEq z]
    (T : Matrix m m ℂ) (A : Matrix z z ℂ)
    (S : Matrix m p ℂ) (n : ℕ) :
    (Matrix.fromBlocks S (0 : Matrix m Unit ℂ)
        (0 : Matrix z p ℂ) (0 : Matrix z Unit ℂ))ᴴ
      * (Matrix.fromBlocks T 0 0 A) ^ n
      * Matrix.fromBlocks S (0 : Matrix m Unit ℂ)
          (0 : Matrix z p ℂ) (0 : Matrix z Unit ℂ)
    = Matrix.fromBlocks (Sᴴ * T ^ n * S)
        (0 : Matrix p Unit ℂ) (0 : Matrix Unit p ℂ)
        (0 : Matrix Unit Unit ℂ) := by
  have hpow : (Matrix.fromBlocks T 0 0 A) ^ n
      = Matrix.fromBlocks (T ^ n) 0 0 (A ^ n) := by
    induction n with
    | zero =>
      simp [pow_zero, Matrix.fromBlocks_one]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ, pow_succ,
        Matrix.fromBlocks_multiply]
      simp
  rw [hpow, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

/-- `cth:generation-number`: tensoring by the trivial
multiplicity space `ℂ^g` multiplies every moment by `I_g` and
scales the carrier dimension by `g`. -/
theorem generation_number_free {m p : Type*} [Fintype m]
    [DecidableEq m] (g : ℕ)
    (T : Matrix m m ℂ) (S : Matrix m p ℂ) (n : ℕ) :
    ((S ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ))ᴴ
        * (T ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ)) ^ n
        * (S ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ))
      = (Sᴴ * T ^ n * S) ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ))
    ∧ Fintype.card (m × Fin g) = Fintype.card m * g := by
  constructor
  · have hkH : (S ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ))ᴴ
        = Sᴴ ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ) := by
      ext ⟨a, b⟩ ⟨c, d⟩
      simp [Matrix.conjTranspose_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply, eq_comm]
      split <;> simp
    have hpow : (T ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ)) ^ n
        = (T ^ n) ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ) := by
      induction n with
      | zero => simp [pow_zero]
      | succ k ih =>
        rw [pow_succ, ih, ← Matrix.mul_kronecker_mul,
          Matrix.one_mul, ← pow_succ]
    rw [hkH, hpow, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.one_mul]
  · simp [Fintype.card_prod]

/-- `cth:Schur-fill-in`: a star system with two couplings whose
Schur response `A - K H⁻¹ L` has all four entries nonzero. -/
theorem schur_fill_in :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℚ) (K : Matrix (Fin 2)
        (Fin 1) ℚ) (L : Matrix (Fin 1) (Fin 2) ℚ)
      (H : Matrix (Fin 1) (Fin 1) ℚ),
      (∀ i j, (A - K * H⁻¹ * L) i j ≠ 0)
      ∧ (∀ i j, i ≠ j → A i j = 0) := by
  refine ⟨!![2, 0; 0, 2], !![1; 1], !![1, 1], !![1], ?_, ?_⟩
  · intro i j
    have hinv : (!![1] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹
        = !![1] := by
      rw [show (!![1] : Matrix (Fin 1) (Fin 1) ℚ) = 1 from by
        ext i j
        fin_cases i
        fin_cases j
        rfl]
      simp
    rw [hinv]
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.sub_apply,
        Fin.sum_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- `cth:relative-interface-frame`: two gluings with equal
component responses (`A_j - K_jH_j⁻¹L_j`) and different glued
responses. -/
theorem relative_interface_frame :
    ∃ (K L K' L' : ℚ),
      -- equal component data (same self-response)
      (0 - K * 1⁻¹ * L = 0 - K' * 1⁻¹ * L')
      -- different glued cross response through the shared
      -- interface H₁ + H₂ = 2
      ∧ (0 - K * (2 : ℚ)⁻¹ * L') ≠ 0 - K' * (2 : ℚ)⁻¹ * L' :=
  ⟨1, 1, -1, -1, by norm_num, by norm_num⟩

/-- `cth:cohomology-rank-not-determinant`: two one-arrow
complexes with equal kernel and cokernel dimensions and
different singular-value Grams. -/
theorem cohomology_rank_not_determinant :
    ∃ d d' : Matrix (Fin 1) (Fin 1) ℂ,
      Module.finrank ℂ (LinearMap.ker d.mulVecLin)
        = Module.finrank ℂ (LinearMap.ker d'.mulVecLin)
      ∧ dᴴ * d ≠ d'ᴴ * d' := by
  refine ⟨!![1], !![2], ?_, ?_⟩
  · have h1 : (!![1] : Matrix (Fin 1) (Fin 1) ℂ).mulVecLin.ker
        = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      funext i
      fin_cases i
      have := congrFun hxy 0
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec,
        dotProduct] using this
    have h2 : (!![2] : Matrix (Fin 1) (Fin 1) ℂ).mulVecLin.ker
        = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      funext i
      fin_cases i
      have := congrFun hxy 0
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_one] at this
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      field_simp at this
      exact this
    rw [h1, h2]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      at this
    norm_num at this

/-- Second-scalar-coupling countertheorem: different couplings,
identical normalized branch probabilities — no retained
discriminator. -/
theorem second_scalar_coupling :
    ∃ a b : ℝ, a ≠ b ∧ 0 < a ∧ 0 < b
      ∧ ∀ v w : ℝ, v ^ 2 + w ^ 2 ≠ 0 →
        (a * v) ^ 2 / ((a * v) ^ 2 + (a * w) ^ 2)
          = (b * v) ^ 2 / ((b * v) ^ 2 + (b * w) ^ 2) := by
  refine ⟨1, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  intro v w hvw
  have h4 : (0:ℝ) < 4 := by norm_num
  rw [show ((2:ℝ) * v) ^ 2 = 4 * v ^ 2 from by ring,
    show ((2:ℝ) * w) ^ 2 = 4 * w ^ 2 from by ring,
    show (4 * v ^ 2 + 4 * w ^ 2 : ℝ)
      = 4 * (v ^ 2 + w ^ 2) from by ring,
    show ((1:ℝ) * v) ^ 2 = v ^ 2 from by ring,
    show ((1:ℝ) * w) ^ 2 = w ^ 2 from by ring,
    mul_div_mul_left _ _ (by norm_num : (4:ℝ) ≠ 0)]

/-- Dimension-coincidence countertheorem: two three-dimensional
carriers whose first moments differ admit no source-fixing
transfer intertwiner. -/
theorem dimension_coincidence :
    ∃ (T T' : Matrix (Fin 3) (Fin 3) ℂ)
      (S S' : Matrix (Fin 3) (Fin 3) ℂ),
      ¬∃ U : Matrix (Fin 3) (Fin 3) ℂ,
        Uᴴ * U = 1 ∧ U * S = S' ∧ U * T = T' * U := by
  refine ⟨1, (2 : ℂ) • 1, 1, 1, ?_⟩
  rintro ⟨U, hU, -, hUT⟩
  rw [Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at hUT
  have hU0 : U = 0 := by
    have h := congrArg (fun M => M - (2 : ℂ) • U) hUT
    simp only [sub_self] at h
    have h' : (-1 : ℂ) • U = 0 := by
      rw [← h]
      module
    have := congrArg (fun M => (-1 : ℂ) • M) h'
    simpa using this
  rw [hU0] at hU
  have := congrFun (congrFun hU 0) 0
  simp at this

/-- `prop:opposite-innovation`: the innovation short supports a
rank-one/large-trace instance and a full-rank/small-trace
instance — neither objective controls the other. -/
theorem opposite_innovation :
    ∃ V1 V2 : Matrix (Fin 3) (Fin 3) ℚ,
      V1.PosSemidef ∧ V2.PosSemidef
      ∧ V1.rank = 1 ∧ V1.trace = 100
      ∧ V2.rank = 3 ∧ V2.trace = 3 := by
  refine ⟨Matrix.diagonal ![100, 0, 0],
    Matrix.diagonal ![1, 1, 1], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Matrix.posSemidef_diagonal_iff.mpr ?_
    intro i
    fin_cases i <;> norm_num
  · refine Matrix.posSemidef_diagonal_iff.mpr ?_
    intro i
    fin_cases i <;> norm_num
  · rw [Matrix.rank_diagonal, Fintype.card_subtype]
    decide
  · simp [Matrix.trace_diagonal, Fin.sum_univ_three]
  · rw [Matrix.rank_diagonal, Fintype.card_subtype]
    decide
  · norm_num [Matrix.trace_diagonal, Fin.sum_univ_succ]

end NCG
