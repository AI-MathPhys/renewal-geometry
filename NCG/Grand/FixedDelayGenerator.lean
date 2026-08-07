/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One isolated continuous delay does not identify a hidden
  generator (`cth:fixed-delay-hidden-generator`, Gran-Tensor
  manuscript)

The boxed countertheorem: for every `t > 0` there are distinct
balanced irreducible three-state Markov generators
`Q⁽⁰⁾ ≠ Q⁽¹⁾` with `e^{tQ⁽⁰⁾} = e^{tQ⁽¹⁾}` — an atom-resolved
panel at one isolated delay cannot recover circulation or a
generator logarithm.

Witness (the manuscript's): `Q_{a,b} = a(C-1) + b(C²-1)` for the
cyclic shift `C`, with `s* = 4π/(√3 t)`, `Q⁽⁰⁾ = Q_{s*/2, s*/2}`
and `Q⁽¹⁾ = Q_{s*, 0}`.  The difference is
`t(Q⁽⁰⁾ - Q⁽¹⁾) = (2π/√3)(C² - C)`, whose exponential is the
identity: `C² - C` is diagonalized by the discrete Fourier
matrix with eigenvalues `0, ∓√3 i`, so the scaled eigenvalues
are `0, ∓2πi` and every eigenfactor exponentiates to `1`.  Since
the two generators commute (both are polynomials in `C`), the
exponentials agree.

Everything is proved here: the cube-root-of-unity algebra, the
DFT inversion `F G = G F = 1`, the eigenrelation
`(2π/√3)(C²-C) F = F · diag(0, -2πi, 2πi)`, the exponential
evaluation through `Matrix.exp_units_conj` and
`Matrix.exp_diagonal`, and the final commuting-splitting
assembly `e^{tQ⁽⁰⁾} = e^{t(Q⁽⁰⁾-Q⁽¹⁾)} e^{tQ⁽¹⁾} = e^{tQ⁽¹⁾}`.
-/

open Matrix Real

namespace NCG

noncomputable section FixedDelay

/-- Primitive cube root of unity `ω = (-1 + √3 i)/2`. -/
def ω : ℂ := (-1 + Real.sqrt 3 * Complex.I) / 2

private lemma sq3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  have h : (Real.sqrt 3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  calc (Real.sqrt 3 : ℂ) ^ 2
      = ((Real.sqrt 3 ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = 3 := by rw [h]; norm_num

private lemma omega_sum : 1 + ω + ω ^ 2 = 0 := by
  unfold ω
  linear_combination (1 / 4 : ℂ) * (Real.sqrt 3 : ℂ) ^ 2
      * Complex.I_sq - (1 / 4 : ℂ) * sq3

private lemma omega_cube : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * omega_sum

private lemma omega_diff :
    ω ^ 2 - ω = -(Real.sqrt 3 : ℂ) * Complex.I := by
  unfold ω
  linear_combination (1 / 4 : ℂ) * (Real.sqrt 3 : ℂ) ^ 2
      * Complex.I_sq - (1 / 4 : ℂ) * sq3

/-- The skew part of the cyclic shift: `M = C² - C`. -/
def Mmat : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -1, 1; 1, 0, -1; -1, 1, 0]

/-- Discrete Fourier eigenvector matrix `F[j][k] = ω^{jk}`. -/
def Fdft : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

/-- Inverse DFT matrix `G = F⁻¹ = (1/3)F̄`. -/
def Gdft : Matrix (Fin 3) (Fin 3) ℂ :=
  (3 : ℂ)⁻¹ • !![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2]

/-- Scaled eigenvalue diagonal `diag(0, -2πi, 2πi)`. -/
def Ddiag : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal
    ![0, -(2 * Real.pi) * Complex.I, (2 * Real.pi) * Complex.I]

/-- The manuscript's spectral scale `α = 2π/√3 = 2π√3/3`,
written division-free in `√3`. -/
def αc : ℂ := ((2 * Real.pi * Real.sqrt 3 / 3 : ℝ) : ℂ)

/-- `2π/√3` agrees with the division-free form `2π√3/3`. -/
private lemma alpha_real :
    2 * Real.pi / Real.sqrt 3 = 2 * Real.pi * Real.sqrt 3 / 3 := by
  have h : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : (Real.sqrt 3 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp
  linear_combination -h

set_option linter.flexible false in
private lemma fdft_mul_gdft : Fdft * Gdft = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fdft, Gdft, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | linear_combination (1 / 3 : ℂ) * omega_sum
      | linear_combination (2 / 3 : ℂ) * (ω - 1) * omega_sum
      | linear_combination
          (1 / 3 : ℂ) * (1 - ω + ω ^ 2) * omega_sum
      | norm_num

set_option linter.flexible false in
private lemma gdft_mul_fdft : Gdft * Fdft = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fdft, Gdft, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | linear_combination (1 / 3 : ℂ) * omega_sum
      | linear_combination (2 / 3 : ℂ) * (ω - 1) * omega_sum
      | linear_combination
          (1 / 3 : ℂ) * (1 - ω + ω ^ 2) * omega_sum
      | norm_num

/-- The DFT unit in the matrix ring. -/
def Udft : (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  ⟨Fdft, Gdft, fdft_mul_gdft, gdft_mul_fdft⟩

private lemma sqrt3_ne : (Real.sqrt 3 : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast h.ne'

private lemma alpha_sqrt3 : αc * (Real.sqrt 3 : ℂ) = 2 * Real.pi := by
  unfold αc
  push_cast
  linear_combination (2 * (Real.pi : ℂ) / 3) * sq3

private lemma key1 :
    αc * (ω ^ 2 - ω) = -(2 * Real.pi) * Complex.I := by
  rw [omega_diff]
  linear_combination (-Complex.I) * alpha_sqrt3

private lemma key2 :
    αc * (1 - ω ^ 2) = -(2 * Real.pi) * Complex.I * ω := by
  linear_combination ω * key1 - αc * (ω - 1) * omega_sum

private lemma key3 :
    αc * (ω - 1) = -(2 * Real.pi) * Complex.I * ω ^ 2 := by
  linear_combination ω ^ 2 * key1 - αc * (ω - 1) ^ 2 * omega_sum

set_option linter.flexible false in
/-- Eigenrelation: `(2π/√3)·M·F = F·diag(0, -2πi, 2πi)`. -/
private lemma alpha_M_mul_F :
    (αc • Mmat) * Fdft = Fdft * Ddiag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mmat, Fdft, Ddiag, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.diagonal] <;>
    first
      | linear_combination key1
      | linear_combination key2
      | linear_combination key3
      | linear_combination -key1
      | linear_combination -key2
      | linear_combination -key3

-- the scoped operator-norm instances provide the Banach-algebra
-- structure for the exponential series; the coercion instance is
-- disabled to avoid the known matrix-exponential timeout
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open NormedSpace in
open scoped Norms.Operator in
/-- The scaled skew shift exponentiates to the identity:
`e^{(2π/√3)(C²-C)} = 1` — every eigenvalue is `0` or `∓2πi`. -/
theorem exp_alpha_skew : exp (αc • Mmat) = 1 := by
  have hconj : αc • Mmat
      = (Udft : Matrix (Fin 3) (Fin 3) ℂ) * Ddiag
        * ((Udft⁻¹ : (Matrix (Fin 3) (Fin 3) ℂ)ˣ)
            : Matrix (Fin 3) (Fin 3) ℂ) := by
    have h1 : (αc • Mmat) * Fdft = Fdft * Ddiag := alpha_M_mul_F
    have h2 : αc • Mmat = ((αc • Mmat) * Fdft) * Gdft := by
      rw [Matrix.mul_assoc, fdft_mul_gdft, Matrix.mul_one]
    rw [h2, h1]
    rfl
  have hD : exp Ddiag = 1 := by
    rw [Ddiag, Matrix.exp_diagonal]
    have h0 : exp (0 : ℂ) = 1 := exp_zero
    have hpos : exp ((2 * Real.pi) * Complex.I) = 1 := by
      rw [← Complex.exp_eq_exp_ℂ]
      simpa [mul_comm, mul_assoc] using Complex.exp_two_pi_mul_I
    have hneg : exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_eq_exp_ℂ, Complex.exp_neg,
        Complex.exp_two_pi_mul_I, inv_one]
    have hfun : exp (![0, -(2 * Real.pi) * Complex.I,
        (2 * Real.pi) * Complex.I] : Fin 3 → ℂ)
        = fun _ => (1 : ℂ) := by
      rw [Pi.exp_def]
      funext i
      fin_cases i <;> simp [h0, hpos, hneg]
    rw [hfun, Matrix.diagonal_one]
  rw [hconj, Matrix.exp_units_conj, hD, mul_one,
    Units.mul_inv_eq_one]

/-- The balanced circulant generator
`Q_{a,b} = a(C-1) + b(C²-1)` in explicit entries. -/
def Qmat (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(a + b), a, b; b, -(a + b), a; a, b, -(a + b)]

/-- Any two balanced circulant generators commute — both are
polynomials in the cyclic shift. -/
theorem qmat_commute (a b a' b' : ℝ) :
    Qmat a b * Qmat a' b' = Qmat a' b' * Qmat a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qmat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The generator difference at the manuscript's parameters is
the scaled skew shift: `t(Q_{s/2,s/2} - Q_{s,0}) = (2π/√3)M` for
`s = 4π/(√3 t)`. -/
theorem qmat_difference (t : ℝ) (ht : 0 < t) :
    (t : ℂ) • (Qmat (4 * Real.pi / (Real.sqrt 3 * t) / 2)
        (4 * Real.pi / (Real.sqrt 3 * t) / 2)
      - Qmat (4 * Real.pi / (Real.sqrt 3 * t)) 0)
    = αc • Mmat := by
  have hs3 : (Real.sqrt 3 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ht' : t ≠ 0 := ht.ne'
  have hscalar : t * (4 * Real.pi / (Real.sqrt 3 * t) / 2)
      = 2 * Real.pi * Real.sqrt 3 / 3 := by
    rw [← alpha_real]
    field_simp
    ring
  have hstep : Qmat (4 * Real.pi / (Real.sqrt 3 * t) / 2)
        (4 * Real.pi / (Real.sqrt 3 * t) / 2)
      - Qmat (4 * Real.pi / (Real.sqrt 3 * t)) 0
      = ((4 * Real.pi / (Real.sqrt 3 * t) / 2 : ℝ) : ℂ)
        • Mmat := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Qmat, Mmat, Matrix.smul_apply] <;> ring
  rw [hstep, smul_smul]
  congr 1
  rw [show αc = ((2 * Real.pi * Real.sqrt 3 / 3 : ℝ) : ℂ)
    from rfl, ← Complex.ofReal_mul]
  exact Complex.ofReal_inj.mpr hscalar

set_option linter.flexible false in
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open NormedSpace in
open scoped Norms.Operator in
/-- Boxed countertheorem `cth:fixed-delay-hidden-generator`: for
every `t > 0` the distinct balanced circulant generators
`Q⁽⁰⁾ = Q_{s*/2, s*/2}` and `Q⁽¹⁾ = Q_{s*, 0}` with
`s* = 4π/(√3 t)` satisfy `e^{tQ⁽⁰⁾} = e^{tQ⁽¹⁾}` — one isolated
continuous delay does not identify the hidden generator. -/
theorem fixed_delay_hidden_generator (t : ℝ) (ht : 0 < t) :
    Qmat (4 * Real.pi / (Real.sqrt 3 * t) / 2)
        (4 * Real.pi / (Real.sqrt 3 * t) / 2)
      ≠ Qmat (4 * Real.pi / (Real.sqrt 3 * t)) 0
    ∧ exp ((t : ℂ) • Qmat (4 * Real.pi / (Real.sqrt 3 * t) / 2)
          (4 * Real.pi / (Real.sqrt 3 * t) / 2))
      = exp ((t : ℂ) • Qmat (4 * Real.pi / (Real.sqrt 3 * t)) 0) := by
  have hspos : 0 < 4 * Real.pi / (Real.sqrt 3 * t) :=
    div_pos (by positivity)
      (mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht)
  refine ⟨?_, ?_⟩
  · intro h
    have h02 := congrFun (congrFun h 0) 2
    simp [Qmat] at h02
    exact absurd h02 ht.ne'
  · have hcommQ := qmat_commute
      (4 * Real.pi / (Real.sqrt 3 * t) / 2)
      (4 * Real.pi / (Real.sqrt 3 * t) / 2)
      (4 * Real.pi / (Real.sqrt 3 * t)) 0
    have hcomm : Commute
        ((t : ℂ) • (Qmat (4 * Real.pi / (Real.sqrt 3 * t) / 2)
            (4 * Real.pi / (Real.sqrt 3 * t) / 2)
          - Qmat (4 * Real.pi / (Real.sqrt 3 * t)) 0))
        ((t : ℂ) • Qmat (4 * Real.pi / (Real.sqrt 3 * t)) 0) := by
      apply Commute.smul_left
      apply Commute.smul_right
      change _ * _ = _ * _
      rw [Matrix.sub_mul, Matrix.mul_sub, hcommQ]
    have hsplit : (t : ℂ) • Qmat
          (4 * Real.pi / (Real.sqrt 3 * t) / 2)
          (4 * Real.pi / (Real.sqrt 3 * t) / 2)
        = (t : ℂ) • (Qmat (4 * Real.pi / (Real.sqrt 3 * t) / 2)
              (4 * Real.pi / (Real.sqrt 3 * t) / 2)
            - Qmat (4 * Real.pi / (Real.sqrt 3 * t)) 0)
          + (t : ℂ) • Qmat (4 * Real.pi / (Real.sqrt 3 * t)) 0 := by
      rw [← smul_add]
      congr 1
      abel
    rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm,
      qmat_difference t ht, exp_alpha_skew, one_mul]

end FixedDelay

end NCG
