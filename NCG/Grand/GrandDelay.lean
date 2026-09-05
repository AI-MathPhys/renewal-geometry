/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive delay and Herglotz interface gluing
  (`thm:positive-delay`, `thm:Herglotz-gluing`,
   Gran-Tensor manuscript)

* `herm_shift_invertible`: for Hermitian `Λ` the Cayley shift
  `Λ + iI` is invertible (no Hermitian matrix has eigenvalue
  `-i`);
* `positive_delay`: the boxed Wigner–Smith identity — with
  `S = (Λ-iI)(Λ+iI)⁻¹` and the Leibniz derivative `S'` built
  from `Λ'`, the delay operator is
  `Q = -iS*S' = 2(Λ+iI)⁻*Λ'(Λ+iI)⁻¹ ≻ 0`, and its trace has
  positive real part — the scattering phase `arg det S` is
  strictly increasing;
* `herglotz_gluing` / `herglotz_strict`: the boxed
  conservative-gluing identity — for the solved interface value
  `u` the glued quadratic form is the sum of the component
  forms; hence with strict component Herglotz forms the glued
  imaginary part is strictly positive and the interface block
  `D₁+D₂` is invertible.

Rendering disclosed: `S'` enters through its Leibniz expansion
in the matrix derivative `Λ'` (the calculus layer is one
displayed formula); the identification of `Tr Q` with
`(arg det S)'` is the Jacobi formula, rendered by the
positive-trace clause.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedSimpArgs false

private lemma quad_real {n : Type*} [Fintype n]
    (L : Matrix n n ℂ) (hL : Lᴴ = L) (v : n → ℂ) :
    (star (star v ⬝ᵥ (L *ᵥ v)) : ℂ) = star v ⬝ᵥ (L *ᵥ v) := by
  have hentry : ∀ j k, star (L j k) = L k j := by
    intro j k
    have h := congrFun (congrFun hL k) j
    rw [Matrix.conjTranspose_apply] at h
    exact h
  rw [dotProduct, star_sum]
  rw [Finset.sum_congr rfl (fun j _ => show
      star (star v j * (L *ᵥ v) j)
        = v j * star ((L *ᵥ v) j) from by
    rw [star_mul', Pi.star_apply, star_star])]
  rw [Finset.sum_congr rfl (fun j _ => show
      v j * star ((L *ᵥ v) j)
        = ∑ k, L k j * (v j * star (v k)) from by
    rw [Matrix.mulVec, dotProduct, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul', hentry j k]
    ring)]
  rw [Finset.sum_comm]
  rw [show (∑ i, star v i * (L *ᵥ v) i)
      = ∑ j, ∑ k, L j k * (v k * star (v j)) from by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.star_apply]
    ring]

private lemma norm_quad_pos {n : Type*} [Fintype n]
    {v : n → ℂ} (hv : v ≠ 0) : 0 < (star v ⬝ᵥ v).re := by
  have hsum : (star v ⬝ᵥ v)
      = ∑ j, (Complex.normSq (v j) : ℂ) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, mul_comm,
      Complex.mul_conj]
  have hex : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  obtain ⟨j0, hj0⟩ := hex
  rw [hsum, Complex.re_sum]
  refine Finset.sum_pos'
    (fun j _ => by
      rw [Complex.ofReal_re]
      exact Complex.normSq_nonneg _)
    ⟨j0, Finset.mem_univ j0, by
      rw [Complex.ofReal_re]
      exact Complex.normSq_pos.mpr hj0⟩

private lemma diag_as_quad {n : Type*} [Fintype n]
    [DecidableEq n] (Q : Matrix n n ℂ) (j : n) :
    star (Pi.single j 1 : n → ℂ) ⬝ᵥ (Q *ᵥ Pi.single j 1)
      = Q j j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite,
    ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- For Hermitian `Λ` the Cayley shift `Λ + iI` is
invertible. -/
theorem herm_shift_invertible {n : Type*} [Fintype n]
    [DecidableEq n] (L : Matrix n n ℂ) (hL : Lᴴ = L) :
    IsUnit (L + Complex.I • 1).det := by
  by_contra hdet
  have hdet0 : (L + Complex.I • 1).det = 0 := by
    by_contra h0
    exact hdet (isUnit_iff_ne_zero.mpr h0)
  obtain ⟨v, hv, hvz⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  have hquad := congrArg (fun w => star v ⬝ᵥ w) hvz
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_zero, smul_eq_mul] at hquad
  have him : (star v ⬝ᵥ (L *ᵥ v)).im = 0 := by
    have hc := congrArg Complex.im (quad_real L hL v)
    simp only [Complex.star_def, Complex.conj_im] at hc
    linarith
  have him2 := congrArg Complex.im hquad
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.zero_im, zero_mul, one_mul,
    zero_add] at him2
  rw [him] at him2
  have := norm_quad_pos hv
  linarith

/-- `thm:positive-delay`: the boxed Wigner–Smith identity, the
strict positivity of the delay operator, and the positive
trace (strictly increasing scattering phase). -/
theorem positive_delay {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (L Ld : Matrix n n ℂ) (hL : Lᴴ = L)
    (hLd : Ld.PosDef) [Invertible (L + Complex.I • 1)] :
    ((-Complex.I) • (((L - Complex.I • 1)
          * (L + Complex.I • 1)⁻¹)ᴴ
        * (Ld * (L + Complex.I • 1)⁻¹
          - (L - Complex.I • 1) * (L + Complex.I • 1)⁻¹
            * Ld * (L + Complex.I • 1)⁻¹))
      = (2 : ℂ) • (((L + Complex.I • 1)⁻¹)ᴴ * Ld
          * (L + Complex.I • 1)⁻¹))
    ∧ (∀ x : n → ℂ, x ≠ 0 →
        0 < star x ⬝ᵥ ((((L + Complex.I • 1)⁻¹)ᴴ * Ld
          * (L + Complex.I • 1)⁻¹) *ᵥ x))
    ∧ 0 < (((((L + Complex.I • 1)⁻¹)ᴴ * Ld
        * (L + Complex.I • 1)⁻¹)).trace).re := by
  have hMN : (L + Complex.I • 1) * (L + Complex.I • 1)⁻¹ = 1 :=
    Matrix.mul_inv_of_invertible _
  have hpos : ∀ x : n → ℂ, x ≠ 0 →
      0 < star x ⬝ᵥ ((((L + Complex.I • 1)⁻¹)ᴴ * Ld
        * (L + Complex.I • 1)⁻¹) *ᵥ x) := by
    intro x hx
    have hNx : (L + Complex.I • 1)⁻¹ *ᵥ x ≠ 0 := by
      intro h0
      apply hx
      have hxeq : x = (L + Complex.I • 1)
          *ᵥ ((L + Complex.I • 1)⁻¹ *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
      rw [hxeq, h0, Matrix.mulVec_zero]
    rw [show (((L + Complex.I • 1)⁻¹)ᴴ * Ld
          * (L + Complex.I • 1)⁻¹) *ᵥ x
        = ((L + Complex.I • 1)⁻¹)ᴴ
          *ᵥ (Ld *ᵥ ((L + Complex.I • 1)⁻¹ *ᵥ x)) from by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    exact hLd.dotProduct_mulVec_pos hNx
  refine ⟨?_, hpos, ?_⟩
  · have h1 : (L + Complex.I • 1) * (L + Complex.I • 1)⁻¹
        - (L - Complex.I • 1) * (L + Complex.I • 1)⁻¹
        = (2 * Complex.I) • (L + Complex.I • 1)⁻¹ := by
      rw [← Matrix.sub_mul]
      rw [show L + Complex.I • (1 : Matrix n n ℂ)
          - (L - Complex.I • 1)
          = (2 * Complex.I) • (1 : Matrix n n ℂ) from by
        rw [two_mul, add_smul]
        abel]
      rw [Matrix.smul_mul, Matrix.one_mul]
    have hfact : Ld * (L + Complex.I • 1)⁻¹
        - (L - Complex.I • 1) * (L + Complex.I • 1)⁻¹
          * Ld * (L + Complex.I • 1)⁻¹
        = ((2 * Complex.I) • (L + Complex.I • 1)⁻¹)
          * (Ld * (L + Complex.I • 1)⁻¹) := by
      have hexp : ((2 * Complex.I) • (L + Complex.I • 1)⁻¹)
          * (Ld * (L + Complex.I • 1)⁻¹)
          = ((L + Complex.I • 1) * (L + Complex.I • 1)⁻¹)
            * (Ld * (L + Complex.I • 1)⁻¹)
            - ((L - Complex.I • 1) * (L + Complex.I • 1)⁻¹)
              * (Ld * (L + Complex.I • 1)⁻¹) := by
        rw [← Matrix.sub_mul, h1]
      rw [hexp, hMN, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    rw [hfact]
    have hSH : ((L - Complex.I • 1) * (L + Complex.I • 1)⁻¹)ᴴ
        = ((L + Complex.I • 1)⁻¹)ᴴ * (L + Complex.I • 1) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        hL, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        Complex.star_def, Complex.conj_I, neg_smul,
        sub_neg_eq_add]
    rw [hSH]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show -Complex.I * (2 * Complex.I) = (2 : ℂ) from by
      linear_combination (-2 : ℂ) * Complex.I_mul_I]
    congr 1
    calc ((L + Complex.I • 1)⁻¹)ᴴ * (L + Complex.I • 1)
          * ((L + Complex.I • 1)⁻¹
            * (Ld * (L + Complex.I • 1)⁻¹))
        = ((L + Complex.I • 1)⁻¹)ᴴ
          * (((L + Complex.I • 1) * (L + Complex.I • 1)⁻¹)
            * (Ld * (L + Complex.I • 1)⁻¹)) := by
          simp only [Matrix.mul_assoc]
      _ = ((L + Complex.I • 1)⁻¹)ᴴ * Ld
          * (L + Complex.I • 1)⁻¹ := by
          rw [hMN, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
  · rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_pos (fun j _ => ?_) Finset.univ_nonempty
    have hsingle : (Pi.single j 1 : n → ℂ) ≠ 0 := by
      intro h0
      simpa [Pi.single_apply] using congrFun h0 j
    have hp := hpos (Pi.single j 1) hsingle
    obtain ⟨hre, -⟩ := Complex.lt_def.mp hp
    rw [Matrix.diag_apply,
      ← diag_as_quad (((L + Complex.I • 1)⁻¹)ᴴ * Ld
        * (L + Complex.I • 1)⁻¹) j]
    simpa using hre

/-- `thm:Herglotz-gluing`, boxed identity: for the solved
interface value the glued quadratic form is the sum of the
component block forms. -/
theorem herglotz_gluing {e1 e2 i : Type*} [Fintype e1]
    [Fintype e2] [Fintype i]
    (A1 : Matrix e1 e1 ℂ) (B1 : Matrix e1 i ℂ)
    (C1 : Matrix i e1 ℂ) (D1 : Matrix i i ℂ)
    (A2 : Matrix e2 e2 ℂ) (B2 : Matrix e2 i ℂ)
    (C2 : Matrix i e2 ℂ) (D2 : Matrix i i ℂ)
    (x1 : e1 → ℂ) (x2 : e2 → ℂ) (u : i → ℂ)
    (hsolve : (D1 + D2) *ᵥ u + (C1 *ᵥ x1 + C2 *ᵥ x2) = 0) :
    star x1 ⬝ᵥ (A1 *ᵥ x1 + B1 *ᵥ u)
      + star x2 ⬝ᵥ (A2 *ᵥ x2 + B2 *ᵥ u)
    = (star x1 ⬝ᵥ (A1 *ᵥ x1 + B1 *ᵥ u)
        + star u ⬝ᵥ (C1 *ᵥ x1 + D1 *ᵥ u))
      + (star x2 ⬝ᵥ (A2 *ᵥ x2 + B2 *ᵥ u)
        + star u ⬝ᵥ (C2 *ᵥ x2 + D2 *ᵥ u)) := by
  have hz : star u ⬝ᵥ ((D1 + D2) *ᵥ u
      + (C1 *ᵥ x1 + C2 *ᵥ x2)) = 0 := by
    rw [hsolve, dotProduct_zero]
  simp only [Matrix.add_mulVec, dotProduct_add] at hz ⊢
  linear_combination -hz

/-- `thm:Herglotz-gluing`, strictness: with strict component
Herglotz forms the glued imaginary part is strictly positive
and the interface block `D₁+D₂` is invertible. -/
theorem herglotz_strict {e1 e2 i : Type*} [Fintype e1]
    [Fintype e2] [Fintype i] [DecidableEq i]
    (A1 : Matrix e1 e1 ℂ) (B1 : Matrix e1 i ℂ)
    (C1 : Matrix i e1 ℂ) (D1 : Matrix i i ℂ)
    (A2 : Matrix e2 e2 ℂ) (B2 : Matrix e2 i ℂ)
    (C2 : Matrix i e2 ℂ) (D2 : Matrix i i ℂ)
    (hH1 : ∀ (y : e1 → ℂ) (v : i → ℂ), ¬(y = 0 ∧ v = 0) →
      0 < (star y ⬝ᵥ (A1 *ᵥ y + B1 *ᵥ v)
        + star v ⬝ᵥ (C1 *ᵥ y + D1 *ᵥ v)).im)
    (hH2 : ∀ (y : e2 → ℂ) (v : i → ℂ), ¬(y = 0 ∧ v = 0) →
      0 < (star y ⬝ᵥ (A2 *ᵥ y + B2 *ᵥ v)
        + star v ⬝ᵥ (C2 *ᵥ y + D2 *ᵥ v)).im) :
    (∀ (x1 : e1 → ℂ) (x2 : e2 → ℂ) (u : i → ℂ),
      (D1 + D2) *ᵥ u + (C1 *ᵥ x1 + C2 *ᵥ x2) = 0 →
      x1 ≠ 0 ∨ x2 ≠ 0 →
      0 < (star x1 ⬝ᵥ (A1 *ᵥ x1 + B1 *ᵥ u)
        + star x2 ⬝ᵥ (A2 *ᵥ x2 + B2 *ᵥ u)).im)
    ∧ IsUnit (D1 + D2).det := by
  constructor
  · intro x1 x2 u hsolve hx
    rw [herglotz_gluing A1 B1 C1 D1 A2 B2 C2 D2 x1 x2 u hsolve,
      Complex.add_im]
    have hterm1 : 0 ≤ (star x1 ⬝ᵥ (A1 *ᵥ x1 + B1 *ᵥ u)
        + star u ⬝ᵥ (C1 *ᵥ x1 + D1 *ᵥ u)).im := by
      by_cases h10 : x1 = 0 ∧ u = 0
      · rw [h10.1, h10.2]
        simp
      · exact (hH1 x1 u h10).le
    have hterm2 : 0 ≤ (star x2 ⬝ᵥ (A2 *ᵥ x2 + B2 *ᵥ u)
        + star u ⬝ᵥ (C2 *ᵥ x2 + D2 *ᵥ u)).im := by
      by_cases h20 : x2 = 0 ∧ u = 0
      · rw [h20.1, h20.2]
        simp
      · exact (hH2 x2 u h20).le
    rcases hx with hx1 | hx2
    · have h1 := hH1 x1 u (fun hand => hx1 hand.1)
      linarith
    · have h2 := hH2 x2 u (fun hand => hx2 hand.1)
      linarith
  · by_contra hdet
    have hdet0 : (D1 + D2).det = 0 := by
      by_contra h0
      exact hdet (isUnit_iff_ne_zero.mpr h0)
    obtain ⟨v, hv, hvz⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    have hq := congrArg (fun w => (star v ⬝ᵥ w).im) hvz
    simp only [Matrix.add_mulVec, dotProduct_add,
      dotProduct_zero, Complex.add_im, Complex.zero_im] at hq
    have h1 := hH1 0 v (fun hand => hv hand.2)
    have h2 := hH2 0 v (fun hand => hv hand.2)
    simp only [star_zero, zero_dotProduct, Matrix.mulVec_zero,
      zero_add] at h1 h2
    linarith

end NCG
