/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spectral functions of Hermitian matrices, Rayleigh forms and the Loewner influence

* `spectralFunction hS f = U · diag(f ∘ λ) · U^*` for a Hermitian `S` (spectral theorem), with
  `spectralFunction_id`, additivity, scaling, constants, finite sums and
  `spectralFunction_posSemidef` (nonnegative `f` gives a positive semidefinite matrix);
* `rayleigh M x = Re ⟪x, M x⟫` with nonnegativity on PSD matrices, linearity, `rayleigh 1 x`
  and monotonicity under the Loewner order (`rayleigh_le_of_posSemidef`);
* `influence B C = inf{λ ≥ 0 : C ⪯ λ B}` in Rayleigh form.

Split out of `GeometricThresholdBankExact` (declaration names unchanged).
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace MathPhys
namespace GeometricThresholdBank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation by the eigenvector unitary: `U · diag(f ∘ λ) · U^*`. -/
noncomputable def spectralFunction {S : Matrix n n ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ) :
    Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hS.eigenvectorUnitary
    (diagonal (RCLike.ofReal ∘ fun i => f (hS.eigenvalues i)))

theorem spectralFunction_id {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    spectralFunction hS id = S := by
  unfold spectralFunction
  exact hS.spectral_theorem.symm

theorem spectralFunction_add {S : Matrix n n ℂ} (hS : S.IsHermitian) (f g : ℝ → ℝ) :
    spectralFunction hS (fun l => f l + g l) = spectralFunction hS f + spectralFunction hS g := by
  unfold spectralFunction
  rw [← map_add, diagonal_add]
  congr 2
  funext i
  simp

theorem spectralFunction_sub {S : Matrix n n ℂ} (hS : S.IsHermitian) (f g : ℝ → ℝ) :
    spectralFunction hS (fun l => f l - g l) = spectralFunction hS f - spectralFunction hS g := by
  unfold spectralFunction
  rw [← map_sub, diagonal_sub]
  congr 2
  funext i
  simp

theorem spectralFunction_smul {S : Matrix n n ℂ} (hS : S.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    spectralFunction hS (fun l => c * f l) = (c : ℂ) • spectralFunction hS f := by
  unfold spectralFunction
  rw [← map_smul]
  congr 1
  rw [← diagonal_smul]
  congr 1
  funext i
  simp

theorem spectralFunction_const {S : Matrix n n ℂ} (hS : S.IsHermitian) (c : ℝ) :
    spectralFunction hS (fun _ => c) = (c : ℂ) • (1 : Matrix n n ℂ) := by
  unfold spectralFunction
  have : diagonal (RCLike.ofReal ∘ fun i => (fun _ : ℝ => c) (hS.eigenvalues i))
      = (c : ℂ) • (1 : Matrix n n ℂ) := by
    rw [← diagonal_one, ← diagonal_smul]
    congr 1
    funext i
    simp
  rw [this, map_smul, map_one]

theorem spectralFunction_sum {S : Matrix n n ℂ} (hS : S.IsHermitian) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) :
    spectralFunction hS (fun l => ∑ k ∈ s, f k l) = ∑ k ∈ s, spectralFunction hS (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [spectralFunction_const]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have : (fun l => ∑ k ∈ insert a s, f k l) = fun l => f a l + ∑ k ∈ s, f k l := by
      funext l; rw [Finset.sum_insert ha]
    rw [this, spectralFunction_add, ih]

/-- A spectral function with nonnegative values on the spectrum is PSD. -/
theorem spectralFunction_posSemidef {S : Matrix n n ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (hS.eigenvalues i)) : (spectralFunction hS f).PosSemidef := by
  unfold spectralFunction
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  refine PosSemidef.mul_mul_conjTranspose_same ?_ _
  rw [posSemidef_diagonal_iff]
  intro i
  simpa [Complex.zero_le_real] using hf i

/-- The real quadratic form `Re ⟪x, M x⟫`. -/
noncomputable def rayleigh (M : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ (M *ᵥ x)).re

omit [DecidableEq n] in
theorem rayleigh_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) (x : n → ℂ) : 0 ≤ rayleigh M x :=
  (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg x)).1

omit [DecidableEq n] in
theorem rayleigh_sub {A B : Matrix n n ℂ} (x : n → ℂ) :
    rayleigh (A - B) x = rayleigh A x - rayleigh B x := by
  unfold rayleigh
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re]

omit [DecidableEq n] in
theorem rayleigh_add {A B : Matrix n n ℂ} (x : n → ℂ) :
    rayleigh (A + B) x = rayleigh A x + rayleigh B x := by
  unfold rayleigh
  rw [add_mulVec, dotProduct_add, Complex.add_re]

omit [DecidableEq n] in
theorem rayleigh_smul (c : ℝ) (A : Matrix n n ℂ) (x : n → ℂ) :
    rayleigh ((c : ℂ) • A) x = c * rayleigh A x := by
  unfold rayleigh
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem rayleigh_one (x : n → ℂ) : rayleigh 1 x = ∑ i, ‖x i‖ ^ 2 := by
  unfold rayleigh
  rw [one_mulVec, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re]

omit [DecidableEq n] in
/-- Loewner order in Rayleigh form. -/
theorem rayleigh_le_of_posSemidef {A B : Matrix n n ℂ} (h : (B - A).PosSemidef) (x : n → ℂ) :
    rayleigh A x ≤ rayleigh B x := by
  have := rayleigh_nonneg h x
  rw [rayleigh_sub] at this
  linarith

/-- The Loewner influence `Λ(B,C) = inf{λ ≥ 0 : C ⪯ λ B}` in Rayleigh form. -/
noncomputable def influence (B C : Matrix n n ℂ) : ℝ :=
  sInf {l : ℝ | 0 ≤ l ∧ ∀ x, rayleigh C x ≤ l * rayleigh B x}

end GeometricThresholdBank
end MathPhys
