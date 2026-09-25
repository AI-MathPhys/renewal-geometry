/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Record-complete nonidentifiability witness: the shared normalization identities

Partial coverage of `prop:record-witness` of the spacetime–gauge duality paper: the
identities that both realizations of `eq:two-system-completions`,

`K_e^b = I/√18 + (i/3) H_e^b`   (`completion`),

share as soon as the `H_e^b` are Hermitian involutions with zero trace and zero sum:

* `completion_conjTranspose_mul_self`: `(K_e^b)^* K_e^b = I/6` (`eq:matching-record-data`,
  first identity), so `√6 K_e^b` is unitary;
* `sum_completion`: `∑_e K_e^b = √2 I` (the coherent-sum constraint of
  `eq:six-edge-normalization`), and `sum_conjTranspose_mul_completion`:
  `∑_e (K_e^b)^* K_e^b = I` (its completeness constraint);
* `trace_conjTranspose_mul_completion`: `Tr[(K_e^b)^* K_f^b] = d/18 + (1/9) Tr(H_e^b H_f^b)`
  on a `d`-dimensional space; with `d = 20` and the Gram values `Tr(H_e H_f) = 20`
  (`e = f`) resp. `−4` (`e ≠ f`, pair correlation `−1/5`) this is
  `eq:matching-record-data`, second identity (`trace_conjTranspose_mul_completion_gram`).

**Not formalised here** (the substance of the proposition): the two explicit families
(commuting sign involutions on `ℂ^{20}` indexed by three-subsets of `Fin 6`, and the
Clifford family `√(6/5) ∑_μ O_{eμ} Γ_μ ⊗ I_5` on `ℂ⁴ ⊗ ℂ⁵`), their Gram relations,
linear independence, the generated algebras `ℂ^{20}` vs `M_4(ℂ) ⊗ I_5`
(`eq:inequivalent-system-algebras`), the word effects `eq:record-word-effect`, and the
Choi spectrum `eq:matching-Choi-spectrum`.
-/

open Matrix

namespace RenewalGeometry
namespace RecordWitness

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `eq:two-system-completions`: `K = I/√18 + (i/3) H`. -/
noncomputable def completion (Hm : Matrix m m ℂ) : Matrix m m ℂ :=
  ((1 / Real.sqrt 18 : ℝ) : ℂ) • (1 : Matrix m m ℂ) + (Complex.I / 3) • Hm

theorem sqrt18_sq : ((1 / Real.sqrt 18 : ℝ) : ℂ) * ((1 / Real.sqrt 18 : ℝ) : ℂ) = 1 / 18 := by
  rw [← Complex.ofReal_mul, ← sq, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  push_cast
  ring

theorem sqrt18_sq' : ((1 / Real.sqrt 18 : ℝ) : ℂ) ^ 2 = 1 / 18 := by
  rw [sq, sqrt18_sq]

theorem six_inv_sqrt18 : (6 : ℂ) * ((1 / Real.sqrt 18 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [show (18 : ℝ) = 3 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have h3 : 6 * (1 / Real.sqrt 18 : ℝ) = Real.sqrt 2 := by
    rw [h]
    field_simp
    nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact_mod_cast h3

/-- The adjoint of a completion of a Hermitian `H`: `K^* = I/√18 − (i/3) H`. -/
theorem completion_conjTranspose (Hm : Matrix m m ℂ) (hH : Hmᴴ = Hm) :
    (completion Hm)ᴴ = ((1 / Real.sqrt 18 : ℝ) : ℂ) • (1 : Matrix m m ℂ) - (Complex.I / 3) • Hm := by
  unfold completion
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hH]
  simp only [Complex.star_def, Complex.conj_ofReal, map_div₀, Complex.conj_I, map_ofNat]
  rw [neg_div, neg_smul, sub_eq_add_neg]

/-- **`eq:matching-record-data`, first identity**: for a Hermitian involution `H`,
`K^* K = I/6` where `K = I/√18 + (i/3) H`. -/
theorem completion_conjTranspose_mul_self (Hm : Matrix m m ℂ) (hH : Hmᴴ = Hm)
    (hinv : Hm * Hm = 1) :
    (completion Hm)ᴴ * completion Hm = (1 / 6 : ℂ) • (1 : Matrix m m ℂ) := by
  rw [completion_conjTranspose Hm hH]
  unfold completion
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub, smul_add, smul_smul, hinv, sqrt18_sq]
  have hI : Complex.I / 3 * (Complex.I / 3) = -1 / 9 := by
    rw [div_mul_div_comm, Complex.I_mul_I]; norm_num
  rw [hI]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `√6 K` is unitary: `(√6 K)^* (√6 K) = I`. -/
theorem sqrt_six_completion_unitary (Hm : Matrix m m ℂ) (hH : Hmᴴ = Hm) (hinv : Hm * Hm = 1) :
    (((Real.sqrt 6 : ℝ) : ℂ) • completion Hm)ᴴ * (((Real.sqrt 6 : ℝ) : ℂ) • completion Hm) =
      1 := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    completion_conjTranspose_mul_self Hm hH hinv, smul_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  norm_num

/-- The coherent-sum constraint: `∑_e K_e = √2 I` when `∑_e H_e = 0`. -/
theorem sum_completion (Hm : Fin 6 → Matrix m m ℂ) (hsum : ∑ e, Hm e = 0) :
    ∑ e, completion (Hm e) = ((Real.sqrt 2 : ℝ) : ℂ) • (1 : Matrix m m ℂ) := by
  unfold completion
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hsum, smul_zero, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ 6,
    smul_smul]
  congr 1
  rw [mul_comm]
  exact_mod_cast six_inv_sqrt18

/-- The completeness constraint: `∑_e K_e^* K_e = I` for six Hermitian involutions. -/
theorem sum_conjTranspose_mul_completion (Hm : Fin 6 → Matrix m m ℂ) (hH : ∀ e, (Hm e)ᴴ = Hm e)
    (hinv : ∀ e, Hm e * Hm e = 1) :
    ∑ e, (completion (Hm e))ᴴ * completion (Hm e) = 1 := by
  simp_rw [fun e => completion_conjTranspose_mul_self (Hm e) (hH e) (hinv e)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ 6,
    smul_smul]
  norm_num

/-- **`eq:matching-record-data`, second identity (generic form)**: for Hermitian
traceless `H_e`, `H_f` on a `d`-dimensional space,
`Tr[K_e^* K_f] = d/18 + (1/9) Tr(H_e H_f)`. -/
theorem trace_conjTranspose_mul_completion (He Hf : Matrix m m ℂ) (hHe : Heᴴ = He)
    (htrE : He.trace = 0) (htrF : Hf.trace = 0) :
    ((completion He)ᴴ * completion Hf).trace =
      (Fintype.card m : ℂ) / 18 + (1 / 9 : ℂ) * (He * Hf).trace := by
  rw [completion_conjTranspose He hHe]
  unfold completion
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, htrE, htrF, smul_zero, sub_zero, add_zero, sqrt18_sq, smul_eq_mul]
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(1 / 9 : ℂ) * (He * Hf).trace) * this +
    (Fintype.card m : ℂ) * sqrt18_sq'

/-- **`eq:matching-record-data`, second identity**: on `ℂ^{20}` with the Gram values
`Tr(H_e H_f) = 20` for `e = f` and `−4` for `e ≠ f` (pair correlation `−1/5`),
`Tr[K_e^* K_f] = 10/3` for `e = f` and `2/3` for `e ≠ f`. -/
theorem trace_conjTranspose_mul_completion_gram (hcard : Fintype.card m = 20)
    (Hm : Fin 6 → Matrix m m ℂ) (hH : ∀ e, (Hm e)ᴴ = Hm e) (htr : ∀ e, (Hm e).trace = 0)
    (hgram : ∀ e f, (Hm e * Hm f).trace = if e = f then 20 else -4) (e f : Fin 6) :
    ((completion (Hm e))ᴴ * completion (Hm f)).trace = if e = f then 10 / 3 else 2 / 3 := by
  rw [trace_conjTranspose_mul_completion _ _ (hH e) (htr e) (htr f), hgram, hcard]
  split_ifs <;> norm_num

end RecordWitness
end RenewalGeometry
