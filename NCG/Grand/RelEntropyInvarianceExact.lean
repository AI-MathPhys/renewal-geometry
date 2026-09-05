/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.QuantumRelativeEntropyExact

/-!
# Isometry invariance of the finite quantum relative entropy

Step (D1) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the spectral functional calculus is a
polynomial calculus, and it transports through isometry conjugations
compatibly with the junk value `log 0 = 0`.

* `matFun_eq_aeval`: on any interpolating polynomial the spectral calculus
  is polynomial evaluation;
* `aeval_isometry_conj`: for an isometry `W` (`W^* W = 1`) and a polynomial
  with `P(0) = 0`, `P(W x W^*) = W P(x) W^*`;
* `matLog_isometry`: `log(W ρ W^*) = W (log ρ) W^*` — the junk value
  `log 0 = 0` is exactly what makes the kernel block invisible;
* `relEntropy_isometry`, `relEntropy_unitary`: the relative entropy is
  invariant under isometry and unitary conjugation — the Stinespring
  dilation step of data processing.
-/

open Matrix Unitary Finset Polynomial

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {S : Matrix n n ℂ}

/-! ### Polynomial functional calculus -/

theorem aeval_unitary_conj (u : unitary (Matrix n n ℂ))
    (x : Matrix n n ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval ((u : Matrix n n ℂ) * x * star (u : Matrix n n ℂ)) P =
      (u : Matrix n n ℂ) * Polynomial.aeval x P *
        star (u : Matrix n n ℂ) := by
  have hpow : ∀ k : ℕ,
      ((u : Matrix n n ℂ) * x * star (u : Matrix n n ℂ)) ^ k =
        (u : Matrix n n ℂ) * x ^ k * star (u : Matrix n n ℂ) := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero, Matrix.mul_one, coe_mul_star]
    | succ k ih =>
        rw [pow_succ, pow_succ, ih]
        have hshape : (u : Matrix n n ℂ) * x ^ k *
            star (u : Matrix n n ℂ) *
            ((u : Matrix n n ℂ) * x * star (u : Matrix n n ℂ)) =
            (u : Matrix n n ℂ) *
              (x ^ k * (star (u : Matrix n n ℂ) * (u : Matrix n n ℂ)) * x) *
              star (u : Matrix n n ℂ) := by
          simp only [Matrix.mul_assoc]
        rw [hshape, star_mul_coe, Matrix.mul_one]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpow k, Matrix.mul_smul, Matrix.smul_mul]

theorem aeval_diagonal_entries (d : n → ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval (diagonal d) P =
      diagonal fun i => Polynomial.aeval (d i) P := by
  rw [Polynomial.aeval_eq_sum_range]
  have hentry : (fun i => Polynomial.aeval (d i) P) = fun i =>
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • d i ^ k :=
    funext fun i => Polynomial.aeval_eq_sum_range (d i)
  rw [hentry]
  ext i j
  rw [Matrix.sum_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.diagonal_apply_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
      Pi.pow_apply]
  · rw [Matrix.diagonal_apply_ne _ hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.smul_apply, Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ hij,
      smul_zero]

theorem aeval_ofReal_complex (x : ℝ) (P : Polynomial ℝ) :
    Polynomial.aeval (RCLike.ofReal (K := ℂ) x) P =
      RCLike.ofReal (K := ℂ) (P.eval x) :=
  Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) x P

/-- **The spectral calculus is polynomial**: on any polynomial interpolating
`f` at the eigenvalues, `matFun hS f = P(S)`. -/
theorem matFun_eq_aeval (hS : S.IsHermitian) (f : ℝ → ℝ) (P : Polynomial ℝ)
    (hP : ∀ i, P.eval (hS.eigenvalues i) = f (hS.eigenvalues i)) :
    matFun hS f = Polynomial.aeval S P := by
  have h0 := hS.spectral_theorem
  rw [conjStarAlgAut_apply] at h0
  have h1 : Polynomial.aeval S P =
      (hS.eigenvectorUnitary : Matrix n n ℂ) *
        Polynomial.aeval (diagonal (RCLike.ofReal ∘ hS.eigenvalues)) P *
        star (hS.eigenvectorUnitary : Matrix n n ℂ) := by
    conv_lhs => rw [h0]
    exact aeval_unitary_conj hS.eigenvectorUnitary _ P
  have harg : (fun i =>
      Polynomial.aeval ((RCLike.ofReal ∘ hS.eigenvalues) i) P) =
      RCLike.ofReal (K := ℂ) ∘ fun i => f (hS.eigenvalues i) := by
    funext i
    rw [Function.comp_apply, Function.comp_apply,
      aeval_ofReal_complex (hS.eigenvalues i) P, hP i]
  rw [h1, aeval_diagonal_entries, harg]
  unfold matFun
  rw [conjStarAlgAut_apply]

/-- **Isometry conjugation of the polynomial calculus**: for `W^* W = 1` and
`P(0) = 0`, `P(W x W^*) = W P(x) W^*`. -/
theorem aeval_isometry_conj {W : Matrix N n ℂ} (hW : Wᴴ * W = 1)
    (x : Matrix n n ℂ) (P : Polynomial ℝ) (h0 : P.coeff 0 = 0) :
    Polynomial.aeval (W * x * Wᴴ) P = W * Polynomial.aeval x P * Wᴴ := by
  have hpow : ∀ k : ℕ, k ≠ 0 →
      (W * x * Wᴴ) ^ k = W * x ^ k * Wᴴ := by
    intro k hk
    induction k with
    | zero => exact absurd rfl hk
    | succ k ih =>
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          rw [pow_one, pow_one]
        · rw [pow_succ, pow_succ, ih h.ne']
          have hshape : W * x ^ k * Wᴴ * (W * x * Wᴴ) =
              W * (x ^ k * (Wᴴ * W) * x) * Wᴴ := by
            simp only [Matrix.mul_assoc]
          rw [hshape, hW, Matrix.mul_one]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    rw [h0]
    simp
  · rw [hpow k h.ne', Matrix.mul_smul, Matrix.smul_mul]

/-! ### Interpolation of the junk-valued scalar function -/

/-- Lagrange interpolation of `f` with `f 0 = 0` on any finite node set,
with vanishing constant coefficient. -/
theorem exists_interpolating (f : ℝ → ℝ) (hf0 : f 0 = 0) (s : Finset ℝ) :
    ∃ P : Polynomial ℝ, P.coeff 0 = 0 ∧ ∀ x ∈ s, P.eval x = f x := by
  refine ⟨Lagrange.interpolate (insert (0 : ℝ) s) id f, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero]
    have h := Lagrange.eval_interpolate_at_node f
      (Set.injOn_id _) (Finset.mem_insert_self (0 : ℝ) s)
    simpa [hf0] using h
  · intro x hx
    have h := Lagrange.eval_interpolate_at_node f
      (Set.injOn_id _) (Finset.mem_insert_of_mem (b := (0 : ℝ)) hx)
    simpa using h

/-! ### The matrix logarithm through isometries -/

/-- **`log(W ρ W^*) = W (log ρ) W^*`** for an isometry `W`: the junk value
`log 0 = 0` makes the kernel block invisible. -/
theorem matLog_isometry {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    {W : Matrix N n ℂ} (hW : Wᴴ * W = 1)
    (hcon : (W * ρ * Wᴴ).IsHermitian) :
    matLog hcon = W * matLog hρ * Wᴴ := by
  obtain ⟨P, hP0, hPval⟩ := exists_interpolating Real.log Real.log_zero
    ((Finset.image hρ.eigenvalues Finset.univ) ∪
      Finset.image hcon.eigenvalues Finset.univ)
  have h1 : matLog hcon = Polynomial.aeval (W * ρ * Wᴴ) P :=
    matFun_eq_aeval hcon Real.log P fun i => hPval _
      (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have h2 : matLog hρ = Polynomial.aeval ρ P :=
    matFun_eq_aeval hρ Real.log P fun i => hPval _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [h1, h2, aeval_isometry_conj hW ρ P hP0]

/-! ### Isometry and unitary invariance of the relative entropy -/

/-- **Isometry invariance** of the finite quantum relative entropy: the
Stinespring dilation step of data processing. -/
theorem relEntropy_isometry {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    {W : Matrix N n ℂ} (hW : Wᴴ * W = 1)
    (hρ' : (W * ρ * Wᴴ).IsHermitian) (hσ' : (W * σ * Wᴴ).IsHermitian) :
    relEntropy hρ' hσ' = relEntropy hρ hσ := by
  unfold relEntropy
  rw [matLog_isometry hρ hW hρ', matLog_isometry hσ hW hσ']
  have hdiff : W * matLog hρ * Wᴴ - W * matLog hσ * Wᴴ =
      W * (matLog hρ - matLog hσ) * Wᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiff]
  have hshape : W * ρ * Wᴴ * (W * (matLog hρ - matLog hσ) * Wᴴ) =
      W * (ρ * (Wᴴ * W) * (matLog hρ - matLog hσ)) * Wᴴ := by
    simp only [Matrix.mul_assoc]
  rw [hshape, hW, Matrix.mul_one, Matrix.trace_mul_cycle, hW,
    Matrix.one_mul]

/-- **Unitary invariance** of the finite quantum relative entropy. -/
theorem relEntropy_unitary {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (u : unitary (Matrix n n ℂ))
    (hρ' : ((u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ)ᴴ).IsHermitian)
    (hσ' : ((u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ)ᴴ).IsHermitian) :
    relEntropy hρ' hσ' = relEntropy hρ hσ := by
  have hW : ((u : Matrix n n ℂ))ᴴ * (u : Matrix n n ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact star_mul_coe u
  exact relEntropy_isometry hρ hσ hW hρ' hσ'

end QRE
end NCG
