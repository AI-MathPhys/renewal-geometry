/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.RelEntropyInvarianceExact

/-!
# Ancilla and scaling transport of the finite quantum relative entropy

Step (D2) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the relative entropy transports exactly
through maximally mixed ancillas — the identity that strips the Weyl-twirl
output `E(X) = (1/d) 1 ⊗ Tr_env X` back to the partial trace.

* `matFun_smul_pos`: the spectral calculus composes with scalings,
  `f(cM) = (f ∘ c·)(M)`;
* `aeval_kron_one`, `matFun_kron_one`: `M ↦ 1 ⊗ M` is a unital algebra
  embedding, so `f(1 ⊗ M) = 1 ⊗ f(M)` — no junk constraint needed;
* `relEntropy_smul_kron_one`: for a state `A` and faithful `B`,
  `D(c(1 ⊗ A) ‖ c(1 ⊗ B)) = c·d·D(A‖B)`; at `c = 1/d` the maximally
  mixed ancilla is invisible.
-/

open Matrix Unitary Finset Polynomial Kronecker
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {M : Matrix n n ℂ}

/-! ### Scaling transport of the polynomial calculus -/

/-- Lagrange interpolation on any finite node set. -/
theorem exists_interpolating' (f : ℝ → ℝ) (s : Finset ℝ) :
    ∃ P : Polynomial ℝ, ∀ x ∈ s, P.eval x = f x :=
  ⟨Lagrange.interpolate s id f, fun x hx => by
    have h := Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hx
    simpa using h⟩

theorem aeval_smul_arg (c : ℝ) (M : Matrix n n ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval (c • M) P =
      Polynomial.aeval M (P.comp (Polynomial.C c * Polynomial.X)) := by
  rw [Polynomial.aeval_comp]
  congr 1
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.smul_def]

/-- `f(cM) = (f ∘ c·)(M)` through the spectral calculus. -/
theorem matFun_smul_pos (hM : M.IsHermitian) (c : ℝ)
    (hcM : (c • M).IsHermitian) (f : ℝ → ℝ) :
    matFun hcM f = matFun hM fun x => f (c * x) := by
  obtain ⟨P, hPval⟩ := exists_interpolating' f
    ((Finset.image hcM.eigenvalues Finset.univ) ∪
      Finset.image (fun i => c * hM.eigenvalues i) Finset.univ)
  have h1 : matFun hcM f = Polynomial.aeval (c • M) P :=
    matFun_eq_aeval hcM f P fun i => hPval _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have h2 : matFun hM (fun x => f (c * x)) =
      Polynomial.aeval M (P.comp (Polynomial.C c * Polynomial.X)) := by
    refine matFun_eq_aeval hM _ _ fun i => ?_
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact hPval _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [h1, h2, aeval_smul_arg]

/-! ### Kronecker-with-identity transport -/

omit [DecidableEq n] in
theorem kron_one_mul (A B : Matrix n n ℂ) :
    ((1 : Matrix κ κ ℂ) ⊗ₖ A) * (1 ⊗ₖ B) = 1 ⊗ₖ (A * B) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem kron_one_pow (A : Matrix n n ℂ) (k : ℕ) :
    ((1 : Matrix κ κ ℂ) ⊗ₖ A) ^ k = 1 ⊗ₖ (A ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.one_kronecker_one]
  | succ k ih => rw [pow_succ, pow_succ, ih, kron_one_mul]

omit [Fintype n] [DecidableEq n] [Fintype κ] in
theorem kron_one_smul (c : ℝ) (A : Matrix n n ℂ) :
    (1 : Matrix κ κ ℂ) ⊗ₖ (c • A) = c • (1 ⊗ₖ A) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kronecker_apply, Matrix.smul_apply]
  rw [mul_smul_comm]

omit [Fintype n] [DecidableEq n] [Fintype κ] in
theorem kron_one_sub (A B : Matrix n n ℂ) :
    (1 : Matrix κ κ ℂ) ⊗ₖ (A - B) = 1 ⊗ₖ A - 1 ⊗ₖ B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kronecker_apply, Matrix.sub_apply, mul_sub]

omit [Fintype n] [DecidableEq n] [Fintype κ] in
theorem kron_one_sum {ι : Type*} (s : Finset ι) (g : ι → Matrix n n ℂ) :
    (1 : Matrix κ κ ℂ) ⊗ₖ (∑ x ∈ s, g x) = ∑ x ∈ s, 1 ⊗ₖ g x := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

theorem aeval_kron_one (A : Matrix n n ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval ((1 : Matrix κ κ ℂ) ⊗ₖ A) P =
      1 ⊗ₖ Polynomial.aeval A P := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    kron_one_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kron_one_smul, kron_one_pow]

omit [Fintype n] [DecidableEq n] [Fintype κ] in
theorem kron_one_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ((1 : Matrix κ κ ℂ) ⊗ₖ A).IsHermitian := by
  unfold Matrix.IsHermitian
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    Matrix.kronecker_apply, star_mul']
  rw [← Matrix.conjTranspose_apply A, hA.eq]
  congr 1
  rw [← Matrix.conjTranspose_apply (1 : Matrix κ κ ℂ),
    Matrix.conjTranspose_one]

/-- `f(1 ⊗ M) = 1 ⊗ f(M)`: the maximally mixed ancilla passes through the
spectral calculus. -/
theorem matFun_kron_one {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hkron : ((1 : Matrix κ κ ℂ) ⊗ₖ A).IsHermitian) (f : ℝ → ℝ) :
    matFun hkron f = 1 ⊗ₖ matFun hA f := by
  obtain ⟨P, hPval⟩ := exists_interpolating' f
    ((Finset.image hkron.eigenvalues Finset.univ) ∪
      Finset.image hA.eigenvalues Finset.univ)
  have h1 : matFun hkron f = Polynomial.aeval (1 ⊗ₖ A) P :=
    matFun_eq_aeval hkron f P fun i => hPval _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have h2 : matFun hA f = Polynomial.aeval A P :=
    matFun_eq_aeval hA f P fun i => hPval _
      (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [h1, h2, aeval_kron_one]

/-! ### The scalar layer of the ancilla identity -/

theorem scaled_log_self (c p : ℝ) (hc : 0 < c) (hp : 0 ≤ p) :
    p * Real.log (c * p) = p * Real.log p + p * Real.log c := by
  rcases eq_or_lt_of_le hp with h0 | hp
  · rw [← h0]
    simp
  · rw [Real.log_mul hc.ne' hp.ne']
    ring

theorem scaled_log_cross (c p q : ℝ) (hc : 0 < c) (hq : 0 < q) :
    p * Real.log (c * q) = p * Real.log q + p * Real.log c := by
  rw [Real.log_mul hc.ne' hq.ne']
  ring

/-! ### The ancilla identity -/

set_option maxHeartbeats 800000 in -- large klein-sum bookkeeping
/-- **The maximally mixed ancilla is invisible**: for a state `A` and a
faithful `B`, `D(c(1 ⊗ A) ‖ c(1 ⊗ B)) = c·d·D(A‖B)`. -/
theorem relEntropy_smul_kron_one {A B : Matrix n n ℂ}
    (hAp : A.PosSemidef) (hBp : B.PosDef) {c : ℝ} (hc : 0 < c)
    (h1A : (c • ((1 : Matrix κ κ ℂ) ⊗ₖ A)).IsHermitian)
    (h1B : (c • ((1 : Matrix κ κ ℂ) ⊗ₖ B)).IsHermitian) :
    relEntropy h1A h1B =
      (c * Fintype.card κ) * relEntropy hAp.1 hBp.1 := by
  have hkA : ((1 : Matrix κ κ ℂ) ⊗ₖ A).IsHermitian :=
    kron_one_isHermitian hAp.1
  have hkB : ((1 : Matrix κ κ ℂ) ⊗ₖ B).IsHermitian :=
    kron_one_isHermitian hBp.1
  -- transport the logarithms
  have hlogA : matLog h1A =
      1 ⊗ₖ matFun hAp.1 fun x => Real.log (c * x) := by
    have h1 : matLog h1A = matFun hkA fun x => Real.log (c * x) :=
      matFun_smul_pos hkA c h1A Real.log
    rw [h1]
    exact matFun_kron_one hAp.1 hkA _
  have hlogB : matLog h1B =
      1 ⊗ₖ matFun hBp.1 fun x => Real.log (c * x) := by
    have h1 : matLog h1B = matFun hkB fun x => Real.log (c * x) :=
      matFun_smul_pos hkB c h1B Real.log
    rw [h1]
    exact matFun_kron_one hBp.1 hkB _
  -- collapse the trace
  unfold relEntropy
  rw [hlogA, hlogB, ← kron_one_sub, Matrix.smul_mul, kron_one_mul,
    Matrix.trace_smul, Matrix.trace_kronecker, Matrix.trace_one]
  have hre : (c • ((Fintype.card κ : ℂ) *
      (A * (matFun hAp.1 (fun x => Real.log (c * x)) -
        matFun hBp.1 fun x => Real.log (c * x))).trace)).re =
      c * (Fintype.card κ : ℝ) *
        ((A * (matFun hAp.1 (fun x => Real.log (c * x)) -
          matFun hBp.1 fun x => Real.log (c * x))).trace).re := by
    rw [Complex.real_smul, Complex.mul_re, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  -- the scalar layer
  have hself := trace_mul_matFun_self hAp.1 fun x => Real.log (c * x)
  have hcross := trace_mul_matFun_re hAp.1 hBp.1 fun x => Real.log (c * x)
  have hselflog := trace_mul_matFun_self hAp.1 Real.log
  have hcrosslog := trace_mul_matFun_re hAp.1 hBp.1 Real.log
  have hrow : ∀ i, ∑ j, Complex.normSq (overlap hAp.1 hBp.1 i j) = 1 :=
    sum_normSq_row (overlap_mul_star hAp.1 hBp.1)
  have hmain : ((A * (matFun hAp.1 (fun x => Real.log (c * x)) -
      matFun hBp.1 fun x => Real.log (c * x))).trace).re =
      relEntropy hAp.1 hBp.1 := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hself, hcross]
    unfold relEntropy matLog
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hselflog,
      hcrosslog]
    have hL : ∑ i, hAp.1.eigenvalues i *
        Real.log (c * hAp.1.eigenvalues i) =
        (∑ i, hAp.1.eigenvalues i * Real.log (hAp.1.eigenvalues i)) +
          (∑ i, hAp.1.eigenvalues i) * Real.log c := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact scaled_log_self c _ hc (hAp.eigenvalues_nonneg i)
    have hR : ∑ i, ∑ j, hAp.1.eigenvalues i *
        Real.log (c * hBp.1.eigenvalues j) *
        Complex.normSq (overlap hAp.1 hBp.1 i j) =
        (∑ i, ∑ j, hAp.1.eigenvalues i *
          Real.log (hBp.1.eigenvalues j) *
          Complex.normSq (overlap hAp.1 hBp.1 i j)) +
          (∑ i, hAp.1.eigenvalues i) * Real.log c := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsplit : ∀ j, hAp.1.eigenvalues i *
          Real.log (c * hBp.1.eigenvalues j) *
          Complex.normSq (overlap hAp.1 hBp.1 i j) =
          hAp.1.eigenvalues i * Real.log (hBp.1.eigenvalues j) *
            Complex.normSq (overlap hAp.1 hBp.1 i j) +
          hAp.1.eigenvalues i * Real.log c *
            Complex.normSq (overlap hAp.1 hBp.1 i j) := by
        intro j
        rw [scaled_log_cross c _ _ hc (hBp.eigenvalues_pos j)]
        ring
      simp only [hsplit]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrow i]
      ring
    rw [hL, hR]
    ring
  rw [hmain]
  rfl

end QRE
end NCG
