/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The derivative of the determinant and Liouville's formula
  (missing Mathlib machinery; `prop:invariant-response`, GR_emergence)

Mathlib has no derivative formula for `Matrix.det` along a
one-parameter family.  This file builds it from the Leibniz
expansion and the finite-product derivative:

* `det_updateCol_expand` — the cofactor expansion
  `det(A.updateCol i c) = Σ_k adj(A) i k · c k` (Cramer);
* `hasDerivAt_det` — for an entrywise differentiable family `U` with
  derivative matrix `V`,
  `(det U)' = tr(adj(U) · V)` — the Jacobi derivative formula;
* `liouville_formula` — for a solution family `U' = B·U`,
  `(det U)' = det(U) · tr(B)` — Liouville's formula: the Wronskian
  satisfies the scalar equation with the trace of the generator.

This is the mechanism behind `log|det U_γ| = -∫_γ Re Tr 𝒜` in
`prop:invariant-response`: the modulus of the path-ordered
determinant sees only the real trace of the transport generator.
-/

namespace NCG

open Matrix

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- Cofactor expansion of a column replacement (Cramer's rule in
adjugate form). -/
theorem det_updateCol_expand (A : Matrix (Fin n) (Fin n) 𝕜)
    (i : Fin n) (c : Fin n → 𝕜) :
    (A.updateCol i c).det = ∑ k, adjugate A i k * c k := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- The Jacobi derivative formula: along an entrywise differentiable
matrix family, `(det U)' = tr(adj(U)·V)` where `V` is the entrywise
derivative. -/
theorem hasDerivAt_det {U : ℝ → Matrix (Fin n) (Fin n) 𝕜}
    {V : Matrix (Fin n) (Fin n) 𝕜} {t : ℝ}
    (hU : ∀ i j, HasDerivAt (fun s => U s i j) (V i j) t) :
    HasDerivAt (fun s => (U s).det)
      (Matrix.trace (adjugate (U t) * V)) t := by
  classical
  -- Leibniz form of the determinant
  have hfun : (fun s => (U s).det)
      = fun s => ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ∏ i, U s (σ i) i := by
    funext s
    rw [Matrix.det_apply']
  rw [hfun]
  -- derivative of each permutation product
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      HasDerivAt (fun s => ∏ i, U s (σ i) i)
        (∑ i, (∏ j ∈ Finset.univ.erase i, U t (σ j) j) • V (σ i) i)
        t := by
    intro σ
    exact HasDerivAt.fun_finsetProd (fun i _ => hU (σ i) i)
  have hsum : HasDerivAt (fun s => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ∏ i, U s (σ i) i)
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : 𝕜) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, U t (σ j) j) • V (σ i) i)
      t := by
    apply HasDerivAt.fun_sum
    intro σ _
    exact ((hprod σ).const_mul _)
  -- identify the derivative with the trace of adj(U)·V
  have hval : (∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : 𝕜) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, U t (σ j) j) • V (σ i) i)
      = Matrix.trace (adjugate (U t) * V) := by
    have hswap : (∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) *
          ∑ i, (∏ j ∈ Finset.univ.erase i, U t (σ j) j) • V (σ i) i)
        = ∑ i, ∑ σ : Equiv.Perm (Fin n),
            ((Equiv.Perm.sign σ : ℤ) : 𝕜) *
              ((∏ j ∈ Finset.univ.erase i, U t (σ j) j) * V (σ i) i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_eq_mul]
    have hdet_i : ∀ i, (∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) *
          ((∏ j ∈ Finset.univ.erase i, U t (σ j) j) * V (σ i) i))
        = ((U t).updateCol i (fun k => V k i)).det := by
      intro i
      rw [Matrix.det_apply']
      apply Finset.sum_congr rfl
      intro σ _
      have hp : (∏ j, ((U t).updateCol i (fun k => V k i)) (σ j) j)
          = V (σ i) i * ∏ j ∈ Finset.univ.erase i, U t (σ j) j := by
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => ((U t).updateCol i (fun k => V k i)) (σ j) j)
          (Finset.mem_univ i)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro j hj
          simp [(Finset.mem_erase.mp hj).1]
      rw [hp]
      ring
    rw [hswap]
    calc ∑ i, ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : 𝕜) *
          ((∏ j ∈ Finset.univ.erase i, U t (σ j) j) * V (σ i) i)
        = ∑ i, ((U t).updateCol i (fun k => V k i)).det :=
          Finset.sum_congr rfl fun i _ => hdet_i i
    _ = ∑ i, ∑ k, adjugate (U t) i k * V k i :=
          Finset.sum_congr rfl fun i _ =>
            det_updateCol_expand (U t) i (fun k => V k i)
    _ = Matrix.trace (adjugate (U t) * V) := by
          simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [← hval]
  exact hsum

/-- Liouville's formula: for a solution family `U' = B·U`, the
determinant satisfies `(det U)' = det(U)·tr(B)`. -/
theorem liouville_formula {U : ℝ → Matrix (Fin n) (Fin n) 𝕜}
    {B : Matrix (Fin n) (Fin n) 𝕜} {t : ℝ}
    (hU : ∀ i j, HasDerivAt (fun s => U s i j) ((B * U t) i j) t) :
    HasDerivAt (fun s => (U s).det)
      ((U t).det * Matrix.trace B) t := by
  have h := hasDerivAt_det hU
  have hval : Matrix.trace (adjugate (U t) * (B * U t))
      = (U t).det * Matrix.trace B := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate,
      Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  rw [hval] at h
  exact h

/-- The Jacobi log-modulus formula: along a transport family
`U' = B·U` with nonvanishing determinant, the log-modulus of the
determinant sees exactly the real trace of the generator:
`(log ‖det U‖)' = Re tr B`. -/
theorem jacobi_log_modulus {U : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (hU : ∀ i j, HasDerivAt (fun s => U s i j) ((B * U t) i j) t)
    (hdet : (U t).det ≠ 0) :
    HasDerivAt (fun s => Real.log ‖(U s).det‖)
      (Matrix.trace B).re t := by
  have hz := liouville_formula hU
  set z : ℝ → ℂ := fun s => (U s).det with hzdef
  set w : ℂ := (U t).det * Matrix.trace B with hw
  -- real and imaginary parts of the determinant path
  have hre : HasDerivAt (fun s => (z s).re) w.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have him : HasDerivAt (fun s => (z s).im) w.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  -- the squared modulus and its derivative
  have hnsq : HasDerivAt (fun s => Complex.normSq (z s))
      (2 * ((z t).re * w.re + (z t).im * w.im)) t := by
    have h := (hre.fun_mul hre).fun_add (him.fun_mul him)
    have hfun : (fun s => (z s).re * (z s).re + (z s).im * (z s).im)
        = fun s => Complex.normSq (z s) := by
      funext s
      rw [Complex.normSq_apply]
    rw [hfun] at h
    exact h.congr_deriv (by ring)
  have hnsq_ne : Complex.normSq (z t) ≠ 0 := by
    simp only [hzdef, ne_eq, Complex.normSq_eq_zero]
    exact hdet
  -- log of the squared modulus
  have hlog := (Real.hasDerivAt_log hnsq_ne).comp t hnsq
  -- identify log ‖z‖ with half the log of normSq
  have hfun2 : (fun s => Real.log ‖z s‖)
      = fun s => 1 / 2 * (Real.log ∘ fun u => Complex.normSq (z u)) s := by
    funext s
    simp only [Function.comp_apply]
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast
    ring
  rw [show (fun s => Real.log ‖(U s).det‖)
    = fun s => Real.log ‖z s‖ from rfl, hfun2]
  have hfinal := hlog.const_mul (1 / 2 : ℝ)
  have hval : 1 / 2 * ((Complex.normSq (z t))⁻¹
      * (2 * ((z t).re * w.re + (z t).im * w.im)))
      = (Matrix.trace B).re := by
    have hexp : (z t).re * w.re + (z t).im * w.im
        = Complex.normSq (z t) * (Matrix.trace B).re := by
      rw [hw]
      have hzt : z t = (U t).det := rfl
      rw [hzt, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
      ring
    rw [hexp]
    field_simp
  rw [hval] at hfinal
  exact hfinal

/-- Unitary geometric holonomy preserves the Hilbert–Schmidt norm:
`tr((UMW)ᴴ(UMW)) = tr(MᴴM)` for `UᴴU = 1` and `WWᴴ = 1` — the
Hilbert–Schmidt modulus response is blind to the anti-Hermitian
Berry transport. -/
theorem hs_unitary_invariance {U M W : Matrix (Fin n) (Fin n) ℂ}
    (hUu : U.conjTranspose * U = 1)
    (hWu : W * W.conjTranspose = 1) :
    Matrix.trace ((U * M * W).conjTranspose * (U * M * W))
      = Matrix.trace (M.conjTranspose * M) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : W.conjTranspose * (M.conjTranspose * U.conjTranspose) *
      (U * M * W)
      = W.conjTranspose * (M.conjTranspose * M) * W := by
    rw [show W.conjTranspose * (M.conjTranspose * U.conjTranspose) *
        (U * M * W)
      = W.conjTranspose * M.conjTranspose *
          (U.conjTranspose * U) * M * W from by
        noncomm_ring, hUu]
    noncomm_ring
  rw [h1, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hWu,
    Matrix.one_mul]

end NCG
