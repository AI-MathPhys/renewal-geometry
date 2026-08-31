/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HermitianRankOneTraceNorm
import NCG.Grand.SourceInfluenceExtremizerAttainmentExact

/-!
# A rank-one head in a finite positive spectrum

This file extracts one selected eigenvector of a positive complex matrix as a
literal rank-one outer product.  Subtracting that spectral head leaves a
positive-semidefinite tail, whose trace is the original trace minus the
selected eigenvalue.  Choosing a largest eigenvalue supplies exactly the
head--tail decomposition used in robust Choi-purity estimates.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace NCG
namespace HermitianSpectralRankOneHead

open HermitianRankOneTraceNorm

variable {m : ℕ}

private theorem selected_projector
    {J : Matrix (Fin m) (Fin m) ℂ} (hJ : J.IsHermitian)
    (k : Fin m) (c : ℝ) :
    (hJ.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun i => if i = k then (c : ℂ) else 0) *
          (hJ.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ =
      ((c : ℝ) : ℂ) • pureOuter (hJ.eigenvectorBasis k) := by
  classical
  ext i j
  simp [Matrix.mul_apply, pureOuter, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- Subtracting one selected positive eigendirection leaves a positive tail. -/
theorem selected_eigen_head_tail
    {J : Matrix (Fin m) (Fin m) ℂ} (hJ : J.PosSemidef)
    (k : Fin m) :
    ∃ (x : EuclideanSpace ℂ (Fin m))
      (T : Matrix (Fin m) (Fin m) ℂ),
      J = pureOuter x + T ∧
      T.PosSemidef ∧
      ‖x‖ ^ 2 = hJ.1.eigenvalues k ∧
      T.trace.re = J.trace.re - hJ.1.eigenvalues k := by
  classical
  let hH : J.IsHermitian := hJ.1
  let lam : ℝ := hH.eigenvalues k
  let v : EuclideanSpace ℂ (Fin m) := hH.eigenvectorBasis k
  let x : EuclideanSpace ℂ (Fin m) := ((Real.sqrt lam : ℝ) : ℂ) • v
  let Dtail : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun i => if i = k then 0 else (hH.eigenvalues i : ℂ))
  let W : Matrix (Fin m) (Fin m) ℂ := hH.eigenvectorUnitary
  let T : Matrix (Fin m) (Fin m) ℂ := W * Dtail * Wᴴ
  have hlam : 0 ≤ lam := hJ.eigenvalues_nonneg k
  have hDtail : Dtail.PosSemidef := by
    change (Matrix.diagonal
      (fun i => if i = k then 0 else (hH.eigenvalues i : ℂ))).PosSemidef
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases hik : i = k
    · simp [hik]
    · simp only [hik, ↓reduceIte]
      exact (RCLike.ofReal_nonneg.mpr (hJ.eigenvalues_nonneg i))
  have hT : T.PosSemidef := by
    exact hDtail.mul_mul_conjTranspose_same W
  have hdiag :
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) =
        Matrix.diagonal (fun i => if i = k then (lam : ℂ) else 0) + Dtail := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k <;>
        simp [Dtail, lam, Matrix.diagonal_apply, hik]
    · simp [Dtail, Matrix.diagonal_apply_ne _ hij]
  have hhead :
      W * Matrix.diagonal (fun i => if i = k then (lam : ℂ) else 0) * Wᴴ =
        pureOuter x := by
    rw [selected_projector hH k lam]
    change ((lam : ℂ) • pureOuter v) =
      pureOuter (((Real.sqrt lam : ℝ) : ℂ) • v)
    rw [pureOuter_smul, RCLike.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hlam]
  have hsplit : J = pureOuter x + T := by
    rw [hH.spectral_theorem]
    change W * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * Wᴴ = _
    rw [hdiag, Matrix.mul_add, Matrix.add_mul, hhead]
  have hvnorm : ‖v‖ = 1 := hH.eigenvectorBasis.orthonormal.norm_eq_one k
  have hxnorm : ‖x‖ ^ 2 = lam := by
    change ‖(((Real.sqrt lam : ℝ) : ℂ) • v)‖ ^ 2 = lam
    rw [norm_smul, hvnorm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hlam]
  have hTtrace : T.trace.re = J.trace.re - lam := by
    have ht := congrArg Matrix.trace hsplit
    rw [Matrix.trace_add, pureOuter_trace, hxnorm] at ht
    have htre := congrArg Complex.re ht
    change J.trace.re = lam + T.trace.re at htre
    linarith
  refine ⟨x, T, hsplit, hT, ?_, ?_⟩
  · change ‖x‖ ^ 2 = lam
    exact hxnorm
  · change T.trace.re = J.trace.re - lam
    exact hTtrace

/-- A largest eigenvector gives a positive rank-one head and a positive tail,
and records the maximizing property alongside the exact tail trace. -/
theorem exists_max_eigen_head_tail
    {J : Matrix (Fin m) (Fin m) ℂ} [Nonempty (Fin m)]
    (hJ : J.PosSemidef) :
    ∃ (k : Fin m) (x : EuclideanSpace ℂ (Fin m))
      (T : Matrix (Fin m) (Fin m) ℂ),
      (∀ i, hJ.1.eigenvalues i ≤ hJ.1.eigenvalues k) ∧
      J = pureOuter x + T ∧
      T.PosSemidef ∧
      ‖x‖ ^ 2 = hJ.1.eigenvalues k ∧
      T.trace.re = J.trace.re - hJ.1.eigenvalues k := by
  obtain ⟨k, hk⟩ :=
    SourceInfluenceAttainment.exists_max_eigenindex hJ.1
  obtain ⟨x, T, hsplit, hT, hx, ht⟩ := selected_eigen_head_tail hJ k
  exact ⟨k, x, T, hk, hsplit, hT, hx, ht⟩

end HermitianSpectralRankOneHead
end NCG
