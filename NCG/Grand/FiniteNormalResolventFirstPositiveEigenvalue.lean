/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactPositiveCircleRieszGap
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# First positive eigenvalue from a finite normal resolvent

For a positive finite-dimensional normal operator, compressing a positive shifted inverse away
from the kernel recovers the least positive eigenvalue.  This version is coordinate-free and is
therefore suitable for transporting cutoff operators through varying Hilbert spaces.
-/

open scoped InnerProduct

noncomputable section

namespace NCG.SpectralGap

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

/-- The inverse-norm gap of a finite shifted normal resolvent is an attained least positive
eigenvalue of the unshifted operator. -/
theorem inverseNormGap_is_leastPositiveEigenvalue_of_normalResolvent
    (A T P : E →L[ℂ] E) (b : ℝ) (hb : 0 < b)
    (hApositive : A.IsPositive) (hTpositive : T.IsPositive)
    (hP : IsStarProjection P) (hrange : LinearMap.range P.toLinearMap =
      LinearMap.ker A.toLinearMap)
    (hcommute : Commute T P)
    (hresolve : ∀ x, A (T x) + (b : ℂ) • T x = x)
    (hresolveEigen : ∀ (ν : ℝ), 0 ≤ ν → ∀ (x : E), A x = (ν : ℂ) • x →
      T x = (((b + ν : ℝ) : ℂ)⁻¹) • x)
    (hne : complementCompression T P ≠ 0) :
    let μ := ‖complementCompression T P‖⁻¹ - b
    0 < μ ∧ Module.End.HasEigenvalue A.toLinearMap (μ : ℂ) ∧
      ∀ ν : ℝ, 0 < ν → Module.End.HasEigenvalue A.toLinearMap (ν : ℂ) → μ ≤ ν := by
  let C : E →L[ℂ] E := complementCompression T P
  let t : ℝ := ‖C‖
  letI : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  have hCcompact : IsCompactOperator C :=
    complementCompression_isCompact T P (isCompactOperator_of_locallyCompactSpace_dom T)
  have hCpositive : C.IsPositive := complementCompression_isPositive T P hTpositive hP
  have ht : 0 < t := by
    exact norm_pos_iff.mpr (by simpa [C] using hne)
  letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp (by
    intro hE
    letI : Subsingleton E := hE
    exact hne (Subsingleton.elim _ _))
  letI : Algebra ℝ (E →L[ℂ] E) := NormedAlgebra.complexToReal.toAlgebra
  have hspecReal : t ∈ spectrum ℝ C := by
    exact CStarAlgebra.norm_mem_spectrum_of_nonneg (a := C)
      (ha := (ContinuousLinearMap.nonneg_iff_isPositive C).mpr hCpositive)
  have hspec : ((t : ℝ) : ℂ) ∈ spectrum ℂ C := by
    simpa [t] using spectrum.algebraMap_mem ℂ hspecReal
  have htComplex : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have heigenC : Module.End.HasEigenvalue C.toLinearMap ((t : ℝ) : ℂ) :=
    (hCcompact.hasEigenvalue_iff_mem_spectrum htComplex).mpr hspec
  obtain ⟨x, hx⟩ := heigenC.exists_hasEigenvector
  have hPC : P * C = 0 := by
    calc
      P * C = (P * (1 - P)) * T * (1 - P) := by
        simp only [C, complementCompression, mul_assoc]
      _ = 0 := by rw [hP.mul_one_sub_self]; simp
  have hPx : P x = 0 := by
    have hzero : P (C x) = 0 := by
      change (P * C) x = 0
      rw [hPC]
      rfl
    have hscalar : ((t : ℝ) : ℂ) • P x = 0 := by
      rw [← map_smul, ← hx.apply_eq_smul]
      exact hzero
    exact (smul_eq_zero.mp hscalar).resolve_left htComplex
  have hPTx : P (T x) = 0 := by
    calc
      P (T x) = T (P x) := congrArg (fun S : E →L[ℂ] E ↦ S x) hcommute.eq.symm
      _ = 0 := by rw [hPx]; exact map_zero T
  have hTx : T x = (t : ℂ) • x := by
    calc
      T x = C x := by simp [C, complementCompression, hPx, hPTx]
      _ = (t : ℂ) • x := hx.apply_eq_smul
  let μ : ℝ := t⁻¹ - b
  have hAx : A x = (μ : ℂ) • x := by
    have heq := hresolve x
    rw [hTx, map_smul] at heq
    have hmul : (t : ℂ) • A x = (t : ℂ) • ((μ : ℂ) • x) := by
      calc
        (t : ℂ) • A x = x - (b : ℂ) • ((t : ℂ) • x) := eq_sub_of_add_eq heq
        _ = (t : ℂ) • ((μ : ℂ) • x) := by
          rw [show (μ : ℂ) = (t : ℂ)⁻¹ - (b : ℂ) by simp [μ]]
          simp only [smul_smul]
          have hs : (1 : ℂ) - (b : ℂ) * (t : ℂ) =
              (t : ℂ) * ((t : ℂ)⁻¹ - (b : ℂ)) := by
            rw [mul_sub, mul_inv_cancel₀ htComplex]
            ring
          simpa [sub_smul, smul_smul] using congrArg (fun z : ℂ ↦ z • x) hs
    exact smul_right_injective E htComplex hmul
  have heigenA : Module.End.HasEigenvalue A.toLinearMap (μ : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hAx, hx.2⟩
  have hμne : μ ≠ 0 := by
    intro hμ
    have hxker : x ∈ LinearMap.ker A.toLinearMap := by
      rw [LinearMap.mem_ker]
      simpa [hμ] using hAx
    have hxrange : x ∈ LinearMap.range P.toLinearMap := hrange.symm ▸ hxker
    obtain ⟨y, hy⟩ := hxrange
    have hfix : P x = x := by
      have hid := congrArg (fun Q : E →L[ℂ] E ↦ Q y) hP.isIdempotentElem.eq
      change P (P y) = P y at hid
      rw [← hy]
      exact hid
    exact hx.2 (hfix ▸ hPx)
  have hμnonneg : 0 ≤ μ :=
    eigenvalue_nonneg_of_nonneg heigenA hApositive.re_inner_nonneg_right
  have hμ : 0 < μ := lt_of_le_of_ne hμnonneg (Ne.symm hμne)
  refine ⟨?_, heigenA, ?_⟩
  · simpa [μ, t, C] using hμ
  · intro ν hν hνeig
    obtain ⟨y, hy⟩ := hνeig.exists_hasEigenvector
    have hPyKer : P y ∈ LinearMap.ker A.toLinearMap := by
      rw [← hrange]
      exact ⟨y, rfl⟩
    have hAPy : A (P y) = 0 := LinearMap.mem_ker.mp hPyKer
    have horth : inner ℂ y (P y) = 0 := by
      have hs := hApositive.isSymmetric y (P y)
      have hAy : A y = (ν : ℂ) • y := hy.apply_eq_smul
      change inner ℂ (A y) (P y) = inner ℂ y (A (P y)) at hs
      rw [hAy, hAPy, inner_zero_right, inner_smul_left] at hs
      have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
      exact (mul_eq_zero.mp hs).resolve_left (by simpa using hνc)
    have hPy : P y = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      calc
        inner ℂ (P y) (P y) = inner ℂ y (P (P y)) :=
          hP.isSelfAdjoint.isSymmetric y (P y)
        _ = inner ℂ y (P y) := by
          have hid := congrArg (fun Q : E →L[ℂ] E ↦ Q y) hP.isIdempotentElem.eq
          change P (P y) = P y at hid
          rw [hid]
        _ = 0 := horth
    have hPTy : P (T y) = 0 := by
      calc
        P (T y) = T (P y) := congrArg (fun S : E →L[ℂ] E ↦ S y) hcommute.eq.symm
        _ = 0 := by rw [hPy]; exact map_zero T
    have hTy := hresolveEigen ν hν.le y hy.apply_eq_smul
    have hCy : C y = (((b + ν : ℝ) : ℂ)⁻¹) • y := by
      simp [C, complementCompression, hPy, hTy]
    have hbound := C.le_opNorm y
    rw [hCy, norm_smul] at hbound
    have hbν : 0 < b + ν := add_pos hb hν
    have hscalarNorm : ‖(((b + ν : ℝ) : ℂ)⁻¹)‖ = (b + ν)⁻¹ := by
      calc
        _ = ‖((b + ν : ℝ) : ℂ)‖⁻¹ := norm_inv _
        _ = |b + ν|⁻¹ := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ = (b + ν)⁻¹ := by rw [abs_of_pos hbν]
    rw [hscalarNorm] at hbound
    have hyNorm : 0 < ‖y‖ := norm_pos_iff.mpr hy.2
    have hscalar : (b + ν)⁻¹ ≤ t := by
      change (b + ν)⁻¹ * ‖y‖ ≤ t * ‖y‖ at hbound
      nlinarith
    have hinv : t⁻¹ ≤ b + ν := (inv_le_comm₀ hbν ht).mp hscalar
    change t⁻¹ - b ≤ ν
    linarith

end NCG.SpectralGap
