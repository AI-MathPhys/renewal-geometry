/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.CompactPositiveCircleRieszGap

/-!
# Complement coercivity from a compressed resolvent, and attained complement eigenvectors

Two general facts used by the compact spectral upgrade of the spacetime–gauge duality
manuscript (`cor:cofinal-spectral-upgrade`, `prop:protected-kernel-locking`).

* `norm_apply_sq_le_norm_mul_re_inner_of_isPositive`: for a positive operator `T`,
  `‖T y‖² ≤ ‖T‖ · Re ⟨T y, y⟩` (the operator inequality `T² ≤ ‖T‖ T`).
* `complementCompression_coercivity`: if `R` is a positive left inverse of `L + b`, and a star
  projection `P` commutes with `L` and `R`, then the inverse-norm gap of the complement
  compression `(1 - P) R (1 - P)` is a **coercivity constant**:
  `(‖(1 - P) R (1 - P)‖⁻¹ - b) ‖x - P x‖² ≤ Re ⟨L x, x⟩` for every `x`.
  This is the spectral-theorem estimate `q(A) ≥ λ₊ ‖(I − P_{Ker})A‖²`, proved without
  diagonalisation.
* `exists_eigenvector_norm_complementCompression`: for a compact positive `T` and a star
  projection `Q` commuting with `T`, a nonzero complement compression attains its norm on an
  eigenvector of `T` annihilated by `Q`.
-/

open Complex

noncomputable section

namespace RenewalGeometry.SpectralGap

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For a positive operator, `‖T y‖² ≤ ‖T‖ · Re ⟨T y, y⟩`. -/
theorem norm_apply_sq_le_norm_mul_re_inner_of_isPositive
    (T : E →L[ℂ] E) (hT : T.IsPositive) (y : E) :
    ‖T y‖ ^ 2 ≤ ‖T‖ * (inner ℂ (T y) y).re := by
  set n := ‖T y‖ with hn
  set a := (inner ℂ (T y) y).re with ha
  set c := (inner ℂ (T (T y)) (T y)).re with hc
  have hcle : c ≤ ‖T‖ * n ^ 2 := by
    calc c ≤ ‖inner ℂ (T (T y)) (T y)‖ := Complex.re_le_norm _
      _ ≤ ‖T (T y)‖ * ‖T y‖ := norm_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖T y‖ * ‖T y‖ := by gcongr; exact T.le_opNorm _
      _ = ‖T‖ * n ^ 2 := by rw [hn]; ring
  have hsymm : inner ℂ (T (T y)) y = inner ℂ (T y) (T y) := hT.isSymmetric (T y) y
  have hnn : (inner ℂ (T y) (T y)).re = n ^ 2 := by
    rw [hn, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  have key : ∀ s : ℝ, 0 ≤ a - 2 * s * n ^ 2 + s ^ 2 * c := by
    intro s
    have h := hT.re_inner_nonneg_left (y - (s : ℂ) • T y)
    have hexp : inner ℂ (T (y - (s : ℂ) • T y)) (y - (s : ℂ) • T y) =
        inner ℂ (T y) y - (s : ℂ) * inner ℂ (T y) (T y) - (s : ℂ) * inner ℂ (T y) (T y) +
          (s : ℂ) * (s : ℂ) * inner ℂ (T (T y)) (T y) := by
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
        inner_smul_right, Complex.conj_ofReal, hsymm]
      ring
    change 0 ≤ (inner ℂ (T (y - (s : ℂ) • T y)) (y - (s : ℂ) • T y)).re at h
    rw [hexp] at h
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero] at h
    rw [hnn, ← ha, ← hc] at h
    nlinarith [h]
  by_cases hT0 : ‖T‖ = 0
  · have hTy : T y = 0 := by
      have := T.le_opNorm y
      rw [hT0, zero_mul] at this
      exact norm_le_zero_iff.mp this
    have hn0 : n = 0 := by rw [hn, hTy, norm_zero]
    rw [hn0, hT0]
    simp
  have hTpos : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hT0)
  have h1 := key (1 / ‖T‖)
  have h2 : (1 / ‖T‖) ^ 2 * c ≤ (1 / ‖T‖) ^ 2 * (‖T‖ * n ^ 2) :=
    mul_le_mul_of_nonneg_left hcle (sq_nonneg _)
  have h3 : (1 / ‖T‖) ^ 2 * (‖T‖ * n ^ 2) = n ^ 2 / ‖T‖ := by
    field_simp
  have h4 : 2 * (1 / ‖T‖) * n ^ 2 = 2 * (n ^ 2 / ‖T‖) := by ring
  have h5 : n ^ 2 / ‖T‖ ≤ a := by linarith
  rw [div_le_iff₀ hTpos] at h5
  linarith

/-- **Coercivity from the compressed resolvent.**  Let `R` be a positive operator with
`R (L x + b x) = x`, and let a star projection `P` commute with `L` and with `R`.  Then for
every `x`,
`(‖(1 - P) R (1 - P)‖⁻¹ - b) ‖x - P x‖² ≤ Re ⟨L x, x⟩`,
provided `L` is positive.  With `P` the kernel projection of `L` the constant is the least
positive eigenvalue, so this is the spectral-theorem estimate `q(A) ≥ λ₊ ‖(I − P)A‖²`. -/
theorem complementCompression_coercivity [CompleteSpace E]
    (Lop R P : E →L[ℂ] E) (b : ℝ)
    (hL : Lop.IsPositive) (hR : R.IsPositive) (hP : IsStarProjection P)
    (hLP : Commute Lop P) (hRP : Commute R P)
    (hRL : ∀ x, R (Lop x + (b : ℂ) • x) = x) (x : E) :
    (‖complementCompression R P‖⁻¹ - b) * ‖x - P x‖ ^ 2 ≤ (inner ℂ (Lop x) x).re := by
  have hPsymm : ∀ u v, inner ℂ (P u) v = inner ℂ u (P v) :=
    hP.isSelfAdjoint.isSymmetric
  have hPP : ∀ u, P (P u) = P u := fun u ↦ by
    have := congrArg (fun S : E →L[ℂ] E ↦ S u) hP.isIdempotentElem.eq
    simpa using this
  have hLPapply : ∀ u, Lop (P u) = P (Lop u) := fun u ↦ by
    have := congrArg (fun S : E →L[ℂ] E ↦ S u) hLP.eq
    simpa using this
  have hRPapply : ∀ u, R (P u) = P (R u) := fun u ↦ by
    have := congrArg (fun S : E →L[ℂ] E ↦ S u) hRP.eq
    simpa using this
  set z := x - P x with hz
  set w := P x with hw
  have hPz : P z = 0 := by rw [hz, map_sub, hPP, sub_self]
  -- splitting of the energy
  have hsplit : (inner ℂ (Lop x) x).re =
      (inner ℂ (Lop z) z).re + (inner ℂ (Lop w) w).re := by
    have hxzw : x = z + w := by rw [hz, hw]; abel
    have hcross1 : inner ℂ (Lop z) w = 0 := by
      rw [hw, ← hPsymm, ← hLPapply, hPz, map_zero, inner_zero_left]
    have hcross2 : inner ℂ (Lop w) z = 0 := by
      rw [hw, hLPapply, hPsymm, hPz, inner_zero_right]
    rw [hxzw, map_add, inner_add_left, inner_add_right, inner_add_right, hcross1, hcross2]
    simp
  have hwnonneg : 0 ≤ (inner ℂ (Lop w) w).re := hL.re_inner_nonneg_left w
  -- the complement estimate
  set C := complementCompression R P with hC
  set y := Lop z + (b : ℂ) • z with hy
  have hRy : R y = z := hRL z
  have hPy : P y = 0 := by
    rw [hy, map_add, map_smul, ← hLPapply, hPz, map_zero, smul_zero, add_zero]
  have hCy : C y = z := by
    change ((1 - P) * R * (1 - P)) y = z
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, hPy, sub_zero, hRy]
    rw [hPz, sub_zero]
  have hCpos : C.IsPositive := complementCompression_isPositive R P hR hP
  have hCS := norm_apply_sq_le_norm_mul_re_inner_of_isPositive C hCpos y
  rw [hCy] at hCS
  -- `Re ⟨y, z⟩ = Re ⟨L z, z⟩ + b ‖z‖²`
  have hyz : (inner ℂ z y).re = (inner ℂ (Lop z) z).re + b * ‖z‖ ^ 2 := by
    have : inner ℂ y z = inner ℂ (Lop z) z + (b : ℂ) * inner ℂ z z := by
      rw [hy, inner_add_left, inner_smul_left, Complex.conj_ofReal]
    have hre : (inner ℂ z y).re = (inner ℂ y z).re := by
      rw [← inner_conj_symm]; rfl
    rw [hre, this, Complex.add_re, Complex.re_ofReal_mul, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  -- conclude
  have hmain : (‖C‖⁻¹ - b) * ‖z‖ ^ 2 ≤ (inner ℂ (Lop z) z).re := by
    by_cases hC0 : ‖C‖ = 0
    · have hz0 : z = 0 := by
        have := hCS
        rw [hC0, zero_mul] at this
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg z])
      rw [hz0, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, map_zero,
        inner_zero_left, Complex.zero_re, le_refl]
    have hCposn : 0 < ‖C‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hC0)
    have hzle : ‖z‖ ^ 2 ≤ ‖C‖ * ((inner ℂ (Lop z) z).re + b * ‖z‖ ^ 2) := by
      rw [← hyz]; exact hCS
    have : ‖C‖⁻¹ * ‖z‖ ^ 2 ≤ (inner ℂ (Lop z) z).re + b * ‖z‖ ^ 2 := by
      rw [inv_mul_le_iff₀ hCposn]; exact hzle
    nlinarith [this]
  rw [hsplit]
  linarith

/-- **Attained complement eigenvector.**  For a compact positive operator `T` and a star
projection `Q` commuting with `T`, a nonzero complement compression `(1 - Q) T (1 - Q)` has an
eigenvector `x ≠ 0` with `Q x = 0` and `T x = ‖(1 - Q) T (1 - Q)‖ x`. -/
theorem exists_eigenvector_norm_complementCompression
    [CompleteSpace E] (T Q : E →L[ℂ] E) (hcompact : IsCompactOperator T)
    (hpositive : T.IsPositive) (hQ : IsStarProjection Q) (hcommute : Commute T Q)
    (hne : complementCompression T Q ≠ 0) :
    ∃ x : E, x ≠ 0 ∧ Q x = 0 ∧
      T x = (((‖complementCompression T Q‖ : ℝ)) : ℂ) • x := by
  set C : E →L[ℂ] E := complementCompression T Q with hCdef
  have hCcompact : IsCompactOperator C := complementCompression_isCompact T Q hcompact
  have hCpositive : C.IsPositive := complementCompression_isPositive T Q hpositive hQ
  letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp (by
    intro hE
    letI : Subsingleton E := hE
    exact hne (Subsingleton.elim C 0))
  have hCnormPos : 0 < ‖C‖ := norm_pos_iff.mpr hne
  letI : Algebra ℝ (E →L[ℂ] E) := NormedAlgebra.complexToReal.toAlgebra
  have hspecReal : ‖C‖ ∈ spectrum ℝ C :=
    CStarAlgebra.norm_mem_spectrum_of_nonneg (a := C)
      (ha := (ContinuousLinearMap.nonneg_iff_isPositive C).mpr hCpositive)
  have hspec : ((‖C‖ : ℝ) : ℂ) ∈ spectrum ℂ C := by
    simpa using spectrum.algebraMap_mem ℂ hspecReal
  have hnormComplex : ((‖C‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hCnormPos.ne'
  have heigen : Module.End.HasEigenvalue C.toLinearMap ((‖C‖ : ℝ) : ℂ) :=
    (hCcompact.hasEigenvalue_iff_mem_spectrum hnormComplex).mpr hspec
  obtain ⟨x, hx⟩ := heigen.exists_hasEigenvector
  have hQC : Q * C = 0 := by
    calc
      Q * C = (Q * (1 - Q)) * T * (1 - Q) := by
        simp only [hCdef, complementCompression, mul_assoc]
      _ = 0 := by rw [hQ.mul_one_sub_self]; simp
  have hQx : Q x = 0 := by
    have hzero : Q (C x) = 0 := by
      change (Q * C) x = 0
      rw [hQC]
      rfl
    have hscalar : ((‖C‖ : ℝ) : ℂ) • Q x = 0 := by
      rw [← map_smul, ← hx.apply_eq_smul]
      exact hzero
    exact (smul_eq_zero.mp hscalar).resolve_left hnormComplex
  have hQTx : Q (T x) = 0 := by
    calc
      Q (T x) = T (Q x) := by
        exact congrArg (fun S : E →L[ℂ] E ↦ S x) hcommute.eq.symm
      _ = 0 := by rw [hQx]; exact map_zero T
  have hCx : C x = T x := by
    simp [hCdef, complementCompression, hQx, hQTx]
  refine ⟨x, hx.2, hQx, ?_⟩
  rw [← hCx]
  exact hx.apply_eq_smul

end RenewalGeometry.SpectralGap
