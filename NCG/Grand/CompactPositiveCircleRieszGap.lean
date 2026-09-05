/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CircleRieszProjectionCommutation
import NCG.Grand.CircleRieszProjectionOrthogonality
import NCG.Grand.ComplementCompressedResolventGap
import NCG.Grand.CompactCircleRieszProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder

import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
/-!
# Strict complement gaps for compact positive operators

For a compact positive operator, compression away from a circle Riesz projection is again
compact and positive.  If the circle contains the top allowed spectral value, a nonzero
complement compression has strictly smaller norm: equality would make its norm a compact
eigenvalue, while the Riesz projection simultaneously fixes and annihilates the corresponding
eigenvector.
-/

open Complex Set

noncomputable section
open scoped ComplexOrder

namespace NCG.SpectralGap

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Compression of a positive operator by the complement of a star projection is positive. -/
theorem complementCompression_isPositive
    (T P : E →L[ℂ] E) (hT : T.IsPositive) (hP : IsStarProjection P) :
    (complementCompression T P).IsPositive := by
  let S : E →L[ℂ] E := 1 - P
  have hSsymm : LinearMap.IsSymmetric S.toLinearMap :=
    hP.one_sub.isSelfAdjoint.isSymmetric
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    change inner ℂ (S (T (S x))) y = inner ℂ x (S (T (S y)))
    calc
      inner ℂ (S (T (S x))) y = inner ℂ (T (S x)) (S y) := hSsymm _ _
      _ = inner ℂ (S x) (T (S y)) := hT.isSymmetric _ _
      _ = inner ℂ x (S (T (S y))) := hSsymm _ _
  · intro x
    change 0 ≤ inner ℂ (S (T (S x))) x
    calc
      0 ≤ inner ℂ (T (S x)) (S x) := hT.inner_nonneg_left (S x)
      _ = inner ℂ (S (T (S x))) x := (hSsymm _ _).symm

omit [CompleteSpace E] in
/-- Complement compression preserves compactness. -/
theorem complementCompression_isCompact
    (T P : E →L[ℂ] E) (hT : IsCompactOperator T) :
    IsCompactOperator (complementCompression T P) := by
  change IsCompactOperator (fun x ↦ (1 - P) (T ((1 - P) x)))
  exact (hT.comp_clm (1 - P)).clm_comp (1 - P)

/-- An injective operator commuting with a star projection has nonzero complement compression
whenever the projection has a nontrivial complement. -/
theorem complementCompression_ne_zero_of_injective_of_commute
    (T P : E →L[ℂ] E) (hinjective : Function.Injective T)
    (hP : IsStarProjection P) (hcommute : Commute T P) (hPne : P ≠ 1) :
    complementCompression T P ≠ 0 := by
  have hSne : (1 : E →L[ℂ] E) - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hPne)
  have hexists : ∃ x : E, ((1 : E →L[ℂ] E) - P) x ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hSne
    ext x
    simpa using hnone x
  obtain ⟨x, hx⟩ := hexists
  have hPcommuteApply : ∀ y, P (T y) = T (P y) := by
    intro y
    exact congrArg (fun S : E →L[ℂ] E ↦ S y) hcommute.eq.symm
  have hPcomplement : P (((1 : E →L[ℂ] E) - P) x) = 0 := by
    change (P * (1 - P)) x = 0
    rw [hP.mul_one_sub_self]
    rfl
  have hcompressionApply : complementCompression T P x =
      T (((1 : E →L[ℂ] E) - P) x) := by
    change ((1 - P) * T * (1 - P)) x = T ((1 - P) x)
    change (1 - P) (T ((1 - P) x)) = T ((1 - P) x)
    simp only [sub_apply, one_apply_eq_self]
    rw [hPcommuteApply]
    have hPcomplement' : P (x - P x) = 0 := by
      simpa only [sub_apply, one_apply_eq_self] using hPcomplement
    rw [hPcomplement', map_zero, sub_zero]
  intro hzero
  have hkill : T (((1 : E →L[ℂ] E) - P) x) = 0 := by
    rw [← hcompressionApply, hzero]
    rfl
  exact hx (hinjective (by simpa using hkill))

/-- On an infinite-dimensional Hilbert space, a zero-avoiding compact circle Riesz projection
cannot be the identity. -/
theorem circleRieszProjection_ne_one_of_not_finiteDimensional
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (hinfinite : ¬FiniteDimensional ℂ E) :
    NCG.ResolventStability.circleRieszProjection T center radius ≠ 1 := by
  intro hQ
  have hQcompact : IsCompactOperator
      ((NCG.ResolventStability.circleRieszProjection T center radius : E →L[ℂ] E) : E → E) :=
    NCG.ResolventStability.circleRieszProjection_isCompactOperator
      T hcompact center radius hR hzero hcontour
  rw [hQ] at hQcompact
  have hone : (((1 : E →L[ℂ] E) : E → E)) = _root_.id := by
    funext x
    rfl
  have hidCompact : IsCompactOperator (_root_.id : E → E) := hone ▸ hQcompact
  exact hinfinite (FiniteDimensional.of_isCompactOperator_id hidCompact)

/-- An injective compact operator has nonzero compression away from its zero-avoiding circle
Riesz projection on every infinite-dimensional Hilbert space. -/
theorem circleRieszProjection_complementCompression_ne_zero_of_injective
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator T)
    (hsymmetric : LinearMap.IsSymmetric T.toLinearMap) (hinjective : Function.Injective T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (hinfinite : ¬FiniteDimensional ℂ E) :
    complementCompression T
      (NCG.ResolventStability.circleRieszProjection T center radius) ≠ 0 := by
  let Q := NCG.ResolventStability.circleRieszProjection T center radius
  have hQstar : IsStarProjection Q :=
    NCG.ResolventStability.circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
      T hcompact hsymmetric center radius hR hcontour
  have hcommute : Commute T Q :=
    NCG.ResolventStability.circleRieszProjection_commute_of_compact_of_isSymmetric
      T hcompact hsymmetric center radius hR hcontour
  exact complementCompression_ne_zero_of_injective_of_commute T Q hinjective hQstar hcommute
    (circleRieszProjection_ne_one_of_not_finiteDimensional
      T hcompact center radius hR hzero hcontour hinfinite)

/-- A nonzero complement compression has norm strictly below a positive spectral value lying
inside the Riesz circle, provided that value bounds the norm of the original operator. -/
theorem norm_complementCompression_circleRieszProjection_lt
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator T) (hpositive : T.IsPositive)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (mu : ℝ) (hmu : 0 < mu) (hmuInside : (mu : ℂ) ∈ Metric.ball center radius)
    (hnorm : ‖T‖ ≤ mu)
    (hne : complementCompression T (NCG.ResolventStability.circleRieszProjection
      T center radius) ≠ 0) :
    ‖complementCompression T (NCG.ResolventStability.circleRieszProjection
      T center radius)‖ < mu := by
  let Q : E →L[ℂ] E :=
    NCG.ResolventStability.circleRieszProjection T center radius
  let C : E →L[ℂ] E := complementCompression T Q
  have hQstar : IsStarProjection Q :=
    NCG.ResolventStability.circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
      T hcompact hpositive.isSymmetric center radius hR hcontour
  have hSNorm : ‖(1 : E →L[ℂ] E) - Q‖ ≤ 1 :=
    IsStarProjection.norm_le (1 - Q) hQstar.one_sub
  have hCcompact : IsCompactOperator C := by
    simpa [C, Q] using complementCompression_isCompact T Q hcompact
  have hCpositive : C.IsPositive := by
    simpa [C, Q] using complementCompression_isPositive T Q hpositive hQstar
  have hCle : ‖C‖ ≤ mu := by
    calc
      ‖C‖ ≤ ‖(1 : E →L[ℂ] E) - Q‖ * ‖T‖ * ‖(1 : E →L[ℂ] E) - Q‖ := by
        simpa [C, complementCompression] using
          norm_mul_le ((1 - Q) * T) (1 - Q) |>.trans
            (mul_le_mul_of_nonneg_right (norm_mul_le (1 - Q) T) (norm_nonneg _))
      _ ≤ 1 * mu * 1 := by gcongr
      _ = mu := by ring
  by_contra hnot
  have hCeq : ‖C‖ = mu := le_antisymm hCle (le_of_not_gt hnot)
  have hCne : C ≠ 0 := by simpa [C, Q] using hne
  letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp (by
    intro hE
    letI : Subsingleton E := hE
    exact hCne (Subsingleton.elim C 0))
  have hCnormPos : 0 < ‖C‖ := norm_pos_iff.mpr hCne
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
        simp only [C, complementCompression, mul_assoc]
      _ = 0 := by rw [hQstar.mul_one_sub_self]; simp
  have hQx : Q x = 0 := by
    have hzero : Q (C x) = 0 := by
      change (Q * C) x = 0
      rw [hQC]
      rfl
    have hscalar : ((‖C‖ : ℝ) : ℂ) • Q x = 0 := by
      rw [← map_smul, ← hx.apply_eq_smul]
      exact hzero
    exact (smul_eq_zero.mp hscalar).resolve_left hnormComplex
  have hcommute : Commute T Q :=
    NCG.ResolventStability.circleRieszProjection_commute_of_compact_of_isSymmetric
      T hcompact hpositive.isSymmetric center radius hR hcontour
  have hQTx : Q (T x) = 0 := by
    calc
      Q (T x) = T (Q x) := by
        exact congrArg (fun S : E →L[ℂ] E ↦ S x) hcommute.eq.symm
      _ = 0 := by rw [hQx]; exact map_zero T
  have hCx : C x = T x := by
    simp [C, complementCompression, hQx, hQTx]
  have hTx : T x = (mu : ℂ) • x := by
    calc
      T x = C x := hCx.symm
      _ = ((‖C‖ : ℝ) : ℂ) • x := hx.apply_eq_smul
      _ = (mu : ℂ) • x := by rw [hCeq]
  have hfix : Q x = x :=
    NCG.ResolventStability.circleRieszProjection_apply_eigenvector_of_mem_ball
      T center (mu : ℂ) radius x hmuInside hcontour hTx
  exact hx.2 (hfix ▸ hQx)

/-- At a positive shift, the strict complement norm bound gives a positive inverse-norm gap. -/
theorem inverseNormGap_circleRieszProjection_pos
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator T) (hpositive : T.IsPositive)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (lam : ℝ) (hlam : 0 < lam)
    (hinvInside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius)
    (hnorm : ‖T‖ ≤ lam⁻¹)
    (hne : complementCompression T (NCG.ResolventStability.circleRieszProjection
      T center radius) ≠ 0) :
    0 < ‖complementCompression T (NCG.ResolventStability.circleRieszProjection
      T center radius)‖⁻¹ - lam := by
  have hlt := norm_complementCompression_circleRieszProjection_lt
    T hcompact hpositive center radius hR hcontour lam⁻¹ (inv_pos.mpr hlam)
      (by simpa using hinvInside) hnorm hne
  have hnormPos : 0 < ‖complementCompression T
      (NCG.ResolventStability.circleRieszProjection T center radius)‖ :=
    norm_pos_iff.mpr hne
  exact sub_pos.mpr ((lt_inv_comm₀ hnormPos hlam).mp hlt)

end NCG.SpectralGap
