/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ComplementCompressedResolventGap
import NCG.Grand.VaryingHilbertFiniteStageCompression

/-!
# Norms and products of finite-stage compressions

Compression through an isometric stage embedding preserves the operator norm exactly.  It also
preserves products of native stage operators: the Hilbert adjoint of the embedding is a left
inverse.  In particular, complement compression by a native projection can be computed before or
after transport to the common carrier.
-/

open scoped InnerProduct
noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Common-carrier compression through an isometric embedding preserves operator norm. -/
theorem norm_compressedOperator (Tn : ∀ n, Hn n →L[K] Hn n) (n : ℕ) :
    ‖J.compressedOperator Tn n‖ = ‖Tn n‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    calc
      ‖J.compressedOperator Tn n x‖ = ‖Tn n (J.adjointLift n x)‖ := by
        simp [compressedOperator]
      _ ≤ ‖Tn n‖ * ‖J.adjointLift n x‖ := (Tn n).le_opNorm _
      _ ≤ ‖Tn n‖ * ‖x‖ := by
        gcongr
        let e : Hn n →L[K] H := (J.embedding n).toContinuousLinearMap
        calc
          ‖(e†) x‖ ≤ ‖e†‖ * ‖x‖ := (e†).le_opNorm x
          _ = ‖e‖ * ‖x‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
          _ ≤ 1 * ‖x‖ := by gcongr; exact (J.embedding n).norm_toContinuousLinearMap_le
          _ = ‖x‖ := one_mul _
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (J.compressedOperator Tn n).le_opNorm (J.embedding n x)
    simpa using h

/-- Compression preserves native composition because the adjoint lift splits the embedding. -/
theorem compressedOperator_comp
    (S T : ∀ n, Hn n →L[K] Hn n) (n : ℕ) :
    J.compressedOperator (fun k ↦ (S k).comp (T k)) n =
      (J.compressedOperator S n).comp (J.compressedOperator T n) := by
  ext x
  simp [compressedOperator, J.adjointLift_embedding]

/-- A native orthogonal projection remains an orthogonal projection after common-carrier
transport. -/
theorem compressedOperator_isStarProjection
    (P : ∀ n, Hn n →L[K] Hn n) (n : ℕ) (hP : IsStarProjection (P n)) :
    IsStarProjection (J.compressedOperator P n) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change J.embedding n
        (P n (J.adjointLift n (J.embedding n (P n (J.adjointLift n x))))) =
      J.embedding n (P n (J.adjointLift n x))
    rw [J.adjointLift_embedding]
    exact congrArg (J.embedding n) <|
      congrArg (fun Q : Hn n →L[K] Hn n ↦ Q (J.adjointLift n x))
        hP.isIdempotentElem.eq
  · change IsSelfAdjoint
      ((J.embedding n).toContinuousLinearMap ∘L P n ∘L
        (J.embedding n).toContinuousLinearMap.adjoint)
    exact hP.isSelfAdjoint.conj_adjoint (J.embedding n).toContinuousLinearMap

/-- The range of a transported operator is the isometric image of its native range. -/
theorem range_compressedOperator
    (T : ∀ n, Hn n →L[K] Hn n) (n : ℕ) :
    LinearMap.range (J.compressedOperator T n).toLinearMap =
      (LinearMap.range (T n).toLinearMap).map (J.embedding n).toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨T n (J.adjointLift n y), ⟨J.adjointLift n y, rfl⟩, ?_⟩
    rfl
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    refine ⟨J.embedding n y, ?_⟩
    simp [compressedOperator, J.adjointLift_embedding]

/-- Transporting the canonical projection onto a native subspace gives the canonical projection
onto its embedded image. -/
theorem compressedOperator_starProjection_range
    (U : ∀ n, Submodule K (Hn n)) [∀ n, (U n).HasOrthogonalProjection] (n : ℕ) :
    LinearMap.range (J.compressedOperator (fun k ↦ (U k).starProjection) n).toLinearMap =
      (U n).map (J.embedding n).toLinearMap := by
  rw [J.range_compressedOperator]
  simp

/-- Complement compression can be performed on the native finite stage and then transported. -/
theorem complementCompression_compressedOperator
    (T P : ∀ n, Hn n →L[K] Hn n) (n : ℕ) :
    NCG.SpectralGap.complementCompression (J.compressedOperator T n)
        (J.compressedOperator P n) =
      J.compressedOperator
        (fun k ↦ NCG.SpectralGap.complementCompression (T k) (P k)) n := by
  ext x
  simp [NCG.SpectralGap.complementCompression, compressedOperator,
    J.adjointLift_embedding,
    sub_eq_add_neg]

/-- Hence complement compression through a finite stage preserves the native compressed norm. -/
theorem norm_complementCompression_compressedOperator
    (T P : ∀ n, Hn n →L[K] Hn n) (n : ℕ) :
    ‖NCG.SpectralGap.complementCompression (J.compressedOperator T n)
        (J.compressedOperator P n)‖ =
      ‖NCG.SpectralGap.complementCompression (T n) (P n)‖ := by
  rw [J.complementCompression_compressedOperator T P n,
    J.norm_compressedOperator]

end NCG.VaryingHilbert.System
