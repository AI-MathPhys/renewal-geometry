/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Algebra.ChoiCriterion
import NCG.Algebra.FiniteHermitianOrderedCone
import NCG.Algebra.PositiveMatrixFunctional
import NCG.Analysis.ApproximationSingularValues
import NCG.Grand.GrandResetAudit

/-!
# Finite reset and record-leakage audit

This module gives the exact finite-dimensional content of
`thm:reset-record-audit`: complete normalized-output reset, rank one of the
Hermitian transfer, and a positive trace-effect factorization are equivalent;
the second approximation singular value is the exact operator-norm distance
to rank-one transfers; and record future-nullity is exactly the vanishing of
the corresponding Gram matrix.
-/

open Matrix
open scoped ComplexOrder MatrixOrder ComplexStarModule

namespace NCG

/-- A positive matrix branch.  Complete positivity implies this property by
`matrixCompletelyPositive_positive`. -/
def IsPositiveMatrixBranch {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ X, X.PosSemidef → (R X).PosSemidef

/-- Complete atomic reset: every occurring positive input has the same
trace-normalized Hermitian output. -/
def IsCompleteAtomicReset {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : IsPositiveMatrixBranch R) : Prop :=
  ∃ ω : HermitianMatrix m,
    ω ∈ (hermitianPsdGeneratingCone m).carrier ∧
    hermitianTraceStrictFunctional m ω = 1 ∧
    HasCommonNormalizedOutput (hermitianPsdGeneratingCone n)
      (hermitianTraceStrictFunctional m) (hermitianTransfer R hpos) ω

/-- The boxed positive trace-effect form of an atomic reset. -/
def HasPsdTraceResetFactorization {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ (E : Matrix (Fin n) (Fin n) ℂ)
      (ω : Matrix (Fin m) (Fin m) ℂ),
    E.PosSemidef ∧ E ≠ 0 ∧ ω.PosSemidef ∧ ω.trace = 1 ∧
      ∀ X, R X = (E * X).trace • ω

/-- Two positive inputs whose outputs both have unit trace but are distinct
rule out complete atomic reset. -/
theorem not_completeAtomicReset_of_distinct_normalized_outputs {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : IsPositiveMatrixBranch R)
    (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrX : (R X).trace = 1) (htrY : (R Y).trace = 1)
    (hne : R X ≠ R Y) : ¬ IsCompleteAtomicReset R hpos := by
  rintro ⟨ω, _hωpos, _hωtr, hcommon⟩
  let Xh : HermitianMatrix n := ⟨X, hX.1⟩
  let Yh : HermitianMatrix n := ⟨Y, hY.1⟩
  have hRX0 : hermitianTransfer R hpos Xh ≠ 0 := by
    intro hz
    have hzval : R X = 0 := by
      rw [← hermitianTransfer_apply R hpos Xh]
      exact congrArg Subtype.val hz
    have : (0 : ℂ) = 1 := by simpa [hzval] using htrX
    exact zero_ne_one this
  have hRY0 : hermitianTransfer R hpos Yh ≠ 0 := by
    intro hz
    have hzval : R Y = 0 := by
      rw [← hermitianTransfer_apply R hpos Yh]
      exact congrArg Subtype.val hz
    have : (0 : ℂ) = 1 := by simpa [hzval] using htrY
    exact zero_ne_one this
  have hnormX : hermitianTraceStrictFunctional m
      (hermitianTransfer R hpos Xh) = 1 := by
    change (R X).trace.re = 1
    rw [htrX]
    norm_num
  have hnormY : hermitianTraceStrictFunctional m
      (hermitianTransfer R hpos Yh) = 1 := by
    change (R Y).trace.re = 1
    rw [htrY]
    norm_num
  have hxω := hcommon (x := Xh) hX hRX0
  have hyω := hcommon (x := Yh) hY hRY0
  rw [hnormX] at hxω
  rw [hnormY] at hyω
  simp only [inv_one, one_smul] at hxω hyω
  apply hne
  have hxy : hermitianTransfer R hpos Xh =
      hermitianTransfer R hpos Yh := hxω.trans hyω.symm
  exact congrArg Subtype.val hxy

/-- For a nonzero positive branch, complete atomic reset is exactly rank one
of its Hermitian transfer. -/
theorem completeAtomicReset_iff_hermitianTransfer_rankOne {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : IsPositiveMatrixBranch R) (hR : R ≠ 0) :
    IsCompleteAtomicReset R hpos ↔
      Module.finrank ℝ (hermitianTransfer R hpos).range = 1 := by
  let CV := hermitianPsdGeneratingCone n
  let CW := hermitianPsdGeneratingCone m
  let u := hermitianTraceStrictFunctional m
  let T := hermitianTransfer R hpos
  have hTpos : ConePositive CV CW T :=
    hermitianTransfer_conePositive R hpos
  have hT0 : T ≠ 0 := hermitianTransfer_ne_zero_of_ne_zero R hpos hR
  constructor
  · intro hreset
    exact ((atomicReset_orderedCone_characterization CV CW u T hTpos hT0).mp
      hreset).2
  · intro hrank
    have hatom := rankOne_positive_atomic CV CW u T hTpos hT0 hrank
    exact (atomicReset_orderedCone_characterization CV CW u T hTpos hT0).2
      ⟨hatom, hrank⟩

/-- Rank one of a nonzero positive Hermitian transfer constructs the unique
positive trace effect and a normalized positive output state. -/
theorem hermitianTransfer_rankOne_implies_psdTraceResetFactorization
    {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : IsPositiveMatrixBranch R) (hR : R ≠ 0)
    (hrank : Module.finrank ℝ (hermitianTransfer R hpos).range = 1) :
    HasPsdTraceResetFactorization R := by
  let CV := hermitianPsdGeneratingCone n
  let CW := hermitianPsdGeneratingCone m
  let u := hermitianTraceStrictFunctional m
  let T := hermitianTransfer R hpos
  have hTpos : ConePositive CV CW T :=
    hermitianTransfer_conePositive R hpos
  have hT0 : T ≠ 0 := hermitianTransfer_ne_zero_of_ne_zero R hpos hR
  obtain ⟨ℓ, ω, hℓ0, hℓpos, hωpsd, hωtr, hω0, hformula⟩ :=
    rankOne_positive_atomic CV CW u T hTpos hT0 hrank
  have hωtrace : ω.val.trace = 1 := by
    have hnon := hωpsd.trace_nonneg
    apply Complex.ext
    · exact hωtr
    · simpa using (Complex.nonneg_iff.mp hnon).2.symm
  let τ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin m) ℂ ℂ).comp R
  have hτpos : ∀ X, X.PosSemidef → 0 ≤ τ X := by
    intro X hX
    exact (hpos X hX).trace_nonneg
  obtain ⟨E, ⟨hEpsd, hErepr⟩, _⟩ :=
    positiveMatrixFunctional_existsUnique_traceRepresenter τ hτpos
  have hE0 : E ≠ 0 := by
    intro hEz
    have hex : ∃ X, ℓ X ≠ 0 := by
      by_contra h
      push Not at h
      apply hℓ0
      ext X
      exact h X
    obtain ⟨X, hX⟩ := hex
    have hmatrixFormula := congrArg Subtype.val (hformula X)
    change R X.val = (ℓ X : ℝ) • ω.val at hmatrixFormula
    have htraceFormula := congrArg Matrix.trace hmatrixFormula
    have hτX : τ X.val = (ℓ X : ℂ) := by
      change (R X.val).trace = (ℓ X : ℂ)
      simpa [T, Matrix.trace_smul, hωtrace, smul_eq_mul] using htraceFormula
    have hz := hErepr X.val
    rw [hEz] at hz
    simp at hz
    exact hX (Complex.ofReal_injective (hτX.symm.trans hz))
  have hHermitianFormula : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      X.IsHermitian → R X = (E * X).trace • ω.val := by
    intro X hX
    let Xh : HermitianMatrix n := ⟨X, hX⟩
    have hf := congrArg Subtype.val (hformula Xh)
    change R X = (ℓ Xh : ℝ) • ω.val at hf
    have ht := congrArg Matrix.trace hf
    have hcoef : ((ℓ Xh : ℝ) : ℂ) = (E * X).trace := by
      have hτ := hErepr X
      calc
        ((ℓ Xh : ℝ) : ℂ) = (R X).trace := by
          simpa [T, Matrix.trace_smul, hωtrace, smul_eq_mul] using ht.symm
        _ = τ X := rfl
        _ = (E * X).trace := hτ
    have hfR : R X = ((ℓ Xh : ℝ) : ℂ) • ω.val := by
      simpa [T] using hf
    rw [hfR, hcoef]
  have hmap : R = matrixAtomicReset E ω.val := by
    apply complexLinearMap_ext_of_isHermitian
    intro X hX
    simpa [matrixAtomicReset_apply] using hHermitianFormula X hX
  refine ⟨E, ω.val, hEpsd, hE0, hωpsd, hωtrace, ?_⟩
  intro X
  rw [hmap]
  rfl

/-- A positive trace-effect factorization has a common normalized output and
hence is a complete atomic reset. -/
theorem psdTraceResetFactorization_implies_completeAtomicReset
    {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : IsPositiveMatrixBranch R) (hR : R ≠ 0)
    (hfac : HasPsdTraceResetFactorization R) :
    IsCompleteAtomicReset R hpos := by
  obtain ⟨E, ω, hE, hE0, hω, hωtrace, hformula⟩ := hfac
  let CV := hermitianPsdGeneratingCone n
  let CW := hermitianPsdGeneratingCone m
  let u := hermitianTraceStrictFunctional m
  let T := hermitianTransfer R hpos
  let ωh : HermitianMatrix m := ⟨ω, hω.1⟩
  let coeff : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => (E * X).trace
      map_add' := by intros; simp [Matrix.mul_add]
      map_smul' := by intros; simp [Matrix.mul_smul] }
  have hcoeffpos : ∀ X, X.PosSemidef → 0 ≤ coeff X := by
    intro X hX
    exact Upstream.PrimitiveWeight.trace_mul_psd_nonneg hE hX
  let ell : HermitianMatrix n →ₗ[ℝ] ℝ := u.toLinearMap.comp T
  have hcoeffReal : ∀ X : HermitianMatrix n,
      (((coeff X.val).re : ℝ) : ℂ) = coeff X.val := by
    intro X
    have hs := positiveMatrixFunctional_star_eq_of_isHermitian
      coeff hcoeffpos X.val X.prop
    apply Complex.ext
    · simp
    · have hi := congrArg Complex.im hs
      simp at hi ⊢
      linarith
  have hell : ∀ X : HermitianMatrix n, ell X = (coeff X.val).re := by
    intro X
    change (R X.val).trace.re = (coeff X.val).re
    rw [hformula X.val, Matrix.trace_smul, hωtrace]
    simp [coeff, smul_eq_mul]
  have hTformula : ∀ X : HermitianMatrix n, T X = ell X • ωh := by
    intro X
    apply Subtype.ext
    change R X.val = ((ell X : ℝ) : ℂ) • ω
    rw [hformula X.val, hell X]
    exact congrArg (fun c : ℂ => c • ω) (hcoeffReal X).symm
  have hTpos : ConePositive CV CW T :=
    hermitianTransfer_conePositive R hpos
  have hT0 : T ≠ 0 := hermitianTransfer_ne_zero_of_ne_zero R hpos hR
  have hell0 : ell ≠ 0 := by
    intro hz
    apply hT0
    apply LinearMap.ext
    intro X
    rw [hTformula X, LinearMap.congr_fun hz X]
    simp
  have hωh0 : ωh ≠ 0 := by
    intro hz
    have hv := congrArg (fun X : HermitianMatrix m => X.val.trace) hz
    simp [ωh, hωtrace] at hv
  have hatom : HasPositiveAtomicFactorization CV CW u T := by
    refine ⟨ell, ωh, hell0, ?_, hω, ?_, hωh0, hTformula⟩
    · intro X hX
      exact u.nonneg (hTpos hX)
    · change ω.trace.re = 1
      rw [hωtrace]
      simp
  have hrank := positiveAtomicFactorization_rank_one CV CW u T hatom
  exact (atomicReset_orderedCone_characterization CV CW u T hTpos hT0).2
    ⟨hatom, hrank⟩

/-- Exact three-way reset characterization for a nonzero positive finite
matrix branch. -/
theorem finitePositiveReset_characterization {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : IsPositiveMatrixBranch R) (hR : R ≠ 0) :
    (IsCompleteAtomicReset R hpos ↔
      Module.finrank ℝ (hermitianTransfer R hpos).range = 1)
    ∧ (Module.finrank ℝ (hermitianTransfer R hpos).range = 1 ↔
      HasPsdTraceResetFactorization R) := by
  refine ⟨completeAtomicReset_iff_hermitianTransfer_rankOne R hpos hR,
    ?_⟩
  constructor
  · exact hermitianTransfer_rankOne_implies_psdTraceResetFactorization
      R hpos hR
  · intro hfac
    exact (completeAtomicReset_iff_hermitianTransfer_rankOne R hpos hR).mp
      (psdTraceResetFactorization_implies_completeAtomicReset R hpos hR hfac)

/-- Exact specialization to a nonzero completely positive matrix branch. -/
theorem finiteCPReset_characterization {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hCP : IsMatrixCompletelyPositive R) (hR : R ≠ 0) :
    let hpos : IsPositiveMatrixBranch R :=
      fun _ hX => matrixCompletelyPositive_positive hCP hX
    (IsCompleteAtomicReset R hpos ↔
      Module.finrank ℝ (hermitianTransfer R hpos).range = 1)
    ∧ (Module.finrank ℝ (hermitianTransfer R hpos).range = 1 ↔
      HasPsdTraceResetFactorization R) := by
  dsimp
  exact finitePositiveReset_characterization R _ hR

/-! ## Exact second singular value and record Gram -/

/-- The second singular value of the finite Hermitian transfer, in its exact
Eckart--Young approximation characterization. -/
noncomputable def hermitianTransferSecondSingularValue {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : IsPositiveMatrixBranch R) : ℝ :=
  linearApproximationNumber (hermitianTransfer R hpos) 1

theorem hermitianTransferSecondSingularValue_eq_distance_to_rankOne
    {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : IsPositiveMatrixBranch R) :
    hermitianTransferSecondSingularValue R hpos =
      linearDistanceToRankAtMost (hermitianTransfer R hpos) 1 :=
  secondLinearApproximationNumber_eq_distance_to_rankOne _

/-- `thm:reset-record-audit`: complete atomic reset, rank-one Hermitian
transfer, positive trace-effect form, exact best-rank-one error, and record
future-nullity are assembled in one theorem for a nonzero finite CP branch. -/
theorem finite_reset_record_audit {n m t h e : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hCP : IsMatrixCompletelyPositive R) (hR : R ≠ 0)
    (C : Matrix (Fin h) (Fin t) ℂ) (J : Matrix (Fin t) (Fin e) ℂ) :
    let hpos : IsPositiveMatrixBranch R :=
      fun _ hX => matrixCompletelyPositive_positive hCP hX
    ((IsCompleteAtomicReset R hpos ↔
        Module.finrank ℝ (hermitianTransfer R hpos).range = 1)
      ∧ (Module.finrank ℝ (hermitianTransfer R hpos).range = 1 ↔
        HasPsdTraceResetFactorization R))
    ∧ (hermitianTransferSecondSingularValue R hpos =
      linearDistanceToRankAtMost (hermitianTransfer R hpos) 1)
    ∧ (Jᴴ * (Cᴴ * C) * J = 0 ↔ C * J = 0) := by
  dsimp
  refine ⟨finitePositiveReset_characterization R _ hR,
    hermitianTransferSecondSingularValue_eq_distance_to_rankOne R _, ?_⟩
  exact (reset_record_audit C J (0 : Matrix (Fin t) (Fin t) ℂ)
    (0 : Matrix (Fin t) (Fin t) ℂ)).1

end NCG
