/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProcessRepresentation
import NCG.Grand.CanonicalPrefixPurificationUniqueness
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.RingTheory.Congruence.Hom

/-!
# The process-history star algebra

This file supplies the star-algebra and support-minimal covariance clauses of
`thm:process-representation`.  A star representation has a star-stable
two-sided kernel, its represented image is a finite-dimensional star
subalgebra of a matrix algebra, and two unitarily covariant representations
have a unique source-fixing star-algebra equivalence between their images.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {F : Type*} [Ring F] [StarRing F] [Algebra ℂ F] [StarModule ℂ F]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The represented process-history algebra as an actual star-subalgebra. -/
noncomputable def processHistoryImage
    (ρ : F →⋆ₐ[ℂ] Matrix n n ℂ) : StarSubalgebra ℂ (Matrix n n ℂ) where
  __ := ρ.toAlgHom.range
  star_mem' := by
    rintro y ⟨x, rfl⟩
    exact ⟨star x, map_star ρ x⟩

/-- The representation kernel is a two-sided ideal closed under star. -/
theorem processHistoryKernel_star_mem
    (ρ : F →⋆ₐ[ℂ] Matrix n n ℂ) {x : F}
    (hx : x ∈ RingHom.ker ρ.toAlgHom.toRingHom) :
    star x ∈ RingHom.ker ρ.toAlgHom.toRingHom := by
  change ρ (star x) = 0
  rw [map_star, show ρ x = 0 from hx]
  exact star_zero _

/-- First isomorphism theorem in the star-compatible setting.  The codomain is
the underlying algebra of `processHistoryImage ρ`; star compatibility is
recorded by `processHistoryImage` and `processHistoryKernel_star_mem`. -/
theorem processHistoryQuotient_equiv_image
    (ρ : F →⋆ₐ[ℂ] Matrix n n ℂ) :
    Nonempty ((RingCon.ker ρ.toAlgHom.toRingHom).Quotient
      ≃ₐ[ℂ] ρ.toAlgHom.range) :=
  ⟨RingCon.quotientKerEquivRangeₐ ρ.toAlgHom⟩

/-- The represented process-history star algebra is finite-dimensional. -/
theorem processHistoryImage_finrank_le
    (ρ : F →⋆ₐ[ℂ] Matrix n n ℂ) :
    Module.finrank ℂ (processHistoryImage ρ)
      ≤ Module.finrank ℂ (Matrix n n ℂ) :=
  Submodule.finrank_le (processHistoryImage ρ).toSubalgebra.toSubmodule

/-- Star on the represented range, with a canonical membership witness. -/
noncomputable def processHistoryRangeStar
    (ρ : F →⋆ₐ[ℂ] Matrix n n ℂ) (
    y : ρ.toAlgHom.range) : ρ.toAlgHom.range :=
  ⟨star (y : Matrix n n ℂ), by
    rcases y.property with ⟨x, hx⟩
    exact ⟨star x, (ρ.map_star' x).trans (congrArg star hx)⟩⟩

@[simp] theorem processHistoryRangeStar_mk
    (ρ : F →⋆ₐ[ℂ] Matrix n n ℂ) (x : F) :
    processHistoryRangeStar ρ
        ⟨ρ x, AlgHom.mem_range_self ρ.toAlgHom x⟩
      = ⟨ρ (star x), AlgHom.mem_range_self ρ.toAlgHom (star x)⟩ := by
  apply Subtype.ext
  exact (ρ.map_star' x).symm

/-- Unitary covariance preserves the complete process kernel. -/
theorem unitaryCovariant_processKernel
    (ρ σ : F →⋆ₐ[ℂ] Matrix n n ℂ) (U : Matrix n n ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1)
    (hcov : ∀ x, σ x = U * ρ x * Uᴴ) (x : F) :
    ρ x = 0 ↔ σ x = 0 := by
  constructor
  · intro hx
    rw [hcov, hx, Matrix.mul_zero, Matrix.zero_mul]
  · intro hx
    have hz : U * ρ x * Uᴴ = 0 := by rw [← hcov, hx]
    have h := congrArg (fun M : Matrix n n ℂ => Uᴴ * M * U) hz
    calc
      ρ x = (Uᴴ * U) * ρ x * (Uᴴ * U) := by
        rw [hleft, Matrix.one_mul, Matrix.mul_one]
      _ = Uᴴ * (U * ρ x * Uᴴ) * U := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by simpa using h

/-- Support-minimal unitary covariance gives the unique generator-fixing
algebra equivalence of represented process histories, and that equivalence
preserves star on every represented word. -/
theorem unitaryCovariant_processHistory_unique
    (ρ σ : F →⋆ₐ[ℂ] Matrix n n ℂ) (U : Matrix n n ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1)
    (hcov : ∀ x, σ x = U * ρ x * Uᴴ) :
    ∃! e : ρ.toAlgHom.range ≃ₐ[ℂ] σ.toAlgHom.range,
      (∀ x : F, e ⟨ρ x, AlgHom.mem_range_self ρ.toAlgHom x⟩
        = ⟨σ x, AlgHom.mem_range_self σ.toAlgHom x⟩)
      ∧ (∀ y : ρ.toAlgHom.range,
        e (processHistoryRangeStar ρ y)
          = processHistoryRangeStar σ (e y)) := by
  have hrel : ∀ a b : F, ρ a = ρ b ↔ σ a = σ b := by
    intro a b
    change ρ a = ρ b ↔ σ a = σ b
    constructor
    · intro hab
      rw [hcov, hcov, hab]
    · intro hab
      have hzσ : σ (a - b) = 0 := by simpa using sub_eq_zero.mpr hab
      have hzρ := (unitaryCovariant_processKernel ρ σ U hleft hright hcov (a - b)).mpr hzσ
      exact sub_eq_zero.mp (by simpa using hzρ)
  have hk : RingCon.ker ρ.toAlgHom.toRingHom =
      RingCon.ker σ.toAlgHom.toRingHom := by
    ext a b
    exact hrel a b
  let eρ := RingCon.quotientKerEquivRangeₐ ρ.toAlgHom
  let eσ := RingCon.quotientKerEquivRangeₐ σ.toAlgHom
  let qeq : (RingCon.ker ρ.toAlgHom.toRingHom).Quotient
      ≃ₐ[ℂ] (RingCon.ker σ.toAlgHom.toRingHom).Quotient :=
    RingCon.congrₐ (R := ℂ) (AlgEquiv.refl)
      (by
        ext a b
        exact hrel a b)
  let e : ρ.toAlgHom.range ≃ₐ[ℂ] σ.toAlgHom.range :=
    eρ.symm.trans (qeq.trans eσ)
  have he : ∀ x : F, e ⟨ρ x, AlgHom.mem_range_self ρ.toAlgHom x⟩
      = ⟨σ x, AlgHom.mem_range_self σ.toAlgHom x⟩ := by
    intro x
    change eσ (qeq (eρ.symm
      ⟨ρ x, AlgHom.mem_range_self ρ.toAlgHom x⟩)) = _
    have hback : eρ.symm
        ⟨ρ x, AlgHom.mem_range_self ρ.toAlgHom x⟩
        = (RingCon.ker ρ.toAlgHom.toRingHom).mkₐ ℂ x := by
      apply eρ.injective
      rw [eρ.apply_symm_apply]
      exact (RingCon.quotientKerEquivRangeₐ_mkₐ ρ.toAlgHom x).symm
    rw [hback]
    rw [show qeq ((RingCon.ker ρ.toAlgHom.toRingHom).mkₐ ℂ x)
        = (RingCon.ker σ.toAlgHom.toRingHom).mkₐ ℂ x from by
          exact RingCon.congrₐ_mk (AlgEquiv.refl) _ x]
    exact RingCon.quotientKerEquivRangeₐ_mkₐ σ.toAlgHom x
  have hstar : ∀ y : ρ.toAlgHom.range,
      e (processHistoryRangeStar ρ y)
        = processHistoryRangeStar σ (e y) := by
    rintro ⟨y, ⟨x, hx⟩⟩
    have hy : (⟨y, ⟨x, hx⟩⟩ : ρ.toAlgHom.range)
        = ⟨ρ x, AlgHom.mem_range_self ρ.toAlgHom x⟩ := by
      apply Subtype.ext
      exact hx.symm
    rw [hy, processHistoryRangeStar_mk, he (star x), he x,
      processHistoryRangeStar_mk]
  refine ⟨e, ⟨he, hstar⟩, ?_⟩
  intro e' he'
  apply AlgEquiv.ext
  rintro ⟨_, ⟨x, rfl⟩⟩
  exact (he'.1 x).trans (he x).symm

end NCG
