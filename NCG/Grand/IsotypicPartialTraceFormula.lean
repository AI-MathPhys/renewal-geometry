/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import NCG.Grand.CompactIsotypicSchur

/-!
# Isotypic partial-trace formula

This file contains the finite matrix algebra behind the diagonal part of the
positive-packet compact-orbit theorem.  Once Schur's lemma has shown that
every multiplicity coefficient block is scalar on an irreducible factor, its
scalar is determined exactly by the partial trace over that factor.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace NCG
namespace IsotypicPartialTrace

variable {I : Type} {M : Type*} [Fintype I] [Fintype M] [DecidableEq I]

/-- The matrix block between two fixed multiplicity coordinates. -/
def multiplicityCoefficientBlock
    (F : Matrix (I × M) (I × M) ℂ) (a b : M) : Matrix I I ℂ :=
  fun i j => F (i, a) (j, b)

/-- Partial trace over the irreducible coordinate of an isotypic matrix. -/
noncomputable def multiplicityPartialTrace
    (F : Matrix (I × M) (I × M) ℂ) : Matrix M M ℂ :=
  fun a b => ∑ i, F (i, a) (i, b)

@[simp]
theorem multiplicityPartialTrace_apply
    (F : Matrix (I × M) (I × M) ℂ) (a b : M) :
    multiplicityPartialTrace F a b = ∑ i, F (i, a) (i, b) := rfl

/-- The partial trace is the sum of the principal multiplicity compressions. -/
theorem multiplicityPartialTrace_eq_sum_submatrix
    (F : Matrix (I × M) (I × M) ℂ) :
    multiplicityPartialTrace F =
      ∑ i : I, F.submatrix (fun a => (i, a)) (fun a => (i, a)) := by
  ext a b
  simp [multiplicityPartialTrace, Matrix.sum_apply]

/-- Positivity is preserved by the multiplicity partial trace. -/
theorem multiplicityPartialTrace_posSemidef
    (F : Matrix (I × M) (I × M) ℂ) (hF : F.PosSemidef) :
    (multiplicityPartialTrace F).PosSemidef := by
  rw [multiplicityPartialTrace_eq_sum_submatrix]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    hF.submatrix (fun a => (i, a))

/-- The multiplicity partial trace is the ordinary matrix trace of each
multiplicity coefficient block. -/
theorem multiplicityPartialTrace_eq_trace_coefficientBlock
    (F : Matrix (I × M) (I × M) ℂ) (a b : M) :
    multiplicityPartialTrace F a b =
      Matrix.trace (multiplicityCoefficientBlock F a b) := rfl

/-- A Kronecker conjugation on the irreducible factor conjugates every
multiplicity coefficient block by the same matrix. -/
theorem coefficientBlock_kronecker_conjugation
    [DecidableEq M] (U : Matrix I I ℂ)
    (F : Matrix (I × M) (I × M) ℂ) (a b : M) :
    multiplicityCoefficientBlock
        ((U ⊗ₖ (1 : Matrix M M ℂ)) * F *
          (U ⊗ₖ (1 : Matrix M M ℂ))ᴴ) a b =
      U * multiplicityCoefficientBlock F a b * Uᴴ := by
  let A : Matrix (I × M) (I × M) ℂ :=
    U ⊗ₖ (1 : Matrix M M ℂ)
  have hleft (H : Matrix (I × M) (I × M) ℂ) :
      multiplicityCoefficientBlock (A * H) a b =
        U * multiplicityCoefficientBlock H a b := by
    ext i j
    simp [A, multiplicityCoefficientBlock, Matrix.mul_apply,
      Matrix.kronecker_apply, Matrix.one_apply,
      ← Finset.univ_product_univ, Finset.sum_product]
  have hright (H : Matrix (I × M) (I × M) ℂ) :
      multiplicityCoefficientBlock (H * Aᴴ) a b =
        multiplicityCoefficientBlock H a b * Uᴴ := by
    ext i j
    simp [A, multiplicityCoefficientBlock, Matrix.mul_apply,
      Matrix.kronecker_apply, Matrix.one_apply,
      ← Finset.univ_product_univ, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro k _
    rw [Fintype.sum_eq_single b]
    · simp
    · intro c hcb
      simp [Ne.symm hcb]
  change multiplicityCoefficientBlock (A * F * Aᴴ) a b = _
  rw [hright, hleft]

/-- Partial trace over the irreducible factor is invariant under unitary
conjugation on that factor. -/
theorem multiplicityPartialTrace_kronecker_unitary_conjugation
    [DecidableEq M] (U : Matrix I I ℂ) (hU : Uᴴ * U = 1)
    (F : Matrix (I × M) (I × M) ℂ) :
    multiplicityPartialTrace
        ((U ⊗ₖ (1 : Matrix M M ℂ)) * F *
          (U ⊗ₖ (1 : Matrix M M ℂ))ᴴ) =
      multiplicityPartialTrace F := by
  ext a b
  rw [multiplicityPartialTrace_eq_trace_coefficientBlock,
    coefficientBlock_kronecker_conjugation,
    Matrix.trace_mul_cycle, hU, Matrix.one_mul,
    ← multiplicityPartialTrace_eq_trace_coefficientBlock]

/-- If every multiplicity coefficient block is scalar on the irreducible
coordinate, then the full operator is exactly `d⁻¹ I ⊗ Tr_I(F)`. -/
theorem eq_invDimension_smul_one_kronecker_partialTrace
    [Nonempty I] (F : Matrix (I × M) (I × M) ℂ)
    (hscalar : ∀ a b, ∃ c : ℂ, ∀ i j,
      F (i, a) (j, b) = c * (1 : Matrix I I ℂ) i j) :
    F = ((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ
      multiplicityPartialTrace F := by
  ext ⟨i, a⟩ ⟨j, b⟩
  obtain ⟨c, hc⟩ := hscalar a b
  have htrace :
      multiplicityPartialTrace F a b = (Fintype.card I : ℂ) * c := by
    simp only [multiplicityPartialTrace, hc]
    simp
  rw [Matrix.kronecker_apply, htrace]
  by_cases hij : i = j
  · subst j
    rw [hc]
    simp [Fintype.card_ne_zero]
  · rw [hc]
    simp [hij]

/-- The unnormalized form: scalar blocks reconstruct as
`I ⊗ (d⁻¹ Tr_I(F))`. -/
theorem eq_one_kronecker_invDimension_smul_partialTrace
    [Nonempty I] (F : Matrix (I × M) (I × M) ℂ)
    (hscalar : ∀ a b, ∃ c : ℂ, ∀ i j,
      F (i, a) (j, b) = c * (1 : Matrix I I ℂ) i j) :
    F = (1 : Matrix I I ℂ) ⊗ₖ
      ((Fintype.card I : ℂ)⁻¹ • multiplicityPartialTrace F) := by
  rw [eq_invDimension_smul_one_kronecker_partialTrace F hscalar]
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp [mul_assoc]
  · simp [hij]

/-- Schur plus partial trace: commuting multiplicity coefficient blocks of
an irreducible representation give the exact normalized isotypic formula. -/
theorem eq_invDimension_smul_one_kronecker_partialTrace_of_irreducible
    {G : Type*} [Group G] [Nonempty I]
    (ρ : G →* Matrix I I ℂ)
    [CategoryTheory.Simple
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation ρ))]
    (F : Matrix (I × M) (I × M) ℂ)
    (hcomm : ∀ g a b,
      multiplicityCoefficientBlock F a b * ρ g =
        ρ g * multiplicityCoefficientBlock F a b) :
    F = ((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ
      multiplicityPartialTrace F := by
  apply eq_invDimension_smul_one_kronecker_partialTrace F
  intro a b
  obtain ⟨c, hc⟩ :=
    NCG.CompactIsotypicSchur.matrix_eq_smul_one_of_commutes_irreducible
      ρ (multiplicityCoefficientBlock F a b) (fun g => hcomm g a b)
  exact ⟨c, fun i j => congrFun (congrFun hc i) j⟩

/-- Global commutation with `ρ(g) ⊗ I_M` implies commutation of every
multiplicity coefficient block with `ρ(g)`. -/
theorem coefficientBlock_commutes_of_kronecker_commutes
    {G : Type*} [Group G] [DecidableEq M]
    (ρ : G →* Matrix I I ℂ)
    (F : Matrix (I × M) (I × M) ℂ)
    (hcomm : ∀ g,
      F * (ρ g ⊗ₖ (1 : Matrix M M ℂ)) =
        (ρ g ⊗ₖ (1 : Matrix M M ℂ)) * F) :
    ∀ g a b,
      multiplicityCoefficientBlock F a b * ρ g =
        ρ g * multiplicityCoefficientBlock F a b := by
  intro g a b
  ext i j
  have hentry := congrFun (congrFun (hcomm g) (i, a)) (j, b)
  simpa [Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, multiplicityCoefficientBlock, ← Finset.univ_product_univ,
    Finset.sum_product] using hentry

/-- Exact single-isotypic Schur formula obtained directly from global
covariance of the averaged packet operator. -/
theorem isotypic_partialTrace_formula_of_global_covariance
    {G : Type*} [Group G] [Nonempty I] [DecidableEq M]
    (ρ : G →* Matrix I I ℂ)
    [CategoryTheory.Simple
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation ρ))]
    (F : Matrix (I × M) (I × M) ℂ)
    (hcomm : ∀ g,
      F * (ρ g ⊗ₖ (1 : Matrix M M ℂ)) =
        (ρ g ⊗ₖ (1 : Matrix M M ℂ)) * F) :
    F = ((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ
      multiplicityPartialTrace F :=
  eq_invDimension_smul_one_kronecker_partialTrace_of_irreducible
    ρ F (coefficientBlock_commutes_of_kronecker_commutes ρ F hcomm)

/-- The normalized identity on a nonempty irreducible coordinate is positive
definite. -/
theorem invDimension_smul_one_posDef [Nonempty I] :
    (((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)).PosDef := by
  have hcard : (0 : ℂ) < (Fintype.card I : ℂ) := by
    norm_cast
    exact Fintype.card_pos_iff.mpr inferInstance
  exact (Matrix.PosDef.one : (1 : Matrix I I ℂ).PosDef).smul
    (inv_pos.mpr hcard)

/-- A normalized single-isotypic block is positive definite exactly when its
multiplicity partial trace is positive definite. -/
theorem invDimension_one_kronecker_posDef_iff [Nonempty I] [DecidableEq M]
    (B : Matrix M M ℂ) :
    ((((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)) ⊗ₖ B).PosDef ↔
      B.PosDef := by
  constructor
  · intro hF
    let i0 : I := Classical.choice inferInstance
    let e : M → I × M := fun a => (i0, a)
    have he : Function.Injective e := fun _ _ h => congrArg Prod.snd h
    have hsub := hF.submatrix he
    have hsubeq :
        ((((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)) ⊗ₖ B).submatrix e e =
          (Fintype.card I : ℂ)⁻¹ • B := by
      ext a b
      simp [e, Matrix.kronecker_apply]
    rw [hsubeq] at hsub
    have hcard : (0 : ℂ) < (Fintype.card I : ℂ) := by
      norm_cast
      exact Fintype.card_pos_iff.mpr inferInstance
    have hscaled := hsub.smul hcard
    simpa [smul_smul, Fintype.card_ne_zero] using hscaled
  · intro hB
    exact (invDimension_smul_one_posDef (I := I)).kronecker hB

/-- Under the exact Schur formula, packet exhaustion (positive definiteness)
is equivalent to positivity of the multiplicity packet. -/
theorem isotypic_posDef_iff_partialTrace_posDef
    [Nonempty I] [DecidableEq M]
    (F : Matrix (I × M) (I × M) ℂ)
    (hformula :
      F = ((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ
        multiplicityPartialTrace F) :
    F.PosDef ↔ (multiplicityPartialTrace F).PosDef := by
  constructor
  · intro hF
    have hnormalized :
        ((((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)) ⊗ₖ
          multiplicityPartialTrace F).PosDef := by
      rw [← hformula]
      exact hF
    exact (invDimension_one_kronecker_posDef_iff (I := I) (M := M)
      (multiplicityPartialTrace F)).mp hnormalized
  · intro hB
    rw [hformula]
    exact (invDimension_one_kronecker_posDef_iff (I := I) (M := M)
      (multiplicityPartialTrace F)).mpr hB

/-- The multiplicity slice of a vector at a fixed irreducible coordinate. -/
def multiplicitySlice (x : I × M → ℂ) (i : I) : M → ℂ :=
  fun a => x (i, a)

/-- Action of the normalized isotypic block on one multiplicity slice. -/
theorem invDimension_one_kronecker_mulVec_apply [Nonempty I] [DecidableEq M]
    (B : Matrix M M ℂ) (x : I × M → ℂ) (i : I) (a : M) :
    (((((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ B) *ᵥ x) (i, a)) =
      (Fintype.card I : ℂ)⁻¹ * (B *ᵥ multiplicitySlice x i) a := by
  simp [Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Matrix.one_apply, multiplicitySlice, ← Finset.univ_product_univ,
    Finset.sum_product, Finset.mul_sum, mul_assoc]

/-- Exact kernel/range-support law for a normalized isotypic block. -/
theorem invDimension_one_kronecker_mulVec_eq_zero_iff
    [Nonempty I] [DecidableEq M]
    (B : Matrix M M ℂ) (x : I × M → ℂ) :
    ((((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ B) *ᵥ x = 0) ↔
      ∀ i, B *ᵥ multiplicitySlice x i = 0 := by
  have hscale : (Fintype.card I : ℂ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  constructor
  · intro hx i
    funext a
    have ha := congrFun hx (i, a)
    rw [invDimension_one_kronecker_mulVec_apply B x i a] at ha
    simpa [hscale] using ha
  · intro hx
    funext p
    rcases p with ⟨i, a⟩
    rw [invDimension_one_kronecker_mulVec_apply B x i a, hx i]
    simp

/-- Exact range identification: the range of `d⁻¹ I ⊗ B` consists precisely
of the vectors whose every irreducible-coordinate slice belongs to `Ran B`. -/
theorem range_invDimension_one_kronecker_mulVec
    [Nonempty I] [DecidableEq M]
    (B : Matrix M M ℂ) :
    Set.range (fun x : I × M → ℂ =>
      ((((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ B) *ᵥ x)) =
      {x | ∀ i, multiplicitySlice x i ∈ LinearMap.range B.mulVecLin} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩ i
    refine ⟨(Fintype.card I : ℂ)⁻¹ • multiplicitySlice z i, ?_⟩
    rw [map_smul]
    funext a
    exact (invDimension_one_kronecker_mulVec_apply B z i a).symm
  · intro hx
    choose z hz using hx
    let y : I × M → ℂ := fun p => (Fintype.card I : ℂ) * z p.1 p.2
    refine ⟨y, ?_⟩
    funext p
    rcases p with ⟨i, a⟩
    change (((((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ B) *ᵥ y)
      (i, a)) = x (i, a)
    rw [invDimension_one_kronecker_mulVec_apply B y i a]
    have hslice : multiplicitySlice y i =
        (Fintype.card I : ℂ) • z i := by
      funext b
      rfl
    rw [hslice, Matrix.mulVec_smul]
    have hza := congrFun (hz i) a
    change (B *ᵥ z i) a = x (i, a) at hza
    rw [Pi.smul_apply, hza]
    change (Fintype.card I : ℂ)⁻¹ *
      ((Fintype.card I : ℂ) * x (i, a)) = x (i, a)
    field_simp

/-- Embed a multiplicity vector into one irreducible coordinate. -/
def embeddedMultiplicityDirection
    (i0 : I) (y : M → ℂ) : I × M → ℂ :=
  fun p => if p.1 = i0 then y p.2 else 0

/-- A nonzero vector in the kernel of the multiplicity packet produces an
explicit nonzero direction missed by the full isotypic packet. -/
theorem singular_multiplicity_gives_missed_direction
    [Nonempty I] [DecidableEq M]
    (B : Matrix M M ℂ) (i0 : I) (y : M → ℂ)
    (hy : y ≠ 0) (hBy : B *ᵥ y = 0) :
    embeddedMultiplicityDirection i0 y ≠ 0 ∧
      ((((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ B) *ᵥ
        embeddedMultiplicityDirection i0 y = 0) := by
  constructor
  · intro hzero
    apply hy
    funext a
    have ha := congrFun hzero (i0, a)
    simpa [embeddedMultiplicityDirection] using ha
  · apply (invDimension_one_kronecker_mulVec_eq_zero_iff B _).mpr
    intro i
    by_cases hi : i = i0
    · subst i
      have hs : multiplicitySlice (embeddedMultiplicityDirection i0 y) i0 = y := by
        funext a
        simp [multiplicitySlice, embeddedMultiplicityDirection]
      rw [hs, hBy]
    · have hs : multiplicitySlice (embeddedMultiplicityDirection i0 y) i = 0 := by
        funext a
        simp [multiplicitySlice, embeddedMultiplicityDirection, hi]
      rw [hs]
      simp

/-- Any Loewner floor for the multiplicity packet transfers with the exact
`1 / dim(V)` normalization to the isotypic packet. -/
theorem multiplicity_floor_transfers_to_isotypic
    [Nonempty I] [DecidableEq M]
    (B : Matrix M M ℂ) (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hfloor : (B - (beta : ℂ) • (1 : Matrix M M ℂ)).PosSemidef) :
    (((((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)) ⊗ₖ B) -
      ((beta / Fintype.card I : ℝ) : ℂ) •
        (1 : Matrix (I × M) (I × M) ℂ)).PosSemidef := by
  have hleft :
      (((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)).PosSemidef :=
    (invDimension_smul_one_posDef (I := I)).posSemidef
  have hk := hleft.kronecker hfloor
  have heq :
      ((((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)) ⊗ₖ B) -
          ((beta / Fintype.card I : ℝ) : ℂ) •
            (1 : Matrix (I × M) (I × M) ℂ) =
        (((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ)) ⊗ₖ
          (B - (beta : ℂ) • (1 : Matrix M M ℂ)) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      by_cases hab : a = b
      · subst b
        simp [Matrix.kronecker_apply, Matrix.one_apply, div_eq_mul_inv,
          Fintype.card_ne_zero]
        ring
      · simp [Matrix.kronecker_apply, Matrix.one_apply, hab]
    · simp [Matrix.kronecker_apply, Matrix.one_apply, hij]
  rw [heq]
  exact hk

end IsotypicPartialTrace
end NCG
