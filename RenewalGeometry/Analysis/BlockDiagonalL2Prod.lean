/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Block-diagonal operators on the Hilbert direct sum `WithLp 2 (E × F)`

Infrastructure for `cor:supp-all-rational` of `papers/predictive_spectral_geometry` (the direct sum
of descriptor realizations).

* `blockDiag S T : WithLp 2 (E × F) →L WithLp 2 (E × F)` is the block-diagonal operator
  `(x, y) ↦ (S x, T y)`.  It is multiplicative, additive, compatible with scalars and the identity
  (`blockDiag_mul`, `blockDiag_add`, `blockDiag_sub`, `blockDiag_smul`, `blockDiag_one`), its
  adjoint is the block diagonal of the adjoints (`adjoint_blockDiag`), and it is invertible with
  block-diagonal inverse when both blocks are (`isUnit_blockDiag`, `inverse_blockDiag`).
* `prodSource Γ₁ Γ₂ : H →L WithLp 2 (E × F)` is the column `h ↦ (Γ₁ h, Γ₂ h)`, with adjoint
  `(x, y) ↦ Γ₁* x + Γ₂* y` (`adjoint_prodSource_apply`).
-/

open scoped InnerProductSpace InnerProduct

noncomputable section

namespace RenewalGeometry
namespace L2Prod

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The block-diagonal operator `(x, y) ↦ (S x, T y)` on `WithLp 2 (E × F)`. -/
def blockDiag (S : E →L[𝕜] E) (T : F →L[𝕜] F) : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm : E × F →L[𝕜] WithLp 2 (E × F)) ∘L
    (S.prodMap T) ∘L (WithLp.prodContinuousLinearEquiv 2 𝕜 E F : WithLp 2 (E × F) →L[𝕜] E × F)

variable (S S' : E →L[𝕜] E) (T T' : F →L[𝕜] F)

theorem blockDiag_apply (x : WithLp 2 (E × F)) :
    blockDiag S T x = WithLp.toLp 2 (S x.fst, T x.snd) := rfl

@[simp] theorem blockDiag_apply_fst (x : WithLp 2 (E × F)) :
    (blockDiag S T x).fst = S x.fst := rfl

@[simp] theorem blockDiag_apply_snd (x : WithLp 2 (E × F)) :
    (blockDiag S T x).snd = T x.snd := rfl

theorem blockDiag_mul : blockDiag S T * blockDiag S' T' = blockDiag (S * S') (T * T') := by
  ext x <;> rfl

theorem blockDiag_add : blockDiag S T + blockDiag S' T' = blockDiag (S + S') (T + T') := by
  ext x <;> rfl

theorem blockDiag_sub : blockDiag S T - blockDiag S' T' = blockDiag (S - S') (T - T') := by
  ext x <;> rfl

theorem blockDiag_smul (c : 𝕜) : c • blockDiag S T = blockDiag (c • S) (c • T) := by
  ext x <;> rfl

theorem blockDiag_one : blockDiag (1 : E →L[𝕜] E) (1 : F →L[𝕜] F) = 1 := by
  ext x <;> rfl

theorem blockDiag_zero : blockDiag (0 : E →L[𝕜] E) (0 : F →L[𝕜] F) = 0 := by
  ext x <;> rfl

theorem blockDiag_algebraMap (c : 𝕜) :
    blockDiag (algebraMap 𝕜 (E →L[𝕜] E) c) (algebraMap 𝕜 (F →L[𝕜] F) c) =
      algebraMap 𝕜 (WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) c := by
  simp only [Algebra.algebraMap_eq_smul_one, ← blockDiag_smul, blockDiag_one]

theorem blockDiag_pow (n : ℕ) : blockDiag S T ^ n = blockDiag (S ^ n) (T ^ n) := by
  induction n with
  | zero => simp [blockDiag_one]
  | succ n ih => rw [pow_succ, ih, blockDiag_mul, ← pow_succ, ← pow_succ]

section Adjoint

variable [CompleteSpace E] [CompleteSpace F]

/-- The adjoint of a block-diagonal operator is block diagonal. -/
theorem adjoint_blockDiag :
    ContinuousLinearMap.adjoint (blockDiag S T) =
      blockDiag (ContinuousLinearMap.adjoint S) (ContinuousLinearMap.adjoint T) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, blockDiag_apply_fst,
    blockDiag_apply_snd, ContinuousLinearMap.adjoint_inner_left]

theorem star_blockDiag : star (blockDiag S T) = blockDiag (star S) (star T) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_blockDiag]

theorem isSelfAdjoint_blockDiag (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (blockDiag S T) := by
  rw [IsSelfAdjoint, star_blockDiag, hS.star_eq, hT.star_eq]

end Adjoint

theorem isUnit_blockDiag (hS : IsUnit S) (hT : IsUnit T) : IsUnit (blockDiag S T) := by
  refine ⟨⟨blockDiag S T, blockDiag (Ring.inverse S) (Ring.inverse T), ?_, ?_⟩, rfl⟩
  · rw [blockDiag_mul, Ring.mul_inverse_cancel S hS, Ring.mul_inverse_cancel T hT, blockDiag_one]
  · rw [blockDiag_mul, Ring.inverse_mul_cancel S hS, Ring.inverse_mul_cancel T hT, blockDiag_one]

theorem inverse_blockDiag (hS : IsUnit S) (hT : IsUnit T) :
    Ring.inverse (blockDiag S T) = blockDiag (Ring.inverse S) (Ring.inverse T) := by
  let u : (WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F))ˣ :=
    ⟨blockDiag S T, blockDiag (Ring.inverse S) (Ring.inverse T),
      by rw [blockDiag_mul, Ring.mul_inverse_cancel S hS, Ring.mul_inverse_cancel T hT,
        blockDiag_one],
      by rw [blockDiag_mul, Ring.inverse_mul_cancel S hS, Ring.inverse_mul_cancel T hT,
        blockDiag_one]⟩
  exact Ring.inverse_unit u

/-! ## Column sources -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The column source `h ↦ (Γ₁ h, Γ₂ h)`. -/
def prodSource (Γ₁ : H →L[𝕜] E) (Γ₂ : H →L[𝕜] F) : H →L[𝕜] WithLp 2 (E × F) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm : E × F →L[𝕜] WithLp 2 (E × F)) ∘L Γ₁.prod Γ₂

variable (Γ₁ : H →L[𝕜] E) (Γ₂ : H →L[𝕜] F)

theorem prodSource_apply (h : H) : prodSource Γ₁ Γ₂ h = WithLp.toLp 2 (Γ₁ h, Γ₂ h) := rfl

@[simp] theorem prodSource_apply_fst (h : H) : (prodSource Γ₁ Γ₂ h).fst = Γ₁ h := rfl

@[simp] theorem prodSource_apply_snd (h : H) : (prodSource Γ₁ Γ₂ h).snd = Γ₂ h := rfl

theorem blockDiag_comp_prodSource :
    blockDiag S T ∘L prodSource Γ₁ Γ₂ = prodSource (S ∘L Γ₁) (T ∘L Γ₂) := by
  ext h <;> rfl

theorem blockDiag_prodSource_apply (h : H) :
    blockDiag S T (prodSource Γ₁ Γ₂ h) = prodSource (S ∘L Γ₁) (T ∘L Γ₂) h := rfl

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace H]

/-- The adjoint of the column source is the row `(x, y) ↦ Γ₁* x + Γ₂* y`. -/
theorem adjoint_prodSource_apply (y : WithLp 2 (E × F)) :
    ContinuousLinearMap.adjoint (prodSource Γ₁ Γ₂) y =
      ContinuousLinearMap.adjoint Γ₁ y.fst + ContinuousLinearMap.adjoint Γ₂ y.snd := by
  apply ext_inner_left 𝕜
  intro h
  rw [ContinuousLinearMap.adjoint_inner_right, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, prodSource_apply_fst,
    prodSource_apply_snd]

/-! ## Block-diagonal linear equivalences -/

section Equiv

variable {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

/-- The block-diagonal linear equivalence `(x, y) ↦ (S₁ x, S₂ y)`. -/
def blockEquiv (S₁ : E ≃ₗ[𝕜] E') (S₂ : F ≃ₗ[𝕜] F') :
    WithLp 2 (E × F) ≃ₗ[𝕜] WithLp 2 (E' × F') :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).trans
    ((S₁.prodCongr S₂).trans (WithLp.linearEquiv 2 𝕜 (E' × F')).symm)

variable (S₁ : E ≃ₗ[𝕜] E') (S₂ : F ≃ₗ[𝕜] F')

theorem blockEquiv_apply (x : WithLp 2 (E × F)) :
    blockEquiv S₁ S₂ x = WithLp.toLp 2 (S₁ x.fst, S₂ x.snd) := rfl

@[simp] theorem blockEquiv_apply_fst (x : WithLp 2 (E × F)) :
    (blockEquiv S₁ S₂ x).fst = S₁ x.fst := rfl

@[simp] theorem blockEquiv_apply_snd (x : WithLp 2 (E × F)) :
    (blockEquiv S₁ S₂ x).snd = S₂ x.snd := rfl

end Equiv

end L2Prod
end RenewalGeometry

end
