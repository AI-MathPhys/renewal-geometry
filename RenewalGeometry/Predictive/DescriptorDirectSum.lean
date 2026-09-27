/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.DescriptorRealization
import RenewalGeometry.Analysis.BlockDiagonalL2Prod

/-!
# The direct sum of descriptor realizations and the primary realization of a general `Q`

Paper `predictive_spectral_geometry`, `cor:supp-all-rational` (partial: the existence direction).

* `DescriptorRealization.prod`: the direct sum `D₁ ⊕ D₂` of two regular Pontryagin descriptor
  realizations with a common regular point, on the Hilbert direct sum `WithLp 2 (N₁ × N₂)`, with
  block-diagonal pencil and Gram operator and column source; its transfer function is the sum of
  the transfer functions at every common regular point (`prod_transfer`), and its indefinite form
  is the orthogonal sum of the forms (`prod_form`: the two blocks are `J`-orthogonal).
* `FiniteRationalHermitianData.descriptor`: the **canonical primary descriptor realization** of a
  general finite rational Hermitian `Q = P + Q₀` — the direct sum of the canonical nilpotent
  infinity chain of the jet `P` and the canonical minimal Pontryagin realization of the strictly
  proper part `Q₀` — and `descriptor_transfer`: it realizes `Q`, `Γ* J (A - z E)⁻¹ Γ = Q(z)`
  for `‖A_{Q₀}‖ < ‖z‖`.
-/

open scoped InnerProductSpace InnerProduct
open Module

noncomputable section

namespace RenewalGeometry

namespace DescriptorRealization

variable {H N₁ N₂ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N₁] [InnerProductSpace ℂ N₁] [CompleteSpace N₁]
  [NormedAddCommGroup N₂] [InnerProductSpace ℂ N₂] [CompleteSpace N₂]

open L2Prod

/-- **The direct sum of two descriptor realizations** with a common regular point: block-diagonal
pencil `(E₁ ⊕ E₂, A₁ ⊕ A₂)`, Gram operator `J₁ ⊕ J₂` and column source `(Γ₁, Γ₂)` on the Hilbert
direct sum `WithLp 2 (N₁ × N₂)`. -/
def prod (D₁ : DescriptorRealization H N₁) (D₂ : DescriptorRealization H N₂)
    (hreg : ∃ z : ℂ, IsUnit (D₁.A - z • D₁.E) ∧ IsUnit (D₂.A - z • D₂.E)) :
    DescriptorRealization H (WithLp 2 (N₁ × N₂)) where
  E := blockDiag D₁.E D₂.E
  A := blockDiag D₁.A D₂.A
  Γ := prodSource D₁.Γ D₂.Γ
  J := blockDiag D₁.J D₂.J
  J_selfAdjoint := isSelfAdjoint_blockDiag _ _ D₁.J_selfAdjoint D₂.J_selfAdjoint
  J_isUnit := isUnit_blockDiag _ _ D₁.J_isUnit D₂.J_isUnit
  J_mul_A := by rw [blockDiag_mul, star_blockDiag, blockDiag_mul, D₁.J_mul_A, D₂.J_mul_A]
  J_mul_E := by rw [blockDiag_mul, star_blockDiag, blockDiag_mul, D₁.J_mul_E, D₂.J_mul_E]
  regular := by
    obtain ⟨z, h₁, h₂⟩ := hreg
    exact ⟨z, by rw [blockDiag_smul, blockDiag_sub]; exact isUnit_blockDiag _ _ h₁ h₂⟩

variable (D₁ : DescriptorRealization H N₁) (D₂ : DescriptorRealization H N₂)
  (hreg : ∃ z : ℂ, IsUnit (D₁.A - z • D₁.E) ∧ IsUnit (D₂.A - z • D₂.E))

/-- **The transfer function of a direct sum is the sum of the transfer functions** at every common
regular point. -/
theorem prod_transfer {z : ℂ} (h₁ : IsUnit (D₁.A - z • D₁.E)) (h₂ : IsUnit (D₂.A - z • D₂.E)) :
    (D₁.prod D₂ hreg).transfer z = D₁.transfer z + D₂.transfer z := by
  ext h
  simp only [transfer, prod, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rw [blockDiag_smul, blockDiag_sub, inverse_blockDiag _ _ h₁ h₂, blockDiag_prodSource_apply,
    blockDiag_prodSource_apply, adjoint_prodSource_apply]
  rfl

/-- The indefinite form of a direct sum is the orthogonal sum of the forms: the two blocks are
`J`-orthogonal. -/
theorem prod_form (x y : WithLp 2 (N₁ × N₂)) :
    (D₁.prod D₂ hreg).form x y = D₁.form x.fst y.fst + D₂.form x.snd y.snd := by
  simp only [form, prod, WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    blockDiag_apply_fst, blockDiag_apply_snd]

end DescriptorRealization

/-! ## The canonical primary descriptor realization of a general finite rational Hermitian `Q` -/

namespace FiniteRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : FiniteRationalHermitianData H)

/-- The nilpotent infinity-chain pencil `1 - z A_P` is invertible for every `z`. -/
theorem isUnit_infinityChain_pencil (z : ℂ) :
    IsUnit (Q.jet.infinityChain.A - z • Q.jet.infinityChain.E) := by
  show IsUnit (1 - z • Q.jet.canonical.A)
  exact IsNilpotent.isUnit_one_sub
    ⟨Q.deg + 1, by rw [smul_pow, Q.jet.canonical_A_pow_eq_zero Q.jet_isJet, smul_zero]⟩

/-- The pencil `A_{Q₀} - z` of the canonical realization of the proper part is invertible for
`‖A_{Q₀}‖ < ‖z‖`. -/
theorem isUnit_canonical_pencil {z : ℂ} (hz : ‖Q.proper.canonical.A‖ < ‖z‖) :
    IsUnit (Q.proper.canonical.toDescriptor.A - z • Q.proper.canonical.toDescriptor.E) := by
  show IsUnit (Q.proper.canonical.A - z • 1)
  rw [← Algebra.algebraMap_eq_smul_one]
  exact isUnit_sub_algebraMap_of_norm_lt _ hz

theorem exists_common_regular :
    ∃ z : ℂ, IsUnit (Q.jet.infinityChain.A - z • Q.jet.infinityChain.E) ∧
      IsUnit (Q.proper.canonical.toDescriptor.A - z • Q.proper.canonical.toDescriptor.E) := by
  obtain ⟨t, ht⟩ := exists_gt ‖Q.proper.canonical.A‖
  refine ⟨t, Q.isUnit_infinityChain_pencil t, Q.isUnit_canonical_pencil ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt (norm_nonneg _) ht)]
  exact ht

/-- **The canonical primary descriptor realization** of `Q = P + Q₀`: the direct sum of the
canonical nilpotent infinity chain of the jet `P` and the canonical minimal Pontryagin realization
of the strictly proper part `Q₀` (`cor:supp-all-rational`, "their primary direct sum"). -/
def descriptor : DescriptorRealization H (WithLp 2 (Q.jet.Carrier × Q.proper.Carrier)) :=
  Q.jet.infinityChain.prod Q.proper.canonical.toDescriptor Q.exists_common_regular

/-- **The canonical primary descriptor realization realizes `Q`**:
`Γ* J (A - z E)⁻¹ Γ = P(z) + Q₀(z)` for `‖A_{Q₀}‖ < ‖z‖` (`cor:supp-all-rational`, existence
direction of `eq:supp-all-rational-equivalence`). -/
theorem descriptor_transfer {z : ℂ} (hz : ‖Q.proper.canonical.A‖ < ‖z‖) :
    Q.descriptor.transfer z = Q.toFun z := by
  rw [descriptor, DescriptorRealization.prod_transfer _ _ _ (Q.isUnit_infinityChain_pencil z)
    (Q.isUnit_canonical_pencil hz), Q.toFun_eq_infinityChain_add_canonical hz,
    PontryaginRealization.toDescriptor_transfer]

/-- The state dimension of the canonical primary descriptor realization is the sum of the McMillan
degrees of the jet and of the strictly proper part. -/
theorem finrank_descriptor_state :
    finrank ℂ (WithLp 2 (Q.jet.Carrier × Q.proper.Carrier)) =
      Q.jet.mcMillanDegree + Q.proper.mcMillanDegree := by
  rw [(WithLp.linearEquiv 2 ℂ (Q.jet.Carrier × Q.proper.Carrier)).finrank_eq, finrank_prod,
    Q.jet.finrank_carrier, Q.proper.finrank_carrier]

end FiniteRationalHermitianData

end RenewalGeometry

end
