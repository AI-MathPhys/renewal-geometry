/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The direct-sum firewall and the anchored port tensor
  (`thm:direct-sum-firewall`, `prop:anchor`, arithmetic monograph)

* `dirsum_posSemidef` — any positive blocks assemble to a positive
  direct sum `T₁ ⊕ T₂ ⪰ 0`;
* `dirsum_compression` / `dirsum_firewall` — the compression of
  `T₁ ⊕ T₂` to the first summand equals `T₁` and is independent of
  `T₂`: coercivity of one typed block is compatible with an
  arbitrary PSD complement, so no conclusion about the second block
  follows from the first compression alone
  (`thm:direct-sum-firewall`);
* `anchor_posSemidef` / `anchor_rank_le_one` / `anchor_recovery` —
  the anchored bi-reflected port tensor `Φ Φ*` is PSD of rank at
  most one, and its cross-entry against the unit anchor recovers
  every port value (`prop:anchor`).
-/

namespace NCG.ArithFirewall

open Matrix

open scoped ComplexOrder

noncomputable section

variable {d₁ d₂ ι : Type*} [Fintype d₁] [Fintype d₂] [Fintype ι]

omit [Fintype d₁] [Fintype d₂] in
/-- `thm:direct-sum-firewall` (assembly): `T₁ ⪰ 0` and any `T₂ ⪰ 0`
give `T₁ ⊕ T₂ ⪰ 0` — including a singular or zero second block. -/
theorem dirsum_posSemidef [Finite d₁] [Finite d₂]
    {T₁ : Matrix d₁ d₁ ℂ} {T₂ : Matrix d₂ d₂ ℂ}
    (h₁ : T₁.PosSemidef) (h₂ : T₂.PosSemidef) :
    (Matrix.fromBlocks T₁ 0 0 T₂).PosSemidef := by
  haveI := Fintype.ofFinite d₁
  haveI := Fintype.ofFinite d₂
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change (Matrix.fromBlocks T₁ 0 0 T₂)ᴴ = _
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_zero, h₁.1, h₂.1]
  · intro v
    obtain ⟨x, y, rfl⟩ : ∃ x y, v = Sum.elim x y :=
      ⟨v ∘ Sum.inl, v ∘ Sum.inr, (Sum.elim_comp_inl_inr v).symm⟩
    have hx := h₁.dotProduct_mulVec_nonneg x
    have hy := h₂.dotProduct_mulVec_nonneg y
    have hstar : star (Sum.elim x y) = Sum.elim (star x) (star y) := by
      funext i
      cases i <;> rfl
    rw [Matrix.fromBlocks_mulVec, hstar, sumElim_dotProduct_sumElim]
    simpa using add_nonneg hx hy

omit [Fintype d₁] [Fintype d₂] in
/-- `thm:direct-sum-firewall` (compression): the compression of
`T₁ ⊕ T₂` to the first summand is exactly `T₁`. -/
theorem dirsum_compression (T₁ : Matrix d₁ d₁ ℂ) (T₂ : Matrix d₂ d₂ ℂ) :
    (Matrix.fromBlocks T₁ 0 0 T₂).toBlocks₁₁ = T₁ :=
  Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

omit [Fintype d₁] [Fintype d₂] in
/-- `thm:direct-sum-firewall` (firewall): the first compression is
independent of the second block, so no coercive statement about the
compression to `H₁` constrains `T₂`. -/
theorem dirsum_firewall (T₁ : Matrix d₁ d₁ ℂ)
    (T₂ T₂' : Matrix d₂ d₂ ℂ) :
    (Matrix.fromBlocks T₁ 0 0 T₂).toBlocks₁₁
      = (Matrix.fromBlocks T₁ 0 0 T₂').toBlocks₁₁ := by
  rw [dirsum_compression, dirsum_compression]

/-! ## The anchored bi-reflected port tensor -/

/-- The anchored port vector: port values `F` extended by the unit
anchor coordinate. -/
def anchored (F : ι → ℂ) : ι ⊕ Unit → ℂ :=
  Sum.elim F fun _ => 1

/-- The anchored bi-reflected affine port tensor `Φ Φ*`. -/
def portTensor (F : ι → ℂ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ :=
  Matrix.vecMulVec (anchored F) (star (anchored F))

omit [Fintype ι] in
/-- `prop:anchor` (positivity): `Φ Φ* ⪰ 0`. -/
theorem anchor_posSemidef [Finite ι] (F : ι → ℂ) :
    (portTensor F).PosSemidef := by
  haveI := Fintype.ofFinite ι
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- `prop:anchor` (rank): the port tensor has rank at most one. -/
theorem anchor_rank_le_one (F : ι → ℂ) : (portTensor F).rank ≤ 1 := by
  rw [portTensor, Matrix.vecMulVec_eq Unit]
  calc (Matrix.replicateCol Unit (anchored F)
        * Matrix.replicateRow Unit (star (anchored F))).rank
      ≤ (Matrix.replicateCol Unit (anchored F)).rank :=
        Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card Unit := Matrix.rank_le_card_width _
    _ = 1 := Fintype.card_unit

omit [Fintype ι] in
/-- `prop:anchor` (anchor recovery): the cross-entry against the
anchor recovers each port value. -/
theorem anchor_recovery (F : ι → ℂ) (α : ι) :
    portTensor F (Sum.inl α) (Sum.inr ()) = F α := by
  simp [portTensor, Matrix.vecMulVec_apply, anchored]

end

end NCG.ArithFirewall
