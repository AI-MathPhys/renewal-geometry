/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Symmetric and alternating sectors are independent

**Proposition `prop:symmetric-alternating-independence`**: the isotropic
second moment lives in `Sym²V_sp` while revision interference lives in
`⋀²V_sp`, and these are inequivalent tensor sectors — no rank-selection
condition transfers from one to the other.

Formal core: over `ℝ` the symmetric and antisymmetric matrix sectors
intersect trivially (`NCG.symm_inter_antisymm_eq_zero`), every matrix
splits uniquely into its symmetric and antisymmetric parts
(`NCG.symm_add_antisymm`), and for rank `≥ 2` both sectors are nonzero
(`NCG.exists_symm_ne_zero`, `NCG.exists_antisymm_ne_zero`) — so neither
sector is contained in, or spans, the other. -/

namespace NCG

open Matrix

variable {n : ℕ}

/-- **Proposition `prop:symmetric-alternating-independence`**
(intersection): a matrix that is both symmetric and antisymmetric
vanishes — `Sym² ∩ ⋀² = 0` over `ℝ`. -/
theorem symm_inter_antisymm_eq_zero (M : Matrix (Fin n) (Fin n) ℝ)
    (hsym : M.IsSymm) (hanti : Mᵀ = -M) : M = 0 := by
  have h : M = -M := by
    conv_lhs => rw [← hsym]
    exact hanti
  ext i j
  rw [Matrix.zero_apply]
  have hij : M i j = (-M) i j := by rw [← h]
  rw [Matrix.neg_apply] at hij
  linarith

/-- Every matrix splits into its symmetric and antisymmetric parts:
the two sectors span the tensor square. -/
theorem symm_add_antisymm (M : Matrix (Fin n) (Fin n) ℝ) :
    M = (1/2 : ℝ) • (M + Mᵀ) + (1/2 : ℝ) • (M - Mᵀ) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]
  ring

/-- The symmetric part is symmetric. -/
theorem symm_part_isSymm (M : Matrix (Fin n) (Fin n) ℝ) :
    ((1/2 : ℝ) • (M + Mᵀ)).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose,
    add_comm]

/-- The antisymmetric part is antisymmetric. -/
theorem antisymm_part_antisymm (M : Matrix (Fin n) (Fin n) ℝ) :
    ((1/2 : ℝ) • (M - Mᵀ))ᵀ = -((1/2 : ℝ) • (M - Mᵀ)) := by
  rw [Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_transpose, ← smul_neg, neg_sub]

/-- For `n ≥ 1` the symmetric sector is nonzero (the isotropic second
moment `(1/d)·I` is a nonzero symmetric tensor). -/
theorem exists_symm_ne_zero (hn : 0 < n) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm ∧ M ≠ 0 := by
  refine ⟨1, Matrix.transpose_one, fun h => ?_⟩
  have h00 : (1 : Matrix (Fin n) (Fin n) ℝ) ⟨0, hn⟩ ⟨0, hn⟩
      = (0 : Matrix (Fin n) (Fin n) ℝ) ⟨0, hn⟩ ⟨0, hn⟩ := by rw [h]
  rw [Matrix.one_apply_eq, Matrix.zero_apply] at h00
  exact one_ne_zero h00

/-- For `n ≥ 2` the antisymmetric sector is nonzero (revision
interference is a nonzero bivector). -/
theorem exists_antisymm_ne_zero (hn : 2 ≤ n) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, Mᵀ = -M ∧ M ≠ 0 := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have h0 : i0 ≠ i1 := by
    simp [hi0, hi1, Fin.ext_iff]
  refine ⟨Matrix.single i0 i1 1 - Matrix.single i1 i0 1, ?_, fun h => ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_single,
      Matrix.transpose_single, neg_sub]
  · have h01 : ((Matrix.single i0 i1 (1:ℝ)
        - Matrix.single i1 i0 1 : Matrix (Fin n) (Fin n) ℝ)) i0 i1
        = (0 : Matrix (Fin n) (Fin n) ℝ) i0 i1 := by rw [h]
    rw [Matrix.sub_apply, Matrix.single_apply_same, Matrix.zero_apply,
      Matrix.single_apply_of_row_ne (Ne.symm h0)] at h01
    norm_num at h01

end NCG
