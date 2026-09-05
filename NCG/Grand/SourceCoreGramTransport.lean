/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Quantitative history-Gram transport
  (`cor:source-core-Gram-transport`, Gran-Tensor manuscript)

* `source_core_gram_transport`:
  (1) the exact Gram-difference expansion
      `B_NᴴB_N − B_AᴴB_A = EᴴB_A + B_NᴴE` for `E = B_N − B_A`;
  (2) the boxed quantitative bound
      `‖B_NᴴB_N − B_AᴴB_A‖ ≤ (‖B_N‖ + ‖B_A‖)·‖E‖` in the
      operator C*-norm.

Rendering disclosed: the semigroup-defect source of `η_t`
(Duhamel) is the proved `source_core` semigroup layer; the
Schur-residual bounds and the cutoff `G_A ⪯ G_N + o(1)I`
order transport are the manuscript's spectral reading of the
proved norm bound (`‖M‖ ≤ δ` with `M` hermitian gives
`M ⪯ δI`), applied along the declared uniform cutoff family.
-/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- `cor:source-core-Gram-transport`. -/
theorem source_core_gram_transport {h k : Type*} [Fintype h]
    [Fintype k] [DecidableEq k]
    (BN BA : Matrix h k ℂ) :
    -- (1) the exact Gram-difference expansion
    (BNᴴ * BN - BAᴴ * BA
      = (BN - BA)ᴴ * BA + BNᴴ * (BN - BA))
    -- (2) the boxed quantitative bound
    ∧ ‖BNᴴ * BN - BAᴴ * BA‖
        ≤ (‖BN‖ + ‖BA‖) * ‖BN - BA‖ := by
  classical
  have hexp : BNᴴ * BN - BAᴴ * BA
      = (BN - BA)ᴴ * BA + BNᴴ * (BN - BA) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul,
      Matrix.mul_sub]
    abel
  refine ⟨hexp, ?_⟩
  rw [hexp]
  calc ‖(BN - BA)ᴴ * BA + BNᴴ * (BN - BA)‖
      ≤ ‖(BN - BA)ᴴ * BA‖ + ‖BNᴴ * (BN - BA)‖ :=
        norm_add_le _ _
    _ ≤ ‖(BN - BA)ᴴ‖ * ‖BA‖ + ‖BNᴴ‖ * ‖BN - BA‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = (‖BN‖ + ‖BA‖) * ‖BN - BA‖ := by
        rw [Matrix.l2_opNorm_conjTranspose,
          Matrix.l2_opNorm_conjTranspose]
        ring

end NCG
