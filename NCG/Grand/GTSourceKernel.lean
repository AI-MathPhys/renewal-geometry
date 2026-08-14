/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Source-minimal kernel realization and uniqueness
  (`thm:GT-source-kernel-realization`,
  Gran-Tensor manuscript)

* `gt_source_kernel_realization`: for a positive block
  kernel `𝕂 ⪰ 0`,
  (i) the canonical square-root synthesis `S = √𝕂`
      realizes it exactly: `𝕂 = S*S` (the SK.1 form, with
      the block `K_{ωη}` the Gram of the `ω` and `η`
      profile columns);
  (ii) every realization `𝕂 = S*S` on a carrier `c` has
      `rank 𝕂 ≤ dim c` — the least possible carrier
      dimension is `rank 𝕂`; and
  (iii) the canonical realization attains it:
      `rank √𝕂 = rank 𝕂`.

* `gt_source_kernel_scale_invariance`: the kernel does not
  determine the probabilities — rescaling any single
  profile block by a unit phase (or compensated positive
  rescale) leaves every Gram `S*S` unchanged when the
  synthesis is replaced by `US` with `U*U = 1`.

The uniqueness clause — any two source-minimal
realizations are related by one global unitary acting
simultaneously on every profile — is the manuscript's
polar-isometry extension (the repo's
`NCG.polar_decomposition` layer); the `ν_ω` rescaling
display is its bookkeeping.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false in
/-- `thm:GT-source-kernel-realization` (existence, the
rank floor, and its attainment). -/
theorem gt_source_kernel_realization {n : Type} [Fintype n]
    [DecidableEq n] (K : Matrix n n ℂ)
    (hK : K.PosSemidef) :
    -- (i) the canonical square-root realization
    (K = (CFC.sqrt K)ᴴ * CFC.sqrt K)
    -- (ii) every realization needs at least rank 𝕂
    -- carrier dimensions
    ∧ (∀ {c : Type} [Fintype c] (S : Matrix c n ℂ),
        K = Sᴴ * S → K.rank ≤ Fintype.card c)
    -- (iii) the canonical realization attains the floor
    ∧ (CFC.sqrt K).rank = K.rank := by
    have hsq : (CFC.sqrt K)ᴴ * CFC.sqrt K = K := by
      rw [sqrt_isHermitian, sqrt_mul_self_eq K hK]
    refine ⟨hsq.symm, ?_, ?_⟩
    · intro c _ S hS
      rw [hS, Matrix.rank_conjTranspose_mul_self]
      exact S.rank_le_card_height
    · rw [← Matrix.rank_conjTranspose_mul_self
        (CFC.sqrt K), hsq]

/-- `thm:GT-source-kernel-realization` (unitary gauge
freedom of the synthesis). -/
theorem gt_source_kernel_scale_invariance {c n : Type}
    [Fintype c] [DecidableEq c]
    (S : Matrix c n ℂ) (U : Matrix c c ℂ)
    (hU : Uᴴ * U = 1) :
    (U * S)ᴴ * (U * S) = Sᴴ * S := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ U S, hU, Matrix.one_mul]

end NCG
