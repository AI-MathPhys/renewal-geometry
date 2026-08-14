/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical source fusion and occurrence innovation
  (`thm:GT-source-fusion`, Gran-Tensor manuscript)

* `gt_source_fusion`: for an isometric fusion `Γ`
  (`Γ*Γ = 1`) and the fused synthesis `S`,
  (i) the boxed occurrence innovation
      `𝕀^fus = S*(1-ΓΓ*)S ⪰ 0` (the leakage projection
      `1-ΓΓ*` is a hermitian idempotent, so the innovation
      is a Gram);
  (ii) it vanishes exactly when `(1-ΓΓ*)S = 0` — and
      vanishes identically exactly when `Γ` is unitary
      (`ΓΓ* = 1`), rendered by the two implications;
  (iii) the boxed dimension count: the leakage trace is
      `Tr(1-ΓΓ*) = dim H_{r+s} - dim(H_r ⊗ H_s)` — for a
      hermitian idempotent this is its rank, the number of
      genuinely new multi-occurrence directions.

The construction of `Γ` from the vanishing metric fusion
defect (`Γ(S_r x ⊗ S_s y) = S_{r+s}m(x ⊗ y)` on pure
tensors, unique by density of the spanned range) is the
manuscript's GNS layer.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false in
/-- `thm:GT-source-fusion` (innovation positivity,
vanishing, and the dimension count). -/
theorem gt_source_fusion {N T k : Type} [Fintype N]
    [Fintype T] [Fintype k] [DecidableEq N]
    [DecidableEq T]
    (Γ : Matrix N T ℂ) (S : Matrix N k ℂ)
    (hiso : Γᴴ * Γ = 1) :
    -- (i) the boxed positive innovation
    ((Sᴴ * (1 - Γ * Γᴴ) * S).PosSemidef)
    -- (ii) vanishing exactly on the fused range
    ∧ (Sᴴ * (1 - Γ * Γᴴ) * S = 0
        ↔ (1 - Γ * Γᴴ) * S = 0)
    ∧ (Γ * Γᴴ = 1 → Sᴴ * (1 - Γ * Γᴴ) * S = 0)
    -- (iii) the boxed dimension count
    ∧ ((1 - Γ * Γᴴ).trace
        = (Fintype.card N : ℂ) - Fintype.card T) := by
  have hPP : (Γ * Γᴴ) * (Γ * Γᴴ) = Γ * Γᴴ := by
    calc (Γ * Γᴴ) * (Γ * Γᴴ)
        = Γ * ((Γᴴ * Γ) * Γᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = Γ * Γᴴ := by
          rw [hiso, Matrix.one_mul]
  have hPH : (Γ * Γᴴ)ᴴ = Γ * Γᴴ := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have h1P : (1 - Γ * Γᴴ) * (1 - Γ * Γᴴ)
      = 1 - Γ * Γᴴ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  have h1PH : (1 - Γ * Γᴴ)ᴴ = 1 - Γ * Γᴴ := by
    rw [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPH]
  have hidem : (1 - Γ * Γᴴ) * ((1 - Γ * Γᴴ) * S)
      = (1 - Γ * Γᴴ) * S := by
    rw [← Matrix.mul_assoc, h1P]
  have hfact : Sᴴ * (1 - Γ * Γᴴ) * S
      = ((1 - Γ * Γᴴ) * S)ᴴ * ((1 - Γ * Γᴴ) * S) := by
    rw [Matrix.conjTranspose_mul, h1PH,
      Matrix.mul_assoc Sᴴ (1 - Γ * Γᴴ) S, ← hidem,
      ← Matrix.mul_assoc, hidem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfact]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [hfact]
    exact Matrix.conjTranspose_mul_self_eq_zero
  · intro huni
    rw [huni]
    simp
  · rw [Matrix.trace_sub, Matrix.trace_one,
      Matrix.trace_mul_comm, hiso, Matrix.trace_one]

end NCG
