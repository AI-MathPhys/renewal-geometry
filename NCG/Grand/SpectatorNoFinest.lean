/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct

/-!
# No canonical finest primitive
  (`cth:no-finest-primitive`, Gran-Tensor manuscript)

* `no_finest_primitive`: tensoring an unread spectator on
  which every declared letter acts trace-preservingly leaves
  all visible readouts unchanged: for any visible letter `Φ`,
  any trace-preserving spectator action `Ψ`, and any
  normalized spectator state `σ`,
  `Tr_K((ΦA) ⊗ (Ψσ)) = ΦA` and `Tr_K(A ⊗ σ) = A`.
  The spectator algebra, dimension, and symmetry are the
  arbitrary quantified data — no unrestricted operational
  table selects a finest finite microscopic lift.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- `cth:no-finest-primitive`. -/
theorem no_finest_primitive {dA dK : Type*} [Fintype dK]
    (Φ : Matrix dA dA ℂ →ₗ[ℂ] Matrix dA dA ℂ)
    (Ψ : Matrix dK dK ℂ →ₗ[ℂ] Matrix dK dK ℂ)
    (hΨ : ∀ B, (Ψ B).trace = B.trace)
    (σ : Matrix dK dK ℂ) (hσ : σ.trace = 1) :
    -- the spectator-extended letter has the same readout
    (∀ A : Matrix dA dA ℂ,
      partialTraceRight ((Φ A) ⊗ₖ (Ψ σ)) = Φ A)
    -- and the unread lift reproduces the visible input
    ∧ (∀ A : Matrix dA dA ℂ,
        partialTraceRight (A ⊗ₖ σ) = A) := by
  obtain ⟨hcol, hcomm⟩ := renewal_spectator_product Φ Ψ hΨ
  constructor
  · intro A
    rw [hcomm, hcol, hσ, one_smul]
  · intro A
    rw [hcol, hσ, one_smul]

end NCG
