/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct

/-!
# Connected residual under exact factorization
  (`thm:connected-residual-factorization`,
   Gran-Tensor manuscript)

* `connected_residual_factorization`: under exact tensor
  factorization with a source supported in one component, the
  compressed source residual equals its component residual
  scaled by the (constant) spectator trace — it is independent
  of every disconnected parameter, and all its mixed derivatives
  in disconnected parameters vanish.

Rendering disclosed: the multi-component cluster statement
follows by grouping the components disjoint from the source
into one spectator block (the manuscript's `A`/`B` split, proved
here); "mixed Taylor coefficients vanish" is the proved
φ-independence plus the zero-derivative clause.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- `thm:connected-residual-factorization`. -/
theorem connected_residual_factorization {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    (G : ℝ → Matrix dA dA ℂ) (H : ℝ → Matrix dB dB ℂ)
    (X : Matrix dA dA ℂ) (c : ℂ)
    (htr : ∀ φ, (H φ).trace = c) :
    -- (1) the compressed residual factors through the source
    --     component with constant spectator weight
    (∀ (θ φ : ℝ),
      partialTraceRight ((G θ * X) ⊗ₖ H φ) = c • (G θ * X))
    -- (2) independence of every disconnected parameter
    ∧ (∀ (θ φ₁ φ₂ : ℝ),
        partialTraceRight ((G θ * X) ⊗ₖ H φ₁)
          = partialTraceRight ((G θ * X) ⊗ₖ H φ₂))
    -- (3) all disconnected derivatives vanish
    ∧ (∀ (θ : ℝ) (i j : dA),
        ∀ φ₀ : ℝ, HasDerivAt
          (fun φ : ℝ =>
            (partialTraceRight ((G θ * X) ⊗ₖ H φ) i j).re)
          0 φ₀) := by
  have hcollapse : ∀ (A : Matrix dA dA ℂ)
      (B : Matrix dB dB ℂ),
      partialTraceRight (A ⊗ₖ B) = B.trace • A :=
    (renewal_spectator_product LinearMap.id LinearMap.id
      (fun _ => rfl)).1
  have h1 : ∀ (θ φ : ℝ),
      partialTraceRight ((G θ * X) ⊗ₖ H φ)
        = c • (G θ * X) := by
    intro θ φ
    rw [hcollapse, htr]
  refine ⟨h1, ?_, ?_⟩
  · intro θ φ₁ φ₂
    rw [h1, h1]
  · intro θ i j φ₀
    have hconst : (fun φ : ℝ =>
        (partialTraceRight ((G θ * X) ⊗ₖ H φ) i j).re)
        = fun _ : ℝ => ((c • (G θ * X)) i j).re := by
      funext φ
      rw [h1]
    rw [hconst]
    exact hasDerivAt_const _ _

end NCG
