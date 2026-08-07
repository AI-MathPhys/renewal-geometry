/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct

/-!
# Exact active no-routing
  (`thm:active-private-no-routing`, Gran-Tensor manuscript)

* `active_private_no_routing`: after the completed-private cut,
  every active recurrent Read factors through the fresh hub and
  discards the old private factor; pure private contrasts
  (traceless in the private slot) therefore lie in the kernel of
  every later active Read, and the boxed identities
  `C_act ∘ J_priv = 0` and `(J_priv)*(C_act)*(C_act)(J_priv) = 0`
  hold.

Rendering disclosed: the discard of the private factor is the
partial trace over the private slot (the manuscript's
identity-or-discard clause); "for the concrete renewal source"
is rendered by the traceless-contrast hypothesis, which the
concrete completed-private packet satisfies.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- `thm:active-private-no-routing`: private contrasts die under
the hub discard, so every later active Read and its Gram
vanish on them. -/
theorem active_private_no_routing {dH dP e W : Type*}
    [Fintype dH] [Fintype dP] [AddCommGroup W] [Module ℂ W]
    (h0 : Matrix dH dH ℂ) (Jp : e → Matrix dP dP ℂ)
    (htr : ∀ v, (Jp v).trace = 0) :
    (∀ v, partialTraceRight (h0 ⊗ₖ Jp v) = 0)
    ∧ (∀ (Cact : Matrix dH dH ℂ →ₗ[ℂ] W) (v : e),
        Cact (partialTraceRight (h0 ⊗ₖ Jp v)) = 0)
    ∧ (∀ (Cact : Matrix dH dH ℂ →ₗ[ℂ] Matrix dH dH ℂ)
        (v w : e),
        ((Cact (partialTraceRight (h0 ⊗ₖ Jp v)))ᴴ
          * Cact (partialTraceRight (h0 ⊗ₖ Jp w))).trace
        = 0) := by
  have hcollapse : ∀ v,
      partialTraceRight (h0 ⊗ₖ Jp v) = 0 := by
    intro v
    ext i j
    simp only [partialTraceRight, Matrix.of_apply,
      Matrix.kroneckerMap_apply, Matrix.zero_apply]
    rw [← Finset.mul_sum]
    rw [show (∑ k, Jp v k k) = (Jp v).trace from rfl, htr,
      mul_zero]
  refine ⟨hcollapse, ?_, ?_⟩
  · intro Cact v
    rw [hcollapse, map_zero]
  · intro Cact v w
    rw [hcollapse, map_zero, Matrix.conjTranspose_zero,
      Matrix.zero_mul, Matrix.trace_zero]

end NCG
