/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ActiveNoRouting

/-!
# Exact EASY batch 12: active/private no-routing
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- Any later active future which factors through discarding the
old private factor annihilates every traceless private contrast. -/
theorem active_future_factors_no_private {dH dP e W : Type*}
    [Fintype dH] [Fintype dP] [AddCommGroup W] [Module ℂ W]
    (h0 : Matrix dH dH ℂ) (Jp : e → Matrix dP dP ℂ)
    (htr : ∀ v, (Jp v).trace = 0)
    (Cfuture : Matrix (dH × dP) (dH × dP) ℂ →ₗ[ℂ] W)
    (Cact : Matrix dH dH ℂ →ₗ[ℂ] W)
    (hfactor : ∀ X, Cfuture X = Cact (partialTraceRight X)) :
    ∀ v, Cfuture (h0 ⊗ₖ Jp v) = 0 := by
  intro v
  rw [hfactor]
  have hbase := active_private_no_routing (W := W) h0 Jp htr
  exact hbase.2.1 Cact v

/-- The corresponding active leakage Gram vanishes for every
matrix-valued family of later Reads. -/
theorem active_future_private_gram_zero {dH dP e y : Type*}
    [Fintype dH] [Fintype dP] [Fintype y]
    (h0 : Matrix dH dH ℂ) (Jp : e → Matrix dP dP ℂ)
    (htr : ∀ v, (Jp v).trace = 0)
    (Cfuture : Matrix (dH × dP) (dH × dP) ℂ →ₗ[ℂ]
      Matrix y y ℂ)
    (Cact : Matrix dH dH ℂ →ₗ[ℂ] Matrix y y ℂ)
    (hfactor : ∀ X, Cfuture X = Cact (partialTraceRight X)) :
    ∀ v w,
      ((Cfuture (h0 ⊗ₖ Jp v))ᴴ * Cfuture (h0 ⊗ₖ Jp w)).trace = 0 := by
  intro v w
  rw [active_future_factors_no_private h0 Jp htr Cfuture Cact hfactor v,
    active_future_factors_no_private h0 Jp htr Cfuture Cact hfactor w,
    Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero]

/-- `thm:active-private-no-routing`, stated with the concrete
factor-through-discard wiring hypothesis used in the manuscript. -/
theorem active_private_no_routing_exact {dH dP e y : Type*}
    [Fintype dH] [Fintype dP] [Fintype y]
    (h0 : Matrix dH dH ℂ) (Jp : e → Matrix dP dP ℂ)
    (htr : ∀ v, (Jp v).trace = 0)
    (Cfuture : Matrix (dH × dP) (dH × dP) ℂ →ₗ[ℂ]
      Matrix y y ℂ)
    (Cact : Matrix dH dH ℂ →ₗ[ℂ] Matrix y y ℂ)
    (hfactor : ∀ X, Cfuture X = Cact (partialTraceRight X)) :
    (∀ v, Cfuture (h0 ⊗ₖ Jp v) = 0)
      ∧ (∀ v w,
        ((Cfuture (h0 ⊗ₖ Jp v))ᴴ
          * Cfuture (h0 ⊗ₖ Jp w)).trace = 0) := by
  exact ⟨active_future_factors_no_private h0 Jp htr Cfuture Cact hfactor,
    active_future_private_gram_zero h0 Jp htr Cfuture Cact hfactor⟩

end NCG
