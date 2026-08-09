/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact EASY batch 20: flatness exhausts the generated algebra
-/

namespace NCG

/-- `lem:flat-exhausts-new`.  The final hypothesis is precisely
the induction principle saying that the unit and the source image
generate the ambient algebra.  Crucially, generator invariance is
derived from the word-step law and flatness; it is not assumed. -/
theorem flat_exhausts_generated_algebra_exact
    {𝕜 A E : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    [FiniteDimensional 𝕜 A]
    (S : E → A) (K : ℕ → Submodule 𝕜 A) (n : ℕ)
    (hmono : ∀ m, K m ≤ K (m + 1))
    (hflat : Module.finrank 𝕜 (K (n + 1))
      ≤ Module.finrank 𝕜 (K n))
    (hstep : ∀ x,
      Submodule.map (Algebra.lmul 𝕜 A (S x)) (K n) ≤ K (n + 1))
    (hone : (1 : A) ∈ K n)
    (hgenerate : ∀ M : Submodule 𝕜 A, (1 : A) ∈ M →
      (∀ x, Submodule.map (Algebra.lmul 𝕜 A (S x)) M ≤ M) →
      M = ⊤) :
    K n = K (n + 1) ∧ K n = ⊤ ∧ K (n + 1) = ⊤ := by
  have heq : K (n + 1) = K n :=
    (Submodule.eq_of_le_of_finrank_le (hmono n) hflat).symm
  have hinv : ∀ x,
      Submodule.map (Algebra.lmul 𝕜 A (S x)) (K n) ≤ K n := by
    intro x
    simpa only [heq] using hstep x
  have htop : K n = ⊤ := hgenerate (K n) hone hinv
  exact ⟨heq.symm, htop, heq.trans htop⟩

end NCG
