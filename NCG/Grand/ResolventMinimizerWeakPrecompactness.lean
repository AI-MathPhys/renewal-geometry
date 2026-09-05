/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventMinimizerBounds
import NCG.Grand.VaryingHilbertWeakSubsequenceCompactness

/-!
# Weak precompactness of resolvent minimizers

Coercive comparison with zero bounds the minimizers, and sequential Banach--Alaoglu then gives
weak subsequential compactness in a separable complete common Hilbert carrier.  This combines two
generic obligations in the varying-space Mosco minimizer argument.
-/

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Bounded sources and nonnegative minimizing resolvent objectives make the minimizer family
sequentially weakly precompact in the common carrier. -/
theorem resolventMinimizers_isSequentiallyWeaklyPrecompact
    (q : (n : ℕ) → Hn n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (f x : ∀ n, Hn n) (F : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ F)
    (hq0 : ∀ n, q n 0 = 0) (hqx : ∀ n, 0 ≤ q n (x n))
    (hmin : ∀ n,
      resolventObjective (K := K) (q n) lam (f n) (x n) ≤
        resolventObjective (K := K) (q n) lam (f n) 0) :
    J.IsSequentiallyWeaklyPrecompact x := by
  have hbound : ∀ n, ‖x n‖ ≤ 2 * F / lam :=
    uniformlyBounded_resolventMinimizers q lam hlam f x F hf hq0 hqx hmin
  exact J.isSequentiallyWeaklyPrecompact_of_bounded x (2 * F / lam) hbound

end NCG.VaryingHilbert.System
