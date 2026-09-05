/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphResolventMinimizer

/-!
# Dense operator domains from resolvent ranges

A weak graph-resolvent equation places every resolvent value in the operator domain.  Therefore
dense range of one resolvent implies that the operator domain itself is dense.  This isolates the
standard domain argument used when a closed operator is specified through its resolvent.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- Dense range of a weak graph resolvent forces density of the operator domain. -/
theorem dense_operatorDomain_of_denseRange_resolvent
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (T : E →L[K] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (T f))
    (hdense : DenseRange T) :
    Dense (D : Set E) := by
  apply hdense.mono
  rintro x ⟨f, rfl⟩
  exact (hequation f).mem

end NCG.VaryingHilbert
