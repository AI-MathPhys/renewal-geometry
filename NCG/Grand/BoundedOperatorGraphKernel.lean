/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealBoundedOperatorEnergy
import NCG.Grand.OperatorGraphResolventKernel

/-!
# Kernel of a bounded operator graph

The ambient graph kernel of a bounded operator on the full domain is exactly
its ordinary linear kernel.  This small identification lets model-facing
spectral theorems state their Riesz range without a graph wrapper.
-/

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- The full-domain graph kernel of a bounded operator is its ordinary kernel. -/
theorem operatorGraphKernel_top_boundedOperatorGraphMap
    (A : E →L[K] F) :
    operatorGraphKernel (⊤ : Submodule K E) (boundedOperatorGraphMap A) =
      LinearMap.ker A.toLinearMap := by
  ext x
  rw [mem_operatorGraphKernel_iff]
  constructor
  · rintro ⟨_, hx⟩
    exact LinearMap.mem_ker.mpr hx
  · intro hx
    exact ⟨Submodule.mem_top, LinearMap.mem_ker.mp hx⟩

end NCG.VaryingHilbert
