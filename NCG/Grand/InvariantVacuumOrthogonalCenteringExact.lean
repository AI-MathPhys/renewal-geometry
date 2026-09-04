/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal centering inside an independently defined invariant sector

Centering a dense source family removes exactly its invariant vacuum line.
The neutral space is the intersection of the fixed space and the orthogonal
complement, not a space defined by the centered orbit's closure.
-/

namespace NCG.InvariantVacuumOrthogonalCentering

noncomputable section

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The common fixed submodule of a family of continuous linear operators. -/
def fixedSubmodule (U : I → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {v | ∀ i, U i v = v}
  zero_mem' := fun i => map_zero (U i)
  add_mem' := by
    intro v w hv hw i
    rw [map_add, hv i, hw i]
  smul_mem' := by
    intro c v hv i
    rw [map_smul, hv i]

theorem isClosed_fixedSubmodule (U : I → H →L[ℂ] H) :
    IsClosed (fixedSubmodule U : Set H) := by
  have heq : (fixedSubmodule U : Set H) = ⋂ i, {v | U i v = v} := by
    ext v
    simp [fixedSubmodule]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_eq (U i).continuous continuous_id

/-- Orthogonal projection of a closed sector containing the vacuum is exactly
its intersection with the vacuum complement. -/
theorem closure_centered_eq_inter (S : Submodule ℂ H) (hclosed : IsClosed (S : Set H))
    (vacuum : H) (hv : vacuum ∈ S) (writers : Set H)
    (hdense : closure writers = (S : Set H)) :
    closure ((Submodule.span ℂ {vacuum})ᗮ.starProjection '' writers) =
      (S : Set H) ∩ ((Submodule.span ℂ {vacuum})ᗮ : Set H) := by
  let L := Submodule.span ℂ ({vacuum} : Set H)
  have hle : L ≤ S := Submodule.span_le.mpr (by simpa using hv)
  have heq : Lᗮ.starProjection '' (S : Set H) = (S : Set H) ∩ (Lᗮ : Set H) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      constructor
      · rw [Submodule.starProjection_orthogonal_val]
        exact S.sub_mem hw (hle (L.starProjection_apply_mem w))
      · exact Lᗮ.starProjection_apply_mem w
    · rintro ⟨hs, hk⟩
      exact ⟨v, hs, Lᗮ.starProjection_mem_subspace_eq_self ⟨v, hk⟩⟩
  have htransport := closure_image_closure Lᗮ.starProjection.continuous (s := writers)
  rw [hdense, heq, (hclosed.inter L.isClosed_orthogonal).closure_eq] at htransport
  exact htransport.symm

/-- A centered fixed-vector source orbit is dense in the full neutral fixed
space, defined independently by operator equations and orthogonality. -/
theorem closure_centered_fixed_eq_inter (U : I → H →L[ℂ] H)
    (vacuum : H) (hv : ∀ i, U i vacuum = vacuum) (writers : Set H)
    (hdense : closure writers = (fixedSubmodule U : Set H)) :
    closure ((Submodule.span ℂ {vacuum})ᗮ.starProjection '' writers) =
      (fixedSubmodule U : Set H) ∩ ((Submodule.span ℂ {vacuum})ᗮ : Set H) :=
  closure_centered_eq_inter (fixedSubmodule U) (isClosed_fixedSubmodule U)
    vacuum hv writers hdense

end

end NCG.InvariantVacuumOrthogonalCentering
