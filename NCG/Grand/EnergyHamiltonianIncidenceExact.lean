/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceCompleteWardAtlasExact

/-!
# Energy-density/Hamiltonian incidence

This file proves `thm:SMOS-energy-Hamiltonian-incidence`.  The finite
certificate is the Gram of `(EΣ-H)B`; a source-complete atlas makes its
vanishing equivalent to equality of the two bounded operators.  For closed
unbounded operators, equality on one common graph core identifies their
closures.
-/

namespace NCG
namespace EnergyHamiltonianIncidenceExact

open SourceCompleteWardAtlasExact

variable {H F : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The finite incidence Gram `B*(EΣ-H)*(EΣ-H)B`. -/
noncomputable def energyHamiltonianGram
    (energy hamiltonian : H →L[ℂ] H) (B : F →L[ℂ] H) : F →L[ℂ] F :=
  wardGram (energy - hamiltonian) B

/-- Source completeness of the atlas on the whole finite carrier. -/
def IsSourceComplete (B : F →L[ℂ] H) : Prop :=
  atlasRange B = ⊤

/-- At finite cutoff, the incidence Gram vanishes exactly when the
integrated energy candidate equals the reconstructed Hamiltonian. -/
theorem energyHamiltonianGram_eq_zero_iff
    (energy hamiltonian : H →L[ℂ] H) (B : F →L[ℂ] H)
    (hcomplete : IsSourceComplete B) :
    energyHamiltonianGram energy hamiltonian B = 0 ↔
      energy = hamiltonian := by
  have hres : atlasResidual (⊤ : Submodule ℂ H) B = 0 :=
    (atlasResidual_eq_zero_iff (⊤ : Submodule ℂ H) B).mpr (by
      rw [hcomplete]
      exact le_rfl)
  have htop : (⊤ : Submodule ℂ H).starProjection = (1 : H →L[ℂ] H) :=
    Submodule.starProjection_top'
  have hcomp : (energy - hamiltonian) ∘L (1 : H →L[ℂ] H) =
      energy - hamiltonian := by
    ext x
    simp
  have hsupp : energy - hamiltonian =
      (energy - hamiltonian) ∘L (⊤ : Submodule ℂ H).starProjection := by
    rw [htop, hcomp]
  have hward := wardGram_eq_zero_iff_target_defect_zero
    (⊤ : Submodule ℂ H) B (energy - hamiltonian) hres hsupp
  rw [htop, hcomp] at hward
  simpa [energyHamiltonianGram, sub_eq_zero] using hward

/-! ## Equality of closed unbounded closures -/

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Closed operators agreeing on a common graph core are equal.  Equivalently,
closable operators agreeing on a common core have equal closures. -/
theorem closed_operators_eq_of_common_core
    (energy hamiltonian : E →ₗ.[ℂ] G)
    (henergyClosed : energy.IsClosed) (hhamiltonianClosed : hamiltonian.IsClosed)
    (S : Submodule ℂ E) (henergyCore : energy.HasCore S)
    (hhamiltonianCore : hamiltonian.HasCore S)
    (hagree : ∀ (x : E) (hx : x ∈ S),
      energy ⟨x, henergyCore.le_domain hx⟩ =
        hamiltonian ⟨x, hhamiltonianCore.le_domain hx⟩) :
    energy = hamiltonian := by
  have hrestrict : energy.domRestrict S = hamiltonian.domRestrict S := by
    apply LinearPMap.ext
    · rw [LinearPMap.domRestrict_domain, LinearPMap.domRestrict_domain]
      rw [inf_eq_left.mpr henergyCore.le_domain,
        inf_eq_left.mpr hhamiltonianCore.le_domain]
    · intro x hxE hxH
      have hxS : x ∈ S := hxE.1
      have he : energy.domRestrict S ⟨x, hxE⟩ =
          energy ⟨x, henergyCore.le_domain hxS⟩ :=
        LinearPMap.domRestrict_apply rfl
      have hh : hamiltonian.domRestrict S ⟨x, hxH⟩ =
          hamiltonian ⟨x, hhamiltonianCore.le_domain hxS⟩ :=
        LinearPMap.domRestrict_apply rfl
      rw [he, hh, hagree x hxS]
  calc
    energy = (energy.domRestrict S).closure := henergyCore.closure_eq.symm
    _ = (hamiltonian.domRestrict S).closure := by rw [hrestrict]
    _ = hamiltonian := hhamiltonianCore.closure_eq

/-- The same result stated directly as equality of the two closures. -/
theorem operator_closures_eq_of_common_core
    (energy hamiltonian : E →ₗ.[ℂ] G)
    (henergy : energy.IsClosable) (hhamiltonian : hamiltonian.IsClosable)
    (S : Submodule ℂ E) (henergyCore : energy.closure.HasCore S)
    (hhamiltonianCore : hamiltonian.closure.HasCore S)
    (hagree : ∀ (x : E) (hx : x ∈ S),
      energy.closure ⟨x, henergyCore.le_domain hx⟩ =
        hamiltonian.closure ⟨x, hhamiltonianCore.le_domain hx⟩) :
    energy.closure = hamiltonian.closure := by
  exact closed_operators_eq_of_common_core energy.closure hamiltonian.closure
    henergy.closure_isClosed hhamiltonian.closure_isClosed S
    henergyCore hhamiltonianCore hagree

end EnergyHamiltonianIncidenceExact
end NCG
