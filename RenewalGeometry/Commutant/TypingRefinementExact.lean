/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.JointTypedActionAlgebra
import RenewalGeometry.Commutant.ReciprocalWedderburnKronecker

/-!
# Order reversal and represented typing refinement

Covers `prop:typing-refinement` of the spacetime–gauge duality paper.

* `starClosed_le_iff_matCommutant_subset` (`eq:incidence-closure-galois`): for two
  star-closed unital subalgebras `O₁, O₂` of a finite matrix algebra (the closed
  coefficient-action algebras `𝒪_Y`, `𝒪_Ỹ`), `O₁ ⊆ O₂ ⟺ O₂' ⊆ O₁'`; taking commutants
  reverses inclusions and the finite bicommutant theorem reverses them back.
* `starClosed_eq_iff_matCommutant_eq`: equality of the closed coefficient-action
  algebras is equivalent to equality of the exact multiplicity algebras.
* `typingRefinement_exact` (`eq:typing-refinement-monotone` and the equivalence):
  for `A_type⁽¹⁾ ⊆ A_type⁽²⁾`, `𝒜ᵢ = C^*(A_Cl, A_type⁽ⁱ⁾, Y, Y^*)`, `ℳᵢ = 𝒜ᵢ'`, one has
  `𝒜₁ ⊆ 𝒜₂`, `ℳ₂ ⊆ ℳ₁`, and
  `ℳ₁ = ℳ₂ ⟺ 𝒜₁ = 𝒜₂ ⟺ A_type⁽²⁾ ⊆ 𝒜₁`.
-/

open Matrix

namespace RenewalGeometry

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Galois order reversal (`eq:incidence-closure-galois`) -/

/-- Commutants of star-closed unital subalgebras reverse and reflect inclusions:
`O₁ ⊆ O₂ ⟺ O₂' ⊆ O₁'` (`eq:incidence-closure-galois`, with `ℳ_type = 𝒪_Y'`). -/
theorem starClosed_le_iff_matCommutant_subset
    (O₁ O₂ : Subalgebra ℂ (Matrix n n ℂ))
    (h₂ : ∀ a ∈ O₂, aᴴ ∈ O₂) :
    O₁ ≤ O₂ ↔ matCommutant (O₂ : Set (Matrix n n ℂ)) ⊆
      matCommutant (O₁ : Set (Matrix n n ℂ)) := by
  constructor
  · intro h
    exact matCommutant_anti (SetLike.coe_subset_coe.mpr h)
  · intro h a ha
    refine double_commutant O₂ h₂ a ?_
    intro b hb
    exact (h hb a ha).symm

/-- Equality of the closed coefficient-action algebras is equivalent to equality of the
exact multiplicity algebras (`prop:typing-refinement`, "Thus ..."). -/
theorem starClosed_eq_iff_matCommutant_eq
    (O₁ O₂ : Subalgebra ℂ (Matrix n n ℂ))
    (h₁ : ∀ a ∈ O₁, aᴴ ∈ O₁) (h₂ : ∀ a ∈ O₂, aᴴ ∈ O₂) :
    O₁ = O₂ ↔ matCommutant (O₁ : Set (Matrix n n ℂ)) =
      matCommutant (O₂ : Set (Matrix n n ℂ)) := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply le_antisymm
    · exact (starClosed_le_iff_matCommutant_subset O₁ O₂ h₂).mpr h.symm.subset
    · exact (starClosed_le_iff_matCommutant_subset O₂ O₁ h₁).mpr h.subset

/-! ### Represented typing refinement -/

/-- The joint action algebra is monotone in the typing algebra. -/
theorem jointActionAlgebra_mono_int (ACl A₁ A₂ : Set (Matrix n n ℂ)) {E : Type*}
    (Y : E → Matrix n n ℂ) (h : A₁ ⊆ A₂) :
    jointActionAlgebra ACl A₁ Y ≤ jointActionAlgebra ACl A₂ Y :=
  jointActionAlgebra_le ACl A₁ Y (jointActionAlgebra_starClosed ACl A₂ Y)
    (ext_subset_jointActionAlgebra ACl A₂ Y)
    (h.trans (int_subset_jointActionAlgebra ACl A₂ Y))
    (incidence_mem_jointActionAlgebra ACl A₂ Y)

/-- `𝒜₂ = C^*(𝒜₁, A_type⁽²⁾)`: the refined action algebra is the least star-closed
unital subalgebra containing `𝒜₁` and `A_type⁽²⁾`. -/
theorem jointActionAlgebra_refined_le (ACl A₁ A₂ : Set (Matrix n n ℂ)) {E : Type*}
    (Y : E → Matrix n n ℂ) {B : Subalgebra ℂ (Matrix n n ℂ)} (hB : ∀ a ∈ B, aᴴ ∈ B)
    (h₁ : jointActionAlgebra ACl A₁ Y ≤ B) (h₂ : A₂ ⊆ B) :
    jointActionAlgebra ACl A₂ Y ≤ B :=
  jointActionAlgebra_le ACl A₂ Y hB
    ((ext_subset_jointActionAlgebra ACl A₁ Y).trans h₁) h₂
    (fun e => h₁ (incidence_mem_jointActionAlgebra ACl A₁ Y e))

/-- **Order reversal and represented typing refinement (`prop:typing-refinement`).**
For `A_type⁽¹⁾ ⊆ A_type⁽²⁾`, with `𝒜ᵢ = C^*(A_Cl, A_type⁽ⁱ⁾, Y, Y^*)` and `ℳᵢ = 𝒜ᵢ'`:
`𝒜₁ ⊆ 𝒜₂`, `ℳ₂ ⊆ ℳ₁` (`eq:typing-refinement-monotone`), and
`ℳ₁ = ℳ₂ ⟺ 𝒜₁ = 𝒜₂ ⟺ A_type⁽²⁾ ⊆ 𝒜₁`.  A typing refinement is multiplicity-neutral
exactly when its added operations already lie in the generated action. -/
theorem typingRefinement_exact (ACl A₁ A₂ : Set (Matrix n n ℂ)) {E : Type*}
    (Y : E → Matrix n n ℂ) (h : A₁ ⊆ A₂) :
    jointActionAlgebra ACl A₁ Y ≤ jointActionAlgebra ACl A₂ Y ∧
    matCommutant (jointActionAlgebra ACl A₂ Y : Set (Matrix n n ℂ)) ⊆
      matCommutant (jointActionAlgebra ACl A₁ Y : Set (Matrix n n ℂ)) ∧
    (matCommutant (jointActionAlgebra ACl A₁ Y : Set (Matrix n n ℂ)) =
        matCommutant (jointActionAlgebra ACl A₂ Y : Set (Matrix n n ℂ)) ↔
      jointActionAlgebra ACl A₁ Y = jointActionAlgebra ACl A₂ Y) ∧
    (jointActionAlgebra ACl A₁ Y = jointActionAlgebra ACl A₂ Y ↔
      A₂ ⊆ jointActionAlgebra ACl A₁ Y) := by
  have hmono := jointActionAlgebra_mono_int ACl A₁ A₂ Y h
  refine ⟨hmono, matCommutant_anti (SetLike.coe_subset_coe.mpr hmono), ?_, ?_⟩
  · exact (starClosed_eq_iff_matCommutant_eq _ _
      (jointActionAlgebra_starClosed ACl A₁ Y) (jointActionAlgebra_starClosed ACl A₂ Y)).symm
  · constructor
    · intro heq
      rw [heq]
      exact int_subset_jointActionAlgebra ACl A₂ Y
    · intro hsub
      exact le_antisymm hmono
        (jointActionAlgebra_refined_le ACl A₁ A₂ Y
          (jointActionAlgebra_starClosed ACl A₁ Y) le_rfl hsub)

end RenewalGeometry
