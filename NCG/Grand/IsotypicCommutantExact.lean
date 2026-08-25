/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The external isotypic algebra and its relative commutant

Fifth machinery layer for `thm:SM-active-residual-algebra` (SM.0i–SM.0j, abstract
form): for any finite-dimensional complex representation of a finite group,

* `image_pi_matrix` (SM.0i): the external Burnside algebra — the range of the
  group-algebra action — is isomorphic as a `ℂ`-algebra to a finite product of full
  matrix algebras `Π M_{dλ}(ℂ)` (Maschke semisimplicity + Wedderburn–Artin over the
  algebraically closed field `ℂ`);
* `commutant_pi_matrix` (SM.0j): the relative commutant — the endomorphism algebra
  of the module over the group algebra — is likewise a finite product of full matrix
  algebras `Π M_{mλ}(ℂ)`, the multiplicity blocks.
-/

open MonoidAlgebra

namespace NCG
namespace IsotypicAlgebra

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V)

theorem neZero_card : NeZero ((Nat.card G : ℂ)) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- **SM.0i, abstract form**: the external Burnside algebra of a finite-dimensional
complex representation of a finite group is a finite product of full matrix
algebras over `ℂ`. -/
theorem image_pi_matrix :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (ρ.asAlgebraHom.range ≃ₐ[ℂ]
        Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  haveI := neZero_card (G := G)
  haveI hsemi : IsSemisimpleRing (MonoidAlgebra ℂ G) := inferInstance
  haveI : IsSemisimpleRing ρ.asAlgebraHom.range :=
    RingHom.isSemisimpleRing_of_surjective
      (ρ.asAlgebraHom.toRingHom.rangeRestrict)
      ρ.asAlgebraHom.toRingHom.rangeRestrict_surjective
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ _

/-- **SM.0j, abstract form**: the relative commutant of a finite-dimensional complex
representation of a finite group is a finite product of full matrix algebras over
`ℂ` — the multiplicity blocks. -/
theorem commutant_pi_matrix :
    ∃ (n : ℕ) (m : Fin n → ℕ), (∀ i, NeZero (m i)) ∧
      Nonempty (Module.End (MonoidAlgebra ℂ G) ρ.asModule ≃ₐ[ℂ]
        Π i, Matrix (Fin (m i)) (Fin (m i)) ℂ) := by
  haveI := neZero_card (G := G)
  haveI hfin : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ _ _
  haveI hsemiEnd : IsSemisimpleRing (Module.End (MonoidAlgebra ℂ G) ρ.asModule) :=
    IsSemisimpleRing.moduleEnd _ _
  haveI hfd : FiniteDimensional ℂ (Module.End (MonoidAlgebra ℂ G) ρ.asModule) := by
    refine FiniteDimensional.of_injective
      (LinearMap.restrictScalarsₗ ℂ (MonoidAlgebra ℂ G) ρ.asModule ρ.asModule ℂ)
      (LinearMap.restrictScalars_injective ℂ)
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ _

end IsotypicAlgebra
end NCG
