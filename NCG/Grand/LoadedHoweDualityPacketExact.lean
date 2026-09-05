/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTDualityAssembly

/-!
# Exact loaded Howe-duality packet

This file gives a typed meaning to the source-complete joint packet used in
`thm:SMST-main-duality` and proves all four forward/reverse presentations in one theorem.
-/

open Matrix

namespace NCG

/-- The duality-facing data certified by a source-complete joint packet.  The forward
commutant identifications are the edge, support-polar, quiver, and (on the connected
invertible branch) root-holonomy reconstructions; no inverse residue map is part of the data. -/
structure SourceCompleteJointDualityPacket
    (n r : Type*) [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    (QEnd : Type*) [Semiring QEnd] [Algebra ℂ QEnd] where
  actionAlgebra : Subalgebra ℂ (Matrix n n ℂ)
  multiplicityAlgebra : Subalgebra ℂ (Matrix n n ℂ)
  supportPolarAlgebra : Subalgebra ℂ (Matrix n n ℂ)
  rootHolonomyAlgebra : Subalgebra ℂ (Matrix r r ℂ)
  rootMultiplicityAlgebra : Subalgebra ℂ (Matrix r r ℂ)
  action_starClosed : ∀ a ∈ actionAlgebra, aᴴ ∈ actionAlgebra
  supportPolar_starClosed : ∀ a ∈ supportPolarAlgebra, aᴴ ∈ supportPolarAlgebra
  rootHolonomy_starClosed : ∀ a ∈ rootHolonomyAlgebra, aᴴ ∈ rootHolonomyAlgebra
  edgeCommutant : matCommutant (actionAlgebra : Set (Matrix n n ℂ)) =
    (multiplicityAlgebra : Set (Matrix n n ℂ))
  supportPolarCommutant : matCommutant (supportPolarAlgebra : Set (Matrix n n ℂ)) =
    (multiplicityAlgebra : Set (Matrix n n ℂ))
  quiverPresentation : multiplicityAlgebra ≃ₐ[ℂ] QEnd
  rootHolonomyCommutant : matCommutant (rootHolonomyAlgebra : Set (Matrix r r ℂ)) =
    (rootMultiplicityAlgebra : Set (Matrix r r ℂ))

/-- **SM--spacetime loaded Howe duality (`thm:SMST-main-duality`).**  Every source-complete
joint duality packet yields the mutual action/multiplicity commutants, the same mutual
support-polar presentation, the canonical quiver endomorphism presentation, and the mutual
root metric--holonomy presentation. -/
theorem sourceCompleteJointPacket_loadedHoweDuality
    {n r QEnd : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r] [Semiring QEnd] [Algebra ℂ QEnd]
    (P : SourceCompleteJointDualityPacket n r QEnd) :
    matCommutant (P.actionAlgebra : Set (Matrix n n ℂ)) =
        (P.multiplicityAlgebra : Set (Matrix n n ℂ))
    ∧ matCommutant (P.multiplicityAlgebra : Set (Matrix n n ℂ)) =
        (P.actionAlgebra : Set (Matrix n n ℂ))
    ∧ matCommutant (P.supportPolarAlgebra : Set (Matrix n n ℂ)) =
        (P.multiplicityAlgebra : Set (Matrix n n ℂ))
    ∧ matCommutant (P.multiplicityAlgebra : Set (Matrix n n ℂ)) =
        (P.supportPolarAlgebra : Set (Matrix n n ℂ))
    ∧ Nonempty (P.multiplicityAlgebra ≃ₐ[ℂ] QEnd)
    ∧ matCommutant (P.rootHolonomyAlgebra : Set (Matrix r r ℂ)) =
        (P.rootMultiplicityAlgebra : Set (Matrix r r ℂ))
    ∧ matCommutant (P.rootMultiplicityAlgebra : Set (Matrix r r ℂ)) =
        (P.rootHolonomyAlgebra : Set (Matrix r r ℂ)) := by
  have hback := smst_main_duality_assembled
    P.actionAlgebra P.supportPolarAlgebra P.multiplicityAlgebra
    P.rootHolonomyAlgebra P.rootMultiplicityAlgebra
    P.action_starClosed P.supportPolar_starClosed P.rootHolonomy_starClosed
    P.edgeCommutant P.supportPolarCommutant P.quiverPresentation P.rootHolonomyCommutant
  exact ⟨P.edgeCommutant, hback.1, P.supportPolarCommutant, hback.2.1,
    hback.2.2.1, P.rootHolonomyCommutant, hback.2.2.2⟩

end NCG
