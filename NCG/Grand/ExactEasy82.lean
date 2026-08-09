/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MainDuality

/-!
# Exact EASY 82: assembly of the SMST dual presentations

The branch theorems identify the same multiplicity algebra as the commutant
of the joint action, support-polar, and rooted holonomy algebras, and identify
it with the quiver endomorphism algebra. This file performs the remaining
finite bicommutant assembly in one theorem.
-/

open Matrix

namespace NCG

/-- Once the four canonical presentations have supplied their forward
commutant identifications, finite bicommutant closure supplies every reverse
identity simultaneously. The quiver algebra equivalence is transported
unchanged as the third presentation of the same multiplicity algebra. -/
theorem smst_main_duality_assembled
    {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (Aact Osup : Subalgebra ℂ (Matrix n n ℂ))
    (Mtype : Subalgebra ℂ (Matrix n n ℂ))
    (Oroot Mroot : Subalgebra ℂ (Matrix r r ℂ))
    {QEnd : Type*} [Semiring QEnd] [Algebra ℂ QEnd]
    (hAstar : ∀ a ∈ Aact, aᴴ ∈ Aact)
    (hOstar : ∀ a ∈ Osup, aᴴ ∈ Osup)
    (hRootStar : ∀ a ∈ Oroot, aᴴ ∈ Oroot)
    (hAct : matCommutant (Aact : Set (Matrix n n ℂ)) =
      (Mtype : Set (Matrix n n ℂ)))
    (hSup : matCommutant (Osup : Set (Matrix n n ℂ)) =
      (Mtype : Set (Matrix n n ℂ)))
    (hQuiver : Mtype ≃ₐ[ℂ] QEnd)
    (hRoot : matCommutant (Oroot : Set (Matrix r r ℂ)) =
      (Mroot : Set (Matrix r r ℂ))) :
    -- joint action and residual multiplicity are mutual commutants
    matCommutant (Mtype : Set (Matrix n n ℂ)) =
        (Aact : Set (Matrix n n ℂ))
    -- support-polar and residual multiplicity are the same dual pair
    ∧ matCommutant (Mtype : Set (Matrix n n ℂ)) =
        (Osup : Set (Matrix n n ℂ))
    -- the canonical multiplicity-quiver presentation
    ∧ Nonempty (Mtype ≃ₐ[ℂ] QEnd)
    -- rooted polar metric--holonomy mutual commutant
    ∧ matCommutant (Mroot : Set (Matrix r r ℂ)) =
        (Oroot : Set (Matrix r r ℂ)) := by
  have hActBack := (smst_main_duality Aact hAstar).1
  have hSupBack := (smst_main_duality Osup hOstar).1
  have hRootBack := (smst_main_duality Oroot hRootStar).1
  refine ⟨?_, ?_, ⟨hQuiver⟩, ?_⟩
  · rw [← hAct]
    exact hActBack
  · rw [← hSup]
    exact hSupBack
  · rw [← hRoot]
    exact hRootBack

end NCG
