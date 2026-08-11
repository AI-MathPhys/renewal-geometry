/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.Bicommutant
import NCG.Grand.FiniteComplexStarSubalgebraSemisimplicity
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Mutual commutants for finite complex star subalgebras

For an arbitrary unital star-closed subalgebra of a finite complex matrix
algebra, this module proves both that the algebra and its commutant are mutual
commutants and that the algebra is abstractly a finite product of full complex
matrix algebras. Semisimplicity is discharged by explicit trace-orthogonal
left-ideal complements.
-/

open Matrix

namespace NCG
namespace FiniteStarSubalgebraMutualCommutant

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An arbitrary unital star-closed finite matrix subalgebra and its matrix
commutant are mutual commutants. -/
theorem mutualCommutants
    (A : Subalgebra ℂ (Matrix n n ℂ))
    (hstar : ∀ a ∈ A, aᴴ ∈ A) :
    matCommutant (matCommutant (A : Set (Matrix n n ℂ))) =
      (A : Set (Matrix n n ℂ)) := by
  ext T
  constructor
  · intro hT
    exact double_commutant A hstar T hT
  · intro hT b hb
    exact (hb T hT).symm

/-- A finite complex matrix star subalgebra is a finite product of full
complex matrix algebras. No semisimplicity assumption is required. -/
theorem starSubalgebra_matrixBlockDecomposition
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (S ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.of_injective
      (Subalgebra.val S.toSubalgebra).toLinearMap
      (fun _ _ h => Subtype.ext h)
  letI : IsSemisimpleRing S :=
    FiniteComplexStarSubalgebraSemisimplicity.starSubalgebra_isSemisimpleRing S
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ S

/-- A unital star-closed subalgebra presented as an ordinary subalgebra is a
finite product of full complex matrix algebras. -/
theorem matrixBlockDecomposition
    (A : Subalgebra ℂ (Matrix n n ℂ))
    (hstar : ∀ a ∈ A, aᴴ ∈ A) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  let S : StarSubalgebra ℂ (Matrix n n ℂ) :=
    { toSubalgebra := A
      star_mem' := fun ha => hstar _ ha }
  let eAS : A ≃ₐ[ℂ] S :=
    Subalgebra.equivOfEq A S.toSubalgebra rfl
  obtain ⟨r, d, hd, ⟨e⟩⟩ :=
    starSubalgebra_matrixBlockDecomposition S
  exact ⟨r, d, hd, ⟨eAS.trans e⟩⟩

end FiniteStarSubalgebraMutualCommutant
end NCG
