/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteMomentKrylovSourceDuality

/-!
# Terminating arithmetic--renewal source test

The five pointed-tetrahedral Gram parameters and a genuinely finite Krylov
moment panel determine the two requested isometries.
-/

open Matrix

namespace NCG
namespace TerminatingArithmeticRenewalSourceTestExact

/-- Complete terminating source test: five parameter equality is equivalent
to the label-fixing range isometry, and moments only through `2d-1` determine
the unique transfer intertwiner. -/
theorem terminating_arithmetic_renewal_source_test
    {h h' : Type} {u p : Type*} [Fintype h] [Fintype h']
    [Fintype u] [Fintype p] [DecidableEq u]
    (S : Matrix h (Fin 5) ℂ) (T : Matrix h' (Fin 5) ℂ)
    (P Q : PointedTetrahedralGramParameters)
    (hS : Sᴴ * S = pointedTetrahedralGramMatrix P)
    (hT : Tᴴ * T = pointedTetrahedralGramMatrix Q)
    (G G' : Matrix u u ℂ) (B B' : Matrix u p ℂ)
    (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (d : ℕ) (hd : 0 < d)
    (hminimal : Function.Surjective (krylovMat G B d).mulVec)
    (hmom : ∀ n : ℕ, n ≤ 2 * d - 1 →
      Bᴴ * G ^ n * B = B'ᴴ * G' ^ n * B') :
    (P = Q ↔ HasUniqueLabelFixingRangeIsometry S T) ∧
    (∃! W : Matrix u u ℂ,
      Wᴴ * W = 1 ∧ W * B = B' ∧ W * G = G' * W) :=
  ⟨pointedTetrahedral_fiveParameters_iff_labelFixingIsometry S T P Q hS hT,
    finiteMoment_sourceFixingIntertwiner_existsUnique G G' B B'
      hG hG' d hd hminimal hmom⟩

end TerminatingArithmeticRenewalSourceTestExact
end NCG
