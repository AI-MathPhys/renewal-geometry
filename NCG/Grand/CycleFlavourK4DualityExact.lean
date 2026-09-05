/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteMomentKrylovSourceDuality

/-!
# K4 cycle--flavour source duality

The finite `2r+1` moment theorem linked directly to the three-dimensional K4
cycle carrier.
-/

open Matrix

namespace NCG
namespace CycleFlavourK4DualityExact

/-- On the concrete K4 carrier the finite moment packet produces the unique
source-fixing unitary and simultaneously identifies the carrier dimension as
three. -/
theorem cycle_flavour_K4_duality
    {u p : Type*} [Fintype u] [Fintype p] [DecidableEq u]
    (Tflav Tcyc : Matrix u u ℂ)
    (Sflav Scyc : Matrix u p ℂ)
    (hTflav : Tflavᴴ = Tflav) (hTcyc : Tcycᴴ = Tcyc)
    (r : ℕ)
    (hminimal : Function.Surjective
      (krylovMat Tflav Sflav (r + 1)).mulVec)
    (hmom : ∀ n : ℕ, n ≤ 2 * r + 1 →
      Sflavᴴ * Tflav ^ n * Sflav = Scycᴴ * Tcyc ^ n * Scyc) :
    (∃! U : Matrix u u ℂ,
      Uᴴ * U = 1 ∧ U * Sflav = Scyc ∧ U * Tflav = Tcyc * U) ∧
      Module.finrank ℂ K4Carrier = 3 :=
  ⟨cycleFlavour_finiteMoment_sourceDuality Tflav Tcyc Sflav Scyc
      hTflav hTcyc r hminimal hmom,
    cycleFlavour_K4_cycleDimension⟩

end CycleFlavourK4DualityExact
end NCG
