/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandTannaka

/-!
# Frobenius as tensor holonomy
  (`corollary:frobenius-as-tensor-holonomy`, Gran-Tensor
   manuscript)

* `frobenius_tensor_holonomy`: every tensor automorphism of the
  fibre functor of a finite group is the reconstructed holonomy
  of a unique group element.  Hence an unramified arithmetic
  packet that assigns to every object of the finite rigid
  representation category a natural multiplicative operator
  compatible with tensor products, duals, and the fibre functor
  is one tensor automorphism and reconstructs one holonomy
  element of the Tannaka group.

Rendering disclosed: the manuscript's compatibility hypotheses
on the packet are precisely the definition of a tensor
automorphism (its proof's first sentence); the rendered formal
core is the unique-holonomy reconstruction, i.e. the bijectivity
of the Tannaka map of `thm:finite-Tannaka` in unique-existence
form.
-/

namespace NCG

open TannakaDuality.FiniteGroup

/-- `corollary:frobenius-as-tensor-holonomy`: every tensor
automorphism of the fibre functor is the holonomy of exactly one
group element. -/
theorem frobenius_tensor_holonomy (G : Type) [Group G]
    [Finite G]
    (η : CategoryTheory.Aut (forget ℂ G)) :
    ∃! g : G, equivHom ℂ G g = η :=
  (finite_tannaka_bijective G).existsUnique η

end NCG
