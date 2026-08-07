/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite Tannaka duality
  (`thm:finite-Tannaka`, `cor:Tannaka-group-iso`,
   Gran-Tensor manuscript)

* `finite_tannaka` / `finite_tannaka_bijective`: the boxed
  reconstruction `G → Aut^⊗(ω_G)`, `g ↦ (ρ_V(g))_V`, is an
  isomorphism — this is Mathlib's finite Tannaka duality
  (`TannakaDuality.FiniteGroup.equiv`) instantiated over `ℂ`;
* `tannaka_group_iso`: two finite groups whose fiber-functor
  tensor-automorphism groups are identified are isomorphic —
  composing the two dualities through the identification.

Rendering disclosed: in the corollary, the symmetric monoidal
equivalence `F : Rep(G) → Rep(H)` with monoidal natural unitary
`ω_H F ≅ ω_G` induces the tensor-automorphism identification;
that induction is the categorical bookkeeping and enters here
as the supplied identification datum.
-/

namespace NCG

open TannakaDuality.FiniteGroup

/-- `thm:finite-Tannaka`: the Tannaka reconstruction map over
`ℂ` is a group isomorphism. -/
noncomputable def finiteTannaka (G : Type) [Group G] [Finite G] :
    G ≃* CategoryTheory.Aut (forget ℂ G) :=
  equiv ℂ G

/-- `thm:finite-Tannaka`, bijectivity form: the boxed map
`g ↦ (ρ_V(g))_V` is bijective. -/
theorem finite_tannaka_bijective (G : Type) [Group G]
    [Finite G] :
    Function.Bijective (equivHom ℂ G) :=
  ⟨equivHom_injective, equivHom_surjective⟩

/-- `cor:Tannaka-group-iso`: identifying the fiber-functor
tensor-automorphism groups identifies the groups. -/
noncomputable def tannaka_group_iso {G H : Type} [Group G]
    [Group H] [Finite G] [Finite H]
    (e : CategoryTheory.Aut (forget ℂ G)
      ≃* CategoryTheory.Aut (forget ℂ H)) :
    G ≃* H :=
  ((equiv ℂ G).trans e).trans (equiv ℂ H).symm

end NCG
