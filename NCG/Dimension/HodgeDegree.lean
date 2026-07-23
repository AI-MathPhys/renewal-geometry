/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The volume-dual degree map `⋀²V ≃ ⋀^{d−2}V`

**Proposition `prop:volume-dual-degree`** (degree and equivariance of
the volume-dual response): the oriented volume-dual map
`H_ren = Vol⁻¹·b_ren` is a linear isomorphism
`⋀²V_sp ≅ ⋀^{d−2}V_sp` — the Clifford realisation of Hodge duality.

This file proves the dimension core: for a `d`-dimensional space,

`dim ⋀²V = C(d,2) = C(d,d−2) = dim ⋀^{d−2}V`

(`NCG.finrank_hodge_pair`), so the two degree sectors are abstractly
linearly isomorphic (`NCG.hodgeDegreeEquiv`).  Together with
`cor:relevance` this is what places the volume-dual response in degree
`d − 2` and makes it degree-one exactly at `d = 3`.  The
`SO(V)`-equivariance of the specific Clifford-product realisation is
not formalised. -/

namespace NCG

open Module exteriorPower

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **Proposition `prop:volume-dual-degree`, dimension identity**: the
bivector sector and the volume-dual sector have equal dimension,
`C(d,2) = C(d,d−2)`. -/
theorem finrank_hodge_pair (h : 2 ≤ finrank K V) :
    finrank K (⋀[K]^2 V)
      = finrank K (⋀[K]^(finrank K V - 2) V) := by
  rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq]
  exact (Nat.choose_symm h).symm

/-- **Proposition `prop:volume-dual-degree`**: the degree-complementing
volume-dual map exists as a linear isomorphism
`⋀²V ≅ ⋀^{d−2}V` (Hodge duality at the dimension level). -/
noncomputable def hodgeDegreeEquiv (h : 2 ≤ finrank K V) :
    (⋀[K]^2 V) ≃ₗ[K] (⋀[K]^(finrank K V - 2) V) :=
  LinearEquiv.ofFinrankEq _ _ (finrank_hodge_pair K V h)

/-- At `d = 3` the volume-dual sector is degree one: `C(3,1) = 3` — the
bivector sector is carried onto the elementary revision sector, the
content of the interference-closure selection. -/
theorem hodge_pair_degree_one (h3 : finrank K V = 3) :
    finrank K (⋀[K]^(finrank K V - 2) V) = 3 := by
  rw [exteriorPower.finrank_eq, h3]
  norm_num

end NCG
