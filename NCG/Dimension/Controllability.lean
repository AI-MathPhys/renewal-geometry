/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Interference controllability (connectedness core)

**Proposition `prop:interference-controllability`**: if the oriented
holonomy transports carry one-parameter families whose generators span
`so(V)`, the closed holonomy group is all of `SO(V)`.  The
connectedness core proved here: **an open subgroup of a connected
topological group is the whole group** (`NCG.open_subgroup_eq_top`) —
an open subgroup is closed (its complement is a union of open
cosets), hence clopen, hence everything by connectedness.  This is
the final step of the closed-subgroup argument; the Lie
closed-subgroup theorem and the rank hypothesis
`Lie⟨Xₑ⟩ = so(V)` are the noted inputs.
-/

namespace NCG

/-- **Proposition `prop:interference-controllability`
(connectedness core)**: an open subgroup of a connected topological
group is the whole group — a closed subgroup whose Lie algebra is
full is open, and openness plus connectedness forces surjectivity of
the holonomy. -/
theorem open_subgroup_eq_top {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [PreconnectedSpace G]
    (H : Subgroup G) (hopen : IsOpen (H : Set G)) : H = ⊤ := by
  have hclosed : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen H hopen
  have hclopen : IsClopen (H : Set G) := ⟨hclosed, hopen⟩
  exact Subgroup.coe_eq_univ.mp (hclopen.eq_univ ⟨1, H.one_mem⟩)

end NCG
