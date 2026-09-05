/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTMobiusSecants

/-!
# Face-connectedness of Möbius generators

Face consistency says that restricting a subset action to a face depends only
on the intersection with that face.  On a proper face there is therefore an
inert slot, and Boolean-lattice Möbius cancellation makes the top connected
generator vanish.  The additive map `R` models the manuscript's compression
`X ↦ Jᴴ X J`.
-/

open Finset

namespace NCG

/-- A Möbius connected component restricts to zero on every proper
face-consistent face. -/
theorem mobius_connected_vanishes_on_proper_face
    {ι M N : Type*} [DecidableEq ι] [AddCommGroup M] [AddCommGroup N]
    (L : Finset ι → M) (R : M →+ N) {A C : Finset ι}
    (hCA : C ⊂ A)
    (hface : ∀ B, R (L B) = R (L (B ∩ C))) :
    R (∑ B ∈ A.powerset,
        (-1 : ℤ) ^ (#A - #B) • L B) = 0 := by
  obtain ⟨hsub, hne⟩ := hCA
  obtain ⟨i, hiA, hiC⟩ : ∃ i, i ∈ A ∧ i ∉ C := by
    by_contra h
    push Not at h
    exact hne (fun i hiA => h i hiA)
  have hinert : ∀ D, i ∉ D →
      R (L (insert i D)) = R (L D) := by
    intro D _hiD
    rw [hface (insert i D), hface D]
    congr 2
    ext x
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨hxi, hxC⟩
      exact ⟨hxi.resolve_left (fun hxi => hiC (hxi ▸ hxC)), hxC⟩
    · rintro ⟨hxD, hxC⟩
      exact ⟨Or.inr hxD, hxC⟩
  have hzero := (gt_subset_secants (fun B => R (L B))).2
    A i hiA hinert
  rw [map_sum]
  simpa only [map_zsmul] using hzero

/-- Exact assembly of Möbius inversion with its proper-face connectedness
clause.  The family `L` is understood on the common ambient carrier and `R`
is the declared face compression. -/
theorem mobius_inversion_and_face_connectedness
    {ι M N : Type*} [DecidableEq ι] [AddCommGroup M] [AddCommGroup N]
    (L : Finset ι → M) (hL0 : L ∅ = 0) (R : M →+ N)
    {A C : Finset ι} (hCA : C ⊂ A)
    (hface : ∀ B, R (L B) = R (L (B ∩ C))) :
    (L A = ∑ B ∈ A.powerset.filter (fun B => B ≠ ∅),
        ∑ D ∈ B.powerset, (-1 : ℤ) ^ (#B - #D) • L D)
      ∧ R (∑ B ∈ A.powerset,
          (-1 : ℤ) ^ (#A - #B) • L B) = 0 := by
  exact ⟨gt_mobius_inversion L hL0 A,
    mobius_connected_vanishes_on_proper_face L R hCA hface⟩

end NCG
