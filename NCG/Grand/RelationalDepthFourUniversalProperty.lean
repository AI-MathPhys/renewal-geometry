/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RelationalDepthFour

/-!
# Universal consequence of the depth-four relation audit

The RC.12 presentation equivalence implies the operational sentence in the
manuscript: every group-valued local router or multiplicative action cochain
that kills the length-two/three/four relation bank is uniquely determined by
the additive endpoint.  Compact deck data remains a separate quotient by a
chosen period subgroup.
-/

namespace NCG

/-- Any multiplicative observable satisfying the RC.12 relation bank factors
uniquely through the free additive `A₃` endpoint accumulator. -/
theorem a3_depth_four_unique_endpoint_factorization
    {G : Type} [Group G]
    (f : FreeGroup (Fin 6) →* G)
    (hrel : ∀ r ∈ a3DepthFourRels, f r = 1) :
    ∃! F : Multiplicative (Fin 3 → ℤ) →* G,
      ∀ w, F (a3EndpointHom w) = f w := by
  obtain ⟨e, he⟩ := relational_depth_four.1
  let fgen : Fin 6 → G := fun a => f (FreeGroup.of a)
  have hfree : FreeGroup.lift fgen = f := by
    apply FreeGroup.ext_hom
    intro a
    simp [fgen]
  have hrel' : ∀ r ∈ a3DepthFourRels, FreeGroup.lift fgen r = 1 := by
    intro r hr
    rw [hfree]
    exact hrel r hr
  let q : PresentedGroup a3DepthFourRels →* G :=
    PresentedGroup.toGroup hrel'
  have hq : ∀ w, q (PresentedGroup.mk a3DepthFourRels w) = f w := by
    intro w
    have hcomp : q.comp (PresentedGroup.mk a3DepthFourRels) = f := by
      rw [← hfree]
      apply FreeGroup.ext_hom
      intro a
      simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      change PresentedGroup.toGroup hrel'
        (PresentedGroup.of a) = fgen a
      rw [PresentedGroup.toGroup.of]
    exact DFunLike.congr_fun hcomp w
  let F : Multiplicative (Fin 3 → ℤ) →* G :=
    q.comp e.symm.toMonoidHom
  refine ⟨F, ?_, ?_⟩
  · intro w
    change q (e.symm (a3EndpointHom w)) = f w
    rw [← he w, e.symm_apply_apply]
    exact hq w
  · intro F' hF'
    apply MonoidHom.ext
    intro z
    obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective
      a3DepthFourRels (e.symm z)
    have hz : a3EndpointHom w = z := by
      rw [← he w, hw]
      exact e.apply_symm_apply z
    calc
      F' z = F' (a3EndpointHom w) := by rw [hz]
      _ = f w := hF' w
      _ = F (a3EndpointHom w) := by
        symm
        change q (e.symm (a3EndpointHom w)) = f w
        rw [← he w, e.symm_apply_apply]
        exact hq w
      _ = F z := by rw [hz]

/-- A compact regulator is extra data: after the local RC.12 reduction to
`ℤ³`, one must still choose a period subgroup and quotient by it. -/
abbrev A3DeckQuotient
    (period : Subgroup (Multiplicative (Fin 3 → ℤ))) :=
  (Multiplicative (Fin 3 → ℤ)) ⧸ period

/-- Endpoint map after supplying an independent compact deck-period bank. -/
noncomputable def a3DeckEndpointHom
    (period : Subgroup (Multiplicative (Fin 3 → ℤ))) :
    FreeGroup (Fin 6) →* A3DeckQuotient period :=
  (QuotientGroup.mk' period).comp a3EndpointHom

end NCG
