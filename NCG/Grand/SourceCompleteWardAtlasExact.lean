/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Source-complete Ward atlases

This file proves the finite and closed-operator clauses of
`thm:SMOS-Ward-atlas`.  At finite cutoff the atlas residual is the Gram of
the part of the target projection missed by the closed atlas range.  Its
vanishing is therefore exactly target-range completeness.  The Ward Gram is
zero exactly when the defect vanishes on that target.  For an unbounded
operator, vanishing on a graph core extends to its closure by closedness.
-/

open scoped ComplexConjugate

namespace NCG
namespace SourceCompleteWardAtlasExact

variable {H F K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The closed range populated by a bounded source atlas. -/
def atlasRange (B : F →L[ℂ] H) : ClosedSubmodule ℂ H :=
  B.range.closure

/-- The part of the target projection missed by the atlas range. -/
noncomputable def atlasMiss (target : Submodule ℂ H)
    [target.HasOrthogonalProjection] (B : F →L[ℂ] H) : H →L[ℂ] H :=
  (1 - (atlasRange B).starProjection) ∘L target.starProjection

/-- The positive atlas residual.  This is the Gram rendering of
`P_tar (I-P_B) P_tar`. -/
noncomputable def atlasResidual (target : Submodule ℂ H)
    [target.HasOrthogonalProjection] (B : F →L[ℂ] H) : H →L[ℂ] H :=
  (atlasMiss target B).adjoint ∘L atlasMiss target B

/-- The Ward Gram `B* D* D B = (DB)*DB`. -/
noncomputable def wardGram (D : H →L[ℂ] K) (B : F →L[ℂ] H) : F →L[ℂ] F :=
  (D ∘L B).adjoint ∘L (D ∘L B)

/-- The positive Gram definition is literally the boxed projection formula
`P_tar (I-P_B) P_tar`. -/
theorem atlasResidual_eq_boxed (target : Submodule ℂ H)
    [target.HasOrthogonalProjection] (B : F →L[ℂ] H) :
    atlasResidual target B =
      target.starProjection ∘L (1 - (atlasRange B).starProjection) ∘L
        target.starProjection := by
  have hp : target.starProjection.adjoint = target.starProjection :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      target.starProjection_isSymmetric
  have hq : (atlasRange B).starProjection.adjoint =
      (atlasRange B).starProjection :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (atlasRange B).starProjection_isSymmetric
  unfold atlasResidual atlasMiss
  rw [ContinuousLinearMap.adjoint_comp, hp]
  simp only [map_sub, hq, ContinuousLinearMap.adjoint_one]
  ext x
  have hpapp : target.starProjection (target.starProjection x) =
      target.starProjection x :=
    target.starProjection_eq_self_iff.mpr (by simp)
  have hqapp : (atlasRange B).starProjection
      ((atlasRange B).starProjection (target.starProjection x)) =
      (atlasRange B).starProjection (target.starProjection x) :=
    (atlasRange B).starProjection_eq_self_iff.mpr (by simp)
  simp [sub_eq_add_neg, add_assoc, hpapp, hqapp]

theorem atlasResidual_eq_zero_iff (target : Submodule ℂ H)
    [target.HasOrthogonalProjection] (B : F →L[ℂ] H) :
    atlasResidual target B = 0 ↔ target ≤ atlasRange B := by
  rw [atlasResidual, ContinuousLinearMap.adjoint_comp_self_eq_zero_iff]
  constructor
  · intro h x hx
    have hzero := congrArg (fun T : H →L[ℂ] H => T x) h
    have htarget : target.starProjection x = x :=
      target.starProjection_eq_self_iff.mpr hx
    have hproj : (atlasRange B).starProjection x = x := by
      have hd : x - (atlasRange B).starProjection x = 0 := by
        simpa [atlasMiss, htarget] using hzero
      exact (sub_eq_zero.mp hd).symm
    exact (atlasRange B).starProjection_eq_self_iff.mp hproj
  · intro h
    ext x
    have htarget : target.starProjection x ∈ target := by simp
    have hatlas : target.starProjection x ∈ atlasRange B := h htarget
    simp [atlasMiss, (atlasRange B).starProjection_eq_self_iff.mpr hatlas]

theorem wardGram_eq_zero_iff (D : H →L[ℂ] K) (B : F →L[ℂ] H) :
    wardGram D B = 0 ↔ D ∘L B = 0 := by
  exact ContinuousLinearMap.adjoint_comp_self_eq_zero_iff

/-- Finite-cutoff operator Ward equivalence.  The support equation says that
the defect has no input outside the declared target carrier. -/
theorem wardGram_eq_zero_iff_target_defect_zero
    (target : Submodule ℂ H) [target.HasOrthogonalProjection]
    (B : F →L[ℂ] H) (D : H →L[ℂ] K)
    (hcomplete : atlasResidual target B = 0)
    (hsupport : D = D ∘L target.starProjection) :
    wardGram D B = 0 ↔ D ∘L target.starProjection = 0 := by
  have htarget : target ≤ atlasRange B :=
    (atlasResidual_eq_zero_iff target B).mp hcomplete
  constructor
  · intro hgram
    have hDB : D ∘L B = 0 := (wardGram_eq_zero_iff D B).mp hgram
    have hrange : B.range ≤ D.ker := by
      rintro x ⟨y, rfl⟩
      have hz := congrArg (fun T : F →L[ℂ] K => T y) hDB
      simpa using hz
    have hclosedRange : atlasRange B ≤ D.ker := by
      exact B.range.topologicalClosure_minimal hrange D.isClosed_ker
    ext x
    have hxmem : target.starProjection x ∈ atlasRange B :=
      htarget (by simp)
    exact hclosedRange hxmem
  · intro htargetZero
    have hD : D = 0 := by
      rw [hsupport, htargetZero]
    exact (wardGram_eq_zero_iff D B).mpr (by rw [hD]; simp)

/-! ## Closed unbounded operators -/

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A closed Ward defect which vanishes on a graph core vanishes throughout
its closed domain.  This is the continuum-atlas clause of the manuscript. -/
theorem closed_defect_vanishes_on_core
    (D : E →ₗ.[ℂ] G) (hclosed : D.IsClosed) (S : Submodule ℂ E)
    (hcore : D.HasCore S)
    (hzero : ∀ (x : E) (hx : x ∈ S),
      D ⟨x, hcore.le_domain hx⟩ = 0) :
    ∀ x : D.domain, D x = 0 := by
  let Z : Submodule ℂ (E × G) := LinearMap.ker (LinearMap.snd ℂ E G)
  have hZclosed : IsClosed (Z : Set (E × G)) := by
    exact isClosed_eq continuous_snd continuous_const
  have hrestrict : (D.domRestrict S).graph ≤ Z := by
    intro z hz
    rw [LinearPMap.mem_graph_iff] at hz
    rcases hz with ⟨x, hx, hval⟩
    change z.2 = 0
    rw [← hval]
    have hxS : (x : E) ∈ S := x.property.1
    have hxeq :
        D.domRestrict S x = D ⟨(x : E), hcore.le_domain hxS⟩ :=
      LinearPMap.domRestrict_apply rfl
    rw [hxeq, hzero (x : E) hxS]
  have hRclosable : (D.domRestrict S).IsClosable :=
    hclosed.isClosable.leIsClosable LinearPMap.domRestrict_le
  have hclosure : (D.domRestrict S).graph.topologicalClosure ≤ Z :=
    (D.domRestrict S).graph.topologicalClosure_minimal hrestrict hZclosed
  intro x
  have hxgraph : ((x : E), D x) ∈ D.graph := D.mem_graph x
  have hxclosure : ((x : E), D x) ∈
      (D.domRestrict S).graph.topologicalClosure := by
    rw [hRclosable.graph_closure_eq_closure_graph, hcore.closure_eq]
    exact hxgraph
  exact hclosure hxclosure

end SourceCompleteWardAtlasExact
end NCG
