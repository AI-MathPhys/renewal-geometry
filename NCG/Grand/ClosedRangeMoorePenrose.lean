/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Moore--Penrose inverse for closed-range Hilbert operators

This file constructs the bounded Moore--Penrose inverse of a bounded operator
between complex Hilbert spaces from the single analytic hypothesis that its
range is closed.  The construction restricts the operator to the orthogonal
complement of its kernel and applies the Banach inverse theorem there.
-/

open Set ContinuousLinearMap Submodule
open scoped InnerProduct

noncomputable section

namespace NCG
namespace ClosedRangeMoorePenrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Restriction of an operator to the orthogonal complement of its kernel. -/
def reduced (S : E →L[ℂ] F) : S.kerᗮ →L[ℂ] F :=
  S.domRestrict S.kerᗮ

/-- The kernel-orthogonal restriction is injective. -/
theorem reduced_injective (S : E →L[ℂ] F) :
    Function.Injective (reduced S) := by
  intro x y hxy
  apply Subtype.ext
  have hk : (x : E) - (y : E) ∈ S.ker := by
    rw [LinearMap.mem_ker]
    rw [map_sub]
    change S (x : E) = S (y : E) at hxy
    exact sub_eq_zero.mpr hxy
  have ho : (x : E) - (y : E) ∈ S.kerᗮ :=
    S.kerᗮ.sub_mem x.2 y.2
  have hz : (x : E) - (y : E) ∈ S.ker ⊓ S.kerᗮ := ⟨hk, ho⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hz
  exact sub_eq_zero.mp hz

/-- Restriction to the kernel orthogonal does not change the range. -/
theorem reduced_range_eq (S : E →L[ℂ] F) :
    (reduced S).range = S.range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    let z : S.kerᗮ :=
      ⟨x - S.ker.starProjection x,
        S.ker.sub_starProjection_mem_orthogonal x⟩
    refine ⟨z, ?_⟩
    change S (x - S.ker.starProjection x) = S x
    rw [map_sub]
    have hp : S (S.ker.starProjection x) = 0 := by
      have hmem := S.ker.starProjection_apply_mem x
      rw [LinearMap.mem_ker] at hmem
      exact hmem
    rw [hp, sub_zero]

/-- Closedness of the reduced range follows from closedness of the original
range. -/
theorem reduced_isClosed_range (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    IsClosed ((reduced S).range : Set F) := by
  rw [reduced_range_eq]
  exact hclosed

/-- The bounded Moore--Penrose inverse of a closed-range operator. -/
noncomputable def pinv (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) : F →L[ℂ] E := by
  let R := reduced S
  have hRclosed : IsClosed (R.range : Set F) :=
    reduced_isClosed_range S hclosed
  letI : CompleteSpace R.range := hRclosed.completeSpace_coe
  exact S.kerᗮ.subtypeL.comp
    ((R.equivRange (reduced_injective S) hRclosed).symm.toContinuousLinearMap.comp
      R.range.orthogonalProjectionOnto)

/-- The pseudoinverse takes values in the kernel orthogonal. -/
theorem pinv_mem_ker_orthogonal (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) (y : F) :
    pinv S hclosed y ∈ S.kerᗮ := by
  unfold pinv
  exact Subtype.mem _

/-- Applying the operator after its pseudoinverse gives the orthogonal
projection onto its closed range. -/
theorem apply_pinv (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) (y : F) :
    S (pinv S hclosed y) = S.range.starProjection y := by
  let R := reduced S
  have hRclosed : IsClosed (R.range : Set F) :=
    reduced_isClosed_range S hclosed
  letI : CompleteSpace R.range := hRclosed.completeSpace_coe
  have hrange : R.range = S.range := reduced_range_eq S
  change R
      ((R.equivRange (reduced_injective S) hRclosed).symm
        (R.range.orthogonalProjectionOnto y)) =
    S.range.starProjection y
  have hleft :=
    (R.equivRange (reduced_injective S) hRclosed).apply_symm_apply
      (R.range.orthogonalProjectionOnto y)
  have hval : R
      ((R.equivRange (reduced_injective S) hRclosed).symm
        (R.range.orthogonalProjectionOnto y)) =
      R.range.starProjection y := congrArg Subtype.val hleft
  rw [hval]
  symm
  apply S.range.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← hrange]
    exact R.range.starProjection_apply_mem y
  · intro w hw
    apply R.range.starProjection_inner_eq_zero
    rw [hrange]
    exact hw

/-- The pseudoinverse after the operator is projection onto the kernel
orthogonal. -/
theorem pinv_apply (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) (x : E) :
    pinv S hclosed (S x) = S.kerᗮ.starProjection x := by
  have hp : pinv S hclosed (S x) ∈ S.kerᗮ :=
    pinv_mem_ker_orthogonal S hclosed (S x)
  have hq : S.kerᗮ.starProjection x ∈ S.kerᗮ :=
    S.kerᗮ.starProjection_apply_mem x
  have hsub :
      (⟨pinv S hclosed (S x), hp⟩ : S.kerᗮ) =
        ⟨S.kerᗮ.starProjection x, hq⟩ := by
    apply reduced_injective S
    change S (pinv S hclosed (S x)) =
      S (S.kerᗮ.starProjection x)
    rw [apply_pinv]
    have hxrange : S x ∈ S.range := ⟨x, rfl⟩
    rw [S.range.starProjection_eq_self_iff.mpr hxrange]
    have hk : x - S.kerᗮ.starProjection x ∈ S.ker := by
      have hmem := S.ker.starProjection_apply_mem x
      rw [S.ker.starProjection_orthogonal_val]
      simpa only [sub_sub_cancel] using hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hk
    exact hk
  exact congrArg Subtype.val hsub

/-- Operator form of the range-projection Penrose identity. -/
theorem comp_pinv (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    S.comp (pinv S hclosed) = S.range.starProjection := by
  ext y
  exact apply_pinv S hclosed y

/-- Operator form of the kernel-complement projection identity. -/
theorem pinv_comp (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    (pinv S hclosed).comp S = S.kerᗮ.starProjection := by
  ext x
  exact pinv_apply S hclosed x

/-- The pseudoinverse absorbs the projection onto the original range. -/
theorem pinv_comp_rangeProjection (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    (pinv S hclosed).comp S.range.starProjection = pinv S hclosed := by
  ext y
  calc
    pinv S hclosed (S.range.starProjection y) =
        pinv S hclosed (S (pinv S hclosed y)) := by
      rw [apply_pinv]
    _ = S.kerᗮ.starProjection (pinv S hclosed y) := pinv_apply S hclosed _
    _ = pinv S hclosed y :=
      S.kerᗮ.starProjection_eq_self_iff.mpr
        (pinv_mem_ker_orthogonal S hclosed y)

/-- The four Moore--Penrose equations for a rectangular Hilbert operator. -/
structure IsMoorePenrose (S : E →L[ℂ] F) (Q : F →L[ℂ] E) : Prop where
  sqs : (S.comp Q).comp S = S
  qsq : (Q.comp S).comp Q = Q
  selfAdjoint_sq : IsSelfAdjoint (S.comp Q)
  selfAdjoint_qs : IsSelfAdjoint (Q.comp S)

/-- The closed-range construction satisfies all four Penrose equations. -/
theorem isMoorePenrose_pinv (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    IsMoorePenrose S (pinv S hclosed) := by
  constructor
  · ext x
    simp only [comp_apply, apply_pinv]
    exact S.range.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
  · ext y
    simp only [comp_apply, pinv_apply]
    exact S.kerᗮ.starProjection_eq_self_iff.mpr
      (pinv_mem_ker_orthogonal S hclosed y)
  · rw [comp_pinv]
    exact isSelfAdjoint_starProjection S.range
  · rw [pinv_comp]
    exact isSelfAdjoint_starProjection S.kerᗮ

/-- The source Gram. -/
def gram (S : E →L[ℂ] F) : E →L[ℂ] E :=
  (S†).comp S

/-- The Moore--Penrose inverse of the source Gram, constructed from the
closed-range pseudoinverse of the source map. -/
def gramPinv (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) : E →L[ℂ] E :=
  (pinv S hclosed).comp ((pinv S hclosed)†)

/-- The adjoint pseudoinverse is absorbed by the source-range projection. -/
theorem rangeProjection_comp_adjoint_pinv (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    S.range.starProjection.comp ((pinv S hclosed)†) =
      (pinv S hclosed)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (pinv_comp_rangeProjection S hclosed)
  simpa only [adjoint_comp, adjoint_adjoint,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection S.range)] using h

/-- Both Gram--pseudoinverse products are the support projection. -/
theorem gram_comp_gramPinv (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    (gram S).comp (gramPinv S hclosed) = S.kerᗮ.starProjection := by
  calc
    (gram S).comp (gramPinv S hclosed) =
        (S†).comp
          ((S.comp (pinv S hclosed)).comp ((pinv S hclosed)†)) := rfl
    _ = (S†).comp
          (S.range.starProjection.comp ((pinv S hclosed)†)) := by
      rw [comp_pinv]
    _ = (S†).comp ((pinv S hclosed)†) := by
      rw [rangeProjection_comp_adjoint_pinv]
    _ = ((pinv S hclosed).comp S)† := by rw [adjoint_comp]
    _ = S.kerᗮ.starProjection† := by rw [pinv_comp]
    _ = S.kerᗮ.starProjection :=
      isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection S.kerᗮ)

theorem gramPinv_comp_gram (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    (gramPinv S hclosed).comp (gram S) = S.kerᗮ.starProjection := by
  have hselfG : (gram S)† = gram S := by
    simp only [gram, adjoint_comp, adjoint_adjoint]
  have hselfD : (gramPinv S hclosed)† = gramPinv S hclosed := by
    simp only [gramPinv, adjoint_comp, adjoint_adjoint]
  have h := congrArg ContinuousLinearMap.adjoint
    (gram_comp_gramPinv S hclosed)
  simpa only [adjoint_comp, hselfG, hselfD,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection S.kerᗮ)] using h

/-- The closed-range Gram inverse really is the Moore--Penrose inverse of
G = S†S. -/
theorem isMoorePenrose_gramPinv (S : E →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    IsMoorePenrose (gram S) (gramPinv S hclosed) := by
  have hGmem : ∀ x : E, gram S x ∈ S.kerᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro k hk
    rw [gram, comp_apply, adjoint_inner_right]
    rw [LinearMap.mem_ker] at hk
    change S k = 0 at hk
    rw [hk, inner_zero_left]
  constructor
  · rw [gram_comp_gramPinv]
    ext x
    simp only [comp_apply]
    exact S.kerᗮ.starProjection_eq_self_iff.mpr (hGmem x)
  · rw [gramPinv_comp_gram]
    ext x
    simp only [comp_apply]
    exact S.kerᗮ.starProjection_eq_self_iff.mpr
      (pinv_mem_ker_orthogonal S hclosed
        (((pinv S hclosed)†) x))
  · rw [gram_comp_gramPinv]
    exact isSelfAdjoint_starProjection S.kerᗮ
  · rw [gramPinv_comp_gram]
    exact isSelfAdjoint_starProjection S.kerᗮ

/-- The Gram pseudoinverse followed by the cross Gram is the minimum-norm
closed-range router. -/
theorem gramPinv_comp_crossGram {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (S : E →L[ℂ] F) (T : G →L[ℂ] F)
    (hclosed : IsClosed (S.range : Set F)) :
    (gramPinv S hclosed).comp ((S†).comp T) =
      (pinv S hclosed).comp T := by
  have hAdj :
      ((pinv S hclosed)†).comp (S†) = S.range.starProjection := by
    calc
      ((pinv S hclosed)†).comp (S†) =
          (S.comp (pinv S hclosed))† := by
        rw [adjoint_comp]
      _ = S.range.starProjection† := by rw [comp_pinv]
      _ = S.range.starProjection :=
        isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection S.range)
  calc
    (gramPinv S hclosed).comp ((S†).comp T) =
        ((pinv S hclosed).comp
          (((pinv S hclosed)†).comp (S†))).comp T := rfl
    _ = ((pinv S hclosed).comp S.range.starProjection).comp T := by
      rw [hAdj]
    _ = (pinv S hclosed).comp T := by
      rw [pinv_comp_rangeProjection]

end ClosedRangeMoorePenrose
end NCG
