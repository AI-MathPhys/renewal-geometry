/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import NCG.Grand.ClosedRangeMoorePenrose

/-!
# Common-action router on Hilbert spaces with closed source range

This module proves the infinite-dimensional closed-range formulation of
thm:common-action-router.  It uses the closed-range Moore--Penrose inverse,
not an invertibility or finite-dimensional surrogate.
-/

open Set ContinuousLinearMap Submodule
open scoped InnerProduct

noncomputable section

namespace NCG
namespace CommonActionHilbert

universe u v w

variable {XΓ : Type u} [NormedAddCommGroup XΓ] [InnerProductSpace ℂ XΓ]
  [CompleteSpace XΓ]
variable {XE : Type v} [NormedAddCommGroup XE] [InnerProductSpace ℂ XE]
  [CompleteSpace XE]
variable {Y : Type w} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
  [CompleteSpace Y]

open ClosedRangeMoorePenrose

def sourceGram (BΓ : XΓ →L[ℂ] Y) : XΓ →L[ℂ] XΓ :=
  (BΓ†).comp BΓ

def crossGram (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y) :
    XE →L[ℂ] XΓ :=
  (BΓ†).comp BE

def targetGram (BE : XE →L[ℂ] Y) : XE →L[ℂ] XE :=
  (BE†).comp BE

/-- The manuscript router K = GΓ† C. -/
def router (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) : XE →L[ℂ] XΓ :=
  (gramPinv BΓ hclosed).comp (crossGram BΓ BE)

/-- The orthogonal Schur innovation source. -/
def residual (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y) :
    XE →L[ℂ] Y :=
  ((1 : Y →L[ℂ] Y) -
    BΓ.range.topologicalClosure.starProjection).comp BE

/-- The Schur residual operator. -/
def schur (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y) :
    XE →L[ℂ] XE :=
  (BE†).comp (residual BΓ BE)

/-- The pseudoinverse router is exactly the minimum-norm closed-range lift. -/
theorem router_eq_pinv_comp
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) :
    router BΓ BE hclosed = (pinv BΓ hclosed).comp BE := by
  exact gramPinv_comp_crossGram BΓ BE hclosed

/-- The router reconstructs the range projection of the second source. -/
theorem source_comp_router
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) :
    BΓ.comp (router BΓ BE hclosed) =
      BΓ.range.topologicalClosure.starProjection.comp BE := by
  ext y
  rw [router_eq_pinv_comp]
  simp only [comp_apply, apply_pinv]
  symm
  apply BΓ.range.topologicalClosure.eq_starProjection_of_mem_of_inner_eq_zero
  · exact BΓ.range.le_topologicalClosure
      (BΓ.range.starProjection_apply_mem (BE y))
  · intro w hw
    apply BΓ.range.starProjection_inner_eq_zero
    rw [hclosed.submodule_topologicalClosure_eq] at hw
    exact hw

theorem residual_apply (BΓ : XΓ →L[ℂ] Y)
    (BE : XE →L[ℂ] Y) (y : XE) :
    residual BΓ BE y =
      BE y - BΓ.range.topologicalClosure.starProjection (BE y) := by
  rfl

/-- The innovation source is the unexplained part after routing. -/
theorem residual_eq_source_sub_router
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) :
    residual BΓ BE = BE - BΓ.comp (router BΓ BE hclosed) := by
  ext y
  rw [residual_apply]
  have hrec := congrArg (fun T : XE →L[ℂ] Y => T y)
    (source_comp_router BΓ BE hclosed)
  simpa only [comp_apply, sub_apply] using
    congrArg (fun z => BE y - z) hrec.symm

/-- The Schur formula is exactly the Gram of the orthogonal innovation. -/
theorem schur_eq_residualGram
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y) :
    schur BΓ BE = (residual BΓ BE)†.comp (residual BΓ BE) := by
  ext x
  refine ext_inner_right ℂ fun y => ?_
  simp only [schur, comp_apply, adjoint_inner_left]
  have horth :
      inner ℂ (residual BΓ BE x)
        (BΓ.range.topologicalClosure.starProjection (BE y)) = 0 := by
    rw [residual_apply]
    exact BΓ.range.topologicalClosure.starProjection_inner_eq_zero _ _
      (BΓ.range.topologicalClosure.starProjection_apply_mem _)
  calc
    inner ℂ (residual BΓ BE x) (BE y) =
        inner ℂ (residual BΓ BE x)
          (residual BΓ BE y +
            BΓ.range.topologicalClosure.starProjection (BE y)) := by
      congr 1
      rw [residual_apply]
      abel
    _ = inner ℂ (residual BΓ BE x) (residual BΓ BE y) := by
      rw [inner_add_right, horth, add_zero]

/-- Positivity of the Hilbert-space Schur residual. -/
theorem schur_isPositive
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y) :
    (schur BΓ BE).IsPositive := by
  rw [schur_eq_residualGram]
  exact isPositive_adjoint_comp_self _

/-- Exact Pythagoras behind the variational formula. -/
theorem variational_pythagoras
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) (x : XΓ) (y : XE) :
    ‖BΓ x + BE y‖ ^ 2 =
      ‖BΓ (x + router BΓ BE hclosed y)‖ ^ 2 +
        ‖residual BΓ BE y‖ ^ 2 := by
  have hdec :
      BΓ x + BE y =
        BΓ (x + router BΓ BE hclosed y) + residual BΓ BE y := by
    rw [map_add, residual_apply]
    have hrec := congrArg (fun T : XE →L[ℂ] Y => T y)
      (source_comp_router BΓ BE hclosed)
    simp only [comp_apply] at hrec
    rw [hrec]
    abel
  have horth :
      inner ℂ (BΓ (x + router BΓ BE hclosed y))
        (residual BΓ BE y) = 0 := by
    rw [← inner_conj_symm, residual_apply]
    have hrange :
        BΓ (x + router BΓ BE hclosed y) ∈ BΓ.range :=
      ⟨_, rfl⟩
    rw [BΓ.range.topologicalClosure.starProjection_inner_eq_zero _ _
      (BΓ.range.le_topologicalClosure hrange)]
    simp
  rw [hdec]
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth

/-- Variational characterization: the Schur value is the attained infimum
over the first Hilbert variable. -/
theorem innovation_variational
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) (y : XE) :
    (∀ x : XΓ, ‖residual BΓ BE y‖ ^ 2 ≤ ‖BΓ x + BE y‖ ^ 2) ∧
      ∃ x : XΓ, ‖BΓ x + BE y‖ ^ 2 = ‖residual BΓ BE y‖ ^ 2 := by
  constructor
  · intro x
    rw [variational_pythagoras BΓ BE hclosed x y]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · refine ⟨-router BΓ BE hclosed y, ?_⟩
    rw [variational_pythagoras BΓ BE hclosed]
    simp

/-- Vanishing Schur residual is equivalent to exact source reconstruction. -/
theorem schur_eq_zero_iff
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) :
    schur BΓ BE = 0 ↔ BE = BΓ.comp (router BΓ BE hclosed) := by
  rw [schur_eq_residualGram, adjoint_comp_self_eq_zero_iff,
    residual_eq_source_sub_router, sub_eq_zero]

/-- The target Gram splits into explained router Gram plus the Schur
innovation. -/
theorem targetGram_eq_routerGram_add_schur
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) :
    targetGram BE =
      (router BΓ BE hclosed)†.comp
        ((sourceGram BΓ).comp (router BΓ BE hclosed)) +
      schur BΓ BE := by
  ext x
  refine ext_inner_right ℂ fun y => ?_
  simp only [targetGram, sourceGram, comp_apply, adjoint_inner_left,
    add_apply, inner_add_left]
  have hdecx :
      BE x = BΓ (router BΓ BE hclosed x) + residual BΓ BE x := by
    have h := congrArg (fun T : XE →L[ℂ] Y => T x)
      (residual_eq_source_sub_router BΓ BE hclosed)
    simp only [sub_apply, comp_apply] at h
    rw [h]
    abel
  have hdecy :
      BE y = BΓ (router BΓ BE hclosed y) + residual BΓ BE y := by
    have h := congrArg (fun T : XE →L[ℂ] Y => T y)
      (residual_eq_source_sub_router BΓ BE hclosed)
    simp only [sub_apply, comp_apply] at h
    rw [h]
    abel
  have hcross₁ :
      inner ℂ (BΓ (router BΓ BE hclosed x)) (residual BΓ BE y) = 0 := by
    have hz :
        inner ℂ (residual BΓ BE y)
          (BΓ (router BΓ BE hclosed x)) = 0 := by
      rw [residual_apply]
      exact BΓ.range.topologicalClosure.starProjection_inner_eq_zero _ _
        (BΓ.range.le_topologicalClosure
          ⟨router BΓ BE hclosed x, rfl⟩)
    calc
      inner ℂ (BΓ (router BΓ BE hclosed x)) (residual BΓ BE y) =
          star (inner ℂ (residual BΓ BE y)
            (BΓ (router BΓ BE hclosed x))) :=
        (inner_conj_symm _ _).symm
      _ = 0 := by rw [hz]; simp
  have hcross₂ :
      inner ℂ (residual BΓ BE x) (BΓ (router BΓ BE hclosed y)) = 0 := by
    rw [residual_apply]
    exact BΓ.range.topologicalClosure.starProjection_inner_eq_zero _ _
      (BΓ.range.le_topologicalClosure ⟨_, rfl⟩)
  rw [hdecx, hdecy, inner_add_left, inner_add_right, inner_add_right,
    hcross₁, hcross₂, zero_add, add_zero]
  rw [schur_eq_residualGram]
  simp only [comp_apply, adjoint_inner_left]

/-- Second vanishing criterion in the manuscript. -/
theorem schur_eq_zero_iff_targetGram
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) :
    schur BΓ BE = 0 ↔
      targetGram BE =
        (router BΓ BE hclosed)†.comp
          ((sourceGram BΓ).comp (router BΓ BE hclosed)) := by
  constructor
  · intro hz
    rw [targetGram_eq_routerGram_add_schur BΓ BE hclosed, hz, add_zero]
  · intro heq
    have h := targetGram_eq_routerGram_add_schur BΓ BE hclosed
    rw [heq] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- Exact source-native Ward routing.  The support equation is precisely the
source-native qualifier for a possibly singular first Gram. -/
theorem exactWard_router
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y)) (W : XE →L[ℂ] XΓ)
    (hC : crossGram BΓ BE = (sourceGram BΓ).comp W)
    (hGE : targetGram BE = (crossGram BΓ BE)†.comp W)
    (hW : BΓ.kerᗮ.starProjection.comp W = W) :
    router BΓ BE hclosed = W ∧
      targetGram BE = W†.comp ((sourceGram BΓ).comp W) ∧
      schur BΓ BE = 0 := by
  have hK : router BΓ BE hclosed = W := by
    rw [router, hC]
    calc
      (gramPinv BΓ hclosed).comp ((sourceGram BΓ).comp W) =
          ((gramPinv BΓ hclosed).comp (sourceGram BΓ)).comp W := rfl
      _ = BΓ.kerᗮ.starProjection.comp W := by
        rw [sourceGram]
        calc
          ((gramPinv BΓ hclosed).comp ((BΓ†).comp BΓ)).comp W =
              ((pinv BΓ hclosed).comp BΓ).comp W := by
            exact congrArg (fun Q => Q.comp W)
              (gramPinv_comp_crossGram BΓ BΓ hclosed)
          _ = BΓ.kerᗮ.starProjection.comp W := by rw [pinv_comp]
      _ = W := hW
  have hmetric : targetGram BE =
      W†.comp ((sourceGram BΓ).comp W) := by
    rw [hGE, hC, adjoint_comp]
    simp only [sourceGram, adjoint_comp, adjoint_adjoint]
    rfl
  refine ⟨hK, hmetric, ?_⟩
  apply (schur_eq_zero_iff_targetGram BΓ BE hclosed).2
  rw [hK]
  exact hmetric

/-! ### Approximate Ward routing -/

/-- Source error along the graph direction (-Wy,y). -/
def wardResidual (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (W : XE →L[ℂ] XΓ) : XE →L[ℂ] Y :=
  BE - BΓ.comp W

/-- Projecting away the first source removes its entire Ward component. -/
theorem residual_eq_projectedWard
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (W : XE →L[ℂ] XΓ) :
    residual BΓ BE =
      ((1 : Y →L[ℂ] Y) -
        BΓ.range.topologicalClosure.starProjection).comp
          (wardResidual BΓ BE W) := by
  ext y
  simp only [residual, wardResidual, comp_apply, sub_apply,
    one_apply_eq_self, map_sub]
  have hfix :
      BΓ.range.topologicalClosure.starProjection (BΓ (W y)) =
        BΓ (W y) :=
    BΓ.range.topologicalClosure.starProjection_eq_self_iff.mpr
      (BΓ.range.le_topologicalClosure ⟨W y, rfl⟩)
  rw [hfix]
  abel

/-- Orthogonal projection cannot enlarge the Ward source error. -/
theorem norm_residual_le_wardResidual
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (W : XE →L[ℂ] XΓ) :
    ‖residual BΓ BE‖ ≤ ‖wardResidual BΓ BE W‖ := by
  rw [residual_eq_projectedWard BΓ BE W]
  let U : Submodule ℂ Y := BΓ.range.topologicalClosure
  change ‖((1 : Y →L[ℂ] Y) - U.starProjection).comp
      (wardResidual BΓ BE W)‖ ≤ ‖wardResidual BΓ BE W‖
  rw [← U.starProjection_orthogonal']
  calc
    ‖Uᗮ.starProjection.comp (wardResidual BΓ BE W)‖
        ≤ ‖Uᗮ.starProjection‖ * ‖wardResidual BΓ BE W‖ :=
      opNorm_comp_le _ _
    _ ≤ 1 * ‖wardResidual BΓ BE W‖ := by
      gcongr
      exact Uᗮ.starProjection_norm_le
    _ = ‖wardResidual BΓ BE W‖ := one_mul _

/-- The approximate Ward quadratic form bounds the positive Schur residual
by the same scalar square. -/
theorem approximateWard_schur_bound
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y))
    (W : XE →L[ℂ] XΓ) (ε : ℝ) (hε : 0 ≤ ε)
    (hWard : ‖wardResidual BΓ BE W‖ ≤ ε) :
    (schur BΓ BE).IsPositive ∧
      ∀ y : XE, (schur BΓ BE).reApplyInnerSelf y ≤ ε ^ 2 * ‖y‖ ^ 2 := by
  constructor
  · exact schur_isPositive BΓ BE
  · intro y
    have hRop : ‖residual BΓ BE‖ ≤ ε :=
      (norm_residual_le_wardResidual BΓ BE W).trans hWard
    have hy : ‖residual BΓ BE y‖ ≤ ε * ‖y‖ :=
      (residual BΓ BE).le_opNorm y |>.trans
        (mul_le_mul_of_nonneg_right hRop (norm_nonneg y))
    rw [schur_eq_residualGram,
      ContinuousLinearMap.reApplyInnerSelf_apply,
      ← apply_norm_sq_eq_inner_adjoint_left]
    nlinarith [norm_nonneg (residual BΓ BE y), norm_nonneg y]

/-- Exact difference formula for the supported approximate Ward router. -/
theorem router_sub_eq_gramPinv_adjoint_wardResidual
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y))
    (W : XE →L[ℂ] XΓ)
    (hW : BΓ.kerᗮ.starProjection.comp W = W) :
    router BΓ BE hclosed - W =
      (gramPinv BΓ hclosed).comp
        ((BΓ†).comp (wardResidual BΓ BE W)) := by
  ext y
  have hgram :
      (gramPinv BΓ hclosed)
          ((BΓ†) (BΓ (W y))) = W y := by
    have hcross := congrArg (fun Q : XΓ →L[ℂ] XΓ => Q (W y))
      (gramPinv_comp_crossGram BΓ BΓ hclosed)
    have hsupp := congrArg (fun Q : XE →L[ℂ] XΓ => Q y) hW
    simp only [comp_apply] at hcross hsupp
    rw [hcross, pinv_apply, hsupp]
  simp only [router, crossGram, wardResidual, sub_apply, comp_apply, map_sub]
  rw [hgram]

/-- Quantitative approximate-Ward router estimate under the manuscript's
support margin and principal-Hessian norm bound. -/
theorem approximateWard_router_bound
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y))
    (W : XE →L[ℂ] XΓ) (ε m Hnorm : ℝ)
    (hε : 0 ≤ ε) (hm : 0 < m) (hH : 0 ≤ Hnorm)
    (hW : BΓ.kerᗮ.starProjection.comp W = W)
    (hWard : ‖wardResidual BΓ BE W‖ ≤ ε)
    (hmargin : ‖gramPinv BΓ hclosed‖ ≤ (m ^ 2)⁻¹)
    (hprincipal : ‖BΓ‖ ≤ Real.sqrt Hnorm) :
    ‖router BΓ BE hclosed - W‖ ≤
      Real.sqrt Hnorm / m ^ 2 * ε := by
  rw [router_sub_eq_gramPinv_adjoint_wardResidual BΓ BE hclosed W hW]
  calc
    ‖(gramPinv BΓ hclosed).comp
        ((BΓ†).comp (wardResidual BΓ BE W))‖
        ≤ ‖gramPinv BΓ hclosed‖ * ‖BΓ†‖ *
            ‖wardResidual BΓ BE W‖ := by
      calc
        _ ≤ ‖gramPinv BΓ hclosed‖ *
              ‖(BΓ†).comp (wardResidual BΓ BE W)‖ :=
          opNorm_comp_le _ _
        _ ≤ ‖gramPinv BΓ hclosed‖ *
              (‖BΓ†‖ * ‖wardResidual BΓ BE W‖) :=
          mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _)
        _ = _ := by ring
    _ ≤ (m ^ 2)⁻¹ * Real.sqrt Hnorm * ε := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
    _ = Real.sqrt Hnorm / m ^ 2 * ε := by
      rw [div_eq_mul_inv]
      ring

omit [CompleteSpace XΓ] [CompleteSpace XE] [CompleteSpace Y] in
/-- The norm-form Ward hypothesis used above is equivalent to a uniform
pointwise estimate. -/
theorem wardResidual_apply_bound_of_opNorm
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (W : XE →L[ℂ] XΓ) (ε : ℝ)
    (hWard : ‖wardResidual BΓ BE W‖ ≤ ε) (y : XE) :
    ‖wardResidual BΓ BE W y‖ ≤ ε * ‖y‖ :=
  (wardResidual BΓ BE W).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_right hWard (norm_nonneg y))

omit [CompleteSpace XΓ] [CompleteSpace XE] [CompleteSpace Y] in
/-- The manuscript inequality R_W† R_W ≤ ε² I, rendered pointwise. -/
def WardQuadraticBound
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (W : XE →L[ℂ] XΓ) (ε : ℝ) : Prop :=
  ∀ y : XE, ‖wardResidual BΓ BE W y‖ ^ 2 ≤ ε ^ 2 * ‖y‖ ^ 2

omit [CompleteSpace XΓ] [CompleteSpace XE] [CompleteSpace Y] in
/-- A nonnegative quadratic Ward bound is equivalent to the operator-norm
input used by the quantitative router theorem. -/
theorem opNorm_wardResidual_le_of_quadratic
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (W : XE →L[ℂ] XΓ) (ε : ℝ) (hε : 0 ≤ ε)
    (hWard : WardQuadraticBound BΓ BE W ε) :
    ‖wardResidual BΓ BE W‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro y
  apply le_of_sq_le_sq
  · simpa [mul_pow] using hWard y
  · exact mul_nonneg hε (norm_nonneg y)

/-- Direct form of the approximate Schur conclusion from the manuscript's
quadratic Ward hypothesis. -/
theorem approximateWard_schur_bound_of_quadratic
    (BΓ : XΓ →L[ℂ] Y) (BE : XE →L[ℂ] Y)
    (hclosed : IsClosed (BΓ.range : Set Y))
    (W : XE →L[ℂ] XΓ) (ε : ℝ) (hε : 0 ≤ ε)
    (hWard : WardQuadraticBound BΓ BE W ε) :
    (schur BΓ BE).IsPositive ∧
      ∀ y : XE, (schur BΓ BE).reApplyInnerSelf y ≤ ε ^ 2 * ‖y‖ ^ 2 :=
  approximateWard_schur_bound BΓ BE hclosed W ε hε
    (opNorm_wardResidual_le_of_quadratic BΓ BE W ε hε hWard)

end CommonActionHilbert
end NCG
