/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact first-return nesting derivative
  (`thm:GT-heldout-nesting`, Gran-Tensor manuscript)

* `gt_heldout_nesting`: the boxed RG.3 — at a tail-free
  point (`G₁(c₀) = 0`) the held-out nested return
  `h(c) = F₂(F₁(c), G₁(c)) - F₂(F₁(c), 0)` is
  differentiable with derivative exactly the factored
  chain `Dh(c₀) = B₂ ∘ C₁`, where
  `B₂ = D_r F₂(F₁(c₀), 0)` is the partial tail-entrance
  derivative and `C₁ = DG₁(c₀)` the retained tangent map:
  the retained-part contributions cancel exactly between
  the two branches, so only tail-entrance directions are
  tested.

The integral representation RG.2
`h(c) = ∫₀¹ D_r F₂(F₁(c), tG₁(c))[G₁(c)] dt` is the
manuscript's fundamental-theorem-of-calculus layer, and
`rank(B₂C₁)` counting the tested retained directions is its
linear-algebra reading of the boxed factorization.
-/

open ContinuousLinearMap

namespace NCG

/-- `thm:GT-heldout-nesting` (the boxed RG.2 integral identity).
Along the affine tail line `t ↦ (y, t • z)`, the derivative is the partial
tail derivative applied to `z`; the Banach-valued fundamental theorem of
calculus then gives the exact held-out difference. -/
theorem heldout_nesting_integral {Y Z W : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (F2 : Y × Z → W) (y : Y) (z : Z)
    (DF2 : ℝ → (Y × Z →L[ℝ] W))
    (hF2 : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasFDerivAt F2 (DF2 t) (y, t • z))
    (hpartial : ContinuousOn
      (fun t : ℝ => DF2 t (0, z)) (Set.uIcc (0 : ℝ) 1)) :
    F2 (y, z) - F2 (y, 0) =
      ∫ t in (0 : ℝ)..1, DF2 t (0, z) := by
  have hline : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => (y, s • z)) (0, z) t := by
    intro t
    exact (hasDerivAt_const t y).prodMk
      (by simpa using (hasDerivAt_id t).smul_const z)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => F2 (y, s • z)) (DF2 t (0, z)) t := by
    intro t ht
    simpa only [Function.comp_def] using
      (hF2 t ht).comp_hasDerivAt t (hline t)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hpartial.intervalIntegrable
  simpa using hFTC.symm

/-- `thm:GT-heldout-nesting` (the boxed RG.3 chain
factorization). -/
theorem gt_heldout_nesting {X Y Z W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F2 : Y × Z → W) (F1 : X → Y) (G1 : X → Z) (c0 : X)
    (F1' : X →L[ℝ] Y) (C1 : X →L[ℝ] Z)
    (DF2 : Y × Z →L[ℝ] W)
    (hF1 : HasFDerivAt F1 F1' c0)
    (hG1 : HasFDerivAt G1 C1 c0)
    (hG0 : G1 c0 = 0)
    (hF2 : HasFDerivAt F2 DF2 (F1 c0, 0)) :
    -- the boxed derivative Dh(c₀) = B₂C₁ with
    -- B₂ = D_r F₂(F₁(c₀), 0)
    HasFDerivAt
      (fun c => F2 (F1 c, G1 c) - F2 (F1 c, 0))
      ((DF2.comp (ContinuousLinearMap.inr ℝ Y Z)).comp C1)
      c0 := by
  have hpair : HasFDerivAt (fun c => (F1 c, G1 c))
      (F1'.prod C1) c0 := hF1.prodMk hG1
  have hF2' : HasFDerivAt F2 DF2 (F1 c0, G1 c0) := by
    rw [hG0]
    exact hF2
  have h1 : HasFDerivAt (fun c => F2 (F1 c, G1 c))
      (DF2.comp (F1'.prod C1)) c0 :=
    hF2'.comp c0 hpair
  have hpair2 : HasFDerivAt (fun c => (F1 c, (0 : Z)))
      (F1'.prod (0 : X →L[ℝ] Z)) c0 :=
    hF1.prodMk (hasFDerivAt_const (0 : Z) c0)
  have h2 : HasFDerivAt (fun c => F2 (F1 c, 0))
      (DF2.comp (F1'.prod (0 : X →L[ℝ] Z))) c0 :=
    hF2.comp c0 hpair2
  have hsub := h1.sub h2
  have hCLM : DF2.comp (F1'.prod C1)
      - DF2.comp (F1'.prod (0 : X →L[ℝ] Z))
      = (DF2.comp
          (ContinuousLinearMap.inr ℝ Y Z)).comp C1 := by
    ext x
    simp only [sub_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.inr_apply]
    rw [← map_sub]
    congr 1
    simp [Prod.mk_sub_mk]
  rw [← hCLM]
  exact hsub

end NCG
