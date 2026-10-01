/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Consistency survives a uniformly regular elimination
  (`lem:supp-initial-elimination-consistency`, `eq:supp-initial-elimination-error`;
  emergent-spacetime manuscript)

All statements are in arbitrary real normed spaces (the paper's Sobolev and
grid spaces after the common Fourier identification).

* `InitialElimination.elimination_error` (`eq:supp-initial-elimination-error`):
  if `F(z) = 0` (the actual equation at fixed `x_h`), the comparison value
  `z_cmp` has residual `‖F(z_cmp)‖ ≤ ε`, and on a convex comparison set `S`
  containing both points `F` has derivative `D_zF` with
  `‖I - A ∘ D_zF‖ ≤ κ < 1`, then `‖z - z_cmp‖ ≤ ‖A‖ ε / (1 - κ)`.
  The proof is the paper's: `z ↦ z - A F(z)` is a `κ`-contraction on `S`
  (mean value inequality).
* `InitialElimination.implicit_derivative_formula`: differentiating
  `F(x, z(x)) = 0` gives `D_x z = -(D_zF)⁻¹ D_xF`.
* `InitialElimination.symm_norm_le_of_preconditioner`: the preconditioner
  hypothesis bounds the inverse block, `‖(D_zF)⁻¹‖ ≤ ‖A‖ / (1 - κ)` (the
  "bounds on the inverse blocks" retained by the lemma).
* `InitialElimination.inverse_difference` and
  `InitialElimination.inverse_comp_difference_le`: the inverse difference
  identity `U⁻¹ - V⁻¹ = U⁻¹ (V - U) V⁻¹` and the resulting transfer
  `‖U⁻¹T - V⁻¹S‖ ≤ M ‖T - S‖ + M² K ‖U - V‖`.
* `InitialElimination.elimination_C1_consistency`: the `C¹`-consistency clause.
  Eliminated maps `z_h`, `z` of the actual and comparison equations
  `F_h(x, z_h(x)) = 0`, `F(x, z(x)) = 0`; if `F_h` is `ε`-consistent with `F`
  at the comparison point, its derivative is `ε₁`-consistent there and
  `Λ`-Lipschitz along the comparison segment, and one preconditioner satisfies
  the contraction bound for both derivative blocks, then
  `‖z_h(x) - z(x)‖ ≤ ‖A‖ε/(1-κ)` and
  `‖D z_h(x) - D z(x)‖ ≤ M δ + M² K δ` with `δ = ε₁ + Λ ‖A‖ε/(1-κ)`,
  `M = ‖A‖/(1-κ)`, `K ≥ ‖D_xF‖`.
* `InitialElimination.comp_consistency` and
  `InitialElimination.comp_deriv_consistency`: consistency (values and first
  derivatives) is stable under composition with uniformly Lipschitz /
  uniformly bounded maps.  Together with the elimination results this is the
  iteration behind the sentence "finite compositions … satisfy
  `ass:supp-initial-consistency` when their raw equations have the stated
  consistency".
-/

namespace RenewalGeometry
namespace InitialElimination

open Filter Topology

variable {X Z W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `eq:supp-initial-elimination-error` (first statement of
`lem:supp-initial-elimination-consistency`).  `F = F_h(x_h, ·)`; `z` is the
eliminated value (`F z = 0`), `zc` the comparison value with
`‖F zc‖ ≤ ε`; on a convex comparison set `S` containing both, `F` has
derivative `DF` and the preconditioner `A` satisfies `‖I - A ∘ DF‖ ≤ κ < 1`.
Then `‖z - zc‖ ≤ ‖A‖ / (1 - κ) * ε`. -/
theorem elimination_error (F : Z → W) (DF : Z → Z →L[ℝ] W) (A : W →L[ℝ] Z)
    {S : Set Z} (hS : Convex ℝ S) (hF : ∀ y ∈ S, HasFDerivWithinAt F (DF y) S y)
    {κ ε : ℝ} (hκ : ∀ y ∈ S, ‖ContinuousLinearMap.id ℝ Z - A.comp (DF y)‖ ≤ κ)
    (hκ1 : κ < 1) {z zc : Z} (hz : z ∈ S) (hzc : zc ∈ S) (hFz : F z = 0)
    (hε : ‖F zc‖ ≤ ε) :
    ‖z - zc‖ ≤ ‖A‖ / (1 - κ) * ε := by
  -- the contraction `G z = z - A F(z)`
  set G : Z → Z := fun y => y - A (F y) with hG
  have hGd : ∀ y ∈ S, HasFDerivWithinAt G (ContinuousLinearMap.id ℝ Z - A.comp (DF y)) S y :=
    fun y hy => (hasFDerivWithinAt_id y S).sub
      (A.hasFDerivAt.comp_hasFDerivWithinAt y (hF y hy))
  have hcontr := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le hGd hκ hzc hz
  have hGz : G z = z := by simp [hG, hFz]
  have hdecomp : z - zc = (G z - G zc) - A (F zc) := by
    simp only [hG, hFz, map_zero, sub_zero]; abel
  have hAF : ‖A (F zc)‖ ≤ ‖A‖ * ε :=
    (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hε (norm_nonneg _))
  have hmain : ‖z - zc‖ ≤ κ * ‖z - zc‖ + ‖A‖ * ε := by
    calc ‖z - zc‖ = ‖(G z - G zc) - A (F zc)‖ := by rw [hdecomp]
      _ ≤ ‖G z - G zc‖ + ‖A (F zc)‖ := norm_sub_le _ _
      _ ≤ κ * ‖z - zc‖ + ‖A‖ * ε := add_le_add hcontr hAF
  have h1 : 0 < 1 - κ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith

/-- Implicit differentiation of the elimination equation: if `F(x, z(x)) = 0`
near `x₀`, `F` has derivative `F'` at `(x₀, z(x₀))` and `z` has derivative `z'`
at `x₀`, then `D_xF + D_zF ∘ z' = 0`, with `D_xF = F' ∘ inl`, `D_zF = F' ∘ inr`. -/
theorem implicit_derivative_relation (F : X × Z → W) (F' : X × Z →L[ℝ] W)
    (z : X → Z) (z' : X →L[ℝ] Z) {x₀ : X} (hF : HasFDerivAt F F' (x₀, z x₀))
    (hz : HasFDerivAt z z' x₀) (hzero : ∀ᶠ x in 𝓝 x₀, F (x, z x) = 0) :
    F'.comp (ContinuousLinearMap.inl ℝ X Z)
      + (F'.comp (ContinuousLinearMap.inr ℝ X Z)).comp z' = 0 := by
  have hcomp : HasFDerivAt (fun x => F (x, z x))
      (F'.comp ((ContinuousLinearMap.id ℝ X).prod z')) x₀ :=
    hF.comp x₀ ((hasFDerivAt_id x₀).prodMk hz)
  have hconst : HasFDerivAt (fun x => F (x, z x)) (0 : X →L[ℝ] W) x₀ :=
    (hasFDerivAt_const (0 : W) x₀).congr_of_eventuallyEq hzero
  have huniq := hcomp.unique hconst
  rw [← huniq]
  ext v
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
  rw [← map_add]
  simp

/-- `D_x z = -(D_zF)⁻¹ D_xF` when the `z`-block `D_zF = F' ∘ inr` is the
invertible map `U`. -/
theorem implicit_derivative_formula (F : X × Z → W) (F' : X × Z →L[ℝ] W)
    (U : Z ≃L[ℝ] W) (hU : F'.comp (ContinuousLinearMap.inr ℝ X Z) = (U : Z →L[ℝ] W))
    (z : X → Z) (z' : X →L[ℝ] Z) {x₀ : X} (hF : HasFDerivAt F F' (x₀, z x₀))
    (hz : HasFDerivAt z z' x₀) (hzero : ∀ᶠ x in 𝓝 x₀, F (x, z x) = 0) :
    z' = -((U.symm : W →L[ℝ] Z).comp (F'.comp (ContinuousLinearMap.inl ℝ X Z))) := by
  have hrel := implicit_derivative_relation F F' z z' hF hz hzero
  rw [hU] at hrel
  ext v
  have hv := congrArg (fun T : X →L[ℝ] W => T v) hrel
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, ContinuousLinearEquiv.coe_coe] at hv
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  have : U (z' v) = -(F' (ContinuousLinearMap.inl ℝ X Z v)) := eq_neg_of_add_eq_zero_right hv
  rw [← map_neg, ← this, U.symm_apply_apply]

/-- The preconditioner hypothesis bounds the inverse block: if
`‖I - A ∘ U‖ ≤ κ < 1` then `‖U⁻¹‖ ≤ ‖A‖ / (1 - κ)`. -/
theorem symm_norm_le_of_preconditioner (U : Z ≃L[ℝ] W) (A : W →L[ℝ] Z) {κ : ℝ}
    (hκ : ‖ContinuousLinearMap.id ℝ Z - A.comp (U : Z →L[ℝ] W)‖ ≤ κ) (hκ1 : κ < 1) :
    ‖(U.symm : W →L[ℝ] Z)‖ ≤ ‖A‖ / (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) h1.le) fun w => ?_
  set v := U.symm w with hv
  have hdec : v = (ContinuousLinearMap.id ℝ Z - A.comp (U : Z →L[ℝ] W)) v + A w := by
    simp [hv]
  have hle : ‖v‖ ≤ κ * ‖v‖ + ‖A‖ * ‖w‖ := by
    calc ‖v‖ = ‖(ContinuousLinearMap.id ℝ Z - A.comp (U : Z →L[ℝ] W)) v + A w‖ := by
          rw [← hdec]
      _ ≤ ‖(ContinuousLinearMap.id ℝ Z - A.comp (U : Z →L[ℝ] W)) v‖ + ‖A w‖ := norm_add_le _ _
      _ ≤ κ * ‖v‖ + ‖A‖ * ‖w‖ := by
          refine add_le_add ?_ (A.le_opNorm w)
          exact ((ContinuousLinearMap.le_opNorm _ v).trans
            (mul_le_mul_of_nonneg_right hκ (norm_nonneg v)))
  show ‖v‖ ≤ ‖A‖ / (1 - κ) * ‖w‖
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith

/-- The inverse difference identity `U⁻¹ - V⁻¹ = U⁻¹ (V - U) V⁻¹`. -/
theorem inverse_difference (U V : Z ≃L[ℝ] W) :
    (U.symm : W →L[ℝ] Z) - (V.symm : W →L[ℝ] Z)
      = (U.symm : W →L[ℝ] Z).comp
          (((V : Z →L[ℝ] W) - (U : Z →L[ℝ] W)).comp (V.symm : W →L[ℝ] Z)) := by
  ext w
  simp

/-- Transfer of consistency through the inverse blocks:
`‖U⁻¹T - V⁻¹S‖ ≤ M ‖T - S‖ + M (M K) ‖U - V‖` when `‖U⁻¹‖, ‖V⁻¹‖ ≤ M` and
`‖S‖ ≤ K`. -/
theorem inverse_comp_difference_le (U V : Z ≃L[ℝ] W) (T S : X →L[ℝ] W) {M K : ℝ}
    (hU : ‖(U.symm : W →L[ℝ] Z)‖ ≤ M) (hV : ‖(V.symm : W →L[ℝ] Z)‖ ≤ M) (hS : ‖S‖ ≤ K) :
    ‖(U.symm : W →L[ℝ] Z).comp T - (V.symm : W →L[ℝ] Z).comp S‖
      ≤ M * ‖T - S‖ + M * (M * K) * ‖(U : Z →L[ℝ] W) - (V : Z →L[ℝ] W)‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hU
  have hdec : (U.symm : W →L[ℝ] Z).comp T - (V.symm : W →L[ℝ] Z).comp S
      = (U.symm : W →L[ℝ] Z).comp (T - S)
        + ((U.symm : W →L[ℝ] Z) - (V.symm : W →L[ℝ] Z)).comp S := by
    ext v; simp
  rw [hdec, inverse_difference]
  have hVU : ‖(V : Z →L[ℝ] W) - (U : Z →L[ℝ] W)‖ = ‖(U : Z →L[ℝ] W) - (V : Z →L[ℝ] W)‖ :=
    norm_sub_rev _ _
  calc _ ≤ ‖(U.symm : W →L[ℝ] Z).comp (T - S)‖
        + ‖((U.symm : W →L[ℝ] Z).comp
            (((V : Z →L[ℝ] W) - (U : Z →L[ℝ] W)).comp (V.symm : W →L[ℝ] Z))).comp S‖ :=
        norm_add_le _ _
    _ ≤ ‖(U.symm : W →L[ℝ] Z)‖ * ‖T - S‖
        + ‖(U.symm : W →L[ℝ] Z)‖ * (‖(V : Z →L[ℝ] W) - (U : Z →L[ℝ] W)‖
            * ‖(V.symm : W →L[ℝ] Z)‖) * ‖S‖ := by
        refine add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _)
    _ ≤ M * ‖T - S‖ + M * (‖(U : Z →L[ℝ] W) - (V : Z →L[ℝ] W)‖ * M) * K := by
        rw [hVU]
        gcongr
    _ = M * ‖T - S‖ + M * (M * K) * ‖(U : Z →L[ℝ] W) - (V : Z →L[ℝ] W)‖ := by ring

/-- Restricting a derivative difference to a block of norm `≤ 1` does not
increase it. -/
theorem comp_sub_norm_le {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (G G' : P →L[ℝ] W) (ι : E →L[ℝ] P)
    (hι : ‖ι‖ ≤ 1) {δ : ℝ} (hδ : ‖G - G'‖ ≤ δ) : ‖G.comp ι - G'.comp ι‖ ≤ δ := by
  have : G.comp ι - G'.comp ι = (G - G').comp ι := by ext; simp
  rw [this]
  calc _ ≤ ‖G - G'‖ * ‖ι‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ δ * 1 := mul_le_mul hδ hι (norm_nonneg _) ((norm_nonneg _).trans hδ)
    _ = δ := mul_one δ

/-- The `C¹`-consistency clause of `lem:supp-initial-elimination-consistency`.

Actual equation `F_h`, comparison equation `F` (both on the common spaces),
eliminated maps `z_h`, `z` with `F_h(x, z_h x) = 0`, `F(x, z x) = 0` near `x₀`,
derivatives `F_h'` at `p_h = (x₀, z_h x₀)` and `F'` at `p = (x₀, z x₀)`, with
invertible `z`-blocks `U_h`, `U`.  Hypotheses:
* value consistency `‖F_h(p) - F(p)‖ ≤ ε` (so `‖F_h(x₀, z x₀)‖ ≤ ε`);
* on a convex comparison set `S` containing `z_h x₀`, `z x₀`,
  `F_h(x₀, ·)` has `z`-derivative `DzF_h` with `‖I - A ∘ DzF_h‖ ≤ κ < 1`;
* `‖I - A ∘ U_h‖ ≤ κ`, `‖I - A ∘ U‖ ≤ κ` (common preconditioner);
* derivative consistency `‖F_h'(p_h) - F'(p)‖ ≤ ε₁ + Λ ‖z_h x₀ - z x₀‖`
  (consistency `ε₁` at the comparison point plus a Lipschitz modulus `Λ`);
* `‖D_xF(p)‖ ≤ K`.
Conclusion: `‖z_h x₀ - z x₀‖ ≤ ‖A‖ε/(1-κ)` and
`‖D z_h(x₀) - D z(x₀)‖ ≤ M δ + M (M K) δ` with `M = ‖A‖/(1-κ)`,
`δ = ε₁ + Λ ‖A‖ ε/(1-κ)`. -/
theorem elimination_C1_consistency (Fh F : X × Z → W) (Fh' F' : X × Z →L[ℝ] W)
    (zh z : X → Z) (zh' z' : X →L[ℝ] Z) {x₀ : X}
    (hFh : HasFDerivAt Fh Fh' (x₀, zh x₀)) (hF : HasFDerivAt F F' (x₀, z x₀))
    (hzh : HasFDerivAt zh zh' x₀) (hz : HasFDerivAt z z' x₀)
    (hzh0 : ∀ᶠ x in 𝓝 x₀, Fh (x, zh x) = 0) (hz0 : ∀ᶠ x in 𝓝 x₀, F (x, z x) = 0)
    (Uh U : Z ≃L[ℝ] W)
    (hUh : Fh'.comp (ContinuousLinearMap.inr ℝ X Z) = (Uh : Z →L[ℝ] W))
    (hU : F'.comp (ContinuousLinearMap.inr ℝ X Z) = (U : Z →L[ℝ] W))
    (A : W →L[ℝ] Z) {κ ε ε₁ Λ K : ℝ} (hκ1 : κ < 1)
    (DzFh : Z → Z →L[ℝ] W) {S : Set Z} (hS : Convex ℝ S) (hzhS : zh x₀ ∈ S)
    (hzS : z x₀ ∈ S)
    (hDz : ∀ y ∈ S, HasFDerivWithinAt (fun w => Fh (x₀, w)) (DzFh y) S y)
    (hκ : ∀ y ∈ S, ‖ContinuousLinearMap.id ℝ Z - A.comp (DzFh y)‖ ≤ κ)
    (hκUh : ‖ContinuousLinearMap.id ℝ Z - A.comp (Uh : Z →L[ℝ] W)‖ ≤ κ)
    (hκU : ‖ContinuousLinearMap.id ℝ Z - A.comp (U : Z →L[ℝ] W)‖ ≤ κ)
    (hε : ‖Fh (x₀, z x₀) - F (x₀, z x₀)‖ ≤ ε)
    (hΛ : 0 ≤ Λ) (hD : ‖Fh' - F'‖ ≤ ε₁ + Λ * ‖zh x₀ - z x₀‖)
    (hK : ‖F'.comp (ContinuousLinearMap.inl ℝ X Z)‖ ≤ K) :
    ‖zh x₀ - z x₀‖ ≤ ‖A‖ / (1 - κ) * ε ∧
    ‖zh' - z'‖ ≤ ‖A‖ / (1 - κ) * (ε₁ + Λ * (‖A‖ / (1 - κ) * ε))
      + ‖A‖ / (1 - κ) * (‖A‖ / (1 - κ) * K) * (ε₁ + Λ * (‖A‖ / (1 - κ) * ε)) := by
  -- value consistency of the eliminated map
  have hFz0 : F (x₀, z x₀) = 0 := hz0.self_of_nhds
  have hFh0 : Fh (x₀, zh x₀) = 0 := hzh0.self_of_nhds
  have hres : ‖Fh (x₀, z x₀)‖ ≤ ε := by simpa [hFz0] using hε
  have hval : ‖zh x₀ - z x₀‖ ≤ ‖A‖ / (1 - κ) * ε :=
    elimination_error (fun w => Fh (x₀, w)) DzFh A hS hDz hκ hκ1 hzhS hzS hFh0 hres
  refine ⟨hval, ?_⟩
  -- derivative consistency
  set M := ‖A‖ / (1 - κ)
  set δ := ε₁ + Λ * (M * ε)
  have hδ : ‖Fh' - F'‖ ≤ δ :=
    hD.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hval hΛ))
  have hx := comp_sub_norm_le Fh' F' (ContinuousLinearMap.inl ℝ X Z)
    (ContinuousLinearMap.norm_inl_le_one _ _ _) hδ
  have hzb := comp_sub_norm_le Fh' F' (ContinuousLinearMap.inr ℝ X Z)
    (ContinuousLinearMap.norm_inr_le_one _ _ _) hδ
  rw [hUh, hU] at hzb
  have hMh := symm_norm_le_of_preconditioner Uh A hκUh hκ1
  have hM := symm_norm_le_of_preconditioner U A hκU hκ1
  rw [implicit_derivative_formula Fh Fh' Uh hUh zh zh' hFh hzh hzh0,
    implicit_derivative_formula F F' U hU z z' hF hz hz0, ← neg_sub', norm_neg]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  calc _ ≤ M * ‖Fh'.comp (ContinuousLinearMap.inl ℝ X Z) - F'.comp (ContinuousLinearMap.inl ℝ X Z)‖
        + M * (M * K) * ‖(Uh : Z →L[ℝ] W) - (U : Z →L[ℝ] W)‖ :=
        inverse_comp_difference_le Uh U _ _ hMh hM hK
    _ ≤ M * δ + M * (M * K) * δ := by
        have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
        gcongr

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℝ Z] in
/-- Composition stability of value consistency: if `‖f_h x - f x‖ ≤ δ_f`,
`‖g_h y - g y‖ ≤ δ_g` for all `y`, and `g_h` is `L`-Lipschitz, then
`‖g_h (f_h x) - g (f x)‖ ≤ L δ_f + δ_g`. -/
theorem comp_consistency {Y : Type*} [NormedAddCommGroup Y] (fh f : X → Z) (gh g : Z → Y)
    {L δf δg : ℝ} (x : X) (hf : ‖fh x - f x‖ ≤ δf) (hg : ∀ y, ‖gh y - g y‖ ≤ δg)
    (hL : 0 ≤ L) (hLip : ∀ y y', ‖gh y - gh y'‖ ≤ L * ‖y - y'‖) :
    ‖gh (fh x) - g (f x)‖ ≤ L * δf + δg := by
  calc ‖gh (fh x) - g (f x)‖ = ‖(gh (fh x) - gh (f x)) + (gh (f x) - g (f x))‖ := by
        congr 1; abel
    _ ≤ ‖gh (fh x) - gh (f x)‖ + ‖gh (f x) - g (f x)‖ := norm_add_le _ _
    _ ≤ L * δf + δg := add_le_add ((hLip _ _).trans (mul_le_mul_of_nonneg_left hf hL)) (hg _)

/-- Composition stability of first-derivative consistency (chain rule):
`‖Dg_h ∘ Df_h - Dg ∘ Df‖ ≤ ‖Dg_h - Dg‖ ‖Df_h‖ + ‖Dg‖ ‖Df_h - Df‖`. -/
theorem comp_deriv_consistency {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Dfh Df : X →L[ℝ] Z) (Dgh Dg : Z →L[ℝ] Y) :
    ‖Dgh.comp Dfh - Dg.comp Df‖ ≤ ‖Dgh - Dg‖ * ‖Dfh‖ + ‖Dg‖ * ‖Dfh - Df‖ := by
  have : Dgh.comp Dfh - Dg.comp Df = (Dgh - Dg).comp Dfh + Dg.comp (Dfh - Df) := by
    ext v; simp
  rw [this]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

end InitialElimination
end RenewalGeometry
