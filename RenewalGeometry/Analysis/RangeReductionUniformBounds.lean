/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.UniformImplicitFunction
import RenewalGeometry.Analysis.LyapunovSchmidtRangeReduction

/-!
# Uniform higher-derivative bounds for the range solution and the mean map
  (`lem:supp-initial-range`, `thm:supp-action-prepared-chart` — the step "the analytic extension
  converges in `C¹` uniformly", which needs a cutoff-uniform Lipschitz bound for `D²Θ_h`;
  emergent-spacetime manuscript)

For range-reduction data `D : LyapunovSchmidt.RangeData E F F₀` (Banach spaces) whose nonlinearity
has **uniform derivative bounds of order three** on the common ball,
`DerivBound D.N (B(0, ρ)) 3 M_N`, the range solution `y(z)` and the mean map
`Θ(z) = P₀𝒞(z + R y(z))` on `ker L` have derivative bounds of order three on a ball whose radius,
like the bound, depends only on `(a, p, ρ, M_N, ‖P₀‖)` and the admissible range radii `(σ, δ)`:

* `RangeUniform.hyp`: the range equation `f(z, y) = P(y + N(z + R y)) = 0` on `ker L × {P y = y}`
  satisfies the hypotheses of the uniform implicit function theorem
  (`UniformImplicit.Hyp`, with `T = id`, `‖T⁻¹‖ ≤ 1`);
* `RangeUniform.sol_eq_imp`: on the small ball the uniform implicit function is the range solution
  `RangeData.sol` (uniqueness of the range contraction);
* **`RangeUniform.derivBound_meanMap`**: `DerivBound (z ↦ Θ(z)) (B(0, δ₀)) 3 C₃`;
* **`RangeUniform.norm_fderiv_fderiv_meanMap_sub_le`**: `‖D²Θ(z) - D²Θ(z')‖ ≤ C₃ ‖z - z'‖` on that
  ball — the cutoff-uniform Lipschitz bound of `D²Θ_h` required by `NormalizedMeanRoot.normalized_ray_bounds`
  (whose `K`-Lipschitz hypothesis on `D²Θ` at `0` is thereby derived from uniform bounds on
  `D²N_h`, `D³N_h`).
-/

open Set Filter Topology Metric
open scoped ContDiff

namespace RenewalGeometry.RangeUniform

open LyapunovSchmidt IteratedDerivBounds UniformDerivBounds UniformImplicit

noncomputable section

set_option linter.unusedSectionVars false

variable {E F F₀ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]

variable (D : RangeData E F F₀)

/-- The embedding `ι(z, y) = z + R y` of `ker L × {P y = y}` into `E`. -/
def iotaKM : D.K × D.M →L[ℝ] E :=
  D.K.subtypeL ∘L ContinuousLinearMap.fst ℝ D.K D.M +
    D.R ∘L D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M

@[simp] theorem iotaKM_apply (v : D.K × D.M) : iotaKM D v = (v.1 : E) + D.R (v.2 : F) := rfl

theorem norm_iotaKM_apply_le (v : D.K × D.M) : ‖iotaKM D v‖ ≤ (1 + D.a) * ‖v‖ := by
  rw [iotaKM_apply]
  have h1 : ‖(v.1 : E)‖ ≤ ‖v‖ := norm_fst_le v
  have h2 : ‖(v.2 : F)‖ ≤ ‖v‖ := norm_snd_le v
  calc ‖(v.1 : E) + D.R (v.2 : F)‖ ≤ ‖(v.1 : E)‖ + ‖D.R‖ * ‖(v.2 : F)‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (D.R.le_opNorm _))
    _ ≤ ‖v‖ + D.a * ‖v‖ := add_le_add h1 (mul_le_mul D.ha h2 (norm_nonneg _) D.a_nonneg)
    _ = (1 + D.a) * ‖v‖ := by ring

theorem norm_iotaKM_le : ‖iotaKM D‖ ≤ 1 + D.a :=
  ContinuousLinearMap.opNorm_le_bound _ (by linarith [D.a_nonneg]) (norm_iotaKM_apply_le D)

/-- The range map `f(z, y) = P(y + N(z + R y))`. -/
def fmap (v : D.K × D.M) : D.M := D.Pc ((v.2 : F) + D.N (iotaKM D v))

/-- The radius of the product ball, `ρ' = ρ/(1 + a)`. -/
def rhoP : ℝ := D.ρ / (1 + D.a)

/-- The order-three bound of the range map. -/
def Mf (MN : ℝ) : ℝ := D.p * (max 1 (rhoP D) + MN * max 1 (1 + D.a) ^ 3)

theorem rhoP_pos (hρ : 0 < D.ρ) : 0 < rhoP D := by
  have := D.a_nonneg; unfold rhoP; positivity

theorem mapsTo_iotaKM (hρ : 0 < D.ρ) :
    MapsTo (iotaKM D) (ball (0 : D.K × D.M) (rhoP D)) (ball (0 : E) D.ρ) := by
  intro v hv
  rw [mem_ball_zero_iff] at hv ⊢
  have ha := D.a_nonneg
  calc ‖iotaKM D v‖ ≤ (1 + D.a) * ‖v‖ := norm_iotaKM_apply_le D v
    _ < (1 + D.a) * rhoP D := by gcongr
    _ = D.ρ := by unfold rhoP; field_simp

theorem derivBound_fmap (hρ : 0 < D.ρ) {MN : ℝ} (hNb : DerivBound D.N (ball 0 D.ρ) 3 MN) :
    DerivBound (fmap D) (ball 0 (rhoP D)) 3 (Mf D MN) := by
  have hMN : 0 ≤ MN := hNb.nonneg (mem_ball_self hρ)
  have hcomp := hNb.comp_clm isOpen_ball (iotaKM D) (mapsTo_iotaKM D hρ)
  have hsnd : DerivBound (fun v : D.K × D.M => (D.M.subtypeL ∘L
      ContinuousLinearMap.snd ℝ D.K D.M) v) (ball 0 (rhoP D)) 3
      (‖D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M‖ * max 1 (rhoP D)) :=
    DerivBound.clm _ (rhoP_pos D hρ).le ball_subset_closedBall 3
  have hsum := hsnd.add hcomp isOpen_ball
  have hP := hsum.clm_comp isOpen_ball D.Pc
  refine hP.mono le_rfl ?_
  have hn1 : ‖D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.coe_snd', one_mul]
    rw [← Submodule.coe_norm]; exact norm_snd_le v
  have hn2 : MN * max 1 ‖iotaKM D‖ ^ 3 ≤ MN * max 1 (1 + D.a) ^ 3 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (max_le_max le_rfl (norm_iotaKM_le D)) 3) hMN
  have h1 : ‖D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M‖ * max 1 (rhoP D) ≤
      max 1 (rhoP D) := by
    have := le_max_left 1 (rhoP D)
    nlinarith [norm_nonneg (D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M)]
  have h2 : 0 ≤ max 1 (rhoP D) + MN * max 1 (1 + D.a) ^ 3 := by positivity
  unfold Mf
  calc ‖D.Pc‖ * (‖D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M‖ * max 1 (rhoP D) +
        MN * max 1 ‖iotaKM D‖ ^ 3)
      ≤ D.p * (max 1 (rhoP D) + MN * max 1 (1 + D.a) ^ 3) :=
        mul_le_mul D.norm_Pc_le (add_le_add h1 hn2) (by positivity) D.p_nonneg

theorem fmap_zero : fmap D 0 = 0 := by
  ext
  simp [fmap, D.hN0]

theorem fderiv_fmap_zero_inr (hρ : 0 < D.ρ) :
    fderiv ℝ (fmap D) 0 ∘L ContinuousLinearMap.inr ℝ D.K D.M =
      ((ContinuousLinearEquiv.refl ℝ D.M : D.M ≃L[ℝ] D.M) : D.M →L[ℝ] D.M) := by
  have h0 : iotaKM D 0 ∈ ball (0 : E) D.ρ := by simpa using hρ
  have hDN0 : D.DN (iotaKM D 0) = 0 := by
    have := D.hDN _ h0
    rw [map_zero] at this ⊢
    simp only [norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hfd : HasFDerivAt (fmap D) (D.Pc ∘L (D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M +
      D.DN (iotaKM D 0) ∘L iotaKM D)) 0 := by
    have h1 : HasFDerivAt (fun v : D.K × D.M => (D.M.subtypeL ∘L
        ContinuousLinearMap.snd ℝ D.K D.M) v + D.N (iotaKM D v))
        (D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M + D.DN (iotaKM D 0) ∘L iotaKM D) 0 :=
      ((D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M).hasFDerivAt).add
        ((D.hN _ h0).comp 0 (iotaKM D).hasFDerivAt)
    exact D.Pc.hasFDerivAt.comp 0 h1
  rw [hfd.fderiv, hDN0]
  ext y
  have hyM : D.P y = y := D.mem_M.mp y.2
  simp [RangeData.coe_Pc, hyM]

/-- The range equation satisfies the hypotheses of the uniform implicit function theorem. -/
theorem hyp (hρ : 0 < D.ρ) {MN : ℝ} (hNb : DerivBound D.N (ball 0 D.ρ) 3 MN) :
    Hyp (fmap D) (ContinuousLinearEquiv.refl ℝ D.M) 1 (Mf D MN) 1 (rhoP D) where
  hρ := rhoP_pos D hρ
  ha := one_pos
  hT := by
    show ‖((ContinuousLinearEquiv.refl ℝ D.M).symm : D.M →L[ℝ] D.M)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  hF := derivBound_fmap D hρ hNb
  hF0 := fmap_zero D
  hDF := fderiv_fmap_zero_inr D hρ

/-- The uniform implicit range function `z ↦ y(z)`. -/
def yU (MN : ℝ) : D.K → D.M := imp (fmap D) (Mf D MN) 1 (rhoP D)

/-- The radius of the uniform ball for the range solution and the mean map. -/
def delta0 (MN σ δ : ℝ) : ℝ :=
  min (del (Mf D MN) 1 (rhoP D)) (min δ (7 * σ / (8 * Mp (Mf D MN))))

/-- The order-three bound of the mean map on the uniform ball. -/
def C3 (MN σ δ : ℝ) : ℝ :=
  ‖D.P0‖ * (Nat.factorial 3 * MN *
    max 1 ((1 + D.a) * (max 1 (delta0 D MN σ δ) + impC 1 (Mf D MN) 1 (rhoP D))) ^ 3)

/-- **The uniform implicit function is the range solution** on the small ball. -/
theorem sol_eq_yU (hρ : 0 < D.ρ) {MN : ℝ} (hNb : DerivBound D.N (ball 0 D.ρ) 3 MN) {σ δ : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : D.K} (hz : ‖z‖ < delta0 D MN σ δ) :
    ((yU D MN z : D.M) : F) = D.sol σ δ (z : E) := by
  have h := hyp D hρ hNb
  have hz1 : ‖z‖ < del (Mf D MN) 1 (rhoP D) := lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : ‖(z : E)‖ ≤ δ := hz.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hz3 : ‖z‖ ≤ 7 * σ / (8 * Mp (Mf D MN)) :=
    hz.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hs := h.imp_spec hz1
  have hn := h.norm_imp_le hz1
  have hzK : D.L z = 0 := LinearMap.mem_ker.mp z.2
  set y := yU D MN z with hy
  have hyM : D.P (y : F) = y := D.mem_M.mp y.2
  refine D.eq_sol hr hzK hz2 ⟨hyM, ?_⟩ ?_
  · -- `‖y‖ ≤ σ`
    have hσ : 0 < σ := hr.1
    have hMp := Mp_pos (Mf D MN)
    have hle : Mf D MN ≤ Mp (Mf D MN) := le_Mp _
    have hMf0 : 0 ≤ Mf D MN := h.hM
    change ‖(imp (fmap D) (Mf D MN) 1 (rhoP D) z : D.M)‖ ≤ σ
    refine hn.trans ?_
    rw [le_div_iff₀ (by positivity)] at hz3
    have : Mf D MN * ‖z‖ * (8 * Mp (Mf D MN)) ≤ Mp (Mf D MN) * (7 * σ) := by
      have h1 : Mf D MN * ‖z‖ ≤ Mp (Mf D MN) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      nlinarith [norm_nonneg z]
    have h2 : 8 * (Mf D MN * ‖z‖) ≤ 7 * σ := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith
  · rw [D.P_full_eq hzK hyM]
    have h0 := congrArg (fun m : D.M => (m : F)) hs.2
    simp only [fmap, iotaKM_apply, map_add, ZeroMemClass.coe_zero, Submodule.coe_add,
      RangeData.coe_Pc] at h0
    have h0' : D.P (y : F) + D.P (D.N ((z : E) + D.R y)) = 0 := h0
    rw [hyM] at h0'
    exact h0'

/-- **Uniform order-three bounds for the mean map** `Θ(z) = P₀𝒞(z + R y(z))` on `ker L`. -/
theorem derivBound_meanMap (hρ : 0 < D.ρ) {MN : ℝ} (hNb : DerivBound D.N (ball 0 D.ρ) 3 MN)
    {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) :
    DerivBound (fun z : D.K => D.meanMap σ δ (z : E)) (ball 0 (delta0 D MN σ δ)) 3
      (C3 D MN σ δ) := by
  have h := hyp D hρ hNb
  have hMN : 0 ≤ MN := hNb.nonneg (mem_ball_self hρ)
  set δ₀ := delta0 D MN σ δ with hδ₀
  have hδ₀del : δ₀ ≤ del (Mf D MN) 1 (rhoP D) := min_le_left _ _
  have hδ₀0 : 0 ≤ δ₀ := by
    have h1 := h.del_pos; have h2 := hr.2.1; have h3 := hr.1; have h4 := Mp_pos (Mf D MN)
    exact le_min h1.le (le_min h2 (by positivity))
  have himpC : 0 ≤ impC 1 (Mf D MN) 1 (rhoP D) :=
    h.derivBound_imp.nonneg (mem_ball_self h.del_pos)
  -- the implicit function on the small ball
  have himp : DerivBound (yU D MN) (ball 0 δ₀) 3 (impC 1 (Mf D MN) 1 (rhoP D)) :=
    h.derivBound_imp.subset (ball_subset_ball hδ₀del)
  have hgraph := derivBound_graph himp isOpen_ball hδ₀0 ball_subset_closedBall himpC
  have hι := hgraph.clm_comp isOpen_ball (iotaKM D)
  -- the arguments stay in the ball `B(0, ρ)`
  have hmaps : MapsTo (fun z : D.K => iotaKM D (z, yU D MN z)) (ball 0 δ₀) (ball (0 : E) D.ρ) := by
    intro z hz
    have hz' : ‖z‖ < δ₀ := mem_ball_zero_iff.mp hz
    have hz1 : ‖z‖ < del (Mf D MN) 1 (rhoP D) := lt_of_lt_of_le hz' hδ₀del
    have hs := (h.imp_spec hz1).1
    have hzs : ‖z‖ ≤ sig (Mf D MN) 1 (rhoP D) := hz1.le.trans h.del_le_sig
    have hn : ‖((z, yU D MN z) : D.K × D.M)‖ ≤ sig (Mf D MN) 1 (rhoP D) :=
      h.norm_prod_le_of hzs hs
    have h2s := h.two_sig_le
    have ha := D.a_nonneg
    rw [mem_ball_zero_iff]
    calc ‖iotaKM D (z, yU D MN z)‖ ≤ (1 + D.a) * ‖((z, yU D MN z) : D.K × D.M)‖ :=
          norm_iotaKM_apply_le D _
      _ ≤ (1 + D.a) * (rhoP D / 2) := by gcongr; linarith
      _ < D.ρ := by
          have : (1 + D.a) * rhoP D = D.ρ := by unfold rhoP; field_simp
          nlinarith [rhoP_pos D hρ]
  have hNc := derivBound_comp hNb isOpen_ball hι isOpen_ball hmaps
  have hP0 := hNc.clm_comp isOpen_ball D.P0
  have heq : ∀ z ∈ ball (0 : D.K) δ₀, D.P0 (D.N (iotaKM D (z, yU D MN z))) =
      D.meanMap σ δ (z : E) := by
    intro z hz
    rw [D.meanMap_eq, ← sol_eq_yU D hρ hNb hr (mem_ball_zero_iff.mp hz)]
    rfl
  refine (derivBound_congrOn hP0 isOpen_ball heq).mono le_rfl ?_
  unfold C3
  gcongr
  exact (norm_iotaKM_le D)

/-- **Cutoff-uniform Lipschitz bound for `D²Θ`** on the uniform ball:
`‖D²Θ(z) - D²Θ(z')‖ ≤ C₃ ‖z - z'‖` (the Lipschitz hypothesis of
`NormalizedMeanRoot.normalized_ray_bounds`, derived from uniform bounds on `D²N`, `D³N`; stated
with the second iterated derivative). -/
theorem norm_iteratedFDeriv_two_meanMap_sub_le (hρ : 0 < D.ρ) {MN : ℝ}
    (hNb : DerivBound D.N (ball 0 D.ρ) 3 MN) {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    {z z' : D.K} (hz : ‖z‖ < delta0 D MN σ δ) (hz' : ‖z'‖ < delta0 D MN σ δ) :
    ‖iteratedFDeriv ℝ 2 (fun z : D.K => D.meanMap σ δ (z : E)) z -
        iteratedFDeriv ℝ 2 (fun z : D.K => D.meanMap σ δ (z : E)) z'‖ ≤
      C3 D MN σ δ * ‖z - z'‖ :=
  norm_iteratedFDeriv_two_sub_le_of_derivBound (K := 0) (derivBound_meanMap D hρ hNb hr)
    isOpen_ball (convex_ball 0 _) (mem_ball_zero_iff.mpr hz) (mem_ball_zero_iff.mpr hz')

end

end RenewalGeometry.RangeUniform
