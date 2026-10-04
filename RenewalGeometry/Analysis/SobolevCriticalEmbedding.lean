/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevLocalRellich
import RenewalGeometry.Analysis.MollifierLpConvergence

/-!
# The critical Sobolev embedding `W^{1,2} ↪ L^{2d/(d-2)}` for compactly supported functions

Generic infrastructure (no renewal notions).  In dimension `d = card ι ≥ 3`, with
`1/p' = 1/2 - 1/d` (`p' = 4` in four dimensions), every `u ∈ W^{1,2}(ℝ^ι)` vanishing outside a
ball satisfies

  `‖u‖_{L^{p'}} ≤ C_d Σ_i ‖∂_i u‖_{L²}`            (`eLpNorm_le_sum_grad_of_ball`),

with `C_d` Mathlib's Gagliardo–Nirenberg–Sobolev constant `SNormLESNormFDerivOfEqConst ℂ volume 2`.
This is the **critical** case (`H¹ ⊂ L⁴` in four dimensions), which the Fourier-side argument of
`TorusSobolevL4.lean` (`H^s ⊂ L⁴` only for `s > d/4`) does not reach.

Proof: mollify, `u_ε = ρ_ε ⋆ u`; `u_ε` is smooth and compactly supported, its partial derivatives
are `ρ_ε ⋆ ∂_i u` (`pd_convolution_eq`, from the weak-derivative identity tested against
`y ↦ ρ_ε(x - y)`), so Mathlib's Gagliardo–Nirenberg–Sobolev inequality
(`eLpNorm_le_eLpNorm_fderiv_of_eq`), `‖Du_ε‖ ≤ Σ_i |∂_i u_ε|` (`norm_le_sum_apply_single`) and
Young's inequality give `‖u_ε‖_{p'} ≤ C Σ ‖∂_i u‖_2`; finally `u_ε → u` in `L²`, hence a.e.
along a subsequence, and Fatou (`Lp.eLpNorm_lim_le_liminf_eLpNorm`) passes the bound to `u`.

The version on a coordinate box `Q` (`H¹(Q) ↪ L^{p'}(Q)`, through the reflection extension) is
`eLpNorm_le_box` in `SobolevBoxCompactness.lean`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Convolution

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a linear form on `ℝ^ι` (sup norm), `‖L‖ ≤ Σ_i ‖L e_i‖`. -/
theorem norm_le_sum_apply_single (L : (ι → ℝ) →L[ℝ] ℂ) : ‖L‖ ≤ ∑ i, ‖L (Pi.single i 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (norm_nonneg _)

/-- **Derivatives of mollifications.**  If `g` is the weak `i`-th partial of `u` on `ℝ^ι` and `ρ`
is a smooth compactly supported kernel, then `∂_i(ρ ⋆ u) = ρ ⋆ g`. -/
theorem pd_convolution_eq {ρ : (ι → ℝ) → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    {i : ι} {u g : (ι → ℝ) → ℂ} (hw : HasWeakPartial univ i u g)
    (hu : LocallyIntegrable u volume) (x : ι → ℝ) :
    pd (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) i x =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  unfold pd
  rw [Mollifier.fderiv_convolution_apply hρ1 hρc hu x (Pi.single i 1), convolution_def]
  set ψ : (ι → ℝ) → ℝ := fun y => ρ (x - y) with hψdef
  have hψs : ContDiff ℝ ∞ ψ := hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hψ : IsTest univ ψ := ⟨hψs, hψc, subset_univ _⟩
  have hpdψ : ∀ y, pd ψ i y = -(fderiv ℝ ρ (x - y) (Pi.single i 1)) := by
    intro y
    unfold pd
    have h1 : HasFDerivAt (fun y : ι → ℝ => x - y) (-ContinuousLinearMap.id ℝ (ι → ℝ)) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((hρ1.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y h1
    rw [show ψ = ρ ∘ fun y => x - y from rfl, h2.fderiv]
    simp
  have key := hw ψ hψ
  simp only [hpdψ] at key
  have e1 : ∫ t, fderiv ℝ ρ t (Pi.single i 1) • u (x - t) =
      ∫ y, fderiv ℝ ρ (x - y) (Pi.single i 1) • u y := by
    rw [← integral_sub_left_eq_self (fun t => fderiv ℝ ρ t (Pi.single i 1) • u (x - t)) volume x]
    simp only [sub_sub_cancel]
  have e2 : ∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t)) =
      ∫ y, ρ (x - y) • g y := by
    rw [← integral_sub_left_eq_self (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t)))
      volume x]
    simp only [sub_sub_cancel, ContinuousLinearMap.lsmul_apply]
  rw [e1, e2]
  simp only [Complex.real_smul]
  have e3 : (fun y => ((-(fderiv ℝ ρ (x - y)) (Pi.single i 1) : ℝ) : ℂ) * u y) =
      fun y => -(((fderiv ℝ ρ (x - y) (Pi.single i 1) : ℝ) : ℂ) * u y) := by
    funext y; push_cast; ring
  rw [e3, integral_neg] at key
  exact neg_inj.mp key

/-- **Critical Sobolev embedding for compactly supported `W^{1,2}` functions.**  If
`d = card ι ≥ 3`, `1/p' = 1/2 - 1/d`, and `u ∈ W^{1,2}(ℝ^ι)` vanishes outside a ball, then
`‖u‖_{L^{p'}} ≤ C_d Σ_i ‖∂_i u‖_{L²}` (in four dimensions: `H¹_c ⊂ L⁴`). -/
theorem eLpNorm_le_sum_grad_of_ball {R : ℝ} {u : (ι → ℝ) → ℂ} {g : ι → (ι → ℝ) → ℂ}
    (hW : MemW12 univ u g) (hu0 : ∀ x, R < ‖x‖ → u x = 0) (hn : 2 < Fintype.card ι)
    {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (Fintype.card ι : ℝ)⁻¹) :
    eLpNorm u p' volume ≤
      SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 *
        ∑ i, eLpNorm (g i) 2 volume := by
  set C := SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2
  have hu2 : MemLp u 2 volume := by simpa using hW.memLp
  have hg2 : ∀ i, MemLp (g i) 2 volume := fun i => by simpa using hW.memLp_grad i
  have hloc : LocallyIntegrable u volume := hu2.locallyIntegrable (by norm_num)
  have hucs : HasCompactSupport u := HasCompactSupport.intro (isCompact_closedBall 0 R)
    (fun x hx => hu0 x (by simpa [Metric.mem_closedBall, dist_zero_right] using hx))
  have hweak : ∀ i, HasWeakPartial univ i u (g i) := hW.weak
  -- mollifiers
  let φk : ℕ → ContDiffBump (0 : ι → ℝ) := fun k =>
    ⟨1 / ((k : ℝ) + 2), 2 / ((k : ℝ) + 2), by positivity,
      by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  set ρ : ℕ → (ι → ℝ) → ℝ := fun k => (φk k).normed volume
  set uk : ℕ → (ι → ℝ) → ℂ := fun k => ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u
  have hρs : ∀ k, ContDiff ℝ ∞ (ρ k) := fun k => (φk k).contDiff_normed
  have hρc : ∀ k, HasCompactSupport (ρ k) := fun k => (φk k).hasCompactSupport_normed
  have hsm : ∀ k, ContDiff ℝ 1 (uk k) := fun k =>
    (hρc k).contDiff_convolution_left _ ((hρs k).of_le (by simp)) hloc
  have hcs : ∀ k, HasCompactSupport (uk k) := fun k => (hρc k).convolution _ hucs
  -- Gagliardo–Nirenberg–Sobolev for the mollifications
  have hfin : 0 < Module.finrank ℝ (ι → ℝ) := by rw [finrank_pi_real]; omega
  have hGNS : ∀ k, eLpNorm (uk k) p' volume ≤ C * eLpNorm (fderiv ℝ (uk k)) 2 volume := by
    intro k
    have := eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℂ) (volume : Measure (ι → ℝ)) (hsm k) (hcs k)
      (p := 2) (p' := p') (by norm_num) hfin (by rw [finrank_pi_real]; push_cast; exact hp')
    simpa using this
  -- the derivative bound
  have hD : ∀ k, eLpNorm (fderiv ℝ (uk k)) 2 volume ≤ ∑ i, eLpNorm (g i) 2 volume := by
    intro k
    have hpd : ∀ i, pd (uk k) i = ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g i := fun i =>
      funext fun x => pd_convolution_eq (hρs k) (hρc k) (hweak i) hloc x
    have hcont : ∀ i, Continuous (pd (uk k) i) := fun i => continuous_pd (hsm k) i
    have h1 : eLpNorm (fderiv ℝ (uk k)) 2 volume ≤
        eLpNorm (∑ i, fun x => ‖pd (uk k) i x‖) 2 volume := by
      refine eLpNorm_mono fun x => ?_
      rw [Finset.sum_apply, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      exact norm_le_sum_apply_single _
    have h2 : eLpNorm (∑ i, fun x => ‖pd (uk k) i x‖) 2 volume ≤
        ∑ i, eLpNorm (fun x => ‖pd (uk k) i x‖) 2 volume :=
      eLpNorm_sum_le (fun i _ => (hcont i).norm.aestronglyMeasurable) (by norm_num)
    refine h1.trans (h2.trans (Finset.sum_le_sum fun i _ => ?_))
    rw [eLpNorm_norm, hpd i]
    exact Mollifier.eLpNorm_convolution_le (φk k).continuous_normed.measurable
      (fun x => (φk k).nonneg_normed x) (φk k).integral_normed (hg2 i).1 (by norm_num)
      (by norm_num)
  have hbound : ∀ k, eLpNorm (uk k) p' volume ≤ C * ∑ i, eLpNorm (g i) 2 volume := fun k =>
    (hGNS k).trans (by gcongr; exact hD k)
  -- `L²` convergence of the mollifications and Fatou
  have hr : Tendsto (fun k => (φk k).rOut) atTop (𝓝 0) := by
    show Tendsto (fun k : ℕ => 2 / ((k : ℝ) + 2)) atTop (𝓝 0)
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
    simpa using this.const_div_atTop 2
  have hL2 := Mollifier.tendsto_eLpNorm_normed_bump_convolution_sub (μ := volume) hr
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hu2
  have hukm : ∀ k, AEStronglyMeasurable (uk k) volume := fun k => (hsm k).continuous.aestronglyMeasurable
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hukm hu2.1 hL2
  obtain ⟨ns, -, hae⟩ := hmeas.exists_seq_tendsto_ae
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun k => hukm (ns k)) u hae).trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall fun k => hbound (ns k))

end RenewalGeometry.SobolevOpen
