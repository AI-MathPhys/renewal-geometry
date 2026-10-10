/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallGaugeAlgebra

/-!
# Smooth families of functions are continuous paths in `H^s(B)`
  (stage D3 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript: the continuity method needs the path of
(pre-gauged, dilated) connections `t ↦ B_t` to be continuous in the Banach algebra `H^s(B)`.

* `exists_pdw_param` — the `x`-derivatives of a jointly smooth `F(t, x)` are jointly smooth;
* `ofSmooth_sub` — `ofSmooth` is additive;
* `norm_ofSmooth_le` — `‖ofSmooth u‖_{H^s} ≤ K_s Σ_{|w| ≤ s} ‖∂^w u‖_{L²(B)}`;
* `continuous_ofSmooth_param` (**main result**) — for jointly smooth `F : ℝ × ℝ⁴ → ℝ`,
  `t ↦ F(t, ·) ∈ H^s(B)` is continuous (uniform convergence on the compact closed ball of all
  derivatives, Heine–Cantor);
* `continuous_matOfSmooth_param` — the same for matrix-valued families in `H^s(B, M_m(ℂ))`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

/-! ### Derivatives of jointly smooth families -/

theorem pd_param {G : ℝ × (Fin 4 → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (t : ℝ) (i : Fin 4)
    (x : Fin 4 → ℝ) :
    pd (fun y => G (t, y)) i x = fderiv ℝ G (t, x) (0, Pi.single i 1) := by
  have h1 : HasFDerivAt (fun y : Fin 4 → ℝ => (t, y))
      ((0 : (Fin 4 → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin 4 → ℝ))) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h2 := ((hG.differentiable (by simp)) (t, x)).hasFDerivAt.comp x h1
  unfold pd
  rw [show (fun y => G (t, y)) = G ∘ fun y => (t, y) from rfl, h2.fderiv]
  simp

theorem contDiff_fderiv_param {G : ℝ × (Fin 4 → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (v : ℝ × (Fin 4 → ℝ)) : ContDiff ℝ ∞ (fun p => fderiv ℝ G p v) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The `x`-derivatives of a jointly smooth family are jointly smooth. -/
theorem exists_pdw_param {F : ℝ × (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ∀ w : List (Fin 4), ∃ G : ℝ × (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ G ∧
      ∀ t x, pdw (fun y => F (t, y)) w x = G (t, x)
  | [] => ⟨F, hF, fun _ _ => rfl⟩
  | i :: w => by
    obtain ⟨G, hG, hGw⟩ := exists_pdw_param hF w
    refine ⟨fun p => fderiv ℝ G p (0, Pi.single i 1), contDiff_fderiv_param hG _, fun t x => ?_⟩
    have e : pdw (fun y => F (t, y)) w = fun y => G (t, y) := funext (hGw t)
    rw [pdw_cons, e, pd_param hG t i x]

/-! ### Norms of smooth elements -/

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)]

theorem ofSmooth_sub {u v : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ofSmooth (c := c) (r := r) (s := s) (fun x => u x - v x) (hu.sub hv) =
      ofSmooth u hu - ofSmooth v hv := by
  apply ext_fn
  filter_upwards [fn_ofSmooth (c := c) (r := r) (s := s) (hu.sub hv),
    fn_ofSmooth (c := c) (r := r) (s := s) hu, fn_ofSmooth (c := c) (r := r) (s := s) hv,
    fn_sub (ofSmooth (c := c) (r := r) (s := s) u hu) (ofSmooth v hv)] with x h1 h2 h3 h4
  rw [h1, h4, h2, h3]

theorem norm_ofSmooth_le {u : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    ‖ofSmooth (c := c) (r := r) (s := s) u hu‖ ≤ Kal c r s * (nW c r s u).toReal := by
  rw [norm_def]
  exact mul_le_mul_of_nonneg_left (norm_smoothJet_le_nW c r hu) (Kal_pos c r s).le

theorem pdw_sub {u v : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ∀ w : List (Fin 4), pdw (fun x => u x - v x) w = fun x => pdw u w x - pdw v w x
  | [] => rfl
  | i :: w => by
    rw [pdw_cons, pdw_sub hu hv w]
    funext x
    rw [pdw_cons, pdw_cons]
    exact pd_sub_real ((contDiff_pdw hu w).differentiable (by simp) x)
      ((contDiff_pdw hv w).differentiable (by simp) x) i

/-- **Jointly smooth families are continuous paths in `H^s(B)`.** -/
theorem continuous_ofSmooth_param {F : ℝ × (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFt : ∀ t, ContDiff ℝ ∞ (fun x => F (t, x))) :
    Continuous fun t => ofSmooth (c := c) (r := r) (s := s) (fun x => F (t, x)) (hFt t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  set ρ := volume.restrict (euclBall c r)
  -- each derivative converges in `L²(B)`
  have hw : ∀ w : List (Fin 4), Tendsto (fun t => eLpNorm
      (pdw (fun x => F (t, x) - F (t₀, x)) w) 2 ρ) (𝓝 t₀) (𝓝 0) := by
    intro w
    obtain ⟨G, hG, hGw⟩ := exists_pdw_param hF w
    have e : ∀ t, pdw (fun x => F (t, x) - F (t₀, x)) w = fun x => G (t, x) - G (t₀, x) := by
      intro t
      rw [pdw_sub (hFt t) (hFt t₀) w]
      funext x; rw [hGw, hGw]
    simp_rw [e]
    -- uniform convergence on the closed ball
    haveI : CompactSpace (closedBall c r) := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
    have hU := Continuous.tendstoUniformly (fun t (y : closedBall c r) => G (t, y))
      (hG.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      t₀
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ρ univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal δ ≤ ε := by
      by_cases hεt : ε = ⊤
      · exact ⟨1, one_pos, by rw [hεt]; exact le_top⟩
      have hV : ρ univ ^ (2 : ℝ≥0∞).toReal⁻¹ ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top ρ univ)
      by_cases hV0 : ρ univ ^ (2 : ℝ≥0∞).toReal⁻¹ = 0
      · exact ⟨1, one_pos, by rw [hV0, zero_mul]; exact zero_le⟩
      refine ⟨(ε / ρ univ ^ (2 : ℝ≥0∞).toReal⁻¹).toReal, ?_, ?_⟩
      · exact ENNReal.toReal_pos (ENNReal.div_pos_iff.mpr ⟨hε.ne', hV⟩).ne'
          (ENNReal.div_ne_top hεt hV0)
      · rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top hεt hV0)]
        exact le_of_eq (ENNReal.mul_div_cancel hV0 hV)
    filter_upwards [Metric.tendstoUniformly_iff.mp hU δ hδ0] with t ht
    refine (eLpNorm_le_of_ae_bound (C := δ) ?_).trans hδ
    rw [ae_restrict_iff' (measurableSet_euclBall c r)]
    refine Eventually.of_forall fun x hx => ?_
    have hx' : x ∈ closedBall c r := euclBall_subset_closedBall c hr.out.le hx
    have := ht ⟨x, hx'⟩
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact this.le
  -- the norm estimate
  have hsum : Tendsto (fun t => nW c r s (fun x => F (t, x) - F (t₀, x))) (𝓝 t₀) (𝓝 0) := by
    unfold nW
    simpa using tendsto_finsetSum (wordsUpTo 4 s) fun w _ => hw w
  have hreal : Tendsto (fun t => Kal c r s * (nW c r s (fun x => F (t, x) - F (t₀, x))).toReal)
      (𝓝 t₀) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsum
    simpa using this.const_mul (Kal c r s)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hreal
  rw [← ofSmooth_sub (hFt t) (hFt t₀)]
  exact norm_ofSmooth_le _

/-! ### Matrix-valued families -/

variable {m : ℕ}

theorem continuous_cx_mk {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] {f g : ℝ → V}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun t => (⟨f t, g t⟩ : Cx V) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp (hf.tendsto t₀)).add
    (tendsto_iff_norm_sub_tendsto_zero.mp (hg.tendsto t₀))
  rw [add_zero] at h1
  refine h1.congr fun t => ?_
  rw [Cx.norm_def]
  rfl

/-- **Jointly smooth matrix families are continuous paths in `H^s(B, M_m(ℂ))`.** -/
theorem continuous_matOfSmooth_param {F : ℝ → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => F p.1 p.2 i j))
    (hFt : ∀ t i j, ContDiff ℝ ∞ (fun x => F t x i j)) :
    Continuous fun t => matOfSmooth (c := c) (r := r) s (F t) (hFt t) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [matOfSmooth, Matrix.of_apply]
  exact continuous_cx_mk
    (continuous_ofSmooth_param (F := fun p => (F p.1 p.2 i j).re)
      (Complex.reCLM.contDiff.comp (hF i j)) _)
    (continuous_ofSmooth_param (F := fun p => (F p.1 p.2 i j).im)
      (Complex.imCLM.contDiff.comp (hF i j)) _)

end RenewalGeometry.BallAnalysis.BallAlg
