/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallCoulombEnergy

/-!
# The quantitative embedding `H^s(B) ⊂ L^∞(B)`, `s ≥ 3`, and continuity of `L^p` norms
  (stages D2/D3 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `exists_ae_abs_le_norm` — there is `C` with `|F(x)| ≤ C ‖F‖_{H^s}` a.e. on `B` for every
  `F ∈ H^s(B)` (`abs_le_n3` on smooth approximants, density, a.e. limits);
* `eLpNorm_fn_le_norm` — hence `‖F‖_{L^p(B)} ≤ C' ‖F‖_{H^s}`;
* `continuous_eLpNorm_fn` — `F ↦ ‖F‖_{L^p(B)}` is continuous on `H^s(B)`;
* `continuous_coordL4` — the coefficient `L⁴` norm is continuous.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)]

/-- Smooth functions are bounded on the ball by their `H^s` norm. -/
theorem exists_abs_le_norm_ofSmooth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (Fin 4 → ℝ) → ℝ) (hu : ContDiff ℝ ∞ u), ∀ x ∈ euclBall c r,
      |u x| ≤ C * ‖ofSmooth (c := c) (r := r) (s := s) u hu‖ := by
  obtain ⟨C, hC, hb⟩ := abs_le_n3 c r hr.out
  have hK := (Kal_pos c r s).le
  refine ⟨C.toReal * (4 * (wordsUpTo 4 s).card * (Kal c r s)⁻¹),
    mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr hK)),
    fun u hu x hx => ?_⟩
  have h1 := hb u hu x hx
  have hfin : nW c r s u ≠ ⊤ := by
    unfold nW
    exact ENNReal.sum_ne_top.mpr fun w _ =>
      (memLp_ball_of_contDiff c r hr.out (contDiff_pdw hu w) 2).eLpNorm_lt_top.ne
  have h2 : n3 c r u ≤ 4 * nW c r s u :=
    (n3_le_nW c r (le_refl 3) u).trans (by gcongr; exact nW_mono c r hs.out u)
  have h3 : (nW c r s u).toReal ≤ (wordsUpTo 4 s).card * ‖smoothJet c r s hu‖ :=
    nW_le_card_mul_norm c r hu
  have h4 : ‖smoothJet c r s hu‖ = (Kal c r s)⁻¹ * ‖ofSmooth (c := c) (r := r) (s := s) u hu‖ := by
    rw [norm_def, ← mul_assoc, inv_mul_cancel₀ (Kal_pos c r s).ne', one_mul]
    rfl
  have h5 : ENNReal.ofReal |u x| ≤ C * (4 * nW c r s u) := h1.trans (by gcongr)
  have h6 : |u x| ≤ C.toReal * (4 * (nW c r s u).toReal) := by
    have := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hC
      (ENNReal.mul_ne_top (by norm_num) hfin))).mp h5
    simpa [ENNReal.toReal_mul] using this
  calc |u x| ≤ C.toReal * (4 * (nW c r s u).toReal) := h6
    _ ≤ C.toReal * (4 * ((wordsUpTo 4 s).card * ‖smoothJet c r s hu‖)) := by gcongr
    _ = C.toReal * (4 * (wordsUpTo 4 s).card * (Kal c r s)⁻¹) *
          ‖ofSmooth (c := c) (r := r) (s := s) u hu‖ := by rw [h4]; ring

/-- **The quantitative embedding `H^s(B) ⊂ L^∞(B)`** (`s ≥ 3`). -/
theorem exists_ae_abs_le_norm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SobAlg c r s, ∀ᵐ x ∂(volume.restrict (euclBall c r)),
      |fn F x| ≤ C * ‖F‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_norm_ofSmooth (c := c) (r := r) (s := s)
  refine ⟨C, hC0, fun F => ?_⟩
  obtain ⟨φ, hφ, hlim⟩ := exists_tendsto_ofSmooth F
  -- `L²` convergence of the functions
  have hL2 : Tendsto (fun k => eLpNorm (fn (ofSmooth (c := c) (r := r) (s := s) (φ k) (hφ k)) -
      fn F) 2 (volume.restrict (euclBall c r))) atTop (𝓝 0) := by
    have h := (jetL (c := c) (r := r) (s := s)).continuous.tendsto F |>.comp hlim
    have h2 := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ↥(wordsUpTo 4 s) => L2B c r) (nilW s)).continuous.comp
      continuous_subtype_val).tendsto (jetL F) |>.comp h
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h2
    exact h2
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun k => (memLp_fn _).aestronglyMeasurable) (memLp_fn F).aestronglyMeasurable hL2).exists_seq_tendsto_ae
  have hall : ∀ k, ∀ᵐ x ∂(volume.restrict (euclBall c r)),
      |fn (ofSmooth (c := c) (r := r) (s := s) (φ (ns k)) (hφ (ns k))) x| ≤
        C * ‖ofSmooth (c := c) (r := r) (s := s) (φ (ns k)) (hφ (ns k))‖ := by
    intro k
    filter_upwards [fn_ofSmooth (c := c) (r := r) (s := s) (hφ (ns k)),
      ae_restrict_mem (measurableSet_euclBall c r)] with x hx hxB
    rw [hx]
    exact hC _ _ x hxB
  rw [← ae_all_iff] at hall
  filter_upwards [hae, hall] with x hx hk
  have hn : Tendsto (fun k => C * ‖ofSmooth (c := c) (r := r) (s := s) (φ (ns k)) (hφ (ns k))‖)
      atTop (𝓝 (C * ‖F‖)) :=
    ((continuous_norm.tendsto F).comp (hlim.comp hns.tendsto_atTop)).const_mul C
  exact le_of_tendsto_of_tendsto hx.abs hn (Eventually.of_forall hk)

/-- **`L^p` norms are controlled by the `H^s` norm.** -/
theorem exists_eLpNorm_fn_le (p : ℝ≥0∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SobAlg c r s,
      eLpNorm (fn F) p (volume.restrict (euclBall c r)) ≤ ENNReal.ofReal (C * ‖F‖) := by
  obtain ⟨C, hC0, hC⟩ := exists_ae_abs_le_norm (c := c) (r := r) (s := s)
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  set V := (volume.restrict (euclBall c r)) univ ^ p.toReal⁻¹
  have hV : V ≠ ⊤ := by
    by_cases hp : p.toReal⁻¹ = 0
    · simp [V, hp]
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
  refine ⟨V.toReal * C, by positivity, fun F => ?_⟩
  refine (eLpNorm_le_of_ae_bound (C := C * ‖F‖) ((hC F).mono fun x hx => by
    rwa [Real.norm_eq_abs])).trans ?_
  rw [mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV]

/-- **`F ↦ ‖F‖_{L^p(B)}` is continuous on `H^s(B)`.** -/
theorem continuous_eLpNorm_fn (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Continuous fun F : SobAlg c r s => eLpNorm (fn F) p (volume.restrict (euclBall c r)) := by
  obtain ⟨C, hC0, hC⟩ := exists_eLpNorm_fn_le (c := c) (r := r) (s := s) p
  rw [continuous_iff_continuousAt]
  intro F₀
  have hdiff : ∀ F, eLpNorm (fn F - fn F₀) p (volume.restrict (euclBall c r)) ≤
      ENNReal.ofReal (C * ‖F - F₀‖) := fun F => by
    refine le_trans (le_of_eq ?_) (hC (F - F₀))
    exact eLpNorm_congr_ae (fn_sub F F₀).symm
  have hfin : ∀ F, eLpNorm (fn F) p (volume.restrict (euclBall c r)) ≠ ⊤ := fun F =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC F)
  have hlim : Tendsto (fun F => ENNReal.ofReal (C * ‖F - F₀‖)) (𝓝 F₀) (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_id (x := 𝓝 F₀))).const_mul C
    simpa using this
  rw [ContinuousAt, ENNReal.tendsto_nhds (hfin F₀)]
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hlim) ε hε] with F hF
  have h1 := eLpNorm_sub_le (p := p) (μ := volume.restrict (euclBall c r))
    (memLp_fn F).aestronglyMeasurable (memLp_fn F₀).aestronglyMeasurable hp
  constructor
  · -- `‖F₀‖ - ε ≤ ‖F‖`
    have h2 : eLpNorm (fn F₀) p (volume.restrict (euclBall c r)) ≤
        eLpNorm (fn F) p (volume.restrict (euclBall c r)) + ε := by
      have := eLpNorm_add_le (p := p) (μ := volume.restrict (euclBall c r))
        (memLp_fn F).aestronglyMeasurable
        ((memLp_fn F₀).aestronglyMeasurable.sub (memLp_fn F).aestronglyMeasurable) hp
      rw [show fn F + (fn F₀ - fn F) = fn F₀ by abel] at this
      refine this.trans (add_le_add le_rfl ?_)
      rw [eLpNorm_sub_comm]; exact (hdiff F).trans hF
    exact tsub_le_iff_right.mpr h2
  · have h2 : eLpNorm (fn F) p (volume.restrict (euclBall c r)) ≤
        eLpNorm (fn F₀) p (volume.restrict (euclBall c r)) + ε := by
      have := eLpNorm_add_le (p := p) (μ := volume.restrict (euclBall c r))
        (memLp_fn F₀).aestronglyMeasurable
        ((memLp_fn F).aestronglyMeasurable.sub (memLp_fn F₀).aestronglyMeasurable) hp
      rw [show fn F₀ + (fn F - fn F₀) = fn F by abel] at this
      exact this.trans (add_le_add le_rfl ((hdiff F).trans hF))
    exact h2

/-- **The coefficient `L⁴` norm is continuous.** -/
theorem continuous_coordL4 {d : ℕ} :
    Continuous fun a : Fin 4 → Fin d → SobAlg c r 4 => coordL4 a := by
  unfold coordL4
  exact continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun b _ =>
    (continuous_eLpNorm_fn (s := 4) 4 (by norm_num)).comp
      ((continuous_apply b).comp (continuous_apply ν))

end RenewalGeometry.BallAnalysis.BallAlg
