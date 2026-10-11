/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientTestSize

/-!
# Componentwise convergences and weak `L²` upgrades
  (support for `thm:critical-quotient-defect`; Einstein–Standard-Model action-closure manuscript)

Generic measure-theoretic glue between the componentwise convergences of the Coulomb-chart
extraction (`CriticalQuotient.QuotientLimit`) and the vector-valued convergences used by the
first-variation rows:

* `eLpNorm_pi_le`, `lpTendsto_pi`: strong `L^p` convergence of `Π`-valued maps from that of the
  components;
* `norm_integral_smul_le`: the Hölder bound `|∫ w • W| ≤ ‖w‖₂ ‖W‖₂`;
* `tendsto_L2_weights`: a sequence bounded in `L²` that converges against every bounded real
  weight converges against every `L²` real weight (density of simple functions);
* `weakL2_of_real_weights`: weak `L²` convergence of complex fields (`WeakL2Tendsto`) from the
  pairings with real `L²` weights.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen EinsteinSM FirstVariationCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Pi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem eLpNorm_pi_le {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] {f : X → ι → F}
    (hf : ∀ i, AEStronglyMeasurable (fun x => f x i) μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm f p μ ≤ ∑ i, eLpNorm (fun x => f x i) p μ := by
  calc eLpNorm f p μ ≤ eLpNorm (fun x => ∑ i, ‖f x i‖) p μ := by
        refine eLpNorm_mono_real fun x => ?_
        exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
          fun i => Finset.single_le_sum (f := fun i => ‖f x i‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ i)
    _ = eLpNorm (∑ i, fun x => ‖f x i‖) p μ := by congr 1; funext x; simp
    _ ≤ ∑ i, eLpNorm (fun x => ‖f x i‖) p μ :=
        eLpNorm_sum_le (fun i _ => (hf i).norm) hp
    _ = ∑ i, eLpNorm (fun x => f x i) p μ := by simp only [eLpNorm_norm]

/-- **Strong `L^p` convergence of `Π`-valued maps from that of the components.** -/
theorem lpTendsto_pi {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] {u : ℕ → X → ι → F}
    {u₀ : X → ι → F} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (h : ∀ i, RenewalGeometry.LpTendsto μ p (fun n x => u n x i) (fun x => u₀ x i)) :
    RenewalGeometry.LpTendsto μ p u u₀ := by
  refine ⟨fun n => memLp_pi_iff.mpr fun i => (h i).memLp n,
    memLp_pi_iff.mpr fun i => (h i).memLp_lim, ?_⟩
  have hb : ∀ n, eLpNorm (u n - u₀) p μ ≤ ∑ i, eLpNorm ((fun n x => u n x i) n - fun x => u₀ x i)
      p μ := fun n => eLpNorm_pi_le (fun i => ((h i).memLp n).1.sub (h i).memLp_lim.1) hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hb
  simpa using tendsto_finset_sum (Finset.univ : Finset ι) fun i _ => (h i).tendsto

end Pi

/-! ### Hölder and weight upgrades -/

section Weights

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem norm_integral_smul_le {w : X → ℝ} {W : X → ℂ} (hw : MemLp w 2 μ) (hW : MemLp W 2 μ) :
    ‖∫ x, w x • W x ∂μ‖ ≤ (eLpNorm w 2 μ).toReal * (eLpNorm W 2 μ).toReal := by
  have h1 : MemLp (w • W) 1 μ := hW.smul hw
  calc ‖∫ x, w x • W x ∂μ‖ ≤ ∫ x, ‖(w • W) x‖ ∂μ := norm_integral_le_integral_norm _
    _ = (eLpNorm (w • W) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm h1.1]
    _ ≤ (eLpNorm w 2 μ * eLpNorm W 2 μ).toReal := by
        refine ENNReal.toReal_mono (ENNReal.mul_ne_top hw.eLpNorm_ne_top hW.eLpNorm_ne_top) ?_
        have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
        exact eLpNorm_smul_le_mul_eLpNorm hW.1 hw.1
    _ = _ := ENNReal.toReal_mul

variable [IsFiniteMeasure μ]

/-- **Upgrade of weights**: a sequence bounded in `L²` converging against every bounded real
weight converges against every `L²` real weight. -/
theorem tendsto_L2_weights {W : ℕ → X → ℂ} {W₀ : X → ℂ} (hW : ∀ n, MemLp (W n) 2 μ)
    (hW₀ : MemLp W₀ 2 μ) {B : ℝ} (hB : ∀ n, (eLpNorm (W n) 2 μ).toReal ≤ B)
    (h : ∀ w : X → ℝ, MemLp w ⊤ μ →
      Tendsto (fun n => ∫ x, w x • W n x ∂μ) atTop (𝓝 (∫ x, w x • W₀ x ∂μ)))
    {w : X → ℝ} (hw : MemLp w 2 μ) :
    Tendsto (fun n => ∫ x, w x • W n x ∂μ) atTop (𝓝 (∫ x, w x • W₀ x ∂μ)) := by
  have hB0 : 0 ≤ B := le_trans ENNReal.toReal_nonneg (hB 0)
  set M₀ := (eLpNorm W₀ 2 μ).toReal
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (3 * (B + M₀ + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hg, -⟩ := hw.exists_simpleFunc_eLpNorm_sub_lt (by norm_num)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  have hgM : MemLp (⇑g) ⊤ μ := g.memLp_top μ
  have hg2 : MemLp (⇑g) 2 μ := hgM.mono_exponent le_top
  have hd : MemLp (w - ⇑g) 2 μ := hw.sub hg2
  have hdδ : (eLpNorm (w - ⇑g) 2 μ).toReal ≤ δ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
    rwa [ENNReal.toReal_ofReal hδ.le] at this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h g hgM) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hint : ∀ {V : X → ℂ}, MemLp V 2 μ → ∀ {u : X → ℝ}, MemLp u 2 μ →
      Integrable (fun x => u x • V x) μ := fun hV _ hu => (hV.smul hu).integrable le_rfl
  have hsplit : ∀ V : X → ℂ, MemLp V 2 μ →
      ∫ x, w x • V x ∂μ = ∫ x, (w - ⇑g) x • V x ∂μ + ∫ x, g x • V x ∂μ := by
    intro V hV
    rw [← integral_add (hint hV hd) (hint hV hg2)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sub_smul]
  rw [dist_eq_norm, hsplit _ (hW n), hsplit _ hW₀]
  have e : ∫ x, (w - ⇑g) x • W n x ∂μ + ∫ x, g x • W n x ∂μ -
      (∫ x, (w - ⇑g) x • W₀ x ∂μ + ∫ x, g x • W₀ x ∂μ) =
      ∫ x, (w - ⇑g) x • W n x ∂μ + (∫ x, g x • W n x ∂μ - ∫ x, g x • W₀ x ∂μ) -
        ∫ x, (w - ⇑g) x • W₀ x ∂μ := by ring
  rw [e]
  have b1 := norm_integral_smul_le hd (hW n)
  have b2 := norm_integral_smul_le hd hW₀
  have b3 : ‖∫ x, g x • W n x ∂μ - ∫ x, g x • W₀ x ∂μ‖ < ε / 3 := by
    have := hN n hn; rwa [dist_eq_norm] at this
  calc ‖∫ x, (w - ⇑g) x • W n x ∂μ + (∫ x, g x • W n x ∂μ - ∫ x, g x • W₀ x ∂μ) -
        ∫ x, (w - ⇑g) x • W₀ x ∂μ‖
      ≤ ‖∫ x, (w - ⇑g) x • W n x ∂μ‖ + ‖∫ x, g x • W n x ∂μ - ∫ x, g x • W₀ x ∂μ‖ +
          ‖∫ x, (w - ⇑g) x • W₀ x ∂μ‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ < δ * B + ε / 3 + δ * M₀ + δ := by
        have h1 : ‖∫ x, (w - ⇑g) x • W n x ∂μ‖ ≤ δ * B :=
          b1.trans (mul_le_mul hdδ (hB n) ENNReal.toReal_nonneg hδ.le)
        have h2 : ‖∫ x, (w - ⇑g) x • W₀ x ∂μ‖ ≤ δ * M₀ :=
          b2.trans (mul_le_mul_of_nonneg_right hdδ ENNReal.toReal_nonneg)
        linarith
    _ ≤ ε := by
        have hne : B + M₀ + 1 ≠ 0 := by positivity
        have : δ * (B + M₀ + 1) = ε / 3 := by
          simp only [δ]; field_simp
        nlinarith

end Weights

/-- **Weak `L²` convergence of complex fields from real `L²` weights** (on a box). -/
theorem weakL2_of_real_weights {a b : E4} {W : ℕ → E4 → ℂ} {W₀ : E4 → ℂ}
    (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box a b)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box a b)))
    (h : ∀ w : E4 → ℝ, MemLp w 2 (volume.restrict (box a b)) →
      Tendsto (fun n => ∫ x, w x • W n x ∂(volume.restrict (box a b))) atTop
        (𝓝 (∫ x, w x • W₀ x ∂(volume.restrict (box a b))))) :
    WeakL2Tendsto a b W W₀ := by
  intro ℓ g hg
  set μ := volume.restrict (box a b)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (volume_box_ne_top a b)
  have key : ∀ V : E4 → ℂ, MemLp V 2 μ →
      ∫ x, g x * ℓ (V x) ∂μ = ℓ 1 * (∫ x, g x • V x ∂μ).re + ℓ Complex.I * (∫ x, g x • V x ∂μ).im := by
    intro V hV
    have hint : Integrable (fun x => g x • V x) μ := (hV.smul hg).integrable le_rfl
    have hre := integral_re hint
    have him := integral_im hint
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, Complex.real_smul,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul] at hre him
    have hi1 : Integrable (fun x => g x * (V x).re) μ :=
      hint.re.congr (Eventually.of_forall fun x => by simp [Complex.real_smul])
    have hi2 : Integrable (fun x => g x * (V x).im) μ :=
      hint.im.congr (Eventually.of_forall fun x => by simp [Complex.real_smul])
    simp only [Complex.real_smul] at hre him ⊢
    rw [← hre, ← him, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi1.const_mul _) (hi2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [clm_complex_eq ℓ (V x)]
    ring
  simp only [key _ (hW _), key _ hW₀]
  exact ((tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp (h g hg))).add
    (tendsto_const_nhds.mul ((Complex.continuous_im.tendsto _).comp (h g hg))))

end RenewalGeometry.CriticalQuotientRows
