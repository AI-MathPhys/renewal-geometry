/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.MonotoneDefectRemovalExact
import RenewalGeometry.Analysis.PositivePacketDefectExact
import RenewalGeometry.Gravity.WeakPalatiniPassageExact

/-!
# Vanishing of both Higgs defects under strong monotonicity
  (`prop:monotonicity`, final sentence; Einstein–SM action closure)

`MonotoneDefectRemovalExact.tendsto_of_monotone` proves the first conclusion of
`prop:monotonicity`: strong monotonicity forces `H_h → H` in `V ∩ L⁴`.  This file proves the
closing sentence: *if `V` controls the covariant `H¹` norm, both Higgs defects vanish*.

Setting.  `K` is a compact metric space with a Borel measure `V₀` (the compact domain with its
reference volume).  The Higgs fields live in a real normed space `V` with a continuous linear
embedding `ι₄ : V →L L⁴(K; F)` (`V ↪ L⁴`, `F` the realified Higgs fibre), and the monotonicity
inequality uses `‖u - v‖₄ = ‖ι₄ (u - v)‖`.  "`V` controls the covariant `H¹` norm" is rendered
as: the (realified) covariant gradients `D_h = D_{A_h} : V →L L²(K; ℝ^r)` are uniformly bounded,
`‖D_h u‖₂ ≤ C_D ‖u‖_V`, and `D_h H → D_A H` in `L²` for the limit field (e.g. `D_h = D_A` fixed,
or `A_h → A` in `L⁴`, which gives `‖(D_{A_h} - D_A) u‖₂ ≤ ‖A_h - A‖₄ ‖u‖₄ ≤ C ‖A_h - A‖₄ ‖u‖_V`).

The two defects are those of `thm:higgs-defect` / `lem:critical-cubic`, defined by their
weak-star defining relations (measures are tested on `C(K)`):

* the kinetic defect `𝔎_H`: for each stress component, the covariant-gradient packet
  `Y_h = D_h H_h` enters through a quadratic form with continuous coefficients `B_h → B`
  uniformly (metric, inverse metric and volume density), and `𝔎` is any functional with
  `B_h(Y_h, Y_h) dV₀ ⇀* B(Y, Y) dV₀ + 𝔎`; in particular the packet defect `𝖰_Y` of
  `lem:positive-packet-defect`;
* the quartic defect `ν_H`: `|H_h|⁴ dV_{g_h} ⇀* |H|⁴ dV_g + ν_H` with volume densities
  `ρ_h → ρ` uniformly.

Results:

* `tendsto_integral_mul_norm_pow_four` — strong `L⁴` convergence `f_h → f` and uniformly
  convergent continuous weights `ψ_h → ψ` give `∫ ψ_h |f_h|⁴ → ∫ ψ |f|⁴` (via the four-factor
  estimate `‖|f_h|⁴ - |f|⁴‖₁ ≤ ‖f_h - f‖₄ (‖f_h‖₄ + ‖f‖₄)³`);
* `isPacketDefect_zero_of_tendsto` — a strongly convergent packet has zero packet defect;
* `monotone_higgs_defects_vanish` — the proposition's closing sentence, bundled with the first
  conclusion: `H_h → H` in `V`, in `L⁴`, `D_h H_h → D H` in `L²`, the packet defect `𝖰_Y`
  vanishes, every kinetic stress defect `𝔎` vanishes and the quartic defect `ν_H` vanishes.
-/

open MeasureTheory Filter Topology ENNReal
open scoped RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.MonotoneHiggsDefect

open PositivePacketDefect

/-- `1 ≤ 4` in `ℝ≥0∞`, needed for the Banach space `L⁴`. -/
theorem fact_one_le_four : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

attribute [local instance] fact_one_le_four

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise quartic difference bound
`| ‖a‖⁴ - ‖b‖⁴ | ≤ ‖a - b‖ (‖a‖ + ‖b‖)³`. -/
theorem abs_norm_pow_four_sub_le (a b : F) :
    |‖a‖ ^ 4 - ‖b‖ ^ 4| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) := by
  set s := ‖a‖
  set t := ‖b‖
  have hs : 0 ≤ s := norm_nonneg a
  have ht : 0 ≤ t := norm_nonneg b
  have hfac : s ^ 4 - t ^ 4 = (s - t) * ((s + t) * (s ^ 2 + t ^ 2)) := by ring
  have h1 : |s - t| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h2 : (s + t) * (s ^ 2 + t ^ 2) ≤ (s + t) * (s + t) * (s + t) := by
    have : s ^ 2 + t ^ 2 ≤ (s + t) * (s + t) := by nlinarith
    calc (s + t) * (s ^ 2 + t ^ 2) ≤ (s + t) * ((s + t) * (s + t)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (s + t) * (s + t) * (s + t) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (s + t) * (s ^ 2 + t ^ 2))]
  calc |s - t| * ((s + t) * (s ^ 2 + t ^ 2))
      ≤ ‖a - b‖ * ((s + t) * (s + t) * (s + t)) :=
        mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    _ = ‖a - b‖ * (s + t) * (s + t) * (s + t) := by ring

/-- `L¹` convergence of the quartic densities under strong `L⁴` convergence:
`∫ | |f_h|⁴ - |f|⁴ | → 0`. -/
theorem tendsto_integral_abs_norm_pow_four_sub {f : ℕ → Lp F 4 V₀} {f₀ : Lp F 4 V₀}
    (hf : Tendsto (fun n => ‖f n - f₀‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4‖ ∂V₀) atTop (𝓝 0) := by
  have hconv : Tendsto f atTop (𝓝 f₀) := tendsto_iff_norm_sub_tendsto_zero.2 hf
  obtain ⟨C, hC⟩ := hconv.norm.bddAbove_range
  have hCn : ∀ n, ‖f n‖ ≤ C := fun n => hC ⟨n, rfl⟩
  have hfm : ∀ n, AEStronglyMeasurable (f n : K → F) V₀ := fun n => Lp.aestronglyMeasurable _
  have hf₀m : AEStronglyMeasurable (f₀ : K → F) V₀ := Lp.aestronglyMeasurable _
  -- `eLpNorm' · 4` of an `L⁴` element is `ofReal` of its norm
  have h4 : ∀ g : Lp F 4 V₀, eLpNorm' (g : K → F) 4 V₀ = ENNReal.ofReal ‖g‖ := fun g => by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g),
      eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
    norm_num
  set A : ℝ≥0∞ := ENNReal.ofReal C + ENNReal.ofReal ‖f₀‖ with hA
  have hAne : A ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  set G : ℕ → K → ℝ := fun n x => ‖f n x‖ + ‖f₀ x‖ with hG
  have hGm : ∀ n, AEStronglyMeasurable (G n) V₀ := fun n => (hfm n).norm.add hf₀m.norm
  have hG4 : ∀ n, eLpNorm' (G n) 4 V₀ ≤ A := fun n => by
    have := eLpNorm'_add_le (hfm n).norm hf₀m.norm (by norm_num : (1 : ℝ) ≤ 4)
    rw [eLpNorm'_norm, eLpNorm'_norm, h4, h4] at this
    exact this.trans (add_le_add (ENNReal.ofReal_le_ofReal (hCn n)) le_rfl)
  have hdiff4 : ∀ n, eLpNorm' (fun x => f n x - f₀ x) 4 V₀ = ENNReal.ofReal ‖f n - f₀‖ :=
    fun n => by
      rw [← h4]
      exact eLpNorm'_congr_ae (Lp.coeFn_sub (f n) f₀).symm
  have hest : ∀ n, eLpNorm (fun x => ‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4) 1 V₀ ≤
      ENNReal.ofReal ‖f n - f₀‖ * A * A * A := fun n => by
    have h := WeakPalatiniPassage.eLpNorm_fourFactor_le (fun x => ‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4)
      (fun x => f n x - f₀ x) (G n) (G n) (G n) ((hfm n).sub hf₀m) (hGm n) (hGm n) (hGm n) 1
      (fun x => by
        have := abs_norm_pow_four_sub_le (f n x) (f₀ x)
        have hg0 : 0 ≤ G n x := by positivity
        rw [Real.norm_eq_abs, Real.norm_of_nonneg hg0]
        simpa [hG] using this)
    refine h.trans ?_
    rw [hdiff4, ENNReal.coe_one, one_mul]
    gcongr <;> exact hG4 n
  have hmaj : Tendsto (fun n => ENNReal.ofReal ‖f n - f₀‖ * A * A * A) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => ENNReal.ofReal ‖f n - f₀‖) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hf
      rwa [ENNReal.ofReal_zero] at this
    have h1 := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.mul_const h0 (Or.inr hAne)) (Or.inr hAne)) (Or.inr hAne)
    simpa using h1
  have hL1 : Tendsto (fun n => eLpNorm (fun x => ‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4) 1 V₀) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj (fun _ => zero_le) hest
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hL1
  simp only [Function.comp_def, ENNReal.toReal_zero] at hreal
  refine hreal.congr fun n => ?_
  have hmeas : AEStronglyMeasurable (fun x => ‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4) V₀ :=
    ((hfm n).norm.pow 4).sub (hf₀m.norm.pow 4)
  rw [integral_norm_eq_lintegral_enorm hmeas, ← eLpNorm_one_eq_lintegral_enorm]

theorem integrable_norm_pow_four (g : Lp F 4 V₀) :
    Integrable (fun x => ‖(g : K → F) x‖ ^ 4) V₀ := by
  have hg : MemLp (g : K → F) ((4 : ℕ) : ℝ≥0∞) V₀ := by
    simpa using Lp.memLp g
  exact hg.integrable_norm_pow (by norm_num)

/-- **Quartic densities pass to the limit.**  If `f_h → f` strongly in `L⁴(K)` and the continuous
weights `ψ_h → ψ` uniformly on `K`, then `∫ ψ_h |f_h|⁴ → ∫ ψ |f|⁴`. -/
theorem tendsto_integral_mul_norm_pow_four {f : ℕ → Lp F 4 V₀} {f₀ : Lp F 4 V₀}
    (hf : Tendsto (fun n => ‖f n - f₀‖) atTop (𝓝 0)) {ψ : ℕ → C(K, ℝ)} {ψ₀ : C(K, ℝ)}
    (hψ : Tendsto ψ atTop (𝓝 ψ₀)) :
    Tendsto (fun n => ∫ x, ψ n x * ‖f n x‖ ^ 4 ∂V₀) atTop
      (𝓝 (∫ x, ψ₀ x * ‖f₀ x‖ ^ 4 ∂V₀)) := by
  have hI := tendsto_integral_abs_norm_pow_four_sub hf
  have hint : ∀ n, Integrable (fun x => ‖f n x‖ ^ 4) V₀ := fun n => integrable_norm_pow_four _
  have hint₀ : Integrable (fun x => ‖f₀ x‖ ^ 4) V₀ := integrable_norm_pow_four _
  have hψb : ∀ (g : C(K, ℝ)) x, ‖g x‖ ≤ ‖g‖ := fun g x => g.norm_coe_le_norm x
  have hsplit : ∀ n, ∫ x, ψ n x * ‖f n x‖ ^ 4 ∂V₀ - ∫ x, ψ₀ x * ‖f₀ x‖ ^ 4 ∂V₀ =
      ∫ x, (ψ n x * (‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4) + (ψ n x - ψ₀ x) * ‖f₀ x‖ ^ 4) ∂V₀ := fun n => by
    rw [← integral_sub ((hint n).bdd_mul (ψ n).continuous.aestronglyMeasurable
        (ae_of_all _ (hψb (ψ n))))
      (hint₀.bdd_mul ψ₀.continuous.aestronglyMeasurable (ae_of_all _ (hψb ψ₀)))]
    congr 1
    funext x
    ring
  have hbound : ∀ n, ‖∫ x, ψ n x * ‖f n x‖ ^ 4 ∂V₀ - ∫ x, ψ₀ x * ‖f₀ x‖ ^ 4 ∂V₀‖ ≤
      ‖ψ n‖ * ∫ x, ‖‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4‖ ∂V₀ + ‖ψ n - ψ₀‖ * ∫ x, ‖f₀ x‖ ^ 4 ∂V₀ :=
    fun n => by
      have hGint : Integrable (fun x => ‖‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4‖) V₀ :=
        ((hint n).sub hint₀).norm
      rw [hsplit n]
      refine (norm_integral_le_of_norm_le ((hGint.const_mul ‖ψ n‖).add
        (hint₀.const_mul ‖ψ n - ψ₀‖)) (ae_of_all _ fun x => ?_)).trans (le_of_eq ?_)
      · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hψb (ψ n) x) (norm_nonneg _)
        · rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖f₀ x‖ ^ 4)]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := hψb (ψ n - ψ₀) x
          simpa using this
      · simp only [Pi.add_apply]
        rw [integral_add (hGint.const_mul _) (hint₀.const_mul _), integral_const_mul,
          integral_const_mul]
  have hψn : Tendsto (fun n => ‖ψ n‖) atTop (𝓝 ‖ψ₀‖) := hψ.norm
  have hψd : Tendsto (fun n => ‖ψ n - ψ₀‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hψ
  have hmaj : Tendsto (fun n => ‖ψ n‖ * ∫ x, ‖‖f n x‖ ^ 4 - ‖f₀ x‖ ^ 4‖ ∂V₀ +
      ‖ψ n - ψ₀‖ * ∫ x, ‖f₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0) := by
    have := (hψn.mul hI).add (hψd.mul_const (∫ x, ‖f₀ x‖ ^ 4 ∂V₀))
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hmaj

variable {r : ℕ}

/-- Strong convergence is weak convergence in `L²(K; ℝ^r)`. -/
theorem weakTendsto_of_tendsto {Y : ℕ → Lp (EuclideanSpace ℝ (Fin r)) 2 V₀}
    {Y₀ : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀} (hY : Tendsto Y atTop (𝓝 Y₀)) :
    WeakTendsto Y Y₀ :=
  fun φ => (φ.continuous.tendsto Y₀).comp hY

/-- A strongly convergent packet has zero packet defect: `Y_h ⊗ Y_h dV₀ ⇀* Y ⊗ Y dV₀`. -/
theorem isPacketDefect_zero_of_tendsto {Y : ℕ → Lp (EuclideanSpace ℝ (Fin r)) 2 V₀}
    {Y₀ : Lp (EuclideanSpace ℝ (Fin r)) 2 V₀} (hY : Tendsto Y atTop (𝓝 Y₀)) :
    IsPacketDefect Y Y₀ 0 := by
  intro P
  rw [zero_apply, add_zero]
  have hmul : Tendsto (fun n => mulField (opField P) (Y n)) atTop
      (𝓝 (mulField (opField P) Y₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hd : Tendsto (fun n => ‖Y n - Y₀‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hY
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by simpa using hd.const_mul ‖opField P‖)
    rw [← mulField_sub_right]
    exact norm_mulField_le _ _
  simpa [quadCLM_apply] using hY.inner hmul

/-! ### The closing sentence of `prop:monotonicity` -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **`prop:monotonicity`** (complete).  Let `V ↪ L⁴(K; F)` (`ι₄`), and let the operators
`A_h : V → V'` satisfy `c₁‖u - v‖² + c₂‖u - v‖₄⁴ ≤ ⟨A_h u - A_h v, u - v⟩`, `c₁, c₂ > 0`.  If
`H_h ⇀ H` in `V`, `A_h(H_h) = J_h → J` and `A_h(H) → J` in `V'`, then `H_h → H` in `V ∩ L⁴`.
If moreover `V` controls the covariant `H¹` norm — the realified covariant gradients
`D_h : V →L L²(K; ℝ^r)` satisfy `‖D_h‖ ≤ C_D` and `D_h H → D H` — then both Higgs defects
vanish:

* `D_h H_h → D H` in `L²`, so the covariance (packet) defect `𝖰_Y` of
  `lem:positive-packet-defect` is zero, and every kinetic stress defect `𝔎` — defined by
  `B_h(Y_h, Y_h) dV₀ ⇀* B(Y, Y) dV₀ + 𝔎` for continuous coefficient fields `B_h → B`
  uniformly — is zero (`𝔎_H = 0`);
* the quartic defect `ν_H`, defined by `|H_h|⁴ ρ_h dV₀ ⇀* |H|⁴ ρ dV₀ + ν_H` for continuous
  volume densities `ρ_h → ρ` uniformly, is zero. -/
theorem monotone_higgs_defects_vanish
    (A : ℕ → V → StrongDual ℝ V) (ι₄ : V →L[ℝ] Lp F 4 V₀) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂)
    (hmono : ∀ n u v, c₁ * ‖u - v‖ ^ 2 + c₂ * ‖ι₄ (u - v)‖ ^ 4 ≤ (A n u - A n v) (u - v))
    (Hs : ℕ → V) (H : V) (J : StrongDual ℝ V)
    (hweak : ∀ φ : StrongDual ℝ V, Tendsto (fun n => φ (Hs n)) atTop (𝓝 (φ H)))
    (hJ : Tendsto (fun n => A n (Hs n)) atTop (𝓝 J))
    (hAH : Tendsto (fun n => A n H) atTop (𝓝 J))
    (D : ℕ → V →L[ℝ] Lp (EuclideanSpace ℝ (Fin r)) 2 V₀)
    (D₀ : V →L[ℝ] Lp (EuclideanSpace ℝ (Fin r)) 2 V₀) (C_D : ℝ) (hD : ∀ n, ‖D n‖ ≤ C_D)
    (hDH : Tendsto (fun n => D n H) atTop (𝓝 (D₀ H))) :
    Tendsto Hs atTop (𝓝 H) ∧
    Tendsto (fun n => ‖ι₄ (Hs n) - ι₄ H‖) atTop (𝓝 0) ∧
    Tendsto (fun n => ‖D n (Hs n) - D₀ H‖) atTop (𝓝 0) ∧
    (∀ Q : StrongDual ℝ C(K, Fin r → Fin r → ℝ),
      IsPacketDefect (fun n => D n (Hs n)) (D₀ H) Q → Q = 0) ∧
    (∀ (B : ℕ → C(K, Fin r → Fin r → ℝ)) (B₀ : C(K, Fin r → Fin r → ℝ)),
      Tendsto B atTop (𝓝 B₀) → ∀ 𝔎 : C(K, ℝ) → ℝ,
        (∀ φ : C(K, ℝ), Tendsto (fun n => quadCLM (D n (Hs n)) (smulField φ (B n))) atTop
          (𝓝 (quadCLM (D₀ H) (smulField φ B₀) + 𝔎 φ))) → 𝔎 = 0) ∧
    (∀ (ρ : ℕ → C(K, ℝ)) (ρ₀ : C(K, ℝ)), Tendsto ρ atTop (𝓝 ρ₀) → ∀ ν : C(K, ℝ) → ℝ,
      (∀ φ : C(K, ℝ), Tendsto (fun n => ∫ x, φ x * ρ n x * ‖ι₄ (Hs n) x‖ ^ 4 ∂V₀) atTop
        (𝓝 (∫ x, φ x * ρ₀ x * ‖ι₄ H x‖ ^ 4 ∂V₀ + ν φ))) → ν = 0) := by
  obtain ⟨hV, h4⟩ := MonotoneDefectRemoval.tendsto_of_monotone A (fun u => ‖ι₄ u‖)
    (fun _ => norm_nonneg _) c₁ c₂ hc₁ hc₂ hmono Hs H J hweak hJ hAH
  have h4' : Tendsto (fun n => ‖ι₄ (Hs n) - ι₄ H‖) atTop (𝓝 0) := by
    simpa [map_sub] using h4
  have hVd : Tendsto (fun n => ‖Hs n - H‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hV
  -- strong `L²` convergence of the covariant gradients
  have hY : Tendsto (fun n => ‖D n (Hs n) - D₀ H‖) atTop (𝓝 0) := by
    have hDHd : Tendsto (fun n => ‖D n H - D₀ H‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hDH
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by simpa using (hVd.const_mul C_D).add hDHd)
    calc ‖D n (Hs n) - D₀ H‖ = ‖D n (Hs n - H) + (D n H - D₀ H)‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ ‖D n (Hs n - H)‖ + ‖D n H - D₀ H‖ := norm_add_le _ _
      _ ≤ C_D * ‖Hs n - H‖ + ‖D n H - D₀ H‖ := by
          gcongr
          exact ((D n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hD n) (norm_nonneg _))
  have hYc : Tendsto (fun n => D n (Hs n)) atTop (𝓝 (D₀ H)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hY
  have hW := weakTendsto_of_tendsto hYc
  have hQ0 := isPacketDefect_zero_of_tendsto hYc
  refine ⟨hV, h4', hY, fun Q hQ => (eq_zero_iff_tendsto hW hQ).2 hY, ?_, ?_⟩
  · intro B B₀ hB 𝔎 h𝔎
    funext φ
    have h1 := tendsto_contraction hW hQ0 hB φ
    rw [zero_apply, add_zero] at h1
    have h2 := tendsto_nhds_unique (h𝔎 φ) h1
    simpa using h2
  · intro ρ ρ₀ hρ ν hν
    funext φ
    have hψ : Tendsto (fun n => φ * ρ n) atTop (𝓝 (φ * ρ₀)) := tendsto_const_nhds.mul hρ
    have h1 := tendsto_integral_mul_norm_pow_four (V₀ := V₀) h4' hψ
    simp only [ContinuousMap.mul_apply] at h1
    have h2 := tendsto_nhds_unique (hν φ) h1
    simpa using h2

/-- Non-vacuity: the hypothesis packet of `monotone_higgs_defects_vanish` is satisfiable
(`V = ℝ`, `A_h u = 2u`, `c₁ = c₂ = 1`, constant sequence, on the unit interval). -/
example : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := by
  have := monotone_higgs_defects_vanish (K := Set.Icc (0 : ℝ) 1) (V₀ := volume) (F := ℝ) (r := 1)
    (V := ℝ) (fun _ (u : ℝ) => (2 * u) • ContinuousLinearMap.id ℝ ℝ) 0 1 1 one_pos one_pos
    (fun n u v => by
      simp only [zero_apply, norm_zero, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (u - v)])
    (fun _ => (1 : ℝ)) 1 ((2 * (1 : ℝ)) • ContinuousLinearMap.id ℝ ℝ) (fun φ => tendsto_const_nhds)
    tendsto_const_nhds tendsto_const_nhds (fun _ => 0) 0 0 (fun _ => by simp) tendsto_const_nhds
  exact this.1

end RenewalGeometry.MonotoneHiggsDefect
