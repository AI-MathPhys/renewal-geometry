/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.PalatiniWedgeHolderExact
import RenewalGeometry.Continuum.StrongInterpolationConvergenceExact
import RenewalGeometry.Continuum.FiniteMeasureL2L6InterpolationExact

/-!
# Weak-curvature Palatini passage (`prop:weak-palatini`, Einstein–SM action closure)

The proposition is formalised on a finite measure space `(α, μ)` (the compact
four-dimensional region), with coframes `e_h, e : α → E`, a bounded bilinear
wedge/internal-dual map `w : E →L E →L Biv` (the map `e ↦ B(e) = w e e`), a
bounded pairing `pr : Biv →L Curv →L ℝ` (the Palatini or Holst contraction) and
curvatures `R_h, R : α → Curv`.  All norms are Mathlib's `eLpNorm`/`eLpNorm'`
(extended-real `L^p` seminorms); weak convergence `R_h ⇀ R` in `L^p` is rendered as
convergence of all pairings `∫ ⟨φ, R_h⟩ → ∫ ⟨φ, R⟩` against `L^{p'}` tests
together with the uniform bound `‖R_h‖_p ≤ C`.

Under the hypotheses `eq:Palatini-hypotheses` — `‖e_h - e‖₂ → 0`,
`‖e_h‖₆, ‖e‖₆ ≤ M`, `‖R_h‖_p ≤ C`, `R_h ⇀ R`, `p > 3/2` — we prove

* `B(e_h) → B(e)` in `L^{p'}`, `p' = p/(p-1)` (`eLpNorm'_wedge_tendsto_zero`), via the
  Hölder/interpolation estimate of `PalatiniWedgeHolderExact` and the finite-measure
  bound `‖·‖_{2p'} ≤ ‖·‖₆ μ(α)^{1/(2p') - 1/6}`;
* the Palatini pairings converge, `∫ pr (B(e_h)) R_h → ∫ pr (B(e)) R`
  (`integral_pairing_tendsto`, `palatini_pairing_tendsto`): the pairing is split as
  `∫ pr (B_h - B) R_h + ∫ pr B R_h`, the first term is bounded by
  `‖pr‖ ‖B_h - B‖_{p'} ‖R_h‖_p` (Hölder), the second converges by weak convergence
  tested against `B ∈ L^{p'}`;
* the volume densities converge in `L¹`: for every bounded four-linear `vol`,
  `‖vol(e_h,e_h,e_h,e_h) - vol(e,e,e,e)‖₁ → 0` (`eLpNorm_fourLinear_tendsto_zero`), by a
  four-factor telescoping estimate in `L⁴` and `L²`–`L⁶` interpolation at `q = 4`;
* the coframe-variation clause: for variations `k_h → k` in `L²` with `L⁶` bounds,
  `‖w e_h k_h - w e k‖_{p'} → 0` (`eLpNorm'_wedge_variation_tendsto_zero`), hence the
  first-variation pairings converge as well (`palatini_variation_pairing_tendsto`).

The hypothesis identifying `R` with the curvature of the limiting connection and the
connection-Euler caveat of the last sentence are hypotheses/remarks of the proposition,
not conclusions, and carry no formal content here.  The bundled statement is
`weak_palatini_passage`.
-/

open MeasureTheory ENNReal Filter Topology

namespace RenewalGeometry.WeakPalatiniPassage

variable {α E Biv Curv : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Biv] [NormedSpace ℝ Biv]
  [NormedAddCommGroup Curv] [NormedSpace ℝ Curv]

/-! ### Exponent bookkeeping -/

/-- The Hölder conjugate pair `(p', p)`, `p' = p/(p-1)`, as an `ℝ≥0∞` Hölder triple with
`r = 1`. -/
theorem holderConjugate_ofReal (p : ℝ) (hp : 1 < p) :
    HolderTriple (ENNReal.ofReal (p / (p - 1))) (ENNReal.ofReal p) 1 := by
  refine ⟨?_⟩
  have hden : 0 < p - 1 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp0,
    ← ENNReal.ofReal_add (by positivity) (by positivity), inv_one, ← ENNReal.ofReal_one]
  congr 1
  field_simp
  ring

theorem toReal_ofReal_conj (p : ℝ) (hp : 1 < p) :
    (ENNReal.ofReal (p / (p - 1))).toReal = p / (p - 1) :=
  ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))

theorem ofReal_conj_ne_zero (p : ℝ) (hp : 1 < p) : ENNReal.ofReal (p / (p - 1)) ≠ 0 := by
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  exact div_pos (by linarith) (by linarith)

/-- `eLpNorm` at the conjugate exponent is the real-exponent `eLpNorm'`. -/
theorem eLpNorm_conj_eq (f : α → Biv) (p : ℝ) (hp : 1 < p) :
    eLpNorm f (ENNReal.ofReal (p / (p - 1))) μ = eLpNorm' f (p / (p - 1)) μ := by
  rw [eLpNorm_eq_eLpNorm' (ofReal_conj_ne_zero p hp) ENNReal.ofReal_ne_top,
    toReal_ofReal_conj p hp]

/-- Finite-measure bound `‖f‖_{2p'} ≤ ‖f‖₆ · μ(α)^{1/(2p') - 1/6}` for `p > 3/2`. -/
theorem eLpNorm'_twoConj_le (f : α → E) (hf : AEStronglyMeasurable f μ) (p : ℝ)
    (hp : 3 / 2 < p) :
    eLpNorm' f (2 * p / (p - 1)) μ ≤
      eLpNorm' f 6 μ * μ Set.univ ^ (1 / (2 * p / (p - 1)) - 1 / 6) :=
  eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (div_pos (by linarith) (by linarith))
    (StrongInterpolationConvergence.palatini_conjugate_exponent_range p hp).2.le hf

/-! ### Strong `L^{p'}` convergence of the coframe bivector -/

/-- **`prop:weak-palatini`, first conclusion.**  If `e_h → e` in `L²` with `‖e_h‖₆, ‖e‖₆ ≤ M`
on a finite measure space and `p > 3/2`, then `B(e_h) = w e_h e_h → B(e)` in `L^{p'}`. -/
theorem eLpNorm'_wedge_tendsto_zero {ι : Type*} {l : Filter ι} [IsFiniteMeasure μ]
    (w : E →L[ℝ] E →L[ℝ] Biv) (e : ι → α → E) (e₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0))
    (p : ℝ) (hp : 3 / 2 < p) :
    Tendsto (fun i => eLpNorm' (fun x => w (e i x) (e i x) - w (e₀ x) (e₀ x)) (p / (p - 1)) μ)
      l (𝓝 0) := by
  have hp1 : 1 < p := by linarith
  have hden : 0 < p - 1 := sub_pos.mpr hp1
  obtain ⟨hq2, hq6⟩ := StrongInterpolationConvergence.palatini_conjugate_exponent_range p hp
  have hθpos : 0 < (2 * p - 3) / (2 * p) := div_pos (by linarith) (by linarith)
  have hVne : μ Set.univ ^ (1 / (2 * p / (p - 1)) - 1 / 6) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (div_pos (by linarith) (by linarith)) hq6.le)
      (measure_ne_top μ _)
  set V : ℝ≥0∞ := μ Set.univ ^ (1 / (2 * p / (p - 1)) - 1 / 6) with hV
  have hbq : ∀ i, eLpNorm' (e i) (2 * p / (p - 1)) μ ≤ M * V := fun i =>
    (eLpNorm'_twoConj_le (e i) (he i) p hp).trans (by gcongr; exact h6 i)
  have hbq₀ : eLpNorm' e₀ (2 * p / (p - 1)) μ ≤ M * V :=
    (eLpNorm'_twoConj_le e₀ he₀ p hp).trans (by gcongr)
  have hdiff6 : ∀ i, eLpNorm' (e i - e₀) 6 μ ≤ M + M := fun i => by
    have := eLpNorm'_add_le (he i) he₀.neg (by norm_num : (1 : ℝ) ≤ 6)
    rw [eLpNorm'_neg] at this
    rw [sub_eq_add_neg]
    exact this.trans (add_le_add (h6 i) h6₀)
  have h32 : (0 : ℝ) ≤ 3 / (2 * p) := div_nonneg (by norm_num) (by linarith)
  set D : ℝ≥0∞ := ‖w‖₊ * (M + M) ^ (3 / (2 * p)) * (M * V + M * V) with hD
  have hDne : D ≠ ∞ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg h32 (ENNReal.add_ne_top.mpr ⟨hM, hM⟩))) ?_
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hM hVne, ENNReal.mul_ne_top hM hVne⟩
  have hest : ∀ i, eLpNorm' (fun x => w (e i x) (e i x) - w (e₀ x) (e₀ x)) (p / (p - 1)) μ ≤
      D * (eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p)) := fun i => by
    have h := PalatiniWedgeHolder.eLpNorm_wedge_sub_le_interpolation w (e i) e₀ (he i) he₀ p hp
    refine h.trans ?_
    calc (‖w‖₊ : ℝ≥0∞) * ((eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p)) *
            (eLpNorm' (e i - e₀) 6 μ) ^ (3 / (2 * p))) *
          (eLpNorm' (e i) (2 * p / (p - 1)) μ + eLpNorm' e₀ (2 * p / (p - 1)) μ)
        ≤ (‖w‖₊ : ℝ≥0∞) * ((eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p)) *
            (M + M) ^ (3 / (2 * p))) * (M * V + M * V) := by
          gcongr <;> first | exact hdiff6 i | exact hbq i | exact hbq₀
      _ = D * (eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p)) := by
          rw [hD]; ring
  have hpow : Tendsto (fun i => (eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p))) l (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (2 * p - 3) / (2 * p))).tendsto 0).comp h2
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hθpos] using this
  have hmajor : Tendsto (fun i => D * (eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p))) l
      (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hpow (Or.inr hDne)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun _ => zero_le) hest

/-! ### The weak–strong pairing passage -/

/-- Hölder bound for a bounded pairing: `‖pr φ ψ‖₁ ≤ ‖pr‖ ‖φ‖_{p'} ‖ψ‖_p`. -/
theorem eLpNorm_pairing_le (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ) (hp : 1 < p)
    (φ : α → Biv) (ψ : α → Curv) (hφ : AEStronglyMeasurable φ μ)
    (hψ : AEStronglyMeasurable ψ μ) :
    eLpNorm (fun x => pr (φ x) (ψ x)) 1 μ ≤
      ‖pr‖₊ * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) μ * eLpNorm ψ (ENNReal.ofReal p) μ := by
  haveI := holderConjugate_ofReal p hp
  exact eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hφ hψ (fun x y => pr x y) ‖pr‖₊
    (Eventually.of_forall fun x => by simpa [mul_assoc] using pr.le_opNorm₂ (φ x) (ψ x))

/-- An `L^{p'}` bivector paired with an `L^p` curvature is integrable. -/
theorem integrable_pairing (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ) (hp : 1 < p)
    (φ : α → Biv) (ψ : α → Curv) (hφ : MemLp φ (ENNReal.ofReal (p / (p - 1))) μ)
    (hψ : MemLp ψ (ENNReal.ofReal p) μ) :
    Integrable (fun x => pr (φ x) (ψ x)) μ := by
  rw [← memLp_one_iff_integrable]
  refine ⟨pr.aestronglyMeasurable_comp₂ hφ.1 hψ.1, ?_⟩
  calc eLpNorm (fun x => pr (φ x) (ψ x)) 1 μ
      ≤ ‖pr‖₊ * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) μ * eLpNorm ψ (ENNReal.ofReal p) μ :=
        eLpNorm_pairing_le pr p hp φ ψ hφ.1 hψ.1
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hφ.2) hψ.2

/-- **`prop:weak-palatini`, pairing passage.**  If `B_h → B` in `L^{p'}`, `‖R_h‖_p ≤ C` and
`R_h ⇀ R` (all pairings against `L^{p'}` tests converge), then
`∫ pr B_h R_h → ∫ pr B R`. -/
theorem integral_pairing_tendsto {ι : Type*} {l : Filter ι}
    (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ) (hp : 1 < p)
    (B : ι → α → Biv) (B₀ : α → Biv)
    (hB : ∀ i, MemLp (B i) (ENNReal.ofReal (p / (p - 1))) μ)
    (hB₀ : MemLp B₀ (ENNReal.ofReal (p / (p - 1))) μ)
    (hBconv : Tendsto (fun i => eLpNorm (B i - B₀) (ENNReal.ofReal (p / (p - 1))) μ) l (𝓝 0))
    (R : ι → α → Curv) (R₀ : α → Curv) (hR : ∀ i, AEStronglyMeasurable (R i) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hRb : ∀ i, eLpNorm (R i) (ENNReal.ofReal p) μ ≤ C)
    (hweak : ∀ φ : α → Biv, MemLp φ (ENNReal.ofReal (p / (p - 1))) μ →
      Tendsto (fun i => ∫ x, pr (φ x) (R i x) ∂μ) l (𝓝 (∫ x, pr (φ x) (R₀ x) ∂μ))) :
    Tendsto (fun i => ∫ x, pr (B i x) (R i x) ∂μ) l (𝓝 (∫ x, pr (B₀ x) (R₀ x) ∂μ)) := by
  have hRmem : ∀ i, MemLp (R i) (ENNReal.ofReal p) μ := fun i =>
    ⟨hR i, (hRb i).trans_lt hC.lt_top⟩
  have hdecomp : ∀ i, ∫ x, pr (B i x) (R i x) ∂μ =
      (∫ x, pr (B i x - B₀ x) (R i x) ∂μ) + ∫ x, pr (B₀ x) (R i x) ∂μ := fun i => by
    have hadd := integral_add
      (integrable_pairing pr p hp (B i - B₀) (R i) ((hB i).sub hB₀) (hRmem i))
      (integrable_pairing pr p hp B₀ (R i) hB₀ (hRmem i))
    simp only [Pi.sub_apply] at hadd
    rw [← hadd]
    congr 1
    funext x
    simp [map_sub]
  have hfirst : Tendsto (fun i => ∫ x, pr (B i x - B₀ x) (R i x) ∂μ) l (𝓝 0) := by
    have hbd : ∀ i, ‖∫ x, pr (B i x - B₀ x) (R i x) ∂μ‖ ≤
        (‖pr‖₊ * eLpNorm (B i - B₀) (ENNReal.ofReal (p / (p - 1))) μ * C).toReal := fun i => by
      have hmeas : AEStronglyMeasurable (fun x => pr (B i x - B₀ x) (R i x)) μ :=
        pr.aestronglyMeasurable_comp₂ ((hB i).sub hB₀).1 (hR i)
      calc ‖∫ x, pr (B i x - B₀ x) (R i x) ∂μ‖
          ≤ ∫ x, ‖pr (B i x - B₀ x) (R i x)‖ ∂μ := norm_integral_le_integral_norm _
        _ = (eLpNorm (fun x => pr (B i x - B₀ x) (R i x)) 1 μ).toReal := by
            rw [integral_norm_eq_lintegral_enorm hmeas, ← eLpNorm_one_eq_lintegral_enorm]
        _ ≤ (‖pr‖₊ * eLpNorm (B i - B₀) (ENNReal.ofReal (p / (p - 1))) μ * C).toReal := by
            apply ENNReal.toReal_mono
              (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ((hB i).sub hB₀).2.ne) hC)
            calc eLpNorm (fun x => pr (B i x - B₀ x) (R i x)) 1 μ
                ≤ ‖pr‖₊ * eLpNorm (B i - B₀) (ENNReal.ofReal (p / (p - 1))) μ *
                  eLpNorm (R i) (ENNReal.ofReal p) μ :=
                  eLpNorm_pairing_le pr p hp (B i - B₀) (R i) ((hB i).sub hB₀).1 (hR i)
              _ ≤ ‖pr‖₊ * eLpNorm (B i - B₀) (ENNReal.ofReal (p / (p - 1))) μ * C := by
                  gcongr
                  exact hRb i
    have hlim : Tendsto
        (fun i => (‖pr‖₊ * eLpNorm (B i - B₀) (ENNReal.ofReal (p / (p - 1))) μ * C).toReal) l
        (𝓝 0) := by
      have h1 : Tendsto (fun i => ‖pr‖₊ * eLpNorm (B i - B₀) (ENNReal.ofReal (p / (p - 1))) μ * C)
          l (𝓝 0) := by
        have h0 : Tendsto (fun i => (‖pr‖₊ : ℝ≥0∞) *
            eLpNorm (B i - B₀) (ENNReal.ofReal (p / (p - 1))) μ) l (𝓝 ((‖pr‖₊ : ℝ≥0∞) * 0)) :=
          ENNReal.Tendsto.const_mul hBconv (Or.inr ENNReal.coe_ne_top)
        have := ENNReal.Tendsto.mul_const h0 (Or.inr hC)
        simpa using this
      have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h1
      simpa [Function.comp_def] using this
    exact squeeze_zero_norm hbd hlim
  have hsum := hfirst.add (hweak B₀ hB₀)
  rw [zero_add] at hsum
  exact hsum.congr fun i => (hdecomp i).symm

/-- `B(e) = w e e` lies in `L^{p'}` when `e ∈ L⁶` on a finite measure space, `p > 3/2`. -/
theorem memLp_wedge (w : E →L[ℝ] E →L[ℝ] Biv) [IsFiniteMeasure μ] (e : α → E)
    (he : AEStronglyMeasurable e μ) (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : eLpNorm' e 6 μ ≤ M)
    (p : ℝ) (hp : 3 / 2 < p) :
    MemLp (fun x => w (e x) (e x)) (ENNReal.ofReal (p / (p - 1))) μ := by
  have hp1 : 1 < p := by linarith
  have hden : 0 < p - 1 := sub_pos.mpr hp1
  refine ⟨w.aestronglyMeasurable_comp₂ he he, ?_⟩
  set r : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hr
  have hr1 : 1 ≤ r := by
    rw [hr, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hden).2 (by linarith))
  have hr0 : r ≠ 0 := ofReal_conj_ne_zero p hp1
  have hrtop : r ≠ ∞ := ENNReal.ofReal_ne_top
  haveI : HolderTriple (2 * r) (2 * r) r := PalatiniWedgeHolder.holderTriple_two_mul r hrtop
  have h2r : 2 * r = ENNReal.ofReal (2 * p / (p - 1)) := by
    rw [hr, mul_div_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hbound : eLpNorm (fun x => w (e x) (e x)) r μ ≤ ‖w‖₊ * eLpNorm e (2 * r) μ *
      eLpNorm e (2 * r) μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm he he (fun x y => w x y) ‖w‖₊
      (Eventually.of_forall fun x => by simpa [mul_assoc] using w.le_opNorm₂ (e x) (e x))
  have hfin : eLpNorm e (2 * r) μ < ∞ := by
    rw [h2r, eLpNorm_eq_eLpNorm' (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact div_pos (by linarith) hden)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (div_nonneg (by linarith) hden.le)]
    refine (eLpNorm'_twoConj_le e he p hp).trans_lt ?_
    exact ENNReal.mul_lt_top (h6.trans_lt hM.lt_top) (ENNReal.rpow_lt_top_of_nonneg (by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (div_pos (by linarith) hden)
        (StrongInterpolationConvergence.palatini_conjugate_exponent_range p hp).2.le)
      (measure_ne_top μ _))
  exact hbound.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin) hfin)

/-- **`prop:weak-palatini`, main conclusions.**  Under `eq:Palatini-hypotheses` on a finite
measure space (`e_h → e` in `L²`, `‖e_h‖₆, ‖e‖₆ ≤ M`, `‖R_h‖_p ≤ C`, `R_h ⇀ R` in `L^p`,
`p > 3/2`): `B(e_h) → B(e)` in `L^{p'}` and the Palatini pairing converges. -/
theorem palatini_pairing_tendsto {ι : Type*} {l : Filter ι} [IsFiniteMeasure μ]
    (w : E →L[ℝ] E →L[ℝ] Biv) (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ) (hp : 3 / 2 < p)
    (e : ι → α → E) (e₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0))
    (R : ι → α → Curv) (R₀ : α → Curv) (hR : ∀ i, AEStronglyMeasurable (R i) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hRb : ∀ i, eLpNorm (R i) (ENNReal.ofReal p) μ ≤ C)
    (hweak : ∀ φ : α → Biv, MemLp φ (ENNReal.ofReal (p / (p - 1))) μ →
      Tendsto (fun i => ∫ x, pr (φ x) (R i x) ∂μ) l (𝓝 (∫ x, pr (φ x) (R₀ x) ∂μ))) :
    Tendsto (fun i => eLpNorm (fun x => w (e i x) (e i x) - w (e₀ x) (e₀ x))
        (ENNReal.ofReal (p / (p - 1))) μ) l (𝓝 0) ∧
    Tendsto (fun i => ∫ x, pr (w (e i x) (e i x)) (R i x) ∂μ) l
      (𝓝 (∫ x, pr (w (e₀ x) (e₀ x)) (R₀ x) ∂μ)) := by
  have hp1 : 1 < p := by linarith
  have hBconv : Tendsto (fun i => eLpNorm (fun x => w (e i x) (e i x) - w (e₀ x) (e₀ x))
      (ENNReal.ofReal (p / (p - 1))) μ) l (𝓝 0) := by
    simp only [eLpNorm_conj_eq _ p hp1]
    exact eLpNorm'_wedge_tendsto_zero w e e₀ he he₀ M hM h6 h6₀ h2 p hp
  refine ⟨hBconv, ?_⟩
  exact integral_pairing_tendsto pr p hp1 (fun i x => w (e i x) (e i x)) (fun x => w (e₀ x) (e₀ x))
    (fun i => memLp_wedge w (e i) (he i) M hM (h6 i) p hp) (memLp_wedge w e₀ he₀ M hM h6₀ p hp)
    hBconv R R₀ hR C hC hRb hweak


/-! ### Volume densities: four-linear products in `L¹` -/

/-- Real-exponent Hölder triples as `ℝ≥0∞` triples. -/
theorem holderTriple_ofReal (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a⁻¹ + b⁻¹ = c⁻¹) :
    HolderTriple (ENNReal.ofReal a) (ENNReal.ofReal b) (ENNReal.ofReal c) := by
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos ha, ← ENNReal.ofReal_inv_of_pos hb,
    ← ENNReal.ofReal_add (by positivity) (by positivity), h, ENNReal.ofReal_inv_of_pos hc]

theorem eLpNorm_ofReal_eq {F : Type*} [NormedAddCommGroup F] (f : α → F) (q : ℝ) (hq : 0 < q) :
    eLpNorm f (ENNReal.ofReal q) μ = eLpNorm' f q μ := by
  rw [eLpNorm_eq_eLpNorm' (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]

/-- Four-factor Hölder estimate: if `‖F x‖ ≤ c ‖u₁ x‖ ‖u₂ x‖ ‖u₃ x‖ ‖u₄ x‖` then
`‖F‖₁ ≤ c ‖u₁‖₄ ‖u₂‖₄ ‖u₃‖₄ ‖u₄‖₄`. -/
theorem eLpNorm_fourFactor_le {G E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup G]
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
    [NormedAddCommGroup E₄] (F : α → G)
    (u₁ : α → E₁) (u₂ : α → E₂) (u₃ : α → E₃) (u₄ : α → E₄)
    (h₁ : AEStronglyMeasurable u₁ μ) (h₂ : AEStronglyMeasurable u₂ μ)
    (h₃ : AEStronglyMeasurable u₃ μ) (h₄ : AEStronglyMeasurable u₄ μ) (c : NNReal)
    (hc : ∀ x, ‖F x‖ ≤ c * ‖u₁ x‖ * ‖u₂ x‖ * ‖u₃ x‖ * ‖u₄ x‖) :
    eLpNorm F 1 μ ≤
      c * eLpNorm' u₁ 4 μ * eLpNorm' u₂ 4 μ * eLpNorm' u₃ 4 μ * eLpNorm' u₄ 4 μ := by
  haveI hT1 : HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal (4 / 3)) 1 :=
    ENNReal.ofReal_one ▸ holderTriple_ofReal 4 (4 / 3) 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  haveI hT2 : HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal 2) (ENNReal.ofReal (4 / 3)) :=
    holderTriple_ofReal 4 2 (4 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  haveI hT3 : HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal 4) (ENNReal.ofReal 2) :=
    holderTriple_ofReal 4 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set g₃₄ : α → ℝ := fun x => ‖u₃ x‖ * ‖u₄ x‖ with hg₃₄
  set g₂₃₄ : α → ℝ := fun x => ‖u₂ x‖ * g₃₄ x with hg₂₃₄
  have hm₃₄ : AEStronglyMeasurable g₃₄ μ := h₃.norm.mul h₄.norm
  have hm₂₃₄ : AEStronglyMeasurable g₂₃₄ μ := h₂.norm.mul hm₃₄
  have hb₃₄ : eLpNorm g₃₄ (ENNReal.ofReal 2) μ ≤
      (1 : NNReal) * eLpNorm u₃ (ENNReal.ofReal 4) μ * eLpNorm u₄ (ENNReal.ofReal 4) μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm h₃ h₄ (fun a b => ‖a‖ * ‖b‖) 1
      (Eventually.of_forall fun x => by simp [abs_mul])
  have hb₂₃₄ : eLpNorm g₂₃₄ (ENNReal.ofReal (4 / 3)) μ ≤
      (1 : NNReal) * eLpNorm u₂ (ENNReal.ofReal 4) μ * eLpNorm g₃₄ (ENNReal.ofReal 2) μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm h₂ hm₃₄ (fun (a : E₂) (t : ℝ) => ‖a‖ * t) 1
      (Eventually.of_forall fun x => by simp [abs_mul])
  have hF : eLpNorm F 1 μ ≤ eLpNorm (fun x => (c : ℝ) * ‖u₁ x‖ * g₂₃₄ x) 1 μ :=
    eLpNorm_mono_real fun x => (hc x).trans (le_of_eq (by
      show (c : ℝ) * ‖u₁ x‖ * ‖u₂ x‖ * ‖u₃ x‖ * ‖u₄ x‖ =
        (c : ℝ) * ‖u₁ x‖ * (‖u₂ x‖ * (‖u₃ x‖ * ‖u₄ x‖))
      ring))
  have hb₁ : eLpNorm (fun x => (c : ℝ) * ‖u₁ x‖ * g₂₃₄ x) 1 μ ≤
      c * eLpNorm u₁ (ENNReal.ofReal 4) μ * eLpNorm g₂₃₄ (ENNReal.ofReal (4 / 3)) μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm h₁ hm₂₃₄ (fun (a : E₁) (t : ℝ) => (c : ℝ) * ‖a‖ * t) c
      (Eventually.of_forall fun x => by simp [abs_mul, mul_assoc, NNReal.abs_eq])
  simp only [ENNReal.coe_one, one_mul] at hb₃₄ hb₂₃₄
  rw [eLpNorm_ofReal_eq u₁ 4 (by norm_num)] at hb₁
  rw [eLpNorm_ofReal_eq u₂ 4 (by norm_num)] at hb₂₃₄
  rw [eLpNorm_ofReal_eq u₃ 4 (by norm_num), eLpNorm_ofReal_eq u₄ 4 (by norm_num)] at hb₃₄
  calc eLpNorm F 1 μ ≤ eLpNorm (fun x => (c : ℝ) * ‖u₁ x‖ * g₂₃₄ x) 1 μ := hF
    _ ≤ c * eLpNorm' u₁ 4 μ * eLpNorm g₂₃₄ (ENNReal.ofReal (4 / 3)) μ := hb₁
    _ ≤ c * eLpNorm' u₁ 4 μ * (eLpNorm' u₂ 4 μ * eLpNorm g₃₄ (ENNReal.ofReal 2) μ) := by
        gcongr
    _ ≤ c * eLpNorm' u₁ 4 μ * (eLpNorm' u₂ 4 μ * (eLpNorm' u₃ 4 μ * eLpNorm' u₄ 4 μ)) := by
        gcongr
    _ = c * eLpNorm' u₁ 4 μ * eLpNorm' u₂ 4 μ * eLpNorm' u₃ 4 μ * eLpNorm' u₄ 4 μ := by ring

/-- Finite-measure bound `‖f‖₄ ≤ ‖f‖₆ · μ(α)^{1/4 - 1/6}`. -/
theorem eLpNorm'_four_le (f : α → E) (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f 4 μ ≤ eLpNorm' f 6 μ * μ Set.univ ^ (1 / (4 : ℝ) - 1 / 6) :=
  eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (by norm_num) (by norm_num) hf

/-- `L⁴` convergence from `L²` convergence and `L⁶` bounds (interpolation at `q = 4`). -/
theorem eLpNorm'_four_tendsto_zero {ι : Type*} {l : Filter ι}
    (e : ι → α → E) (e₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm' (e i - e₀) 4 μ) l (𝓝 0) := by
  have hdiff6 : ∀ i, eLpNorm' (e i - e₀) 6 μ ≤ M + M := fun i => by
    have := eLpNorm'_add_le (he i) he₀.neg (by norm_num : (1 : ℝ) ≤ 6)
    rw [eLpNorm'_neg] at this
    rw [sub_eq_add_neg]
    exact this.trans (add_le_add (h6 i) h6₀)
  have hest : ∀ i, eLpNorm' (e i - e₀) 4 μ ≤
      (M + M) ^ ((3 : ℝ) * (4 - 2) / (2 * 4)) * (eLpNorm' (e i - e₀) 2 μ) ^ ((6 - 4) / (2 * 4) : ℝ) :=
    fun i => by
      have h := FiniteMeasureL2L6Interpolation.eLpNorm'_interpolate_two_six (e i - e₀)
        ((he i).sub he₀) 4 (by norm_num) (by norm_num)
      refine h.trans ?_
      rw [mul_comm]
      gcongr
      exact hdiff6 i
  have hpow : Tendsto (fun i => (eLpNorm' (e i - e₀) 2 μ) ^ ((6 - 4) / (2 * 4) : ℝ)) l (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := ((6 - 4) / (2 * 4) : ℝ))).tendsto 0).comp h2
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (6 - 4) / (2 * 4))]
      using this
  have hDne : (M + M) ^ ((3 : ℝ) * (4 - 2) / (2 * 4)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.add_ne_top.mpr ⟨hM, hM⟩)
  have hmajor : Tendsto (fun i => (M + M) ^ ((3 : ℝ) * (4 - 2) / (2 * 4)) *
      (eLpNorm' (e i - e₀) 2 μ) ^ ((6 - 4) / (2 * 4) : ℝ)) l (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hpow (Or.inr hDne)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor (fun _ => zero_le) hest

/-- Pointwise telescoping estimate for a bounded four-linear map on the diagonal:
`‖vol(a,a,a,a) - vol(b,b,b,b)‖ ≤ 4 ‖vol‖ ‖a - b‖ (‖a‖ + ‖b‖)³`. -/
theorem norm_fourLinear_diag_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V) (a b : E) :
    ‖vol (fun _ => a) - vol (fun _ => b)‖ ≤
      (4 * ‖vol‖) * ‖a - b‖ * (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) := by
  have h := vol.norm_image_sub_le (fun _ => a) (fun _ => b)
  have hsub : (fun _ : Fin 4 => a) - (fun _ => b) = fun _ => a - b := by
    funext i
    simp
  rw [hsub, pi_norm_const a, pi_norm_const b, pi_norm_const (a - b)] at h
  simp only [Fintype.card_fin, Nat.cast_ofNat, Nat.add_one_sub_one] at h
  refine h.trans ?_
  have hmax : max ‖a‖ ‖b‖ ≤ ‖a‖ + ‖b‖ := max_le (by linarith [norm_nonneg b]) (by
    linarith [norm_nonneg a])
  have h0 : 0 ≤ max ‖a‖ ‖b‖ := le_max_of_le_left (norm_nonneg a)
  calc ‖vol‖ * 4 * max ‖a‖ ‖b‖ ^ 3 * ‖a - b‖
      ≤ ‖vol‖ * 4 * (‖a‖ + ‖b‖) ^ 3 * ‖a - b‖ := by gcongr
    _ = (4 * ‖vol‖) * ‖a - b‖ * (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) := by ring

/-- **`prop:weak-palatini`, volume clause.**  For a bounded four-linear map `vol` (the
four-coframe volume product `v(e) dV`), `vol(e_h,e_h,e_h,e_h) → vol(e,e,e,e)` in `L¹`. -/
theorem eLpNorm_fourLinear_tendsto_zero {ι : Type*} {l : Filter ι} [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V) (e : ι → α → E) (e₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => vol (fun _ => e i x) - vol (fun _ => e₀ x)) 1 μ) l
      (𝓝 0) := by
  set V₄ : ℝ≥0∞ := μ Set.univ ^ (1 / (4 : ℝ) - 1 / 6) with hV₄
  have hV₄ne : V₄ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ _)
  have hb4 : ∀ i, eLpNorm' (e i) 4 μ ≤ M * V₄ := fun i =>
    (eLpNorm'_four_le (e i) (he i)).trans (by gcongr; exact h6 i)
  have hb4₀ : eLpNorm' e₀ 4 μ ≤ M * V₄ := (eLpNorm'_four_le e₀ he₀).trans (by gcongr)
  have hd : ∀ i, AEStronglyMeasurable (e i - e₀) μ := fun i => (he i).sub he₀
  set g : ι → α → ℝ := fun i x => ‖e i x‖ + ‖e₀ x‖ with hg
  have hgm : ∀ i, AEStronglyMeasurable (g i) μ := fun i => (he i).norm.add he₀.norm
  have hg4 : ∀ i, eLpNorm' (g i) 4 μ ≤ M * V₄ + M * V₄ := fun i => by
    have := eLpNorm'_add_le (he i).norm he₀.norm (by norm_num : (1 : ℝ) ≤ 4)
    rw [eLpNorm'_norm, eLpNorm'_norm] at this
    exact this.trans (add_le_add (hb4 i) hb4₀)
  set D : ℝ≥0∞ := (4 * ‖vol‖₊ : NNReal) * (M * V₄ + M * V₄) * (M * V₄ + M * V₄) *
    (M * V₄ + M * V₄) with hD
  have hDne : D ≠ ∞ := by
    have h1 : M * V₄ + M * V₄ ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hM hV₄ne, ENNReal.mul_ne_top hM hV₄ne⟩
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h1) h1) h1
  have hest : ∀ i, eLpNorm (fun x => vol (fun _ => e i x) - vol (fun _ => e₀ x)) 1 μ ≤
      D * eLpNorm' (e i - e₀) 4 μ := fun i => by
    have h := eLpNorm_fourFactor_le (fun x => vol (fun _ => e i x) - vol (fun _ => e₀ x))
      (e i - e₀) (g i) (g i) (g i) (hd i) (hgm i) (hgm i) (hgm i) (4 * ‖vol‖₊)
      (fun x => by
        have := norm_fourLinear_diag_sub_le vol (e i x) (e₀ x)
        have hg0 : 0 ≤ ‖e i x‖ + ‖e₀ x‖ := by positivity
        simp only [hg, Pi.sub_apply, Real.norm_of_nonneg hg0, NNReal.coe_mul, NNReal.coe_ofNat,
          coe_nnnorm]
        exact this)
    refine h.trans ?_
    calc ((4 * ‖vol‖₊ : NNReal) : ℝ≥0∞) * eLpNorm' (e i - e₀) 4 μ * eLpNorm' (g i) 4 μ *
          eLpNorm' (g i) 4 μ * eLpNorm' (g i) 4 μ
        ≤ ((4 * ‖vol‖₊ : NNReal) : ℝ≥0∞) * eLpNorm' (e i - e₀) 4 μ * (M * V₄ + M * V₄) *
          (M * V₄ + M * V₄) * (M * V₄ + M * V₄) := by
          gcongr <;> exact hg4 i
      _ = D * eLpNorm' (e i - e₀) 4 μ := by rw [hD]; ring
  have h4 := eLpNorm'_four_tendsto_zero e e₀ he he₀ M hM h6 h6₀ h2
  have hmajor : Tendsto (fun i => D * eLpNorm' (e i - e₀) 4 μ) l (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul h4 (Or.inr hDne)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor (fun _ => zero_le) hest

/-! ### The coframe-variation clause -/

/-- Mixed Hölder bound `‖w f g‖_{p'} ≤ ‖w‖ ‖f‖_{2p'} ‖g‖_{2p'}` for `p > 1`. -/
theorem eLpNorm'_wedge_mixed_le (w : E →L[ℝ] E →L[ℝ] Biv) (f g : α → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (p : ℝ) (hp : 1 < p) :
    eLpNorm' (fun x => w (f x) (g x)) (p / (p - 1)) μ ≤
      ‖w‖₊ * eLpNorm' f (2 * p / (p - 1)) μ * eLpNorm' g (2 * p / (p - 1)) μ := by
  have hden : 0 < p - 1 := sub_pos.mpr hp
  set r : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hr
  have hr0 : r ≠ 0 := ofReal_conj_ne_zero p hp
  have hrtop : r ≠ ∞ := ENNReal.ofReal_ne_top
  haveI : HolderTriple (2 * r) (2 * r) r := PalatiniWedgeHolder.holderTriple_two_mul r hrtop
  have h2r : 2 * r = ENNReal.ofReal (2 * p / (p - 1)) := by
    rw [hr, mul_div_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hbound : eLpNorm (fun x => w (f x) (g x)) r μ ≤ ‖w‖₊ * eLpNorm f (2 * r) μ *
      eLpNorm g (2 * r) μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hf hg (fun x y => w x y) ‖w‖₊
      (Eventually.of_forall fun x => by simpa [mul_assoc] using w.le_opNorm₂ (f x) (g x))
  rwa [h2r, hr, eLpNorm_ofReal_eq _ _ (div_pos (by linarith) hden),
    eLpNorm_ofReal_eq _ _ (div_pos (by linarith) hden),
    eLpNorm_ofReal_eq _ _ (div_pos (by linarith) hden)] at hbound

/-- **`prop:weak-palatini`, variation clause.**  If the coframes `e_h → e` and the
variations `k_h → k` converge in `L²` with `L⁶` bounds, then the mixed bivectors
`w e_h k_h → w e k` in `L^{p'}` (the first variation `Ḃ_h`, a sum of such terms). -/
theorem eLpNorm'_wedge_variation_tendsto_zero {ι : Type*} {l : Filter ι} [IsFiniteMeasure μ]
    (w : E →L[ℝ] E →L[ℝ] Biv) (e : ι → α → E) (e₀ : α → E) (k : ι → α → E) (k₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (hk : ∀ i, AEStronglyMeasurable (k i) μ) (hk₀ : AEStronglyMeasurable k₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (hk6 : ∀ i, eLpNorm' (k i) 6 μ ≤ M) (hk6₀ : eLpNorm' k₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0))
    (hk2 : Tendsto (fun i => eLpNorm' (k i - k₀) 2 μ) l (𝓝 0))
    (p : ℝ) (hp : 3 / 2 < p) :
    Tendsto (fun i => eLpNorm' (fun x => w (e i x) (k i x) - w (e₀ x) (k₀ x)) (p / (p - 1)) μ)
      l (𝓝 0) := by
  have hp1 : 1 < p := by linarith
  have hden : 0 < p - 1 := sub_pos.mpr hp1
  obtain ⟨hq2, hq6⟩ := StrongInterpolationConvergence.palatini_conjugate_exponent_range p hp
  have hr1 : 1 ≤ p / (p - 1) := (le_div_iff₀ hden).2 (by linarith)
  have hθpos : 0 < (2 * p - 3) / (2 * p) := div_pos (by linarith) (by linarith)
  have h32 : (0 : ℝ) ≤ 3 / (2 * p) := div_nonneg (by norm_num) (by linarith)
  set V : ℝ≥0∞ := μ Set.univ ^ (1 / (2 * p / (p - 1)) - 1 / 6) with hV
  have hVne : V ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (div_pos (by linarith) (by linarith)) hq6.le)
      (measure_ne_top μ _)
  have hbq : ∀ (f : α → E), AEStronglyMeasurable f μ → eLpNorm' f 6 μ ≤ M →
      eLpNorm' f (2 * p / (p - 1)) μ ≤ M * V := fun f hf h6f =>
    (eLpNorm'_twoConj_le f hf p hp).trans (by gcongr)
  have hdiff6 : ∀ (f g : α → E), AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
      eLpNorm' f 6 μ ≤ M → eLpNorm' g 6 μ ≤ M → eLpNorm' (f - g) 6 μ ≤ M + M :=
    fun f g hf hg h6f h6g => by
      have := eLpNorm'_add_le hf hg.neg (by norm_num : (1 : ℝ) ≤ 6)
      rw [eLpNorm'_neg] at this
      rw [sub_eq_add_neg]
      exact this.trans (add_le_add h6f h6g)
  -- interpolation bound for a difference in `L^{2p'}`
  have hinterp : ∀ (f g : α → E), AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
      eLpNorm' f 6 μ ≤ M → eLpNorm' g 6 μ ≤ M →
      eLpNorm' (f - g) (2 * p / (p - 1)) μ ≤
        (M + M) ^ (3 / (2 * p)) * (eLpNorm' (f - g) 2 μ) ^ ((2 * p - 3) / (2 * p)) :=
    fun f g hf hg h6f h6g => by
      refine (FiniteMeasureL2L6Interpolation.palatini_eLpNorm'_interpolation (f - g) (hf.sub hg)
        p hp).trans ?_
      rw [mul_comm]
      gcongr
      exact hdiff6 f g hf hg h6f h6g
  set D : ℝ≥0∞ := ‖w‖₊ * (M + M) ^ (3 / (2 * p)) * (M * V) with hD
  have hDne : D ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg h32 (ENNReal.add_ne_top.mpr ⟨hM, hM⟩)))
      (ENNReal.mul_ne_top hM hVne)
  have hest : ∀ i, eLpNorm' (fun x => w (e i x) (k i x) - w (e₀ x) (k₀ x)) (p / (p - 1)) μ ≤
      D * (eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p)) +
        D * (eLpNorm' (k i - k₀) 2 μ) ^ ((2 * p - 3) / (2 * p)) := by
    intro i
    have hfun : (fun x => w (e i x) (k i x) - w (e₀ x) (k₀ x)) =
        (fun x => w ((e i - e₀) x) (k i x)) + fun x => w (e₀ x) ((k i - k₀) x) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
      abel
    have hm1 : AEStronglyMeasurable (fun x => w ((e i - e₀) x) (k i x)) μ :=
      w.aestronglyMeasurable_comp₂ ((he i).sub he₀) (hk i)
    have hm2 : AEStronglyMeasurable (fun x => w (e₀ x) ((k i - k₀) x)) μ :=
      w.aestronglyMeasurable_comp₂ he₀ ((hk i).sub hk₀)
    rw [hfun]
    refine (eLpNorm'_add_le hm1 hm2 hr1).trans (add_le_add ?_ ?_)
    · refine (eLpNorm'_wedge_mixed_le w _ _ ((he i).sub he₀) (hk i) p hp1).trans ?_
      calc (‖w‖₊ : ℝ≥0∞) * eLpNorm' (e i - e₀) (2 * p / (p - 1)) μ *
            eLpNorm' (k i) (2 * p / (p - 1)) μ
          ≤ ‖w‖₊ * ((M + M) ^ (3 / (2 * p)) *
              (eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p))) * (M * V) := by
            gcongr
            · exact hinterp _ _ (he i) he₀ (h6 i) h6₀
            · exact hbq _ (hk i) (hk6 i)
        _ = D * (eLpNorm' (e i - e₀) 2 μ) ^ ((2 * p - 3) / (2 * p)) := by rw [hD]; ring
    · refine (eLpNorm'_wedge_mixed_le w _ _ he₀ ((hk i).sub hk₀) p hp1).trans ?_
      calc (‖w‖₊ : ℝ≥0∞) * eLpNorm' e₀ (2 * p / (p - 1)) μ *
            eLpNorm' (k i - k₀) (2 * p / (p - 1)) μ
          ≤ ‖w‖₊ * (M * V) * ((M + M) ^ (3 / (2 * p)) *
              (eLpNorm' (k i - k₀) 2 μ) ^ ((2 * p - 3) / (2 * p))) := by
            gcongr
            · exact hbq _ he₀ h6₀
            · exact hinterp _ _ (hk i) hk₀ (hk6 i) hk6₀
        _ = D * (eLpNorm' (k i - k₀) 2 μ) ^ ((2 * p - 3) / (2 * p)) := by rw [hD]; ring
  have hpow : ∀ (f : ι → α → E) (f₀ : α → E), Tendsto (fun i => eLpNorm' (f i - f₀) 2 μ) l (𝓝 0) →
      Tendsto (fun i => D * (eLpNorm' (f i - f₀) 2 μ) ^ ((2 * p - 3) / (2 * p))) l (𝓝 0) := by
    intro f f₀ hf
    have h1 := ((ENNReal.continuous_rpow_const (y := (2 * p - 3) / (2 * p))).tendsto 0).comp hf
    simp only [Function.comp_def, ENNReal.zero_rpow_of_pos hθpos] at h1
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hDne)
    simpa using this
  have hmajor := (hpow e e₀ h2).add (hpow k k₀ hk2)
  rw [add_zero] at hmajor
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor (fun _ => zero_le) hest

/-- `w e k ∈ L^{p'}` for `e, k ∈ L⁶` on a finite measure space, `p > 3/2`. -/
theorem memLp_wedge_mixed (w : E →L[ℝ] E →L[ℝ] Biv) [IsFiniteMeasure μ] (e k : α → E)
    (he : AEStronglyMeasurable e μ) (hk : AEStronglyMeasurable k μ) (M : ℝ≥0∞) (hM : M ≠ ∞)
    (h6 : eLpNorm' e 6 μ ≤ M) (hk6 : eLpNorm' k 6 μ ≤ M) (p : ℝ) (hp : 3 / 2 < p) :
    MemLp (fun x => w (e x) (k x)) (ENNReal.ofReal (p / (p - 1))) μ := by
  have hp1 : 1 < p := by linarith
  refine ⟨w.aestronglyMeasurable_comp₂ he hk, ?_⟩
  rw [eLpNorm_conj_eq _ p hp1]
  refine (eLpNorm'_wedge_mixed_le w e k he hk p hp1).trans_lt ?_
  have hfin : ∀ (f : α → E), AEStronglyMeasurable f μ → eLpNorm' f 6 μ ≤ M →
      eLpNorm' f (2 * p / (p - 1)) μ < ∞ := fun f hf h6f =>
    (eLpNorm'_twoConj_le f hf p hp).trans_lt (ENNReal.mul_lt_top (h6f.trans_lt hM.lt_top)
      (ENNReal.rpow_lt_top_of_nonneg (by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (div_pos (by linarith) (by linarith))
          (StrongInterpolationConvergence.palatini_conjugate_exponent_range p hp).2.le)
        (measure_ne_top μ _)))
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top (hfin e he h6)) (hfin k hk hk6)

/-- **`prop:weak-palatini`, variation pairings.**  The first-variation pairings
`∫ pr (w e_h k_h) R_h → ∫ pr (w e k) R` converge under the same curvature hypotheses. -/
theorem palatini_variation_pairing_tendsto {ι : Type*} {l : Filter ι} [IsFiniteMeasure μ]
    (w : E →L[ℝ] E →L[ℝ] Biv) (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ) (hp : 3 / 2 < p)
    (e : ι → α → E) (e₀ : α → E) (k : ι → α → E) (k₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (hk : ∀ i, AEStronglyMeasurable (k i) μ) (hk₀ : AEStronglyMeasurable k₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (hk6 : ∀ i, eLpNorm' (k i) 6 μ ≤ M) (hk6₀ : eLpNorm' k₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0))
    (hk2 : Tendsto (fun i => eLpNorm' (k i - k₀) 2 μ) l (𝓝 0))
    (R : ι → α → Curv) (R₀ : α → Curv) (hR : ∀ i, AEStronglyMeasurable (R i) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hRb : ∀ i, eLpNorm (R i) (ENNReal.ofReal p) μ ≤ C)
    (hweak : ∀ φ : α → Biv, MemLp φ (ENNReal.ofReal (p / (p - 1))) μ →
      Tendsto (fun i => ∫ x, pr (φ x) (R i x) ∂μ) l (𝓝 (∫ x, pr (φ x) (R₀ x) ∂μ))) :
    Tendsto (fun i => ∫ x, pr (w (e i x) (k i x)) (R i x) ∂μ) l
      (𝓝 (∫ x, pr (w (e₀ x) (k₀ x)) (R₀ x) ∂μ)) := by
  have hp1 : 1 < p := by linarith
  have hBconv : Tendsto (fun i => eLpNorm (fun x => w (e i x) (k i x) - w (e₀ x) (k₀ x))
      (ENNReal.ofReal (p / (p - 1))) μ) l (𝓝 0) := by
    simp only [eLpNorm_conj_eq _ p hp1]
    exact eLpNorm'_wedge_variation_tendsto_zero w e e₀ k k₀ he he₀ hk hk₀ M hM h6 h6₀ hk6 hk6₀
      h2 hk2 p hp
  exact integral_pairing_tendsto pr p hp1 (fun i x => w (e i x) (k i x)) (fun x => w (e₀ x) (k₀ x))
    (fun i => memLp_wedge_mixed w (e i) (k i) (he i) (hk i) M hM (h6 i) (hk6 i) p hp)
    (memLp_wedge_mixed w e₀ k₀ he₀ hk₀ M hM h6₀ hk6₀ p hp) hBconv R R₀ hR C hC hRb hweak

/-! ### Bundled statement -/

/-- **`prop:weak-palatini`** (bundled).  On a finite measure space, under
`eq:Palatini-hypotheses` (`e_h → e` in `L²`, `‖e_h‖₆, ‖e‖₆ ≤ M`, `R_h ⇀ R` in `L^p` rendered as
`‖R_h‖_p ≤ C` plus convergence of all pairings against `L^{p'}` tests, `p > 3/2`, `R` being by
hypothesis the curvature of the limiting represented connection):
(1) `B(e_h) = w e_h e_h → B(e)` in `L^{p'}`; (2) the Palatini pairing converges;
(3) every bounded four-linear volume density converges in `L¹`; (4) if variations `k_h → k`
converge in `L²` with `L⁶` bounds, the coframe first-variation pairings converge. -/
theorem weak_palatini_passage {ι : Type*} {l : Filter ι} [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : E →L[ℝ] E →L[ℝ] Biv) (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ)
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V) (p : ℝ) (hp : 3 / 2 < p)
    (e : ι → α → E) (e₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0))
    (R : ι → α → Curv) (R₀ : α → Curv) (hR : ∀ i, AEStronglyMeasurable (R i) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hRb : ∀ i, eLpNorm (R i) (ENNReal.ofReal p) μ ≤ C)
    (hweak : ∀ φ : α → Biv, MemLp φ (ENNReal.ofReal (p / (p - 1))) μ →
      Tendsto (fun i => ∫ x, pr (φ x) (R i x) ∂μ) l (𝓝 (∫ x, pr (φ x) (R₀ x) ∂μ))) :
    Tendsto (fun i => eLpNorm (fun x => w (e i x) (e i x) - w (e₀ x) (e₀ x))
        (ENNReal.ofReal (p / (p - 1))) μ) l (𝓝 0) ∧
    Tendsto (fun i => ∫ x, pr (w (e i x) (e i x)) (R i x) ∂μ) l
      (𝓝 (∫ x, pr (w (e₀ x) (e₀ x)) (R₀ x) ∂μ)) ∧
    Tendsto (fun i => eLpNorm (fun x => vol (fun _ => e i x) - vol (fun _ => e₀ x)) 1 μ) l
      (𝓝 0) ∧
    (∀ (k : ι → α → E) (k₀ : α → E), (∀ i, AEStronglyMeasurable (k i) μ) →
      AEStronglyMeasurable k₀ μ → (∀ i, eLpNorm' (k i) 6 μ ≤ M) → eLpNorm' k₀ 6 μ ≤ M →
      Tendsto (fun i => eLpNorm' (k i - k₀) 2 μ) l (𝓝 0) →
      Tendsto (fun i => ∫ x, pr (w (e i x) (k i x)) (R i x) ∂μ) l
        (𝓝 (∫ x, pr (w (e₀ x) (k₀ x)) (R₀ x) ∂μ))) := by
  obtain ⟨h1, h2'⟩ := palatini_pairing_tendsto w pr p hp e e₀ he he₀ M hM h6 h6₀ h2 R R₀ hR C hC
    hRb hweak
  refine ⟨h1, h2', eLpNorm_fourLinear_tendsto_zero vol e e₀ he he₀ M hM h6 h6₀ h2, ?_⟩
  intro k k₀ hk hk₀ hk6 hk6₀ hk2
  exact palatini_variation_pairing_tendsto w pr p hp e e₀ k k₀ he he₀ hk hk₀ M hM h6 h6₀ hk6 hk6₀
    h2 hk2 R R₀ hR C hC hRb hweak

end RenewalGeometry.WeakPalatiniPassage
