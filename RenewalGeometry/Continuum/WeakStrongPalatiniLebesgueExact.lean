/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.WeakPalatiniPassageExact
import RenewalGeometry.Continuum.CoframeStrongInterpolationExact
import RenewalGeometry.Continuum.MonotoneDefectRemovalExact

/-!
# Weak–strong curvature pairing and volume convergence on `L^p(K)`
  (`lem:supp-weak-strong-palatini`, emergent-spacetime manuscript)

The lemma is stated on concrete Lebesgue spaces of a finite measure space `(α, μ)` (the compact
cylinder `K` with its finite reconstructed volume measure).

* Curvatures are elements `R_X ∈ L^p(K; Curv)` (Mathlib's `Lp Curv (ENNReal.ofReal p) μ`), and
  `R_X ⇀ R` weakly in `L^p(K)` (`eq:supp-curvature-weak`) means literally: `φ (R_X) → φ (R)` for
  every continuous linear functional `φ` on `L^p(K)`.
* The uniform bound `sup_X ‖R_X‖_{L^p} < ∞` is *derived* from weak convergence by the
  Banach–Steinhaus theorem (`lp_norm_bounded_of_weakTendsto`), as in the paper's proof.
* For `B ∈ L^{p'}(K; Biv)` the curvature pairing `R ↦ ∫_K pr(B, R)` is a continuous linear
  functional on `L^p(K)` (`lpPairingCLM`, Hölder), so weak convergence gives the convergence of
  all `L^{p'}` pairings (`tendsto_integral_pairing_of_weakTendsto`).
* The coframes `e_X → e` strongly in `L²(K)` with `sup_X ‖e_X‖_{L⁶} ≤ M₆`
  (`eq:supp-coframe-l2-l6`); the limit bound `‖e‖₆ ≤ M₆` is derived (Fatou,
  `CoframeInterpolation.eLpNorm'_limit_le_of_tendsto_L2`).
* `Φ` is a bounded (measurable) coefficient tensor field `x ↦ Φ(x) : Biv →L Biv`.

Main results:

* `weak_strong_pairing_tendsto` (`eq:supp-weak-strong-pairing`): for every bounded bilinear
  pointwise product `w` and every bounded coefficient field `Φ`,
  `∫_K ⟨Φ(e_X ∧ e_X), R_X⟩ → ∫_K ⟨Φ(e ∧ e), R⟩`;
* `weak_strong_pairing_tendsto_star_left`, `…_star_right`: the same with an internal Hodge star
  (any fixed bounded linear map of the fibre) applied to either bivector factor;
* `volume_strong_L1` (`eq:supp-volume-strong`): for every bounded four-linear pointwise product,
  `e_X^{∧4} → e^{∧4}` strongly in `L¹(K)`;
* `coframeWedge`, `coframeWedgeFour`: the actual exterior products of `ℝ⁴`-valued coframe
  one-forms on `ℝ⁴` (`(e∧f)^{IJ}_{μν} = e^I_μ f^J_ν - e^I_ν f^J_μ` and
  `(e₁∧e₂∧e₃∧e₄)^{IJKL}_{0123} = Σ_σ sgn σ e₁^I_{σ0} e₂^J_{σ1} e₃^K_{σ2} e₄^L_{σ3}`), as a
  bounded bilinear and a bounded four-linear map of the coefficient fibres;
* `supp_weak_strong_palatini` — the lemma for the concrete coframe exterior products, bundling
  the pairing convergence (plain and with an internal star on either factor) and the strong
  `L¹` convergence of `e_X ∧ e_X ∧ e_X ∧ e_X`.
-/

open MeasureTheory ENNReal Filter Topology

noncomputable section

namespace RenewalGeometry.WeakStrongPalatiniLebesgue

variable {α E Biv Curv : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Biv] [NormedSpace ℝ Biv]
  [NormedAddCommGroup Curv] [NormedSpace ℝ Curv]

/-! ### Weak convergence in `L^p(K)` -/

/-- Weak convergence `R_X ⇀ R` in `L^p(K; Curv)`: every continuous linear functional converges. -/
def LpWeakTendsto {q : ℝ≥0∞} [Fact (1 ≤ q)] (R : ℕ → Lp Curv q μ) (R₀ : Lp Curv q μ) : Prop :=
  ∀ φ : StrongDual ℝ (Lp Curv q μ), Tendsto (fun n => φ (R n)) atTop (𝓝 (φ R₀))

/-- **Uniform `L^p` bound from weak convergence** (Banach–Steinhaus): a weakly convergent
sequence in `L^p(K)` satisfies `sup_X ‖R_X‖_{L^p} < ∞`. -/
theorem lp_norm_bounded_of_weakTendsto {q : ℝ≥0∞} [Fact (1 ≤ q)] {R : ℕ → Lp Curv q μ}
    {R₀ : Lp Curv q μ} (hR : LpWeakTendsto R R₀) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n, eLpNorm (R n) q μ ≤ C := by
  obtain ⟨C, hC⟩ := MonotoneDefectRemoval.norm_bounded_of_weak_tendsto R R₀ hR
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n => ?_⟩
  rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (R n)), ← Lp.norm_def]
  exact ENNReal.ofReal_le_ofReal (hC n)

/-- The curvature pairing `R ↦ ∫ pr(B x, R x) dμ` against a fixed `B ∈ L^{p'}` is a continuous
linear functional on `L^p(K)` (Hölder). -/
def lpPairingCLM (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (B : α → Biv)
    (hB : MemLp B (ENNReal.ofReal (p / (p - 1))) μ) :
    StrongDual ℝ (Lp Curv (ENNReal.ofReal p) μ) :=
  LinearMap.mkContinuous
    { toFun := fun R => ∫ x, pr (B x) (R x) ∂μ
      map_add' := fun R S => by
        have hR := WeakPalatiniPassage.integrable_pairing pr p hp B R hB (Lp.memLp R)
        have hS := WeakPalatiniPassage.integrable_pairing pr p hp B S hB (Lp.memLp S)
        rw [← integral_add hR hS]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add R S] with x hx
        rw [hx, Pi.add_apply, map_add]
      map_smul' := fun c R => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c R] with x hx
        rw [hx, Pi.smul_apply, map_smul, smul_eq_mul] }
    (‖pr‖ * (eLpNorm B (ENNReal.ofReal (p / (p - 1))) μ).toReal) fun R => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have hmeas : AEStronglyMeasurable (fun x => pr (B x) (R x)) μ :=
        pr.aestronglyMeasurable_comp₂ hB.1 (Lp.aestronglyMeasurable R)
      calc ‖∫ x, pr (B x) (R x) ∂μ‖
          ≤ ∫ x, ‖pr (B x) (R x)‖ ∂μ := norm_integral_le_integral_norm _
        _ = (eLpNorm (fun x => pr (B x) (R x)) 1 μ).toReal := by
            rw [integral_norm_eq_lintegral_enorm hmeas, ← eLpNorm_one_eq_lintegral_enorm]
        _ ≤ (‖pr‖₊ * eLpNorm B (ENNReal.ofReal (p / (p - 1))) μ *
              eLpNorm R (ENNReal.ofReal p) μ).toReal := by
            apply ENNReal.toReal_mono
              (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hB.2.ne)
                (Lp.eLpNorm_ne_top R))
            exact WeakPalatiniPassage.eLpNorm_pairing_le pr p hp B R hB.1
              (Lp.aestronglyMeasurable R)
        _ = ‖pr‖ * (eLpNorm B (ENNReal.ofReal (p / (p - 1))) μ).toReal * ‖R‖ := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_mul, Lp.norm_def]
            simp

theorem lpPairingCLM_apply (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (B : α → Biv)
    (hB : MemLp B (ENNReal.ofReal (p / (p - 1))) μ) (R : Lp Curv (ENNReal.ofReal p) μ) :
    lpPairingCLM pr p hp B hB R = ∫ x, pr (B x) (R x) ∂μ := rfl

/-- Weak `L^p` convergence gives the convergence of every `L^{p'}` pairing (the definition of
weak convergence applied to `lpPairingCLM`). -/
theorem tendsto_integral_pairing_of_weakTendsto (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ)
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] {R : ℕ → Lp Curv (ENNReal.ofReal p) μ}
    {R₀ : Lp Curv (ENNReal.ofReal p) μ} (hR : LpWeakTendsto R R₀) (φ : α → Biv)
    (hφ : MemLp φ (ENNReal.ofReal (p / (p - 1))) μ) :
    Tendsto (fun n => ∫ x, pr (φ x) (R n x) ∂μ) atTop (𝓝 (∫ x, pr (φ x) (R₀ x) ∂μ)) :=
  hR (lpPairingCLM pr p hp φ hφ)

/-! ### Bounded coefficient tensors -/

theorem aestronglyMeasurable_coeff_apply (Φ : α → Biv →L[ℝ] Biv)
    (hΦ : AEStronglyMeasurable Φ μ) (b : α → Biv) (hb : AEStronglyMeasurable b μ) :
    AEStronglyMeasurable (fun x => Φ x (b x)) μ :=
  Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Biv →L[ℝ] Biv) (v : Biv) => A v)
    (continuous_fst.clm_apply continuous_snd) hΦ hb

/-! ### The weak–strong pairing -/

/-- **`eq:supp-weak-strong-pairing`** (general pointwise product).  On a finite measure space,
assume `eq:supp-coframe-l2-l6` (`e_X → e` in `L²`, `‖e_X‖₆ ≤ M₆`), `p > 3/2` and
`R_X ⇀ R` weakly in `L^p(K)`.  Then for every bounded bilinear pointwise product `w`, every
bounded fibre pairing `pr` and every bounded measurable coefficient tensor `Φ`,
`∫_K ⟨Φ(e_X ∧ e_X), R_X⟩ → ∫_K ⟨Φ(e ∧ e), R⟩`.  The uniform `L^p` bound on `R_X` and the
`L⁶` bound on `e` are derived, not assumed. -/
theorem weak_strong_pairing_tendsto [IsFiniteMeasure μ]
    (w : E →L[ℝ] E →L[ℝ] Biv) (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (p : ℝ) (hp : 3 / 2 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (e : ℕ → α → E) (e₀ : α → E)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (hL2 : Tendsto (fun n => eLpNorm' (e n - e₀) 2 μ) atTop (𝓝 0))
    (M₆ : ℝ≥0∞) (hM₆ : M₆ ≠ ∞) (hL6 : ∀ n, eLpNorm' (e n) 6 μ ≤ M₆)
    (R : ℕ → Lp Curv (ENNReal.ofReal p) μ) (R₀ : Lp Curv (ENNReal.ofReal p) μ)
    (hR : LpWeakTendsto R R₀)
    (Φ : α → Biv →L[ℝ] Biv) (hΦ : AEStronglyMeasurable Φ μ) (CΦ : ℝ) (hCΦ : ∀ x, ‖Φ x‖ ≤ CΦ) :
    Tendsto (fun n => ∫ x, pr (Φ x (w (e n x) (e n x))) (R n x) ∂μ) atTop
      (𝓝 (∫ x, pr (Φ x (w (e₀ x) (e₀ x))) (R₀ x) ∂μ)) := by
  have hp1 : 1 < p := by linarith
  have h6₀ : eLpNorm' e₀ 6 μ ≤ M₆ :=
    CoframeInterpolation.eLpNorm'_limit_le_of_tendsto_L2 e e₀ he he₀ hL2 hL6
  obtain ⟨C, hC, hRb⟩ := lp_norm_bounded_of_weakTendsto hR
  -- the coefficient bivectors `B_X = Φ(e_X ∧ e_X)`
  set B : ℕ → α → Biv := fun n x => Φ x (w (e n x) (e n x)) with hBdef
  set B₀ : α → Biv := fun x => Φ x (w (e₀ x) (e₀ x)) with hB₀def
  have hpt : ∀ x (v : Biv), ‖Φ x v‖ ≤ CΦ * ‖v‖ := fun x v =>
    ((Φ x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hCΦ x) (norm_nonneg v))
  have hwconv : Tendsto (fun n => eLpNorm (fun x => w (e n x) (e n x) - w (e₀ x) (e₀ x))
      (ENNReal.ofReal (p / (p - 1))) μ) atTop (𝓝 0) := by
    simp only [WeakPalatiniPassage.eLpNorm_conj_eq _ p hp1]
    exact WeakPalatiniPassage.eLpNorm'_wedge_tendsto_zero w e e₀ he he₀ M₆ hM₆ hL6 h6₀ hL2 p hp
  have hB : ∀ n, MemLp (B n) (ENNReal.ofReal (p / (p - 1))) μ := fun n =>
    (WeakPalatiniPassage.memLp_wedge w (e n) (he n) M₆ hM₆ (hL6 n) p hp).of_le_mul
      (aestronglyMeasurable_coeff_apply Φ hΦ _ (w.aestronglyMeasurable_comp₂ (he n) (he n)))
      (ae_of_all _ fun x => hpt x _)
  have hB₀ : MemLp B₀ (ENNReal.ofReal (p / (p - 1))) μ :=
    (WeakPalatiniPassage.memLp_wedge w e₀ he₀ M₆ hM₆ h6₀ p hp).of_le_mul
      (aestronglyMeasurable_coeff_apply Φ hΦ _ (w.aestronglyMeasurable_comp₂ he₀ he₀))
      (ae_of_all _ fun x => hpt x _)
  have hBle : ∀ n, eLpNorm (B n - B₀) (ENNReal.ofReal (p / (p - 1))) μ ≤
      ENNReal.ofReal CΦ * eLpNorm (fun x => w (e n x) (e n x) - w (e₀ x) (e₀ x))
        (ENNReal.ofReal (p / (p - 1))) μ := fun n => by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all _ fun x => ?_) _
    simp only [hBdef, hB₀def, Pi.sub_apply, ← map_sub]
    exact hpt x _
  have hBconv : Tendsto (fun n => eLpNorm (B n - B₀) (ENNReal.ofReal (p / (p - 1))) μ) atTop
      (𝓝 0) := by
    have hmaj : Tendsto (fun n => ENNReal.ofReal CΦ * eLpNorm (fun x => w (e n x) (e n x) -
        w (e₀ x) (e₀ x)) (ENNReal.ofReal (p / (p - 1))) μ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hwconv (Or.inr (ENNReal.ofReal_ne_top (r := CΦ)))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj (fun _ => zero_le) hBle
  exact WeakPalatiniPassage.integral_pairing_tendsto pr p hp1 B B₀ hB hB₀ hBconv
    (fun n => (R n : α → Curv)) (R₀ : α → Curv) (fun n => Lp.aestronglyMeasurable (R n)) C hC hRb
    (tendsto_integral_pairing_of_weakTendsto pr p hp1 hR)

/-- `eq:supp-weak-strong-pairing` with an internal Hodge star (any fixed bounded linear map
`⋆` of the bivector fibre) applied to the coframe bivector factor:
`∫_K ⟨⋆Φ(e_X ∧ e_X), R_X⟩ → ∫_K ⟨⋆Φ(e ∧ e), R⟩`. -/
theorem weak_strong_pairing_tendsto_star_left [IsFiniteMeasure μ]
    (w : E →L[ℝ] E →L[ℝ] Biv) (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (star : Biv →L[ℝ] Biv)
    (p : ℝ) (hp : 3 / 2 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (e : ℕ → α → E) (e₀ : α → E)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (hL2 : Tendsto (fun n => eLpNorm' (e n - e₀) 2 μ) atTop (𝓝 0))
    (M₆ : ℝ≥0∞) (hM₆ : M₆ ≠ ∞) (hL6 : ∀ n, eLpNorm' (e n) 6 μ ≤ M₆)
    (R : ℕ → Lp Curv (ENNReal.ofReal p) μ) (R₀ : Lp Curv (ENNReal.ofReal p) μ)
    (hR : LpWeakTendsto R R₀)
    (Φ : α → Biv →L[ℝ] Biv) (hΦ : AEStronglyMeasurable Φ μ) (CΦ : ℝ) (hCΦ : ∀ x, ‖Φ x‖ ≤ CΦ) :
    Tendsto (fun n => ∫ x, pr (star (Φ x (w (e n x) (e n x)))) (R n x) ∂μ) atTop
      (𝓝 (∫ x, pr (star (Φ x (w (e₀ x) (e₀ x)))) (R₀ x) ∂μ)) := by
  have h := weak_strong_pairing_tendsto w pr p hp e e₀ he he₀ hL2 M₆ hM₆ hL6 R R₀ hR
    (fun x => star.comp (Φ x))
    ((ContinuousLinearMap.compL ℝ Biv Biv Biv star).continuous.comp_aestronglyMeasurable hΦ)
    (‖star‖ * CΦ) (fun x => (star.opNorm_comp_le (Φ x)).trans
      (mul_le_mul_of_nonneg_left (hCΦ x) (norm_nonneg _)))
  simpa using h

/-- `eq:supp-weak-strong-pairing` with an internal Hodge star (any fixed bounded linear map
`⋆` of the curvature fibre) applied to the curvature factor:
`∫_K ⟨Φ(e_X ∧ e_X), ⋆R_X⟩ → ∫_K ⟨Φ(e ∧ e), ⋆R⟩`. -/
theorem weak_strong_pairing_tendsto_star_right [IsFiniteMeasure μ]
    (w : E →L[ℝ] E →L[ℝ] Biv) (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ) (star : Curv →L[ℝ] Curv)
    (p : ℝ) (hp : 3 / 2 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (e : ℕ → α → E) (e₀ : α → E)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (hL2 : Tendsto (fun n => eLpNorm' (e n - e₀) 2 μ) atTop (𝓝 0))
    (M₆ : ℝ≥0∞) (hM₆ : M₆ ≠ ∞) (hL6 : ∀ n, eLpNorm' (e n) 6 μ ≤ M₆)
    (R : ℕ → Lp Curv (ENNReal.ofReal p) μ) (R₀ : Lp Curv (ENNReal.ofReal p) μ)
    (hR : LpWeakTendsto R R₀)
    (Φ : α → Biv →L[ℝ] Biv) (hΦ : AEStronglyMeasurable Φ μ) (CΦ : ℝ) (hCΦ : ∀ x, ‖Φ x‖ ≤ CΦ) :
    Tendsto (fun n => ∫ x, pr (Φ x (w (e n x) (e n x))) (star (R n x)) ∂μ) atTop
      (𝓝 (∫ x, pr (Φ x (w (e₀ x) (e₀ x))) (star (R₀ x)) ∂μ)) := by
  have h := weak_strong_pairing_tendsto w (pr.bilinearComp (ContinuousLinearMap.id ℝ Biv) star)
    p hp e e₀ he he₀ hL2 M₆ hM₆ hL6 R R₀ hR Φ hΦ CΦ hCΦ
  simpa using h

/-- **`eq:supp-volume-strong`** (general pointwise product).  Under `eq:supp-coframe-l2-l6` on a
finite measure space, every bounded four-linear pointwise product converges strongly in
`L¹(K)`: `vol(e_X, e_X, e_X, e_X) → vol(e, e, e, e)`.  (Interpolation at `q = 4` and the
four-factor Hölder estimate; the limit `L⁶` bound is derived.) -/
theorem volume_strong_L1 [IsFiniteMeasure μ] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V)
    (e : ℕ → α → E) (e₀ : α → E)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (hL2 : Tendsto (fun n => eLpNorm' (e n - e₀) 2 μ) atTop (𝓝 0))
    (M₆ : ℝ≥0∞) (hM₆ : M₆ ≠ ∞) (hL6 : ∀ n, eLpNorm' (e n) 6 μ ≤ M₆) :
    Tendsto (fun n => eLpNorm (fun x => vol (fun _ => e n x) - vol (fun _ => e₀ x)) 1 μ) atTop
      (𝓝 0) :=
  WeakPalatiniPassage.eLpNorm_fourLinear_tendsto_zero vol e e₀ he he₀ M₆ hM₆ hL6
    (CoframeInterpolation.eLpNorm'_limit_le_of_tendsto_L2 e e₀ he he₀ hL2 hL6) hL2

/-! ### The concrete coframe exterior products -/

/-- The coefficient fibre of an `ℝ⁴`-valued coframe one-form on a chart of `ℝ⁴`:
`e^I_μ`, `I` the internal and `μ` the form index. -/
abbrev CoframeFibre : Type := Fin 4 → Fin 4 → ℝ

/-- The coefficient fibre of four-index arrays (bivector-valued two-forms `B^{IJ}_{μν}`,
curvature two-forms `R^{IJ}_{μν}`, and the top-degree components `(·)^{IJKL}` of
internal-four-index four-forms). -/
abbrev FourIndexFibre : Type := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The component `e^I_μ` as a continuous linear functional on the coframe fibre. -/
def coframeEval (I μ : Fin 4) : CoframeFibre →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) I)

@[simp] theorem coframeEval_apply (I μ : Fin 4) (a : CoframeFibre) : coframeEval I μ a = a I μ :=
  rfl

theorem abs_coeff_le (a : CoframeFibre) (I μ : Fin 4) : |a I μ| ≤ ‖a‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (a I) μ).trans (norm_le_pi_norm a I)

/-- The exterior product of two coframe one-forms, as a bilinear map of the coefficient
fibres: `(a ∧ b)^{IJ}_{μν} = a^I_μ b^J_ν - a^I_ν b^J_μ`. -/
def coframeWedgeLin : CoframeFibre →ₗ[ℝ] CoframeFibre →ₗ[ℝ] FourIndexFibre :=
  LinearMap.mk₂ ℝ (fun a b I J μ ν => a I μ * b J ν - a I ν * b J μ)
    (fun a a' b => by funext I J μ ν; simp; ring)
    (fun c a b => by funext I J μ ν; simp; ring)
    (fun a b b' => by funext I J μ ν; simp; ring)
    (fun c a b => by funext I J μ ν; simp; ring)

/-- The coframe exterior product `e ∧ f` as a bounded bilinear map (`‖a ∧ b‖ ≤ 2‖a‖‖b‖`). -/
def coframeWedge : CoframeFibre →L[ℝ] CoframeFibre →L[ℝ] FourIndexFibre :=
  coframeWedgeLin.mkContinuous₂ 2 fun a b => by
    have h0 : 0 ≤ 2 * ‖a‖ * ‖b‖ := by positivity
    refine (pi_norm_le_iff_of_nonneg h0).2 fun I => (pi_norm_le_iff_of_nonneg h0).2 fun J =>
      (pi_norm_le_iff_of_nonneg h0).2 fun μ' => (pi_norm_le_iff_of_nonneg h0).2 fun ν => ?_
    simp only [coframeWedgeLin, LinearMap.mk₂_apply, Real.norm_eq_abs]
    have h1 : |a I μ' * b J ν| ≤ ‖a‖ * ‖b‖ := by
      rw [abs_mul]; exact mul_le_mul (abs_coeff_le a I μ') (abs_coeff_le b J ν) (abs_nonneg _)
        (norm_nonneg _)
    have h2 : |a I ν * b J μ'| ≤ ‖a‖ * ‖b‖ := by
      rw [abs_mul]; exact mul_le_mul (abs_coeff_le a I ν) (abs_coeff_le b J μ') (abs_nonneg _)
        (norm_nonneg _)
    calc |a I μ' * b J ν - a I ν * b J μ'| ≤ |a I μ' * b J ν| + |a I ν * b J μ'| := abs_sub _ _
      _ ≤ 2 * ‖a‖ * ‖b‖ := by linarith

@[simp] theorem coframeWedge_apply (a b : CoframeFibre) (I J μ ν : Fin 4) :
    coframeWedge a b I J μ ν = a I μ * b J ν - a I ν * b J μ := rfl

/-- The fourfold exterior product of coframe one-forms on `ℝ⁴`: the coefficient of
`dx⁰ ∧ dx¹ ∧ dx² ∧ dx³` in `e₁^I ∧ e₂^J ∧ e₃^K ∧ e₄^L`,
`Σ_σ sgn σ e₁^I_{σ0} e₂^J_{σ1} e₃^K_{σ2} e₄^L_{σ3}`, as a bounded four-linear map. -/
def coframeWedgeFour :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => CoframeFibre) FourIndexFibre :=
  ContinuousMultilinearMap.pi fun I => ContinuousMultilinearMap.pi fun J =>
    ContinuousMultilinearMap.pi fun K => ContinuousMultilinearMap.pi fun L =>
      ∑ σ : Equiv.Perm (Fin 4), ((Equiv.Perm.sign σ : ℤ) : ℝ) •
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun j => coframeEval (![I, J, K, L] j) (σ j))

theorem coframeWedgeFour_apply (m : Fin 4 → CoframeFibre) (I J K L : Fin 4) :
    coframeWedgeFour m I J K L =
      ∑ σ : Equiv.Perm (Fin 4), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ j, m j (![I, J, K, L] j) (σ j) := by
  simp [coframeWedgeFour]

/-! ### The lemma for the concrete exterior products -/

/-- **`lem:supp-weak-strong-palatini`.**  Let `(α, μ)` be a finite measure space (the compact
cylinder `K`).  Assume `eq:supp-coframe-l2-l6`: coframes `e_X → e` strongly in `L²(K)` with
`sup_X ‖e_X‖_{L⁶} ≤ M₆`; let `p > 3/2` and `R_X ⇀ R` weakly in `L^p(K)`
(`eq:supp-curvature-weak`, every continuous linear functional of `L^p(K)` converges).  Then for
every bounded measurable coefficient tensor `Φ` and bounded fibre pairing `⟨·,·⟩`:

1. `∫_K ⟨Φ(e_X ∧ e_X), R_X⟩ → ∫_K ⟨Φ(e ∧ e), R⟩` (`eq:supp-weak-strong-pairing`);
2. the same with an internal Hodge star `⋆` (any fixed bounded linear fibre map) applied to the
   bivector factor, and
3. to the curvature factor;
4. `e_X ∧ e_X ∧ e_X ∧ e_X → e ∧ e ∧ e ∧ e` strongly in `L¹(K)` (`eq:supp-volume-strong`).

Here `∧` are the actual coframe exterior products `coframeWedge`, `coframeWedgeFour`; the
uniform `L^p` bound on `R_X` and the `L⁶` bound on `e` are derived from the hypotheses. -/
theorem supp_weak_strong_palatini [IsFiniteMeasure μ]
    (pr : FourIndexFibre →L[ℝ] Curv →L[ℝ] ℝ) (starB : FourIndexFibre →L[ℝ] FourIndexFibre)
    (starR : Curv →L[ℝ] Curv) (p : ℝ) (hp : 3 / 2 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (e : ℕ → α → CoframeFibre) (e₀ : α → CoframeFibre)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (hL2 : Tendsto (fun n => eLpNorm' (e n - e₀) 2 μ) atTop (𝓝 0))
    (M₆ : ℝ≥0∞) (hM₆ : M₆ ≠ ∞) (hL6 : ∀ n, eLpNorm' (e n) 6 μ ≤ M₆)
    (R : ℕ → Lp Curv (ENNReal.ofReal p) μ) (R₀ : Lp Curv (ENNReal.ofReal p) μ)
    (hR : LpWeakTendsto R R₀)
    (Φ : α → FourIndexFibre →L[ℝ] FourIndexFibre) (hΦ : AEStronglyMeasurable Φ μ) (CΦ : ℝ)
    (hCΦ : ∀ x, ‖Φ x‖ ≤ CΦ) :
    Tendsto (fun n => ∫ x, pr (Φ x (coframeWedge (e n x) (e n x))) (R n x) ∂μ) atTop
      (𝓝 (∫ x, pr (Φ x (coframeWedge (e₀ x) (e₀ x))) (R₀ x) ∂μ)) ∧
    Tendsto (fun n => ∫ x, pr (starB (Φ x (coframeWedge (e n x) (e n x)))) (R n x) ∂μ) atTop
      (𝓝 (∫ x, pr (starB (Φ x (coframeWedge (e₀ x) (e₀ x)))) (R₀ x) ∂μ)) ∧
    Tendsto (fun n => ∫ x, pr (Φ x (coframeWedge (e n x) (e n x))) (starR (R n x)) ∂μ) atTop
      (𝓝 (∫ x, pr (Φ x (coframeWedge (e₀ x) (e₀ x))) (starR (R₀ x)) ∂μ)) ∧
    Tendsto (fun n => eLpNorm (fun x => coframeWedgeFour (fun _ => e n x) -
        coframeWedgeFour (fun _ => e₀ x)) 1 μ) atTop (𝓝 0) :=
  ⟨weak_strong_pairing_tendsto coframeWedge pr p hp e e₀ he he₀ hL2 M₆ hM₆ hL6 R R₀ hR Φ hΦ CΦ
      hCΦ,
    weak_strong_pairing_tendsto_star_left coframeWedge pr starB p hp e e₀ he he₀ hL2 M₆ hM₆ hL6
      R R₀ hR Φ hΦ CΦ hCΦ,
    weak_strong_pairing_tendsto_star_right coframeWedge pr starR p hp e e₀ he he₀ hL2 M₆ hM₆ hL6
      R R₀ hR Φ hΦ CΦ hCΦ,
    volume_strong_L1 coframeWedgeFour e e₀ he he₀ hL2 M₆ hM₆ hL6⟩

/-! ### Non-vacuity -/

/-- The identity coframe `e^I_μ = δ^I_μ`. -/
def identityCoframe : CoframeFibre := fun I μ => if I = μ then 1 else 0

theorem vecFour_eq_self (j : Fin 4) : ![(0 : Fin 4), 1, 2, 3] j = j := by
  fin_cases j <;> rfl

/-- The fourfold exterior product is not the zero map: for the identity coframe,
`(e ∧ e ∧ e ∧ e)^{0123}_{0123} = 1`. -/
theorem coframeWedgeFour_identity :
    coframeWedgeFour (fun _ => identityCoframe) 0 1 2 3 = 1 := by
  rw [coframeWedgeFour_apply]
  simp only [vecFour_eq_self, identityCoframe]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin 4))]
  · simp
  · intro σ _ hσ
    obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
      by_contra h
      push_neg at h
      exact hσ (Equiv.ext fun j => h j)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Ne.symm hj])]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Non-vacuity of the hypothesis packet of `supp_weak_strong_palatini`: constant coframes and a
constant curvature sequence in `L²` of the unit interval satisfy all hypotheses (`p = 2`,
`Φ = id`, star maps the identity). -/
example (pr : FourIndexFibre →L[ℝ] FourIndexFibre →L[ℝ] ℝ)
    (R₀ : Lp FourIndexFibre (ENNReal.ofReal 2) (volume : Measure (Set.Icc (0 : ℝ) 1))) :
    haveI : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by simp⟩
    Tendsto (fun _ : ℕ => ∫ x, pr (coframeWedge identityCoframe identityCoframe) (R₀ x)) atTop
      (𝓝 (∫ x, pr (coframeWedge identityCoframe identityCoframe) (R₀ x))) := by
  haveI : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by simp⟩
  have hfin : eLpNorm' (fun _ : Set.Icc (0 : ℝ) 1 => identityCoframe) 6 volume ≠ ∞ := by
    have h := (memLp_const (μ := (volume : Measure (Set.Icc (0 : ℝ) 1))) (p := 6)
      identityCoframe).2
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)] at h
    simpa using h.ne
  have h0 : Tendsto (fun _ : ℕ => eLpNorm' ((fun _ : Set.Icc (0 : ℝ) 1 => identityCoframe) -
      fun _ => identityCoframe) 2 volume) atTop (𝓝 0) := by
    simp [eLpNorm'_zero (by norm_num : (0 : ℝ) < 2)]
  have hw : LpWeakTendsto (fun _ : ℕ => R₀) R₀ := fun φ => tendsto_const_nhds
  have := (supp_weak_strong_palatini pr (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _)
    2 (by norm_num) (fun _ _ => identityCoframe) (fun _ => identityCoframe)
    (fun _ => aestronglyMeasurable_const) aestronglyMeasurable_const h0 _ hfin (fun _ => le_rfl)
    (fun _ => R₀) R₀ hw (fun _ => ContinuousLinearMap.id ℝ _) aestronglyMeasurable_const 1
    (fun _ => ContinuousLinearMap.norm_id_le)).1
  simpa using this

end RenewalGeometry.WeakStrongPalatiniLebesgue
