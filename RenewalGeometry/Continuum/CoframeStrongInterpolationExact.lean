/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.FiniteMeasureL2L6InterpolationExact
import RenewalGeometry.Continuum.StrongInterpolationConvergenceExact

/-!
# Strong interpolation for the reconstructed coframes
  (`lem:supp-coframe-interpolation`, `eq:supp-coframe-l2-l6`,
  `eq:supp-strong-lq`, `eq:supp-interpolation-explicit`,
  `eq:supp-bivector-strong`; emergent-spacetime manuscript)

On a finite measure space `(K, μ)` (the compact spacetime cylinder with its
finite reconstructed volume measure), let the common-cylinder interpolants
`e_X : K → E` of the finite coframes converge strongly in `L²` to `e` and be
uniformly bounded in `L⁶` by `M₆ < ∞` (`eq:supp-coframe-l2-l6`).  Then

* `eLpNorm'_limit_le_of_tendsto_L2`: `e ∈ L⁶(K)` with `‖e‖₆ ≤ M₆`.  Instead
  of weak compactness, an a.e.-convergent subsequence is extracted from the
  `L²` convergence (convergence in measure, `TendstoInMeasure.exists_seq_tendsto_ae`)
  and Fatou's lemma (`lintegral_liminf_le'`) is applied to `‖e_X‖⁶`;
* `coframe_interpolation_explicit` (`eq:supp-interpolation-explicit`): for
  `2 ≤ q ≤ 6` and `θ_q = 3/q − 1/2`,
  `‖e_X − e‖_q ≤ ‖e_X − e‖_2^{θ_q} ‖e_X − e‖_6^{1−θ_q}` (Hölder interpolation
  `eLpNorm'_interpolate_two_six`, whose exponents `(6−q)/(2q)` and
  `3(q−2)/(2q)` are `θ_q` and `1 − θ_q`);
* `coframe_strong_Lq` (`eq:supp-strong-lq`): `e_X → e` strongly in `L^q(K)`
  for every `2 ≤ q < 6`, since `‖e_X − e‖_6 ≤ 2 M₆` and `θ_q > 0`;
* `coframe_bivector_strong` (`eq:supp-bivector-strong`): for `p > 3/2`,
  `p' = p/(p−1)`, `2 < 2p' < 6` (`palatini_conjugate_exponent_range`) and
  for every bounded bilinear map `B` (the exterior product on the
  finite-dimensional coframe fibres, `|a ∧ b| ≤ C|a||b|`),
  `B(e_X, e_X) → B(e, e)` strongly in `L^{p'}(K)`: write
  `B(e_X,e_X) − B(e,e) = B(e_X − e, e_X) + B(e, e_X − e)`, apply Hölder
  (`eLpNorm'_le_eLpNorm'_mul_eLpNorm'`) with `1/p' = 1/(2p') + 1/(2p')`, the
  uniform `L^{2p'}` bounds on `e_X` and `e` (finite measure), and
  `‖e_X − e‖_{2p'} → 0`.

`coframe_interpolation` bundles the four clauses.  Norms are Mathlib's
`eLpNorm'` with real exponents; the cutoffs are indexed by `ℕ` (a sequence
of cutoffs, as the a.e.-subsequence extraction requires a sequence).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.CoframeInterpolation

open FiniteMeasureL2L6Interpolation StrongInterpolationConvergence

variable {K E : Type*} [MeasurableSpace K] {μ : Measure K}
variable [NormedAddCommGroup E]

/-- `e ∈ L⁶` with `‖e‖₆ ≤ M₆`: the limit of an `L²`-convergent sequence that
is uniformly bounded in `L⁶` on a finite measure space inherits the `L⁶`
bound (a.e. subsequence + Fatou; no weak compactness). -/
theorem eLpNorm'_limit_le_of_tendsto_L2 [IsFiniteMeasure μ]
    (e : ℕ → K → E) (elim : K → E)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (helim : AEStronglyMeasurable elim μ)
    (hL2 : Tendsto (fun n => eLpNorm' (e n - elim) 2 μ) atTop (𝓝 0))
    {M6 : ℝ≥0∞} (hL6 : ∀ n, eLpNorm' (e n) 6 μ ≤ M6) :
    eLpNorm' elim 6 μ ≤ M6 := by
  -- convergence in measure and an a.e.-convergent subsequence
  have hL2' : Tendsto (fun n => eLpNorm (e n - elim) 2 μ) atTop (𝓝 0) := by
    refine hL2.congr fun n => ?_
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
    norm_num
  have hmeas : TendstoInMeasure μ e atTop elim :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) he helim hL2'
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  -- Fatou on the sextic power integrals
  have hpt : ∀ᵐ x ∂μ, ‖elim x‖ₑ ^ (6 : ℝ) =
      liminf (fun i => ‖e (ns i) x‖ₑ ^ (6 : ℝ)) atTop := by
    filter_upwards [hae] with x hx
    have h1 : Tendsto (fun i => ‖e (ns i) x‖ₑ ^ (6 : ℝ)) atTop (𝓝 (‖elim x‖ₑ ^ (6 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp (hx.enorm)
    exact h1.liminf_eq.symm
  have hfatou : ∫⁻ x, ‖elim x‖ₑ ^ (6 : ℝ) ∂μ ≤ M6 ^ (6 : ℝ) := by
    calc ∫⁻ x, ‖elim x‖ₑ ^ (6 : ℝ) ∂μ
        = ∫⁻ x, liminf (fun i => ‖e (ns i) x‖ₑ ^ (6 : ℝ)) atTop ∂μ := lintegral_congr_ae hpt
      _ ≤ liminf (fun i => ∫⁻ x, ‖e (ns i) x‖ₑ ^ (6 : ℝ) ∂μ) atTop :=
          lintegral_liminf_le' fun i => (he (ns i)).enorm.pow_const _
      _ ≤ M6 ^ (6 : ℝ) := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun i => ?_)
          rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)]
          exact ENNReal.rpow_le_rpow (hL6 (ns i)) (by norm_num)
  -- take the sixth root
  have h6 : eLpNorm' elim 6 μ = (∫⁻ x, ‖elim x‖ₑ ^ (6 : ℝ) ∂μ) ^ (1 / 6 : ℝ) := rfl
  rw [h6]
  calc (∫⁻ x, ‖elim x‖ₑ ^ (6 : ℝ) ∂μ) ^ (1 / 6 : ℝ)
      ≤ (M6 ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := ENNReal.rpow_le_rpow hfatou (by norm_num)
    _ = M6 := by rw [← ENNReal.rpow_mul]; norm_num

/-- `eq:supp-interpolation-explicit`: with `θ_q = 3/q − 1/2`,
`‖e_X − e‖_q ≤ ‖e_X − e‖_2^{θ_q} ‖e_X − e‖_6^{1 − θ_q}` for `2 ≤ q ≤ 6`. -/
theorem coframe_interpolation_explicit (f : K → E) (hf : AEStronglyMeasurable f μ)
    (q : ℝ) (hq2 : 2 ≤ q) (hq6 : q ≤ 6) :
    eLpNorm' f q μ ≤
      eLpNorm' f 2 μ ^ (3 / q - 1 / 2) * eLpNorm' f 6 μ ^ (1 - (3 / q - 1 / 2)) := by
  have hq : q ≠ 0 := by positivity
  have h := eLpNorm'_interpolate_two_six f hf q hq2 hq6
  have h1 : (6 - q) / (2 * q) = 3 / q - 1 / 2 := by field_simp; ring
  have h2 : 3 * (q - 2) / (2 * q) = 1 - (3 / q - 1 / 2) := by field_simp; ring
  rwa [h1, h2] at h

/-- `eq:supp-strong-lq`: an `L²`-convergent sequence uniformly bounded in
`L⁶` (limit included) converges strongly in `L^q` for every `2 ≤ q < 6`. -/
theorem coframe_strong_Lq
    (e : ℕ → K → E) (elim : K → E)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (helim : AEStronglyMeasurable elim μ)
    (hL2 : Tendsto (fun n => eLpNorm' (e n - elim) 2 μ) atTop (𝓝 0))
    {M6 : ℝ≥0∞} (hM6 : M6 ≠ ∞) (hL6 : ∀ n, eLpNorm' (e n) 6 μ ≤ M6)
    (hlim6 : eLpNorm' elim 6 μ ≤ M6)
    (q : ℝ) (hq2 : 2 ≤ q) (hq6 : q < 6) :
    Tendsto (fun n => eLpNorm' (e n - elim) q μ) atTop (𝓝 0) := by
  set θ : ℝ := 3 / q - 1 / 2 with hθ
  have hθpos : 0 < θ := by
    rw [hθ]
    have hq0 : 0 < q := by linarith
    rw [sub_pos, div_lt_div_iff₀ (by norm_num) hq0]
    linarith
  have hθle : 0 ≤ 1 - θ := by
    rw [hθ]
    have hq0 : 0 < q := by linarith
    have : 3 / q ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq2
    linarith
  -- uniform bound on the `L⁶` norm of the difference
  have hdiff6 : ∀ n, eLpNorm' (e n - elim) 6 μ ≤ 2 * M6 := by
    intro n
    have h := eLpNorm'_add_le (he n) helim.neg (q := 6) (by norm_num)
    rw [eLpNorm'_neg] at h
    calc eLpNorm' (e n - elim) 6 μ = eLpNorm' (e n + -elim) 6 μ := by rw [sub_eq_add_neg]
      _ ≤ eLpNorm' (e n) 6 μ + eLpNorm' elim 6 μ := h
      _ ≤ M6 + M6 := add_le_add (hL6 n) hlim6
      _ = 2 * M6 := (two_mul M6).symm
  -- the interpolation majorant tends to zero
  have hpow : Tendsto (fun n => eLpNorm' (e n - elim) 2 μ ^ θ) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := θ)).tendsto 0
    rw [ENNReal.zero_rpow_of_pos hθpos] at h
    exact h.comp hL2
  have hmajor : Tendsto (fun n => eLpNorm' (e n - elim) 2 μ ^ θ * (2 * M6) ^ (1 - θ))
      atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hpow (b := (2 * M6) ^ (1 - θ))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg hθle (ENNReal.mul_ne_top (by norm_num) hM6)))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun _ => zero_le) fun n => ?_
  calc eLpNorm' (e n - elim) q μ
      ≤ eLpNorm' (e n - elim) 2 μ ^ θ * eLpNorm' (e n - elim) 6 μ ^ (1 - θ) :=
        coframe_interpolation_explicit _ ((he n).sub helim) q hq2 hq6.le
    _ ≤ eLpNorm' (e n - elim) 2 μ ^ θ * (2 * M6) ^ (1 - θ) := by
        gcongr
        exact hdiff6 n

variable [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Hölder for a bounded bilinear map: `‖B(f, g)‖_{r} ≤ ‖B‖ ‖f‖_{2r} ‖g‖_{2r}`. -/
theorem eLpNorm'_bilinear_le (B : E →L[ℝ] E →L[ℝ] F) (f g : K → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (r : ℝ) (hr : 0 < r) :
    eLpNorm' (fun x => B (f x) (g x)) r μ ≤
      (‖B‖₊ : ℝ≥0∞) * eLpNorm' f (2 * r) μ * eLpNorm' g (2 * r) μ := by
  refine eLpNorm'_le_eLpNorm'_mul_eLpNorm' hf hg (fun a b => B a b) ‖B‖₊ ?_ hr (by linarith) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    have := B.le_opNorm₂ (f x) (g x)
    rw [← NNReal.coe_le_coe]
    push_cast
    exact this
  · field_simp
    ring

/-- `eq:supp-bivector-strong`: for `p > 3/2`, `p' = p/(p−1)`, and a bounded
bilinear map `B` (the exterior product on the coframe fibres), strong `L^{2p'}`
convergence `e_X → e` with uniform `L^{2p'}` bounds gives
`B(e_X, e_X) → B(e, e)` strongly in `L^{p'}`. -/
theorem coframe_bivector_strong (B : E →L[ℝ] E →L[ℝ] F)
    (e : ℕ → K → E) (elim : K → E)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (helim : AEStronglyMeasurable elim μ)
    (p : ℝ) (hp : 3 / 2 < p)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ n, eLpNorm' (e n) (2 * (p / (p - 1))) μ ≤ C)
    (hlimbound : eLpNorm' elim (2 * (p / (p - 1))) μ ≤ C)
    (hconv : Tendsto (fun n => eLpNorm' (e n - elim) (2 * (p / (p - 1))) μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm' (fun x => B (e n x) (e n x) - B (elim x) (elim x))
      (p / (p - 1)) μ) atTop (𝓝 0) := by
  set r : ℝ := p / (p - 1) with hr
  have hp1 : 1 < p := by linarith
  have hden : 0 < p - 1 := sub_pos.mpr hp1
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ hden]; linarith
  have hr0 : 0 < r := by linarith
  -- algebraic splitting of the bivector difference
  have hsplit : ∀ n, (fun x => B (e n x) (e n x) - B (elim x) (elim x)) =
      (fun x => B (e n x - elim x) (e n x)) + fun x => B (elim x) (e n x - elim x) := by
    intro n
    funext x
    simp only [Pi.add_apply, map_sub, sub_apply]
    abel
  have hmeasA : ∀ n, AEStronglyMeasurable (fun x => B (e n x - elim x) (e n x)) μ := fun n =>
    ((B.continuous₂).comp_aestronglyMeasurable (((he n).sub helim).prodMk (he n)))
  have hmeasB : ∀ n, AEStronglyMeasurable (fun x => B (elim x) (e n x - elim x)) μ := fun n =>
    ((B.continuous₂).comp_aestronglyMeasurable (helim.prodMk ((he n).sub helim)))
  -- the two Hölder majorants
  have hA : ∀ n, eLpNorm' (fun x => B (e n x - elim x) (e n x)) r μ ≤
      (‖B‖₊ : ℝ≥0∞) * eLpNorm' (e n - elim) (2 * r) μ * C := fun n => by
    calc eLpNorm' (fun x => B (e n x - elim x) (e n x)) r μ
        ≤ (‖B‖₊ : ℝ≥0∞) * eLpNorm' (e n - elim) (2 * r) μ * eLpNorm' (e n) (2 * r) μ :=
          eLpNorm'_bilinear_le B _ _ ((he n).sub helim) (he n) r hr0
      _ ≤ (‖B‖₊ : ℝ≥0∞) * eLpNorm' (e n - elim) (2 * r) μ * C :=
          mul_le_mul_right (hbound n) _
  have hB : ∀ n, eLpNorm' (fun x => B (elim x) (e n x - elim x)) r μ ≤
      (‖B‖₊ : ℝ≥0∞) * C * eLpNorm' (e n - elim) (2 * r) μ := fun n => by
    calc eLpNorm' (fun x => B (elim x) (e n x - elim x)) r μ
        ≤ (‖B‖₊ : ℝ≥0∞) * eLpNorm' elim (2 * r) μ * eLpNorm' (e n - elim) (2 * r) μ :=
          eLpNorm'_bilinear_le B _ _ helim ((he n).sub helim) r hr0
      _ ≤ (‖B‖₊ : ℝ≥0∞) * C * eLpNorm' (e n - elim) (2 * r) μ :=
          mul_le_mul_left (mul_le_mul_right hlimbound _) _
  -- the majorant tends to zero
  have hmajor : Tendsto (fun n => (‖B‖₊ : ℝ≥0∞) * eLpNorm' (e n - elim) (2 * r) μ * C +
      (‖B‖₊ : ℝ≥0∞) * C * eLpNorm' (e n - elim) (2 * r) μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (‖B‖₊ : ℝ≥0∞) * eLpNorm' (e n - elim) (2 * r) μ * C)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul hconv
        (a := (‖B‖₊ : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)) (b := C) (Or.inr hC)
      simpa using this
    have h2 : Tendsto (fun n => (‖B‖₊ : ℝ≥0∞) * C * eLpNorm' (e n - elim) (2 * r) μ)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hconv (a := (‖B‖₊ : ℝ≥0∞) * C)
        (Or.inr (ENNReal.mul_ne_top ENNReal.coe_ne_top hC))
      simpa using this
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun _ => zero_le) fun n => ?_
  rw [hsplit n]
  calc eLpNorm' ((fun x => B (e n x - elim x) (e n x)) +
        fun x => B (elim x) (e n x - elim x)) r μ
      ≤ eLpNorm' (fun x => B (e n x - elim x) (e n x)) r μ +
          eLpNorm' (fun x => B (elim x) (e n x - elim x)) r μ :=
        eLpNorm'_add_le (hmeasA n) (hmeasB n) hr1
    _ ≤ _ := add_le_add (hA n) (hB n)

/-- **`lem:supp-coframe-interpolation`.**  On a finite measure space, if the
coframe interpolants satisfy `eq:supp-coframe-l2-l6` (`e_X → e` strongly in
`L²`, `sup_X ‖e_X‖₆ ≤ M₆ < ∞`), then: `e ∈ L⁶` with `‖e‖₆ ≤ M₆`; the
explicit interpolation `eq:supp-interpolation-explicit` holds for
`2 ≤ q ≤ 6`; `e_X → e` strongly in `L^q` for every `2 ≤ q < 6`
(`eq:supp-strong-lq`); and for `p > 3/2`, `p' = p/(p−1)` satisfies
`2 < 2p' < 6` and `B(e_X, e_X) → B(e, e)` strongly in `L^{p'}` for every
bounded bilinear `B` (`eq:supp-bivector-strong`). -/
theorem coframe_interpolation [IsFiniteMeasure μ]
    (e : ℕ → K → E) (elim : K → E)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (helim : AEStronglyMeasurable elim μ)
    (hL2 : Tendsto (fun n => eLpNorm' (e n - elim) 2 μ) atTop (𝓝 0))
    {M6 : ℝ≥0∞} (hM6 : M6 ≠ ∞) (hL6 : ∀ n, eLpNorm' (e n) 6 μ ≤ M6) :
    eLpNorm' elim 6 μ ≤ M6 ∧
    (∀ n (q : ℝ), 2 ≤ q → q ≤ 6 →
      eLpNorm' (e n - elim) q μ ≤
        eLpNorm' (e n - elim) 2 μ ^ (3 / q - 1 / 2) *
          eLpNorm' (e n - elim) 6 μ ^ (1 - (3 / q - 1 / 2))) ∧
    (∀ q : ℝ, 2 ≤ q → q < 6 →
      Tendsto (fun n => eLpNorm' (e n - elim) q μ) atTop (𝓝 0)) ∧
    (∀ p : ℝ, 3 / 2 < p →
      (2 < 2 * (p / (p - 1)) ∧ 2 * (p / (p - 1)) < 6) ∧
      ∀ (B : E →L[ℝ] E →L[ℝ] F),
        Tendsto (fun n => eLpNorm' (fun x => B (e n x) (e n x) - B (elim x) (elim x))
          (p / (p - 1)) μ) atTop (𝓝 0)) := by
  have hlim6 := eLpNorm'_limit_le_of_tendsto_L2 e elim he helim hL2 hL6
  refine ⟨hlim6, fun n q hq2 hq6 =>
    coframe_interpolation_explicit _ ((he n).sub helim) q hq2 hq6,
    fun q hq2 hq6 => coframe_strong_Lq e elim he helim hL2 hM6 hL6 hlim6 q hq2 hq6,
    fun p hp => ?_⟩
  obtain ⟨hlo₀, hhi₀⟩ := palatini_conjugate_exponent_range p hp
  have hlo : 2 < 2 * (p / (p - 1)) := by rwa [mul_div_assoc] at hlo₀
  have hhi : 2 * (p / (p - 1)) < 6 := by rwa [mul_div_assoc] at hhi₀
  refine ⟨⟨hlo, hhi⟩, fun B => ?_⟩
  -- uniform `L^{2p'}` bounds from the `L⁶` bounds on the finite measure space
  set s : ℝ := 2 * (p / (p - 1)) with hs
  have hs0 : 0 < s := lt_trans (by norm_num) hlo
  set C : ℝ≥0∞ := M6 * μ Set.univ ^ (1 / s - 1 / 6) with hC
  have hCne : C ≠ ∞ :=
    ENNReal.mul_ne_top hM6 (ENNReal.rpow_ne_top_of_nonneg
      (by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hs0 hhi.le) (measure_ne_top μ _))
  have hbound : ∀ n, eLpNorm' (e n) s μ ≤ C := fun n =>
    (eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hs0 hhi.le (he n)).trans
      (mul_le_mul_left (hL6 n) _)
  have hlimbound : eLpNorm' elim s μ ≤ C :=
    (eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hs0 hhi.le helim).trans
      (mul_le_mul_left hlim6 _)
  have hconv : Tendsto (fun n => eLpNorm' (e n - elim) s μ) atTop (𝓝 0) :=
    coframe_strong_Lq e elim he helim hL2 hM6 hL6 hlim6 s hlo.le hhi
  exact coframe_bivector_strong B e elim he helim p hp hCne hbound hlimbound hconv

end RenewalGeometry.CoframeInterpolation
