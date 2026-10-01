/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PositiveHiggsAmplitudeCompilerExact

/-!
# Positive kinetic envelope and the `L^{8/3}` endpoint
  (`prop:positive-Higgs-envelope`, Einstein–SM action closure)

Completes `prop:positive-Higgs-envelope` on top of
`DiscreteAnalysis/PositiveHiggsAmplitudeCompilerExact.lean` (which has the pointwise envelope
`positiveHiggs_envelope` and the direction `positiveHiggs_L83_le_L43`).  Everything lives in
the namespace `RenewalGeometry.PositiveHiggsEnvelope`.

* `amp` — the packet amplitude `|K| = √(Σ_μ ‖K_μ‖²)` (the `PiLp 2` norm, `amp_eq_norm`).
* `lpNorm_equiv` — the boxed two-sided equivalence `eq:positive-Higgs-L43-L83`:
  `c^{1/2} ‖K‖_{L_h^{8/3}} ≤ ‖e‖_{L_h^{4/3}}^{1/2} ≤ C^{1/2} ‖K‖_{L_h^{8/3}}`.
* `lpNorm83_sub_le` — weighted Minkowski: the `L_h^{8/3}` criteria of two packets differ by
  at most the `L_h^{8/3}` norm of their difference (continuum identification through a
  consistency estimate).
* `tendsto_density_lintegral` — strong `L²` convergence of reconstructed packets plus uniform
  convergence of the comparison metrics gives strong `L¹` convergence of the positive
  densities (any measure; restricting to compact sets gives `L¹_loc`).
* `no_automatic_upgrade` — the sampled concentrating family `K_h = h^{-7/4} 1_{cell} e₀`:
  `‖K_h‖_{L_h²} → 0`, `‖e_h‖_{L_h¹} → 0`, but `‖e_h‖_{L_h^{4/3}} → ∞`, `‖K_h‖_{L_h^{8/3}} → ∞`.
* `positive_higgs_envelope` — assembly of the envelope, the norm equivalence and the
  continuum identification for a family of cutoffs.

Scoped renderings: the comparison constants satisfy `0 < c_r ≤ C_r`; only `m_h ≥ 0` of the
mass comparison is used (the norm equivalence needs no lower mass bound).  The continuum
identification is rendered as the exact triangle inequality relating the discrete
criterion for `K_h^H` to that of any comparison packet (the sampled `D_{A_h} H_h`), with the
consistency error of `prop:mesh-consistency` entering only as the bounded difference norm.
The `L¹` clause is stated after reconstruction on an arbitrary measure space, with the
reconstructed fields' amplitudes a.e.-measurable.
-/

namespace RenewalGeometry

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace PositiveHiggsEnvelope

variable {D : Type*} [Fintype D]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The packet amplitude `|K| = √(Σ_μ ‖K_μ‖²)`. -/
def amp (K : D → F) : ℝ := Real.sqrt (positiveHiggsAmpSq K)

theorem amp_nonneg (K : D → F) : 0 ≤ amp K := Real.sqrt_nonneg _

theorem amp_sq (K : D → F) : amp K ^ 2 = positiveHiggsAmpSq K :=
  Real.sq_sqrt (positiveHiggsAmpSq_nonneg K)

/-- The amplitude is the Euclidean (`PiLp 2`) norm of the packet. -/
theorem amp_eq_norm (K : D → F) :
    amp K = ‖(WithLp.toLp 2 K : PiLp 2 (fun _ : D => F))‖ := by
  rw [PiLp.norm_eq_of_L2]
  rfl

theorem amp_add_le (K K' : D → F) : amp (K + K') ≤ amp K + amp K' := by
  rw [amp_eq_norm, amp_eq_norm, amp_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

theorem norm_le_amp (K : D → F) (μ : D) : ‖K μ‖ ≤ amp K := by
  rw [amp]
  apply Real.le_sqrt_of_sq_le
  unfold positiveHiggsAmpSq
  exact Finset.single_le_sum (f := fun ν => ‖K ν‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ μ)


section NormEquivalence

variable {C : Type*} [Fintype C]

/-- Pointwise sandwich `c^{4/3} Q^{4/3} ≤ e^{4/3} ≤ C^{4/3} Q^{4/3}` summed against
nonnegative masses. -/
theorem sum_rpow_sandwich (m e Q : C → ℝ) (c Cc : ℝ) (hc : 0 < c) (hcC : c ≤ Cc)
    (hm : ∀ x, 0 ≤ m x) (hQ : ∀ x, 0 ≤ Q x) (henv : ∀ x, c * Q x ≤ e x ∧ e x ≤ Cc * Q x) :
    c ^ (4 / 3 : ℝ) * ∑ x, m x * Q x ^ (4 / 3 : ℝ) ≤ ∑ x, m x * |e x| ^ (4 / 3 : ℝ) ∧
      ∑ x, m x * |e x| ^ (4 / 3 : ℝ) ≤ Cc ^ (4 / 3 : ℝ) * ∑ x, m x * Q x ^ (4 / 3 : ℝ) := by
  have hCc : 0 ≤ Cc := hc.le.trans hcC
  have he0 : ∀ x, 0 ≤ e x := fun x => le_trans (mul_nonneg hc.le (hQ x)) (henv x).1
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_of_nonneg (he0 x)]
    have h1 : (c * Q x) ^ (4 / 3 : ℝ) ≤ e x ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg hc.le (hQ x)) (henv x).1 (by norm_num)
    rw [Real.mul_rpow hc.le (hQ x)] at h1
    have := mul_le_mul_of_nonneg_left h1 (hm x)
    linarith
  · refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_of_nonneg (he0 x)]
    have h1 : e x ^ (4 / 3 : ℝ) ≤ (Cc * Q x) ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (he0 x) (henv x).2 (by norm_num)
    rw [Real.mul_rpow hCc (hQ x)] at h1
    have := mul_le_mul_of_nonneg_left h1 (hm x)
    linarith

/-- `‖√Q‖_{L_h^{8/3}} = (Σ m Q^{4/3})^{3/8}`. -/
theorem lpNorm_sqrt_eq (m Q : C → ℝ) (hQ : ∀ x, 0 ≤ Q x) :
    positiveHiggsLpNorm m (8 / 3) (fun x => Real.sqrt (Q x)) =
      (∑ x, m x * Q x ^ (4 / 3 : ℝ)) ^ (3 / 8 : ℝ) := by
  unfold positiveHiggsLpNorm
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_of_nonneg (Real.sqrt_nonneg _), positiveHiggs_amp_rpow _ (hQ x)]
  · norm_num

/-- `‖e‖_{L_h^{4/3}}^{1/2} = (Σ m |e|^{4/3})^{3/8}`. -/
theorem lpNorm_sqrt_rpow (m e : C → ℝ) (hm : ∀ x, 0 ≤ m x) :
    positiveHiggsLpNorm m (4 / 3) e ^ (1 / 2 : ℝ) =
      (∑ x, m x * |e x| ^ (4 / 3 : ℝ)) ^ (3 / 8 : ℝ) := by
  unfold positiveHiggsLpNorm
  have hS : 0 ≤ ∑ x, m x * |e x| ^ (4 / 3 : ℝ) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hm x) (Real.rpow_nonneg (abs_nonneg _) _)
  rw [← Real.rpow_mul hS]
  norm_num

/-- **`prop:positive-Higgs-envelope`, boxed norm equivalence `eq:positive-Higgs-L43-L83`.**
If `c |K(x)|² ≤ e(x) ≤ C |K(x)|²` on every cell (the envelope `eq:positive-Higgs-envelope`,
with `Q = |K|²`) and the masses are nonnegative, then
`c^{1/2} ‖K‖_{L_h^{8/3}} ≤ ‖e‖_{L_h^{4/3}}^{1/2} ≤ C^{1/2} ‖K‖_{L_h^{8/3}}`. -/
theorem lpNorm_equiv (m e Q : C → ℝ) (c Cc : ℝ) (hc : 0 < c) (hcC : c ≤ Cc)
    (hm : ∀ x, 0 ≤ m x) (hQ : ∀ x, 0 ≤ Q x) (henv : ∀ x, c * Q x ≤ e x ∧ e x ≤ Cc * Q x) :
    c ^ (1 / 2 : ℝ) * positiveHiggsLpNorm m (8 / 3) (fun x => Real.sqrt (Q x)) ≤
        positiveHiggsLpNorm m (4 / 3) e ^ (1 / 2 : ℝ) ∧
      positiveHiggsLpNorm m (4 / 3) e ^ (1 / 2 : ℝ) ≤
        Cc ^ (1 / 2 : ℝ) * positiveHiggsLpNorm m (8 / 3) (fun x => Real.sqrt (Q x)) := by
  have hCc : 0 ≤ Cc := hc.le.trans hcC
  obtain ⟨hlo, hhi⟩ := sum_rpow_sandwich m e Q c Cc hc hcC hm hQ henv
  rw [lpNorm_sqrt_eq m Q hQ, lpNorm_sqrt_rpow m e hm]
  have hSK : 0 ≤ ∑ x, m x * Q x ^ (4 / 3 : ℝ) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hm x) (Real.rpow_nonneg (hQ x) _)
  have hpow : ∀ a : ℝ, 0 ≤ a → a ^ (1 / 2 : ℝ) = (a ^ (4 / 3 : ℝ)) ^ (3 / 8 : ℝ) := by
    intro a ha
    rw [← Real.rpow_mul ha]
    norm_num
  constructor
  · rw [hpow c hc.le, ← Real.mul_rpow (Real.rpow_nonneg hc.le _) hSK]
    exact Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hc.le _) hSK) hlo (by norm_num)
  · rw [hpow Cc hCc, ← Real.mul_rpow (Real.rpow_nonneg hCc _) hSK]
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun x _ => mul_nonneg (hm x) (Real.rpow_nonneg (abs_nonneg _) _))
      hhi (by norm_num)

end NormEquivalence

section Minkowski

variable {C : Type*} [Fintype C]

/-- Weighted Minkowski inequality for the discrete positive norms: if `0 ≤ f ≤ g + k`
with `g, k ≥ 0`, then `‖f‖_{L_h^p} ≤ ‖g‖_{L_h^p} + ‖k‖_{L_h^p}` for `p ≥ 1`. -/
theorem lpNorm_le_add (m f g k : C → ℝ) (p : ℝ) (hp : 1 ≤ p) (hm : ∀ x, 0 ≤ m x)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hk : ∀ x, 0 ≤ k x)
    (hfgk : ∀ x, f x ≤ g x + k x) :
    positiveHiggsLpNorm m p f ≤ positiveHiggsLpNorm m p g + positiveHiggsLpNorm m p k := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  set w : C → ℝ := fun x => m x ^ (1 / p) with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => Real.rpow_nonneg (hm x) _
  -- `m |a|^p = |w a|^p`
  have hmul : ∀ x (a : ℝ), m x * |a| ^ p = |w x * a| ^ p := by
    intro x a
    rw [abs_mul, abs_of_nonneg (hw0 x), Real.mul_rpow (hw0 x) (abs_nonneg _), hw]
    rw [← Real.rpow_mul (hm x), one_div_mul_cancel hp0.ne', Real.rpow_one]
  unfold positiveHiggsLpNorm
  simp_rw [hmul]
  refine le_trans ?_ (Real.Lp_add_le Finset.univ (fun x => w x * g x) (fun x => w x * k x) hp)
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _)
    (Finset.sum_le_sum fun x _ => ?_) (by positivity)
  rw [← mul_add]
  refine Real.rpow_le_rpow (abs_nonneg _) ?_ hp0.le
  rw [abs_of_nonneg (mul_nonneg (hw0 x) (hf x)),
    abs_of_nonneg (mul_nonneg (hw0 x) (add_nonneg (hg x) (hk x)))]
  exact mul_le_mul_of_nonneg_left (hfgk x) (hw0 x)

/-- **`prop:positive-Higgs-envelope`, continuum identification.**  For two packets
`K, K'` on the same cells (e.g. `K = K_h^H` and `K'` the sampled continuum covariant
gradient `D_{A_h} H_h`), the `L_h^{8/3}` criteria differ by at most the `L_h^{8/3}` norm of
the consistency error `K - K'`. -/
theorem lpNorm83_sub_le (m : C → ℝ) (hm : ∀ x, 0 ≤ m x) (K K' : C → D → F) :
    |positiveHiggsLpNorm m (8 / 3) (fun x => amp (K x)) -
        positiveHiggsLpNorm m (8 / 3) (fun x => amp (K' x))| ≤
      positiveHiggsLpNorm m (8 / 3) (fun x => amp (K x - K' x)) := by
  rw [abs_sub_le_iff]
  constructor
  · have := lpNorm_le_add m (fun x => amp (K x)) (fun x => amp (K' x))
      (fun x => amp (K x - K' x)) (8 / 3) (by norm_num) hm (fun x => amp_nonneg _)
      (fun x => amp_nonneg _) (fun x => amp_nonneg _) (fun x => by
        have := amp_add_le (K' x) (K x - K' x)
        simpa [add_sub_cancel] using this)
    linarith
  · have := lpNorm_le_add m (fun x => amp (K' x)) (fun x => amp (K x))
      (fun x => amp (K x - K' x)) (8 / 3) (by norm_num) hm (fun x => amp_nonneg _)
      (fun x => amp_nonneg _) (fun x => amp_nonneg _) (fun x => by
        have h1 := amp_add_le (K x) (K' x - K x)
        have h2 : amp (K' x - K x) = amp (K x - K' x) := by
          rw [amp_eq_norm, amp_eq_norm, WithLp.toLp_sub, WithLp.toLp_sub, norm_sub_rev]
        rw [h2] at h1
        simpa using h1)
    linarith

end Minkowski

section Bilinear

/-- The sampled bilinear pairing `r^{μν} Re⟨u_μ, v_ν⟩`. -/
def bil (r : D → D → ℝ) (u v : D → F) : ℝ :=
  ∑ μ, ∑ ν, r μ ν * inner ℝ (u μ) (v ν)

/-- `Σ_{μν} |r^{μν}|`, the coefficient size. -/
def coeffAbs (r : D → D → ℝ) : ℝ := ∑ μ, ∑ ν, |r μ ν|

theorem coeffAbs_nonneg (r : D → D → ℝ) : 0 ≤ coeffAbs r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem density_eq_bil (r : D → D → ℝ) (K : D → F) :
    positiveHiggsDensity r K = bil r K K := rfl

theorem abs_bil_le (r : D → D → ℝ) (u v : D → F) :
    |bil r u v| ≤ coeffAbs r * amp u * amp v := by
  unfold bil coeffAbs
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
  rw [abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul (norm_le_amp u μ) (norm_le_amp v ν) (norm_nonneg _) (amp_nonneg _)

theorem bil_sub_coeff (r r' : D → D → ℝ) (u v : D → F) :
    bil r u v - bil r' u v = bil (r - r') u v := by
  unfold bil
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem bil_self_sub (r : D → D → ℝ) (K K' : D → F) :
    bil r K K - bil r K' K' = bil r (K - K') K + bil r K' (K - K') := by
  unfold bil
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [Pi.sub_apply, inner_sub_left, inner_sub_right]
  ring

theorem coeffAbs_le_add (r r' : D → D → ℝ) :
    coeffAbs r ≤ coeffAbs r' + coeffAbs (r - r') := by
  unfold coeffAbs
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ν _ => ?_
  have := abs_add_le (r' μ ν) (r μ ν - r' μ ν)
  simpa using this

/-- Pointwise quadratic difference bound behind the `L¹` statement: with `a = |K - K'|`,
`b = |K'|`, `β = Σ|r|`, `δ = Σ|r - r'|` and any `η > 0`,
`|e(r,K) - e(r',K')| ≤ β (1 + η⁻¹) a² + (β η + δ) b²`. -/
theorem abs_density_sub_le (r r' : D → D → ℝ) (K K' : D → F) (η : ℝ) (hη : 0 < η) :
    |positiveHiggsDensity r K - positiveHiggsDensity r' K'| ≤
      coeffAbs r * (1 + η⁻¹) * amp (K - K') ^ 2 +
        (coeffAbs r * η + coeffAbs (r - r')) * amp K' ^ 2 := by
  set a := amp (K - K')
  set b := amp K'
  set β := coeffAbs r
  have ha : 0 ≤ a := amp_nonneg _
  have hb : 0 ≤ b := amp_nonneg _
  have hβ : 0 ≤ β := coeffAbs_nonneg _
  have hKle : amp K ≤ a + b := by
    have := amp_add_le (K - K') K'
    simpa using this
  rw [density_eq_bil, density_eq_bil]
  have hsplit : bil r K K - bil r' K' K' =
      (bil r (K - K') K + bil r K' (K - K')) + bil (r - r') K' K' := by
    rw [← bil_self_sub, ← bil_sub_coeff]
    ring
  rw [hsplit]
  have h1 := abs_bil_le r (K - K') K
  have h2 := abs_bil_le r K' (K - K')
  have h3 := abs_bil_le (r - r') K' K'
  have hab : 2 * a * b ≤ η⁻¹ * a ^ 2 + η * b ^ 2 := by
    have hη' : 0 < η⁻¹ := inv_pos.mpr hη
    have key : 0 ≤ (η⁻¹ * a - b) ^ 2 * η := mul_nonneg (sq_nonneg _) hη.le
    have : (η⁻¹ * a - b) ^ 2 * η = η⁻¹ * a ^ 2 - 2 * a * b + η * b ^ 2 := by
      field_simp
      ring
    linarith
  have hδ := coeffAbs_nonneg (r - r')
  calc |bil r (K - K') K + bil r K' (K - K') + bil (r - r') K' K'|
      ≤ |bil r (K - K') K| + |bil r K' (K - K')| + |bil (r - r') K' K'| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ β * a * amp K + β * b * a + coeffAbs (r - r') * b * b := by
        gcongr
    _ ≤ β * a * (a + b) + β * b * a + coeffAbs (r - r') * b * b := by
        gcongr
    _ = β * (a ^ 2 + 2 * a * b) + coeffAbs (r - r') * b ^ 2 := by ring
    _ ≤ β * (a ^ 2 + (η⁻¹ * a ^ 2 + η * b ^ 2)) + coeffAbs (r - r') * b ^ 2 := by
        gcongr
    _ = β * (1 + η⁻¹) * a ^ 2 + (β * η + coeffAbs (r - r')) * b ^ 2 := by ring

end Bilinear

section StrongL1

open MeasureTheory Filter Topology

/-- **`prop:positive-Higgs-envelope`, strong `L¹` clause.**  On any measure space (the
reconstruction domain; restrict the measure to a compact set for `L¹_loc`), let the
reconstructed packets `K_h → K` strongly in `L²` (`∫ |K_h - K|² → 0`, `∫ |K|² < ∞`) and the
reconstructed comparison metrics `r_h → r` uniformly, with `r` bounded.  Then the positive
densities converge strongly in `L¹`:
`∫ |r_h^{μν}⟨K_{h,μ},K_{h,ν}⟩ - r^{μν}⟨K_μ,K_ν⟩| → 0`. -/
theorem tendsto_density_lintegral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {ι : Type*} (l : Filter ι) (K : ι → X → D → F) (K₀ : X → D → F)
    (r : ι → X → D → D → ℝ) (r₀ : X → D → D → ℝ) (B : ℝ)
    (hB : ∀ x, coeffAbs (r₀ x) ≤ B)
    (hr : ∀ ε > 0, ∀ᶠ h in l, ∀ x, coeffAbs (r h x - r₀ x) ≤ ε)
    (hmeas_a : ∀ h, AEMeasurable (fun x => amp (K h x - K₀ x) ^ 2) μ)
    (hK : Tendsto (fun h => ∫⁻ x, ENNReal.ofReal (amp (K h x - K₀ x) ^ 2) ∂μ) l (𝓝 0))
    (hKfin : ∫⁻ x, ENNReal.ofReal (amp (K₀ x) ^ 2) ∂μ ≠ ⊤) :
    Tendsto (fun h => ∫⁻ x, ENNReal.ofReal
        |positiveHiggsDensity (r h x) (K h x) - positiveHiggsDensity (r₀ x) (K₀ x)| ∂μ)
      l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨t, ht0, htpos, htε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have ht : 0 < t := ENNReal.ofReal_pos.1 htpos
  set Ib : ℝ := (∫⁻ x, ENNReal.ofReal (amp (K₀ x) ^ 2) ∂μ).toReal with hIb_def
  have hIb : ∫⁻ x, ENNReal.ofReal (amp (K₀ x) ^ 2) ∂μ = ENNReal.ofReal Ib :=
    (ENNReal.ofReal_toReal hKfin).symm
  have hIb0 : 0 ≤ Ib := ENNReal.toReal_nonneg
  set B' : ℝ := max B 0 + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  set η : ℝ := t / (3 * B' * (Ib + 1)) with hη_def
  have hη : 0 < η := by positivity
  set δ₀ : ℝ := min 1 (t / (3 * (Ib + 1))) with hδ₀_def
  have hδ₀ : 0 < δ₀ := lt_min one_pos (by positivity)
  set P : ℝ := B' * (1 + η⁻¹) with hP_def
  have hP : 0 < P := by positivity
  set ta : ℝ := t / (3 * P) with hta_def
  have hta : 0 < ta := by positivity
  have hev_a := (ENNReal.tendsto_nhds_zero.1 hK) (ENNReal.ofReal ta)
    (ENNReal.ofReal_pos.2 hta)
  filter_upwards [hr δ₀ hδ₀, hev_a] with h hrh hKh
  set R : ℝ := B' * η + δ₀ with hR_def
  have hR : 0 ≤ R := by positivity
  -- pointwise bound
  have hpt : ∀ x, ENNReal.ofReal
      |positiveHiggsDensity (r h x) (K h x) - positiveHiggsDensity (r₀ x) (K₀ x)| ≤
      ENNReal.ofReal P * ENNReal.ofReal (amp (K h x - K₀ x) ^ 2) +
        ENNReal.ofReal R * ENNReal.ofReal (amp (K₀ x) ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul hP.le, ← ENNReal.ofReal_mul hR,
      ← ENNReal.ofReal_add (mul_nonneg hP.le (sq_nonneg _)) (mul_nonneg hR (sq_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    refine (abs_density_sub_le (r h x) (r₀ x) (K h x) (K₀ x) η hη).trans ?_
    have hβ : coeffAbs (r h x) ≤ B' := by
      have := coeffAbs_le_add (r h x) (r₀ x)
      have h1 := hB x
      have h2 := hrh x
      have h3 : δ₀ ≤ 1 := min_le_left _ _
      have h4 : B ≤ max B 0 := le_max_left _ _
      linarith
    have hδx : coeffAbs (r h x - r₀ x) ≤ δ₀ := hrh x
    have hβ0 := coeffAbs_nonneg (r h x)
    have hηinv : 0 ≤ 1 + η⁻¹ := by positivity
    gcongr
    · rw [hP_def]; gcongr
    · rw [hR_def]; gcongr
  calc ∫⁻ x, ENNReal.ofReal
        |positiveHiggsDensity (r h x) (K h x) - positiveHiggsDensity (r₀ x) (K₀ x)| ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal P * ENNReal.ofReal (amp (K h x - K₀ x) ^ 2) +
          ENNReal.ofReal R * ENNReal.ofReal (amp (K₀ x) ^ 2)) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal P * ∫⁻ x, ENNReal.ofReal (amp (K h x - K₀ x) ^ 2) ∂μ +
          ENNReal.ofReal R * ∫⁻ x, ENNReal.ofReal (amp (K₀ x) ^ 2) ∂μ := by
        rw [lintegral_add_left' (((hmeas_a h).ennreal_ofReal).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal P * ENNReal.ofReal ta + ENNReal.ofReal R * ENNReal.ofReal Ib := by
        rw [hIb]
        gcongr
    _ = ENNReal.ofReal (P * ta + R * Ib) := by
        rw [ENNReal.ofReal_add (mul_nonneg hP.le hta.le) (mul_nonneg hR hIb0),
          ENNReal.ofReal_mul hP.le, ENNReal.ofReal_mul hR]
    _ ≤ ENNReal.ofReal t := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : P * ta = t / 3 := by
          rw [hta_def]; field_simp
        have hIb1 : 0 < Ib + 1 := by linarith
        have h2 : B' * η * Ib ≤ t / 3 := by
          rw [hη_def]
          have : B' * (t / (3 * B' * (Ib + 1))) * Ib = t / 3 * (Ib / (Ib + 1)) := by
            field_simp
          rw [this]
          have : Ib / (Ib + 1) ≤ 1 := by rw [div_le_one hIb1]; linarith
          nlinarith
        have h3 : δ₀ * Ib ≤ t / 3 := by
          have hd : δ₀ ≤ t / (3 * (Ib + 1)) := min_le_right _ _
          have : t / (3 * (Ib + 1)) * Ib = t / 3 * (Ib / (Ib + 1)) := by
            field_simp
          have hle : Ib / (Ib + 1) ≤ 1 := by rw [div_le_one hIb1]; linarith
          nlinarith [mul_le_mul_of_nonneg_right hd hIb0]
        have : R * Ib = B' * η * Ib + δ₀ * Ib := by rw [hR_def]; ring
        linarith
    _ ≤ ε := htε.le

end StrongL1

section NoUpgrade

open Filter Topology

/-- The Euclidean comparison metric `r^{μν} = δ^{μν}`. -/
def identityMetric (D : Type*) [DecidableEq D] : D → D → ℝ := fun μ ν => if μ = ν then 1 else 0

theorem density_identityMetric [DecidableEq D] (K : D → F) :
    positiveHiggsDensity (identityMetric D) K = positiveHiggsAmpSq K := by
  unfold positiveHiggsDensity positiveHiggsAmpSq identityMetric
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_eq_single μ (fun ν _ hν => by simp [Ne.symm hν]) (by simp)]
  simp

/-- The cells of the side-`(n+1)` grid on the unit box: `(n+1)⁴` cells. -/
abbrev noUpgradeCell (n : ℕ) := Fin ((n + 1) ^ 4)

/-- The base cell. -/
def noUpgradeBase (n : ℕ) : noUpgradeCell n := ⟨0, by positivity⟩

/-- Mesh `h = 1/(n+1)`; cell mass `m_h = h⁴ = (n+1)^{-4}`. -/
def noUpgradeMass (n : ℕ) : noUpgradeCell n → ℝ := fun _ => ((n : ℝ) + 1) ^ (-4 : ℝ)

/-- The sampled concentrating family `K_h = h^{-7/4} φ e₀` with `φ` the indicator of the
base cell (the discrete counterpart of `Y_n = n^{7/4} φ(n(x - x₀)) v`). -/
def noUpgradePacket (n : ℕ) : noUpgradeCell n → Fin 4 → ℝ := fun x =>
  if x = noUpgradeBase n then Pi.single 0 (((n : ℝ) + 1) ^ (7 / 4 : ℝ)) else 0

theorem ampSq_single (c : ℝ) : positiveHiggsAmpSq (Pi.single (0 : Fin 4) c : Fin 4 → ℝ) = c ^ 2 := by
  simp [positiveHiggsAmpSq, Pi.single_apply]

theorem amp_noUpgradePacket_base (n : ℕ) :
    amp (noUpgradePacket n (noUpgradeBase n)) = ((n : ℝ) + 1) ^ (7 / 4 : ℝ) := by
  have hN : 0 ≤ (n : ℝ) + 1 := by positivity
  have hb : noUpgradePacket n (noUpgradeBase n) =
      Pi.single 0 (((n : ℝ) + 1) ^ (7 / 4 : ℝ)) := by simp [noUpgradePacket]
  rw [hb, amp, ampSq_single]
  exact Real.sqrt_sq (Real.rpow_nonneg hN _)

theorem amp_noUpgradePacket_ne (n : ℕ) (x : noUpgradeCell n) (hx : x ≠ noUpgradeBase n) :
    amp (noUpgradePacket n x) = 0 := by
  simp [noUpgradePacket, hx, amp, positiveHiggsAmpSq]

/-- One-cell sums of the discrete norms. -/
theorem sum_noUpgrade (n : ℕ) (f : noUpgradeCell n → ℝ) (p : ℝ) (hp : p ≠ 0)
    (hf : ∀ x, x ≠ noUpgradeBase n → f x = 0) :
    ∑ x, noUpgradeMass n x * |f x| ^ p =
      ((n : ℝ) + 1) ^ (-4 : ℝ) * |f (noUpgradeBase n)| ^ p := by
  rw [Finset.sum_eq_single (noUpgradeBase n)]
  · rfl
  · intro x _ hx
    rw [hf x hx, abs_zero, Real.zero_rpow hp, mul_zero]
  · simp

theorem noUpgrade_power (N a p q : ℝ) (hN : 0 < N) :
    (N ^ (-4 : ℝ) * |N ^ a| ^ p) ^ q = N ^ ((-4 + a * p) * q) := by
  rw [abs_of_nonneg (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le,
    ← Real.rpow_add hN, ← Real.rpow_mul hN.le]

/-- **`prop:positive-Higgs-envelope`, sharpness of the `L¹` clause.**  For the sampled
concentrating family on the side-`(n+1)` unit-box grid (cell masses `h⁴`, Euclidean
comparison metric, so `c_r = C_r = 1`), `K_h → 0` strongly in `L_h²` and
`e_h^{H,+} → 0` strongly in `L_h¹`, while `‖e_h^{H,+}‖_{L_h^{4/3}} → ∞` and
`‖K_h^H‖_{L_h^{8/3}} → ∞`: strong `L²` convergence alone gives no cutoff-uniform
`L^{4/3}` bound for the density nor `L^{8/3}` bound for the packet. -/
theorem no_automatic_upgrade :
    (∀ n, ∀ x, noUpgradeMass n x = (((n : ℝ) + 1)⁻¹) ^ 4) ∧
    (∀ ξ : Fin 4 → ℝ, 1 * positiveHiggsAmpSq ξ ≤
        positiveHiggsDensity (identityMetric (Fin 4)) ξ ∧
      positiveHiggsDensity (identityMetric (Fin 4)) ξ ≤ 1 * positiveHiggsAmpSq ξ) ∧
    Tendsto (fun n => positiveHiggsLpNorm (noUpgradeMass n) 2
      (fun x => amp (noUpgradePacket n x))) atTop (𝓝 0) ∧
    Tendsto (fun n => positiveHiggsLpNorm (noUpgradeMass n) 1
      (fun x => positiveHiggsDensity (identityMetric (Fin 4)) (noUpgradePacket n x)))
      atTop (𝓝 0) ∧
    Tendsto (fun n => positiveHiggsLpNorm (noUpgradeMass n) (4 / 3)
      (fun x => positiveHiggsDensity (identityMetric (Fin 4)) (noUpgradePacket n x)))
      atTop atTop ∧
    Tendsto (fun n => positiveHiggsLpNorm (noUpgradeMass n) (8 / 3)
      (fun x => amp (noUpgradePacket n x))) atTop atTop := by
  have hN : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  have hNt : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  -- density = amp² pointwise
  have hdens : ∀ n x, positiveHiggsDensity (identityMetric (Fin 4)) (noUpgradePacket n x) =
      amp (noUpgradePacket n x) ^ 2 := by
    intro n x
    rw [density_identityMetric, amp_sq]
  -- closed forms
  have hL2 : ∀ n : ℕ, positiveHiggsLpNorm (noUpgradeMass n) 2
      (fun x => amp (noUpgradePacket n x)) = ((n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
    intro n
    unfold positiveHiggsLpNorm
    rw [sum_noUpgrade n _ 2 (by norm_num) (fun x hx => amp_noUpgradePacket_ne n x hx),
      amp_noUpgradePacket_base, noUpgrade_power _ _ _ _ (hN n)]
    norm_num
  have hL1 : ∀ n : ℕ, positiveHiggsLpNorm (noUpgradeMass n) 1
      (fun x => positiveHiggsDensity (identityMetric (Fin 4)) (noUpgradePacket n x)) =
      ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
    intro n
    unfold positiveHiggsLpNorm
    simp_rw [hdens]
    rw [sum_noUpgrade n _ 1 (by norm_num) (fun x hx => by
        rw [amp_noUpgradePacket_ne n x hx]; norm_num),
      amp_noUpgradePacket_base, ← Real.rpow_natCast, ← Real.rpow_mul (hN n).le,
      noUpgrade_power _ _ _ _ (hN n)]
    norm_num
  have hL43 : ∀ n : ℕ, positiveHiggsLpNorm (noUpgradeMass n) (4 / 3)
      (fun x => positiveHiggsDensity (identityMetric (Fin 4)) (noUpgradePacket n x)) =
      ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := by
    intro n
    unfold positiveHiggsLpNorm
    simp_rw [hdens]
    rw [sum_noUpgrade n _ (4 / 3) (by norm_num) (fun x hx => by
        rw [amp_noUpgradePacket_ne n x hx]; norm_num),
      amp_noUpgradePacket_base, ← Real.rpow_natCast, ← Real.rpow_mul (hN n).le,
      noUpgrade_power _ _ _ _ (hN n)]
    norm_num
  have hL83 : ∀ n : ℕ, positiveHiggsLpNorm (noUpgradeMass n) (8 / 3)
      (fun x => amp (noUpgradePacket n x)) = ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := by
    intro n
    unfold positiveHiggsLpNorm
    rw [sum_noUpgrade n _ (8 / 3) (by norm_num) (fun x hx => amp_noUpgradePacket_ne n x hx),
      amp_noUpgradePacket_base, noUpgrade_power _ _ _ _ (hN n)]
    norm_num
  refine ⟨fun n x => ?_, fun ξ => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [noUpgradeMass]
    rw [Real.rpow_neg (hN n).le, inv_pow]
    norm_cast
  · rw [density_identityMetric, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  · simp_rw [hL2]
    exact (tendsto_rpow_neg_atTop (by norm_num)).comp hNt
  · simp_rw [hL1]
    exact (tendsto_rpow_neg_atTop (by norm_num)).comp hNt
  · simp_rw [hL43]
    exact (tendsto_rpow_atTop (by norm_num)).comp hNt
  · simp_rw [hL83]
    exact (tendsto_rpow_atTop (by norm_num)).comp hNt

end NoUpgrade

section Assembly

variable {ι : Type*} {Cell : ι → Type*} [∀ h, Fintype (Cell h)]

/-- **`prop:positive-Higgs-envelope`** (finite part).  Let `K h x : D → F` be the covariant
Higgs edge packets, `r h x` the sampled positive one-form metrics with the uniform comparison
`c_r |ξ|² ≤ r^{μν} Re⟨ξ_μ, ξ_ν⟩ ≤ C_r |ξ|²` (`eq:positive-Higgs-Hodge-comparison`,
`0 < c_r ≤ C_r` cutoff-independent) and `m h x ≥ 0` the cell masses.  Then
1. (`eq:positive-Higgs-envelope`) `c₀ |K_h^H|² ≤ e_h^{H,+} ≤ C₀ |K_h^H|²` on every cell with
   `c₀ = c_r`, `C₀ = C_r`;
2. (`eq:positive-Higgs-L43-L83`) `c₀^{1/2} ‖K_h^H‖_{L_h^{8/3}} ≤ ‖e_h^{H,+}‖_{L_h^{4/3}}^{1/2}
   ≤ C₀^{1/2} ‖K_h^H‖_{L_h^{8/3}}` for every cutoff;
3. (continuum identification) for any comparison family `K'_h` (the sampled continuum
   gradient `D_{A_h} H_h`) whose consistency error `‖K_h^H - K'_h‖_{L_h^{8/3}}` is bounded
   uniformly in `h`, the criterion `sup_h ‖K_h^H‖_{L_h^{8/3}} < ∞` holds iff
   `sup_h ‖K'_h‖_{L_h^{8/3}} < ∞`, and for each `h` the two norms differ by at most the
   consistency error.
The strong `L¹` clause is `tendsto_density_lintegral`; its sharpness (no automatic
`L^{4/3}`/`L^{8/3}` upgrade) is `no_automatic_upgrade`. -/
theorem positive_higgs_envelope
    (K : ∀ h, Cell h → D → F) (r : ∀ h, Cell h → D → D → ℝ) (m : ∀ h, Cell h → ℝ)
    (cr Cr : ℝ) (hcr : 0 < cr) (hcC : cr ≤ Cr) (hm : ∀ h x, 0 ≤ m h x)
    (hcomp : ∀ h x, ∀ ξ : D → F,
      cr * positiveHiggsAmpSq ξ ≤ positiveHiggsDensity (r h x) ξ ∧
        positiveHiggsDensity (r h x) ξ ≤ Cr * positiveHiggsAmpSq ξ) :
    (∀ h x, cr * amp (K h x) ^ 2 ≤ positiveHiggsDensity (r h x) (K h x) ∧
        positiveHiggsDensity (r h x) (K h x) ≤ Cr * amp (K h x) ^ 2) ∧
    (∀ h, cr ^ (1 / 2 : ℝ) * positiveHiggsLpNorm (m h) (8 / 3) (fun x => amp (K h x)) ≤
          positiveHiggsLpNorm (m h) (4 / 3)
            (fun x => positiveHiggsDensity (r h x) (K h x)) ^ (1 / 2 : ℝ) ∧
        positiveHiggsLpNorm (m h) (4 / 3)
            (fun x => positiveHiggsDensity (r h x) (K h x)) ^ (1 / 2 : ℝ) ≤
          Cr ^ (1 / 2 : ℝ) * positiveHiggsLpNorm (m h) (8 / 3) (fun x => amp (K h x))) ∧
    (∀ K' : ∀ h, Cell h → D → F,
      (∀ h, |positiveHiggsLpNorm (m h) (8 / 3) (fun x => amp (K h x)) -
          positiveHiggsLpNorm (m h) (8 / 3) (fun x => amp (K' h x))| ≤
        positiveHiggsLpNorm (m h) (8 / 3) (fun x => amp (K h x - K' h x))) ∧
      ((∃ E, ∀ h, positiveHiggsLpNorm (m h) (8 / 3) (fun x => amp (K h x - K' h x)) ≤ E) →
        ((∃ B, ∀ h, positiveHiggsLpNorm (m h) (8 / 3) (fun x => amp (K h x)) ≤ B) ↔
          (∃ B, ∀ h, positiveHiggsLpNorm (m h) (8 / 3) (fun x => amp (K' h x)) ≤ B)))) := by
  have henv : ∀ h x, cr * amp (K h x) ^ 2 ≤ positiveHiggsDensity (r h x) (K h x) ∧
      positiveHiggsDensity (r h x) (K h x) ≤ Cr * amp (K h x) ^ 2 := by
    intro h x
    rw [amp_sq]
    exact positiveHiggs_envelope (r h x) cr Cr (hcomp h x) (K h x)
  refine ⟨henv, fun h => ?_, fun K' => ⟨fun h => lpNorm83_sub_le (m h) (hm h) (K h) (K' h), ?_⟩⟩
  · have := lpNorm_equiv (m h) (fun x => positiveHiggsDensity (r h x) (K h x))
      (fun x => positiveHiggsAmpSq (K h x)) cr Cr hcr hcC (hm h)
      (fun x => positiveHiggsAmpSq_nonneg _) (fun x => by
        rw [← amp_sq]; exact henv h x)
    exact this
  · rintro ⟨E, hE⟩
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨B + E, fun h => ?_⟩
      have := lpNorm83_sub_le (m h) (hm h) (K h) (K' h)
      have h1 := hB h
      have h2 := hE h
      rw [abs_sub_le_iff] at this
      linarith [this.2]
    · rintro ⟨B, hB⟩
      refine ⟨B + E, fun h => ?_⟩
      have := lpNorm83_sub_le (m h) (hm h) (K h) (K' h)
      have h1 := hB h
      have h2 := hE h
      rw [abs_sub_le_iff] at this
      linarith [this.1]

end Assembly

end PositiveHiggsEnvelope

end

end RenewalGeometry
