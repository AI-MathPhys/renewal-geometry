/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.KolmogorovRieszTorus

/-!
# Local Kolmogorov–Riesz on a chart of the periodic box

Generic infrastructure (no renewal notions).  Let `Ω` be an open chart of the torus
`𝕋^d = UnitAddTorus d` (the periodic comparison box of the Einstein–SM manuscript, unit-torus
rendering).  A family `f_i : 𝕋^d → V` (`V` finite-dimensional) that is bounded in `L²(Ω)` and
whose coordinate translation moduli vanish on every compact `K ⊆ Ω` (outside finitely many
indices, as in `limsup_{h↓0}` formulations) is relatively compact in `L²_loc(Ω)`: on every compact
`K ⊆ Ω` it has finite `ε`-nets in `L²(K)` drawn from the family itself.

Proof: a Lipschitz cutoff `χ = max(0, 1 - dist(·,K)/r)` with `cthickening (3r) K ⊆ Ω`; the
products `χ f_i` are bounded in `L²(𝕋^d)` with translation moduli
`‖τ_y(χf) - χf‖ ≤ ‖τ_y f - f‖_{L²(K₂)} + (|y|/r)‖f‖_{L²(K₂)}`, `K₂ = cthickening (2r) K`;
the torus Kolmogorov–Riesz theorem (`KolmogorovRieszTorus.kolmogorovRiesz_torus_vector_cofinite`)
makes them totally bounded, and `χ = 1` on `K`.

* `cutoff`, `cutoff_eq_one`, `cutoff_eq_zero`, `abs_cutoff_sub_le`.
* `exists_net_of_local_modulus` (**local Kolmogorov–Riesz**, `ε`-nets of indices).
* `totallyBounded_restrict_of_local_modulus` (the same as total boundedness in `L²(K)`).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.LocalKRTorus

open KolmogorovRieszTorus

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### The cutoff -/

/-- The Lipschitz cutoff `χ_{K,r}(t) = max(0, 1 - dist(t,K)/r)`. -/
def cutoff (K : Set (UnitAddTorus d)) (r : ℝ) (t : UnitAddTorus d) : ℝ :=
  max 0 (1 - infDist t K / r)

theorem cutoff_nonneg (K : Set (UnitAddTorus d)) (r : ℝ) (t : UnitAddTorus d) :
    0 ≤ cutoff K r t := le_max_left _ _

theorem cutoff_le_one (K : Set (UnitAddTorus d)) {r : ℝ} (hr : 0 < r) (t : UnitAddTorus d) :
    cutoff K r t ≤ 1 := by
  refine max_le zero_le_one ?_
  have := div_nonneg (infDist_nonneg (x := t) (s := K)) hr.le
  linarith

theorem cutoff_eq_one {K : Set (UnitAddTorus d)} (r : ℝ) {t : UnitAddTorus d} (ht : t ∈ K) :
    cutoff K r t = 1 := by
  simp [cutoff, infDist_zero_of_mem ht]

theorem mem_cthickening_of_cutoff_ne_zero {K : Set (UnitAddTorus d)} (hK : K.Nonempty) {r : ℝ}
    (hr : 0 < r) {t : UnitAddTorus d} (ht : cutoff K r t ≠ 0) : t ∈ cthickening r K := by
  by_contra hc
  apply ht
  have : r < infDist t K := by
    rw [mem_cthickening_iff, not_le] at hc
    rw [infDist, ← ENNReal.ofReal_lt_iff_lt_toReal hr.le (infEdist_ne_top hK)] at *
    · exact hc
  have : 1 ≤ infDist t K / r := by rw [le_div_iff₀ hr]; linarith
  simp only [cutoff]
  exact max_eq_left (by linarith)

theorem continuous_cutoff (K : Set (UnitAddTorus d)) (r : ℝ) : Continuous (cutoff K r) :=
  continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))

theorem abs_cutoff_sub_le (K : Set (UnitAddTorus d)) {r : ℝ} (hr : 0 < r) (t t' : UnitAddTorus d) :
    |cutoff K r t - cutoff K r t'| ≤ dist t t' / r := by
  have h1 : |(1 - infDist t K / r) - (1 - infDist t' K / r)| ≤ dist t t' / r := by
    rw [show (1 - infDist t K / r) - (1 - infDist t' K / r) = (infDist t' K - infDist t K) / r by
      ring, abs_div, abs_of_pos hr]
    gcongr
    rw [abs_sub_comm]
    exact abs_sub_le_iff.2 ⟨by linarith [infDist_le_infDist_add_dist (x := t) (y := t') (s := K)],
      by linarith [infDist_le_infDist_add_dist (x := t') (y := t) (s := K), dist_comm t t']⟩
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp only [sub_self, abs_zero]; positivity) h1)

/-- `‖coordPt μ s‖ ≤ |s|`. -/
theorem dist_add_coordPt_le (t : UnitAddTorus d) (μ : d) (s : ℝ) :
    dist (t + coordPt μ s) t ≤ |s| := by
  rw [dist_self_add_left]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg s)).2 fun i => ?_
  by_cases hi : i = μ
  · subst hi
    simp only [coordPt, Pi.single_eq_same]
    exact (QuotientAddGroup.norm_mk_le_norm).trans (le_of_eq (Real.norm_eq_abs s))
  · simp [coordPt, hi]

/-! ### Cut-off families -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The cut-off function `χ_{K,r} f`. -/
def cut (K : Set (UnitAddTorus d)) (r : ℝ) (f : UnitAddTorus d → V) : UnitAddTorus d → V :=
  fun t => cutoff K r t • f t

theorem cut_eq_of_mem {K : Set (UnitAddTorus d)} (r : ℝ) (f : UnitAddTorus d → V)
    {t : UnitAddTorus d} (ht : t ∈ K) : cut K r f t = f t := by
  simp [cut, cutoff_eq_one r ht]

theorem cut_eq_zero_of_notMem {K : Set (UnitAddTorus d)} (hK : K.Nonempty) {r : ℝ} (hr : 0 < r)
    (f : UnitAddTorus d → V) {t : UnitAddTorus d} (ht : t ∉ cthickening r K) : cut K r f t = 0 := by
  have : cutoff K r t = 0 := by
    by_contra hne; exact ht (mem_cthickening_of_cutoff_ne_zero hK hr hne)
  simp [cut, this]

theorem norm_cut_le (K : Set (UnitAddTorus d)) {r : ℝ} (hr : 0 < r) (f : UnitAddTorus d → V)
    (t : UnitAddTorus d) : ‖cut K r f t‖ ≤ ‖f t‖ := by
  rw [cut, norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg K r t)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one K hr t)

theorem aestronglyMeasurable_cut (K : Set (UnitAddTorus d)) (r : ℝ) {f : UnitAddTorus d → V}
    (hf : AEStronglyMeasurable f volume) : AEStronglyMeasurable (cut K r f) volume :=
  (continuous_cutoff K r).aestronglyMeasurable.smul hf

/-- The cut-off function is bounded in `L²(𝕋^d)` by `‖f‖_{L²(Ω)}` when `cthickening r K ⊆ Ω`. -/
theorem eLpNorm_cut_le {K Ω : Set (UnitAddTorus d)} (hK : K.Nonempty) {r : ℝ} (hr : 0 < r)
    (hΩ : MeasurableSet Ω) (hKΩ : cthickening r K ⊆ Ω) (f : UnitAddTorus d → V) :
    eLpNorm (cut K r f) 2 volume ≤ eLpNorm f 2 (volume.restrict Ω) := by
  have h1 : eLpNorm (cut K r f) 2 volume ≤ eLpNorm (Ω.indicator fun t => ‖f t‖) 2 volume := by
    refine eLpNorm_mono_real fun t => ?_
    by_cases ht : t ∈ Ω
    · rw [indicator_of_mem ht]; exact norm_cut_le K hr f t
    · rw [indicator_of_notMem ht, cut_eq_zero_of_notMem hK hr f (fun h => ht (hKΩ h)), norm_zero]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hΩ, eLpNorm_norm] at h1
  exact h1

/-- **Translation modulus of a cut-off function**: for `0 ≤ s ≤ r`,
`‖τ_{se_μ}(χf) - χf‖_{L²(𝕋^d)} ≤ ‖τ_{se_μ}f - f‖_{L²(K₂)} + (s/r)‖f‖_{L²(K₂)}`,
`K₂ = cthickening (2r) K`. -/
theorem eLpNorm_cut_transl_sub_le {K : Set (UnitAddTorus d)} (hK : K.Nonempty) {r : ℝ}
    (hr : 0 < r) {f : UnitAddTorus d → V} (hf : AEStronglyMeasurable f volume) (μ : d) {s : ℝ}
    (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    eLpNorm (fun t => cut K r f (t + coordPt μ s) - cut K r f t) 2 volume ≤
      eLpNorm (fun t => f (t + coordPt μ s) - f t) 2 (volume.restrict (cthickening (2 * r) K)) +
        ENNReal.ofReal (s / r) * eLpNorm f 2 (volume.restrict (cthickening (2 * r) K)) := by
  set K₂ := cthickening (2 * r) K
  set y := coordPt μ s
  have hK₂ : MeasurableSet K₂ := isClosed_cthickening.measurableSet
  have hy : ∀ t, dist (t + y) t ≤ s := fun t => (dist_add_coordPt_le t μ s).trans (le_of_eq
    (abs_of_nonneg hs0))
  have hfy : AEStronglyMeasurable (fun t => f (t + y)) volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume y)
  set φ₁ : UnitAddTorus d → ℝ := K₂.indicator fun t => ‖f (t + y) - f t‖
  set φ₂ : UnitAddTorus d → ℝ := K₂.indicator fun t => (s / r) * ‖f t‖
  have hpt : ∀ t, ‖cut K r f (t + y) - cut K r f t‖ ≤ φ₁ t + φ₂ t := by
    intro t
    by_cases ht : t ∈ K₂
    · simp only [φ₁, φ₂, indicator_of_mem ht]
      have e : cut K r f (t + y) - cut K r f t =
          cutoff K r (t + y) • (f (t + y) - f t) + (cutoff K r (t + y) - cutoff K r t) • f t := by
        simp only [cut, smul_sub, sub_smul]; abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg K r _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one K hr _)
      · rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ((abs_cutoff_sub_le K hr _ _).trans ?_) (norm_nonneg _)
        exact div_le_div_of_nonneg_right (hy t) hr.le
    · simp only [φ₁, φ₂, indicator_of_notMem ht, add_zero]
      have h0 : cut K r f t = 0 := cut_eq_zero_of_notMem hK hr f (fun h => ht
        (cthickening_mono (by linarith) K h))
      have h1 : cut K r f (t + y) = 0 := by
        refine cut_eq_zero_of_notMem hK hr f fun h => ht ?_
        have : t ∈ cthickening (s + r) K := by
          have := mem_cthickening_of_dist_le t (t + y) s (cthickening r K) h
            (by rw [dist_comm]; exact hy t)
          exact cthickening_cthickening_subset hs0 hr.le K this
        exact cthickening_mono (by linarith) K this
      rw [h0, h1, sub_zero, norm_zero]
  have hφ₁ : AEStronglyMeasurable φ₁ volume := ((hfy.sub hf).norm).indicator hK₂
  have hφ₂ : AEStronglyMeasurable φ₂ volume :=
    ((aestronglyMeasurable_const (b := s / r)).mul hf.norm).indicator hK₂
  calc eLpNorm (fun t => cut K r f (t + y) - cut K r f t) 2 volume
      ≤ eLpNorm (fun t => φ₁ t + φ₂ t) 2 volume := eLpNorm_mono_real hpt
    _ ≤ eLpNorm φ₁ 2 volume + eLpNorm φ₂ 2 volume := eLpNorm_add_le hφ₁ hφ₂ (by norm_num)
    _ = eLpNorm (fun t => f (t + y) - f t) 2 (volume.restrict K₂) +
        ENNReal.ofReal (s / r) * eLpNorm f 2 (volume.restrict K₂) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hK₂, eLpNorm_indicator_eq_eLpNorm_restrict hK₂,
        eLpNorm_norm]
      congr 1
      rw [show (fun t => s / r * ‖f t‖) = (s / r) • fun t => ‖f t‖ by funext t; simp,
        eLpNorm_const_smul, eLpNorm_norm, Real.enorm_of_nonneg (by positivity)]

/-! ### Local Kolmogorov–Riesz -/

/-- **Local Kolmogorov–Riesz on a chart of the periodic box.**  Let `Ω ⊆ 𝕋^d` be open and
`f_i : 𝕋^d → V` (`V` finite-dimensional) a.e.-strongly measurable with `‖f_i‖_{L²(Ω)} ≤ M`.
Suppose that on every compact `K' ⊆ Ω` the coordinate translation moduli vanish: for every
`ε > 0` there are `δ > 0` and a finite exceptional set of indices outside which
`‖f_i(· + se_μ) - f_i‖_{L²(K')} ≤ ε` for all `μ` and `0 ≤ s ≤ δ`.  Then on every compact
`K ⊆ Ω` the family has, for every `ε > 0`, a finite `ε`-net in `L²(K)` drawn from the family
(relative compactness in `L²_loc(Ω)`). -/
theorem exists_net_of_local_modulus [FiniteDimensional ℝ V] {α : Type*}
    (f : α → UnitAddTorus d → V) {Ω : Set (UnitAddTorus d)} (hΩ : IsOpen Ω)
    (hmeas : ∀ i, AEStronglyMeasurable (f i) volume) (M : ℝ)
    (hbdd : ∀ i, eLpNorm (f i) 2 (volume.restrict Ω) ≤ ENNReal.ofReal M)
    (hmod : ∀ K', IsCompact K' → K' ⊆ Ω → ∀ ε > 0, ∃ δ > 0, ∃ T : Set α, T.Finite ∧
      ∀ i ∉ T, ∀ μ, ∀ s ∈ Icc (0 : ℝ) δ,
        eLpNorm (fun t => f i (t + coordPt μ s) - f i t) 2 (volume.restrict K') ≤
          ENNReal.ofReal ε)
    {K : Set (UnitAddTorus d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∀ ε > 0, ∃ J : Finset α, ∀ i, ∃ j ∈ J,
      eLpNorm (fun t => f i t - f j t) 2 (volume.restrict K) ≤ ENNReal.ofReal ε := by
  classical
  intro ε hε
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨∅, fun i => isEmptyElim i⟩
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · obtain ⟨i₀⟩ := hα
    exact ⟨{i₀}, fun i => ⟨i₀, Finset.mem_singleton_self _, by simp⟩⟩
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  set r := δ₀ / 3 with hrdef
  have hr : 0 < r := by positivity
  set K₂ := cthickening (2 * r) K
  have hK₂c : IsCompact K₂ := isClosed_cthickening.isCompact
  have hK₂Ω : K₂ ⊆ Ω := (cthickening_mono (by linarith) K).trans hsub
  have hK₁Ω : cthickening r K ⊆ Ω := (cthickening_mono (by linarith) K).trans hsub
  set Mp := max M 0
  have hbdd' : ∀ i, eLpNorm (f i) 2 (volume.restrict Ω) ≤ ENNReal.ofReal Mp := fun i =>
    (hbdd i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hcutb : ∀ i, eLpNorm (cut K r (f i)) 2 volume ≤ ENNReal.ofReal Mp := fun i =>
    (eLpNorm_cut_le hKne hr hΩ.measurableSet hK₁Ω (f i)).trans (hbdd' i)
  have hmem : ∀ i, MemLp (cut K r (f i)) 2 volume := fun i =>
    ⟨aestronglyMeasurable_cut K r (hmeas i), (hcutb i).trans_lt ENNReal.ofReal_lt_top⟩
  set G : α → Lp V 2 (volume : Measure (UnitAddTorus d)) := fun i => (hmem i).toLp _
  have hG : ∀ i, G i =ᵐ[volume] cut K r (f i) := fun i => (hmem i).coeFn_toLp
  have hGb : ∃ C, ∀ i, ‖G i‖ ≤ C := ⟨Mp, fun i => by
    rw [Lp.norm_def, eLpNorm_congr_ae (hG i)]
    exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (hcutb i)⟩
  have hGmod : ∀ ε' > 0, ∃ δ > 0, ∃ S : Set α, S.Finite ∧ ∀ i ∉ S, ∀ μ, ∀ s ∈ Icc (0 : ℝ) δ,
      ‖transl (coordPt μ s) (G i) - G i‖ ≤ ε' := by
    intro ε' hε'
    obtain ⟨δ₁, hδ₁, T, hT, hTmod⟩ := hmod K₂ hK₂c hK₂Ω (ε' / 2) (by positivity)
    refine ⟨min δ₁ (min r (ε' * r / (2 * (Mp + 1)))), by positivity, T, hT, fun i hi μ s hs => ?_⟩
    have hsδ : s ≤ δ₁ := hs.2.trans (min_le_left _ _)
    have hsr : s ≤ r := hs.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsε : s ≤ ε' * r / (2 * (Mp + 1)) := hs.2.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hae : ⇑(transl (coordPt μ s) (G i) - G i) =ᵐ[volume]
        fun t => cut K r (f i) (t + coordPt μ s) - cut K r (f i) t := by
      have hq := (measurePreserving_add_right (volume : Measure (UnitAddTorus d))
        (coordPt μ s)).quasiMeasurePreserving
      filter_upwards [Lp.coeFn_sub (transl (coordPt μ s) (G i)) (G i),
        coeFn_transl (coordPt μ s) (G i), hG i, hq.ae_eq_comp (hG i)] with t h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3]
      exact congrArg (· - _) h4
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    have hb := eLpNorm_cut_transl_sub_le hKne hr (hmeas i) μ hs.1 hsr
    have hK₂b : eLpNorm (f i) 2 (volume.restrict K₂) ≤ ENNReal.ofReal Mp :=
      (eLpNorm_mono_measure _ (Measure.restrict_mono hK₂Ω le_rfl)).trans (hbdd' i)
    have hsum : eLpNorm (fun t => cut K r (f i) (t + coordPt μ s) - cut K r (f i) t) 2 volume ≤
        ENNReal.ofReal (ε' / 2 + s / r * Mp) := by
      refine hb.trans ?_
      have hM : 0 ≤ Mp := le_max_right _ _
      rw [ENNReal.ofReal_add (half_pos hε').le (mul_nonneg (div_nonneg hs.1 hr.le) hM),
        ENNReal.ofReal_mul (div_nonneg hs.1 hr.le)]
      exact add_le_add (hTmod i hi μ s ⟨hs.1, hsδ⟩) (by gcongr)
    refine (ENNReal.toReal_le_of_le_ofReal (add_nonneg (half_pos hε').le
      (mul_nonneg (div_nonneg hs.1 hr.le) (le_max_right _ _))) hsum).trans ?_
    have : s / r * Mp ≤ ε' / 2 := by
      have hM : 0 ≤ Mp := le_max_right _ _
      rw [div_mul_eq_mul_div, div_le_iff₀ hr]
      have := mul_le_mul_of_nonneg_right hsε (by positivity : (0 : ℝ) ≤ Mp)
      have h2 : ε' * r / (2 * (Mp + 1)) * Mp ≤ ε' / 2 * r := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_pos hε' hr]
      linarith
    linarith
  have hTB := kolmogorovRiesz_torus_vector_cofinite G hGb hGmod
  obtain ⟨t, htsub, htfin, hcover⟩ := EMetric.totallyBounded_iff'.1 hTB (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε)
  have hpre : ∀ y ∈ t, ∃ j, G j = y := fun y hy => htsub hy
  choose! φ hφ using hpre
  refine ⟨htfin.toFinset.image φ, fun i => ?_⟩
  obtain ⟨y, hyt, hiy⟩ := mem_iUnion₂.1 (hcover (mem_range_self i))
  refine ⟨φ y, Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hyt), ?_⟩
  have hed : edist (G i) (G (φ y)) < ENNReal.ofReal ε := by rw [hφ y hyt]; exact hiy
  rw [Lp.edist_def] at hed
  have hK : eLpNorm (fun t => f i t - f (φ y) t) 2 (volume.restrict K) =
      eLpNorm (fun t => cut K r (f i) t - cut K r (f (φ y)) t) 2 (volume.restrict K) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' hK.isClosed.measurableSet).2
      (Eventually.of_forall fun t ht => ?_))
    simp only [cut_eq_of_mem r _ ht]
  rw [hK]
  refine ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (le_of_eq ?_)).trans hed.le
  refine eLpNorm_congr_ae ?_
  filter_upwards [hG i, hG (φ y)] with t h2 h3
  rw [Pi.sub_apply, h2, h3]

/-- Finite `ε`-nets of indices (for every `ε`) make the `L²` classes totally bounded. -/
theorem totallyBounded_of_nets {X : Type*} [MeasurableSpace X] {μ' : Measure X} {α : Type*}
    (f : α → X → V) (hmem : ∀ i, MemLp (f i) 2 μ')
    (hnet : ∀ ε > 0, ∃ J : Finset α, ∀ i, ∃ j ∈ J,
      eLpNorm (fun t => f i t - f j t) 2 μ' ≤ ENNReal.ofReal ε) :
    TotallyBounded (range fun i => (hmem i).toLp (f i)) := by
  refine EMetric.totallyBounded_iff.2 fun ε hε => ?_
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr : 0 < r := by
    rcases eq_or_lt_of_le hr0 with h | h
    · subst h; simp at hr1
    · exact h
  obtain ⟨J, hJ⟩ := hnet r hr
  refine ⟨(J : Set α).image fun j => (hmem j).toLp (f j), (J.finite_toSet.image _), ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj, hij⟩ := hJ i
  refine mem_iUnion₂.2 ⟨(hmem j).toLp (f j), ⟨j, hj, rfl⟩, ?_⟩
  rw [EMetric.mem_ball, Lp.edist_def]
  refine lt_of_le_of_lt (le_of_eq ?_) (hij.trans_lt hr2)
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hmem i).coeFn_toLp, (hmem j).coeFn_toLp] with t h1 h2
  rw [Pi.sub_apply, h1, h2]

/-- **Local Kolmogorov–Riesz, total-boundedness form**: under the hypotheses of
`exists_net_of_local_modulus`, the `L²(K)` classes of the family are totally bounded (relatively
compact) for every compact `K ⊆ Ω`. -/
theorem totallyBounded_restrict_of_local_modulus [FiniteDimensional ℝ V] {α : Type*}
    (f : α → UnitAddTorus d → V) {Ω : Set (UnitAddTorus d)} (hΩ : IsOpen Ω)
    (hmeas : ∀ i, AEStronglyMeasurable (f i) volume) (M : ℝ)
    (hbdd : ∀ i, eLpNorm (f i) 2 (volume.restrict Ω) ≤ ENNReal.ofReal M)
    (hmod : ∀ K', IsCompact K' → K' ⊆ Ω → ∀ ε > 0, ∃ δ > 0, ∃ T : Set α, T.Finite ∧
      ∀ i ∉ T, ∀ μ, ∀ s ∈ Icc (0 : ℝ) δ,
        eLpNorm (fun t => f i (t + coordPt μ s) - f i t) 2 (volume.restrict K') ≤
          ENNReal.ofReal ε)
    {K : Set (UnitAddTorus d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hmem : ∀ i, MemLp (f i) 2 (volume.restrict K)) :
    TotallyBounded (range fun i => (hmem i).toLp (f i)) :=
  totallyBounded_of_nets f hmem (exists_net_of_local_modulus f hΩ hmeas M hbdd hmod hK hKΩ)

/-- The `L²(K)` membership needed above holds for `K ⊆ Ω`. -/
theorem memLp_restrict_of_le {f : UnitAddTorus d → V} {Ω K : Set (UnitAddTorus d)}
    (hf : AEStronglyMeasurable f volume) (hKΩ : K ⊆ Ω) {M : ℝ}
    (hb : eLpNorm f 2 (volume.restrict Ω) ≤ ENNReal.ofReal M) : MemLp f 2 (volume.restrict K) :=
  ⟨hf.restrict, ((eLpNorm_mono_measure _ (Measure.restrict_mono hKΩ le_rfl)).trans hb).trans_lt
    ENNReal.ofReal_lt_top⟩

end RenewalGeometry.LocalKRTorus
