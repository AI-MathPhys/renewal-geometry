/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CoefficientAubinLionsCompactness
import RenewalGeometry.DiscreteAnalysis.PeriodicGridInterpolation

/-!
# Test
-/

open MeasureTheory Filter Topology Set

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GridAubinLions

open CoefficientAubinLions

theorem isW12Rep_zero (T : ℝ) : IsW12Rep T (fun _ => (0 : ℂ)) (fun _ => 0) :=
  ⟨MemLp.zero', fun t _ => by simp⟩

theorem isW12Rep_const_mul {T : ℝ} {c g : ℝ → ℂ} (h : IsW12Rep T c g) (a : ℂ) :
    IsW12Rep T (fun t => a * c t) (fun t => a * g t) := by
  refine ⟨h.memLp.const_mul a, fun t ht => ?_⟩
  rw [h.rep t ht, intervalIntegral.integral_const_mul, mul_add]

theorem isW12Rep_intervalIntegrable {T : ℝ} {c g : ℝ → ℂ} (h : IsW12Rep T c g) {t : ℝ}
    (ht : t ∈ Icc 0 T) : IntervalIntegrable g volume 0 t := by
  have : IsFiniteMeasure (volume.restrict (Ioc 0 T)) := by constructor; simp
  have hint : IntegrableOn g (Ioc 0 T) := h.memLp.integrable (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2
      (hint.mono_set (Ioc_subset_Ioc le_rfl ht.2))

theorem isW12Rep_add {T : ℝ} {c g c' g' : ℝ → ℂ} (h : IsW12Rep T c g) (h' : IsW12Rep T c' g') :
    IsW12Rep T (fun t => c t + c' t) (fun t => g t + g' t) := by
  refine ⟨h.memLp.add h'.memLp, fun t ht => ?_⟩
  rw [h.rep t ht, h'.rep t ht, intervalIntegral.integral_add (isW12Rep_intervalIntegrable h ht)
    (isW12Rep_intervalIntegrable h' ht)]
  ring

theorem isW12Rep_finset_sum {T : ℝ} {ι : Type*} (s : Finset ι) {c g : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, IsW12Rep T (c i) (g i)) :
    IsW12Rep T (fun t => ∑ i ∈ s, c i t) (fun t => ∑ i ∈ s, g i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isW12Rep_zero T
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact isW12Rep_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))


/-- `CoefficientAubinLions.aubinLions_coefficients` with the additional (constructed) information
that every limit coefficient `c' k` is continuous on `[0,T]` (it is a uniform limit of the
continuous `W^{1,2}` coefficients); the proof is that of `aubinLions_coefficients`. -/
theorem aubinLions_coefficients_continuous {ι : Type*} [Countable ι] {T : ℝ} (hT : 0 < T) (w : ι → ℝ)
    (hw1 : ∀ k, 1 ≤ w k) (hwfin : ∀ R, {k | w k ≤ R}.Finite)
    (c g : ℕ → ι → ℝ → ℂ) (hW : ∀ m k, IsW12Rep T (c m k) (g m k)) {B : ℝ}
    (h0s : ∀ m, Summable fun k => w k * ∫ u in Ioc 0 T, ‖c m k u‖ ^ 2)
    (h0 : ∀ m, ∑' k, w k * ∫ u in Ioc 0 T, ‖c m k u‖ ^ 2 ≤ B)
    (B1 : ι → ℝ) (h1 : ∀ m k, ∫ u in Ioc 0 T, ‖g m k u‖ ^ 2 ≤ B1 k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c' : ι → ℝ → ℂ, (∀ k, ContinuousOn (c' k) (Icc 0 T)) ∧
      (∀ m, Summable fun k => ∫ u in Ioc 0 T, ‖c (φ m) k u - c' k u‖ ^ 2) ∧
      Tendsto (fun m => ∑' k, ∫ u in Ioc 0 T, ‖c (φ m) k u - c' k u‖ ^ 2) atTop (𝓝 0) := by
  classical
  set a : ℕ → ι → ℝ := fun m k => ∫ u in Ioc 0 T, ‖c m k u‖ ^ 2 with ha_def
  have ha0 : ∀ m k, 0 ≤ a m k := fun m k => integral_nonneg fun _ => by positivity
  have hw0 : ∀ k, 0 < w k := fun k => lt_of_lt_of_le one_pos (hw1 k)
  have hwa : ∀ m k, w k * a m k ≤ B := fun m k =>
    ((h0s m).le_tsum k fun j _ => mul_nonneg (hw0 j).le (ha0 m j)).trans (h0 m)
  have hB : 0 ≤ B := (tsum_nonneg fun k => mul_nonneg (hw0 k).le (ha0 0 k)).trans (h0 0)
  have haB : ∀ m k, a m k ≤ B := fun m k => by
    have := hwa m k
    nlinarith [hw1 k, ha0 m k]
  obtain ⟨φ, hφ, c', hc'⟩ := exists_subseq_tendstoUniformlyOn hT c g hW (fun _ => B)
    B1 haB h1
  refine ⟨φ, hφ, c', fun k => (hc' k).1, ?_⟩
  -- integrability
  have hcont : ∀ m k, ContinuousOn (c m k) (Icc 0 T) := fun m k => (hW m k).continuousOn
  have hintsq : ∀ f : ℝ → ℂ, ContinuousOn f (Icc 0 T) →
      IntegrableOn (fun u => ‖f u‖ ^ 2) (Ioc 0 T) := fun f hf =>
    ((hf.norm.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  set d : ℕ → ι → ℝ := fun m k => ∫ u in Ioc 0 T, ‖c (φ m) k u - c' k u‖ ^ 2 with hd_def
  set A : ι → ℝ := fun k => ∫ u in Ioc 0 T, ‖c' k u‖ ^ 2 with hA_def
  have hd0 : ∀ m k, 0 ≤ d m k := fun m k => integral_nonneg fun _ => by positivity
  have hA0 : ∀ k, 0 ≤ A k := fun k => integral_nonneg fun _ => by positivity
  have hdiffcont : ∀ m k, ContinuousOn (fun u => c (φ m) k u - c' k u) (Icc 0 T) :=
    fun m k => (hcont _ k).sub (hc' k).1
  have hd_le : ∀ m k, d m k ≤ 2 * a (φ m) k + 2 * A k := by
    intro m k
    have := integral_mono (μ := volume.restrict (Ioc 0 T)) (hintsq _ (hdiffcont m k))
      (((hintsq _ (hcont (φ m) k)).const_mul 2).add ((hintsq _ (hc' k).1).const_mul 2))
      fun u => norm_sub_sq_le_two (c (φ m) k u) (c' k u)
    simp only [Pi.add_apply] at this
    rw [integral_add ((hintsq _ (hcont (φ m) k)).const_mul 2)
      ((hintsq _ (hc' k).1).const_mul 2), integral_const_mul, integral_const_mul] at this
    exact this
  have hA_le : ∀ m k, A k ≤ 2 * a (φ m) k + 2 * d m k := by
    intro m k
    have := integral_mono (μ := volume.restrict (Ioc 0 T)) (hintsq _ (hc' k).1)
      (((hintsq _ (hcont (φ m) k)).const_mul 2).add ((hintsq _ (hdiffcont m k)).const_mul 2))
      fun u => by
        have := norm_sub_sq_le_two (c (φ m) k u) (c (φ m) k u - c' k u)
        simpa using this
    simp only [Pi.add_apply] at this
    rw [integral_add ((hintsq _ (hcont (φ m) k)).const_mul 2)
      ((hintsq _ (hdiffcont m k)).const_mul 2), integral_const_mul, integral_const_mul] at this
    exact this
  -- per-mode convergence
  have hd_tend : ∀ k, Tendsto (fun m => d m k) atTop (𝓝 0) := by
    intro k
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ := Real.sqrt (ε / (2 * T))
    have hδ : 0 < δ := Real.sqrt_pos.2 (by positivity)
    obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 (hc' k).2) δ hδ)
    refine ⟨M, fun m hm => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 m k)]
    have hb : ∀ t ∈ Icc 0 T, ‖c (φ m) k t - c' k t‖ ≤ δ := fun t ht => by
      have := hM m hm t ht
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this.le
    refine lt_of_le_of_lt (setIntegral_sq_le_of_norm_le hT.le hb) ?_
    rw [Real.sq_sqrt (by positivity)]
    rw [div_mul_eq_mul_div, mul_comm, ← div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  -- the limit energy is summable
  have hAsum_fin : ∀ F : Finset ι, ∑ k ∈ F, w k * A k ≤ 2 * B := by
    intro F
    have hlim : Tendsto (fun m => 2 * B + 2 * ∑ k ∈ F, w k * d m k) atTop (𝓝 (2 * B)) := by
      have := (tendsto_finsetSum F fun k _ => (hd_tend k).const_mul (w k)).const_mul 2
      simpa using this.const_add (2 * B)
    refine ge_of_tendsto' hlim fun m => ?_
    calc ∑ k ∈ F, w k * A k ≤ ∑ k ∈ F, (2 * (w k * a (φ m) k) + 2 * (w k * d m k)) :=
          Finset.sum_le_sum fun k _ => by
            have := mul_le_mul_of_nonneg_left (hA_le m k) (hw0 k).le; linarith
      _ = 2 * ∑ k ∈ F, w k * a (φ m) k + 2 * ∑ k ∈ F, w k * d m k := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * B + 2 * ∑ k ∈ F, w k * d m k := by
          gcongr
          exact ((h0s (φ m)).sum_le_tsum F fun j _ => mul_nonneg (hw0 j).le (ha0 _ j)).trans
            (h0 (φ m))
  have hwA0 : 0 ≤ fun k => w k * A k := fun k => mul_nonneg (hw0 k).le (hA0 k)
  have hAsum : Summable fun k => w k * A k := summable_of_sum_le hwA0 hAsum_fin
  have hAtsum : ∑' k, w k * A k ≤ 2 * B := Real.tsum_le_of_sum_le hwA0 hAsum_fin
  -- summability of the errors
  have hdom : ∀ m k, d m k ≤ 2 * (w k * a (φ m) k) + 2 * (w k * A k) := fun m k => by
    have := hd_le m k
    have h1' : a (φ m) k ≤ w k * a (φ m) k := le_mul_of_one_le_left (ha0 _ k) (hw1 k)
    have h2' : A k ≤ w k * A k := le_mul_of_one_le_left (hA0 k) (hw1 k)
    linarith
  have hsum2 : ∀ m, Summable fun k => 2 * (w k * a (φ m) k) + 2 * (w k * A k) := fun m =>
    ((h0s (φ m)).mul_left 2).add (hAsum.mul_left 2)
  have hdsum : ∀ m, Summable fun k => d m k := fun m =>
    Summable.of_nonneg_of_le (hd0 m) (hdom m) (hsum2 m)
  refine ⟨hdsum, ?_⟩
  -- tail argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R := 12 * B / ε + 1 with hR
  have hRpos : 0 < R := by positivity
  set Fs := (hwfin R).toFinset
  have hfin := tendsto_finsetSum Fs fun k _ => hd_tend k
  simp only [Finset.sum_const_zero] at hfin
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hfin (ε / 2) (by positivity)
  refine ⟨M, fun m hm => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg (hd0 m))]
  have hhead := hM m hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun k _ => hd0 m k)] at hhead
  have htail : ∑' k : ↑((Fs : Set ι)ᶜ), d m k ≤ 6 * B / R := by
    have hle : ∀ k : ↑((Fs : Set ι)ᶜ), d m k ≤
        (2 / R) * (w k * a (φ m) k + w k * A k) := by
      rintro ⟨k, hk⟩
      have hwk : R < w k := by
        simp only [Fs, Set.mem_compl_iff, Finset.mem_coe,
          Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hk
        exact hk
      have e1 : a (φ m) k ≤ (w k * a (φ m) k) / R := by
        rw [le_div_iff₀ hRpos]; nlinarith [ha0 (φ m) k]
      have e2 : A k ≤ (w k * A k) / R := by
        rw [le_div_iff₀ hRpos]; nlinarith [hA0 k]
      have := hd_le m k
      calc d m k ≤ 2 * a (φ m) k + 2 * A k := this
        _ ≤ 2 * ((w k * a (φ m) k) / R) + 2 * ((w k * A k) / R) := by linarith
        _ = (2 / R) * (w k * a (φ m) k + w k * A k) := by ring
    have hS : Summable fun k => (2 / R) * (w k * a (φ m) k + w k * A k) :=
      ((h0s (φ m)).add hAsum).mul_left _
    calc ∑' k : ↑((Fs : Set ι)ᶜ), d m k
        ≤ ∑' k : ↑((Fs : Set ι)ᶜ), (2 / R) * (w k * a (φ m) k + w k * A k) :=
          Summable.tsum_le_tsum hle ((hdsum m).subtype _) (hS.subtype _)
      _ ≤ ∑' k, (2 / R) * (w k * a (φ m) k + w k * A k) := by
          rw [← hS.sum_add_tsum_compl (s := Fs)]
          have : 0 ≤ ∑ k ∈ Fs, (2 / R) * (w k * a (φ m) k + w k * A k) :=
            Finset.sum_nonneg fun k _ => by
              have := mul_nonneg (hw0 k).le (ha0 (φ m) k)
              have := mul_nonneg (hw0 k).le (hA0 k)
              positivity
          linarith
      _ = (2 / R) * (∑' k, w k * a (φ m) k + ∑' k, w k * A k) := by
          rw [tsum_mul_left, (h0s (φ m)).tsum_add hAsum]
      _ ≤ (2 / R) * (B + 2 * B) := by gcongr; exact h0 (φ m)
      _ = 6 * B / R := by ring
  have hsplit := (hdsum m).sum_add_tsum_compl (s := Fs)
  have hRB : 6 * B / R ≤ ε / 2 := by
    rw [div_le_iff₀ hRpos, hR]
    field_simp
    nlinarith
  rw [← hsplit]
  linarith


/-! ### Grid arrays with a `W^{1,2}` time representation -/

section Grid

open PeriodicGridSobolev LatticeTorusPlancherel UnitAddTorus

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

variable {N : ℕ} [NeZero N]

/-- A time-dependent grid array `u : ℝ → (ℤ/N)³ → ℂ` has weak time derivative `g` on `[0,T]`:
every grid value is `W^{1,2}(0,T)`, `u(t,x) = u(0,x) + ∫₀ᵗ g(s,x) ds`, `g(·,x) ∈ L²(0,T)`. -/
def IsGridW12Rep (T : ℝ) (u g : ℝ → Grid N → ℂ) : Prop :=
  ∀ x, IsW12Rep T (fun t => u t x) (fun t => g t x)

theorem IsGridW12Rep.linear {T : ℝ} {u g : ℝ → Grid N → ℂ} (h : IsGridW12Rep T u g)
    (β : Grid N → ℂ) :
    IsW12Rep T (fun t => ∑ x, β x * u t x) (fun t => ∑ x, β x * g t x) :=
  isW12Rep_finset_sum _ fun x _ => isW12Rep_const_mul (h x) (β x)

theorem dft_eq_sum (u : Grid N → ℂ) (k : Grid N) :
    dft u k = ∑ x, (((N : ℂ) ^ 3)⁻¹ * (starRingEnd ℂ) (latticeChar k x)) * u x := by
  simp only [dft, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem IsGridW12Rep.dft {T : ℝ} {u g : ℝ → Grid N → ℂ} (h : IsGridW12Rep T u g)
    (k : Grid N) : IsW12Rep T (fun t => dft (u t) k) (fun t => dft (g t) k) := by
  simp only [dft_eq_sum]
  exact h.linear _

/-- The Fourier coefficients of the interpolants inherit the `W^{1,2}` time representation. -/
theorem IsGridW12Rep.coeff {T : ℝ} {u g : ℝ → Grid N → ℂ} (h : IsGridW12Rep T u g)
    (n : Fin 3 → ℤ) :
    IsW12Rep T (fun t => mFourierCoeff (⇑(interp (u t))) n)
      (fun t => mFourierCoeff (⇑(interp (g t))) n) := by
  simp only [mFourierCoeff_interp]
  refine isW12Rep_finset_sum _ fun k _ => ?_
  by_cases hk : freqVec k = n
  · simp only [hk, ite_true]; exact h.dft k
  · simp only [hk, ite_false]; exact isW12Rep_zero T

theorem IsGridW12Rep.continuousOn {T : ℝ} {u g : ℝ → Grid N → ℂ} (h : IsGridW12Rep T u g) :
    ContinuousOn u (Icc 0 T) :=
  continuousOn_pi.2 fun x => (h x).continuousOn

theorem continuous_dft (k : Grid N) : Continuous fun u : Grid N → ℂ => dft u k := by
  simp only [dft_eq_sum]
  fun_prop


/-! ### Trigonometric weights and negative norms -/

/-- The trigonometric `H¹` weight `1 + 4π²|n|²` on `ℤ³`. -/
def tW (n : Fin 3 → ℤ) : ℝ := 1 + ∑ i, (2 * Real.pi * n i) ^ 2

theorem one_le_tW (n : Fin 3 → ℤ) : 1 ≤ tW n := by
  unfold tW; have : 0 ≤ ∑ i, (2 * Real.pi * n i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem tW_pos (n : Fin 3 → ℤ) : 0 < tW n := lt_of_lt_of_le one_pos (one_le_tW n)

/-- The squared trigonometric `H^{-s}(𝕋³)` norm
`‖f‖²_{H^{-s}} = Σ_{n ∈ ℤ³} (1 + 4π²|n|²)^{-s} |f̂(n)|²`. -/
def trigNegSq (s : ℕ) (f : UnitAddTorus (Fin 3) → ℂ) : ℝ :=
  ∑' n, (tW n ^ s)⁻¹ * ‖mFourierCoeff f n‖ ^ 2

theorem trigNegSq_interp (s : ℕ) (u : Grid N → ℂ) :
    trigNegSq s (interp u) = ∑ k, (tW (freqVec k) ^ s)⁻¹ * ‖dft u k‖ ^ 2 :=
  tsum_interp _ u

theorem coordForm_nonneg (u : Grid N → ℂ) : 0 ≤ coordForm u :=
  Finset.sum_nonneg fun i _ => gridNormSq_nonneg _

/-- The interpolant's trigonometric `H¹` norm is controlled by the grid `H¹` norm:
`Σ_k (1 + 4π²|k̃|²) |û(k)|² ≤ 3 (‖u‖_h² + Σ_i ‖D_i⁺u‖_h²)`, uniformly in `N`. -/
theorem sum_tW_le (u : Grid N → ℂ) :
    ∑ k, tW (freqVec k) * ‖dft u k‖ ^ 2 ≤ 3 * (gridNormSq u + coordForm u) := by
  have e : ∑ k, tW (freqVec k) * ‖dft u k‖ ^ 2 = gridNormSq u + trigGradSq (interp u) := by
    rw [gridNormSq_eq_sum_dft, trigGradSq_interp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold tW; ring
  rw [e]
  have h1 := trigGradSq_interp_le_coordForm u
  have h2 := coordForm_nonneg u
  have h3 := gridNormSq_nonneg u
  have hpi : (2 / Real.pi) ^ 2 * trigGradSq (interp u) = trigGradSq (interp u) * (4 / Real.pi ^ 2) := by
    ring
  have hπ := Real.pi_gt_three
  have hπ' := Real.pi_lt_d2
  have hT : 0 ≤ trigGradSq (interp u) := by
    rw [trigGradSq_interp]; exact Finset.sum_nonneg fun k _ => by positivity
  have : trigGradSq (interp u) ≤ 3 * coordForm u := by
    rw [hpi] at h1
    have hpp : 0 < Real.pi ^ 2 := by positivity
    have key : trigGradSq (interp u) =
        (Real.pi ^ 2 / 4) * (trigGradSq (interp u) * (4 / Real.pi ^ 2)) := by
      field_simp
    rw [key]
    have hp12 : Real.pi ^ 2 / 4 ≤ 3 := by nlinarith
    calc (Real.pi ^ 2 / 4) * (trigGradSq (interp u) * (4 / Real.pi ^ 2))
        ≤ (Real.pi ^ 2 / 4) * coordForm u := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 3 * coordForm u := mul_le_mul_of_nonneg_right hp12 h2
  linarith


theorem continuous_gridNormSq : Continuous (gridNormSq : (Grid N → ℂ) → ℝ) := by
  have : (gridNormSq : (Grid N → ℂ) → ℝ) = fun u => ∑ k, ‖dft u k‖ ^ 2 :=
    funext gridNormSq_eq_sum_dft
  rw [this]
  exact continuous_finsetSum _ fun k _ => ((continuous_dft k).norm.pow 2)

theorem continuous_coordForm : Continuous (coordForm : (Grid N → ℂ) → ℝ) := by
  have : (coordForm : (Grid N → ℂ) → ℝ) =
      fun u => ∑ k, (∑ i, ‖sym i k‖ ^ 2) * ‖dft u k‖ ^ 2 := funext coordForm_eq
  rw [this]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul ((continuous_dft k).norm.pow 2)

theorem integrableOn_of_continuousOn {f : ℝ → ℝ} {T : ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    IntegrableOn f (Ioc 0 T) :=
  (hf.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- The weight sublevel sets `{(c, n) : 1 + 4π²|n|² ≤ R}` are finite. -/
theorem finite_tW_le (C : Type*) [Finite C] (R : ℝ) :
    {p : C × (Fin 3 → ℤ) | tW p.2 ≤ R}.Finite := by
  have hfin : (Set.univ ×ˢ Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-⌈R⌉) ⌈R⌉) :
      Set (C × (Fin 3 → ℤ))).Finite :=
    Set.finite_univ.prod (Set.Finite.pi fun _ => Set.finite_Icc _ _)
  refine hfin.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp
  refine ⟨Set.mem_univ _, fun i _ => ?_⟩
  have hsum : (2 * Real.pi * p.2 i) ^ 2 ≤ R := by
    have : (2 * Real.pi * p.2 i) ^ 2 ≤ ∑ j, (2 * Real.pi * p.2 j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (2 * Real.pi * p.2 j) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    unfold tW at hp; linarith
  have hsq : ((p.2 i : ℤ) : ℝ) ^ 2 ≤ R := by
    have hπ := Real.pi_gt_three
    have : ((p.2 i : ℤ) : ℝ) ^ 2 ≤ (2 * Real.pi * p.2 i) ^ 2 := by
      rw [mul_pow]
      have h4 : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith
      nlinarith [sq_nonneg ((p.2 i : ℤ) : ℝ)]
    linarith
  have hR := Int.le_ceil R
  have h1 : p.2 i ≤ p.2 i ^ 2 := Int.le_self_sq _
  have h2 : -p.2 i ≤ p.2 i ^ 2 := by have := Int.le_self_sq (-p.2 i); simpa using this
  have h1' : ((p.2 i : ℤ) : ℝ) ≤ ⌈R⌉ := by
    have : ((p.2 i : ℤ) : ℝ) ≤ ((p.2 i ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have h2' : -((p.2 i : ℤ) : ℝ) ≤ ⌈R⌉ := by
    have : ((-p.2 i : ℤ) : ℝ) ≤ ((p.2 i ^ 2 : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at this; linarith
  constructor
  · have : (-(⌈R⌉ : ℤ) : ℝ) ≤ ((p.2 i : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · exact_mod_cast h1'


theorem coeff_interp_freqVec_or (u : Grid N → ℂ) (n : Fin 3 → ℤ) :
    (∃ k, freqVec k = n ∧ mFourierCoeff (⇑(interp u)) n = dft u k) ∨
      (n ∉ Set.range (freqVec (N := N)) ∧ mFourierCoeff (⇑(interp u)) n = 0) := by
  by_cases hn : n ∈ Set.range (freqVec (N := N))
  · obtain ⟨k, rfl⟩ := hn
    exact Or.inl ⟨k, rfl, mFourierCoeff_interp_freqVec u k⟩
  · exact Or.inr ⟨hn, mFourierCoeff_interp_of_not_mem u n hn⟩

section Budget

variable {C : Type*} [Fintype C]

/-- The finite set of `(component, frequency)` pairs carrying the interpolants' coefficients. -/
def modeSet (C : Type*) [Fintype C] (N : ℕ) [NeZero N] : Finset (C × (Fin 3 → ℤ)) :=
  (Finset.univ : Finset C) ×ˢ ((Finset.univ : Finset (Grid N)).image freqVec)

theorem coeff_eq_zero_of_not_mem_modeSet (u : Grid N → ℂ) {p : C × (Fin 3 → ℤ)}
    (hp : p ∉ modeSet C N) : mFourierCoeff (⇑(interp u)) p.2 = 0 := by
  have hn : p.2 ∉ Set.range (freqVec (N := N)) := by
    rintro ⟨k, hk⟩
    exact hp (Finset.mem_product.2 ⟨Finset.mem_univ _, hk ▸ Finset.mem_image_of_mem _
      (Finset.mem_univ k)⟩)
  exact mFourierCoeff_interp_of_not_mem _ _ hn

/-- Spatial budget in coefficient form: the `L²_t H¹` coefficient energy of the interpolants is
at most `3 ∫₀ᵀ Σ_c (‖U‖_h² + Σ_i ‖D_i⁺U‖_h²)`. -/
theorem coeff_energy_le {T : ℝ} (U G : ℝ → C → Grid N → ℂ)
    (hW : ∀ c, IsGridW12Rep T (fun t => U t c) (fun t => G t c)) :
    (Summable fun p : C × (Fin 3 → ℤ) =>
      tW p.2 * ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U t p.1))) p.2‖ ^ 2) ∧
    ∑' p : C × (Fin 3 → ℤ), tW p.2 * ∫ t in Ioc 0 T,
        ‖mFourierCoeff (⇑(interp (U t p.1))) p.2‖ ^ 2 ≤
      3 * ∫ t in Ioc 0 T, ∑ c, (gridNormSq (U t c) + coordForm (U t c)) := by
  classical
  have hcont : ∀ c, ContinuousOn (fun t => U t c) (Icc 0 T) := fun c => (hW c).continuousOn
  have hdftint : ∀ c (k : Grid N), IntegrableOn (fun t => ‖dft (U t c) k‖ ^ 2) (Ioc 0 T) :=
    fun c k => integrableOn_of_continuousOn
      ((((continuous_dft k).comp_continuousOn (hcont c)).norm).pow 2)
  have hterm0 : ∀ p ∉ modeSet C N,
      tW p.2 * ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U t p.1))) p.2‖ ^ 2 = 0 := by
    intro p hp
    have : ∀ t, mFourierCoeff (⇑(interp (U t p.1))) p.2 = 0 := fun t =>
      coeff_eq_zero_of_not_mem_modeSet _ hp
    simp only [this, norm_zero]
    simp
  refine ⟨summable_of_ne_finset_zero (s := modeSet C N) hterm0, ?_⟩
  rw [tsum_eq_sum (s := modeSet C N) hterm0, modeSet, Finset.sum_product]
  have e1 : ∀ c, ∑ n ∈ (Finset.univ : Finset (Grid N)).image freqVec,
      tW (c, n).2 * ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U t (c, n).1))) (c, n).2‖ ^ 2 =
      ∫ t in Ioc 0 T, ∑ k, tW (freqVec k) * ‖dft (U t c) k‖ ^ 2 := by
    intro c
    rw [Finset.sum_image fun a _ b _ h => freqVec_injective h,
      integral_finsetSum _ fun k _ => (hdftint c k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    simp only [mFourierCoeff_interp_freqVec]
  simp only [e1]
  rw [← integral_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun k _ => (hdftint c k).const_mul _]
  have hRint : IntegrableOn
      (fun t => ∑ c, (gridNormSq (U t c) + coordForm (U t c))) (Ioc 0 T) :=
    integrableOn_of_continuousOn (continuousOn_finsetSum _ fun c _ =>
      (continuous_gridNormSq.comp_continuousOn (hcont c)).add
        (continuous_coordForm.comp_continuousOn (hcont c)))
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun t => ?_) (hRint.const_mul 3)
    (ae_of_all _ fun t => ?_)
  · exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (tW_pos _).le (sq_nonneg _)
  · simp only
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => sum_tW_le _

theorem trigNegSq_nonneg (s : ℕ) (f : UnitAddTorus (Fin 3) → ℂ) : 0 ≤ trigNegSq s f :=
  tsum_nonneg fun n => mul_nonneg (inv_nonneg.2 (pow_nonneg (tW_pos n).le _)) (sq_nonneg _)

/-- Per-mode time-derivative budget: a single coefficient of the interpolated time derivative
satisfies `∫₀ᵀ |ĝ_n|² ≤ (1 + 4π²|n|²)^s ∫₀ᵀ Σ_c ‖𝓘_h G‖²_{H^{-s}}`. -/
theorem coeff_deriv_le {T : ℝ} (U G : ℝ → C → Grid N → ℂ)
    (hW : ∀ c, IsGridW12Rep T (fun t => U t c) (fun t => G t c)) (s : ℕ)
    (p : C × (Fin 3 → ℤ)) :
    ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (G t p.1))) p.2‖ ^ 2 ≤
      tW p.2 ^ s * ∫ t in Ioc 0 T, ∑ c, trigNegSq s (interp (G t c)) := by
  classical
  have hpos : 0 < tW p.2 ^ s := pow_pos (tW_pos _) _
  have hRnn : 0 ≤ ∫ t in Ioc 0 T, ∑ c, trigNegSq s (interp (G t c)) :=
    integral_nonneg fun t => Finset.sum_nonneg fun c _ => trigNegSq_nonneg _ _
  rcases coeff_interp_freqVec_or (G 0 p.1) p.2 with ⟨k, hk, -⟩ | ⟨hn, -⟩
  · have hg : ∀ t, mFourierCoeff (⇑(interp (G t p.1))) p.2 = dft (G t p.1) k := fun t => by
      rw [← hk, mFourierCoeff_interp_freqVec]
    simp only [hg]
    have hgint : ∀ c (k' : Grid N),
        IntegrableOn (fun t => ‖dft (G t c) k'‖ ^ 2) (Ioc 0 T) := fun c k' =>
      ((hW c).dft k').memLp.norm.integrable_sq
    have hle : ∀ t, ‖dft (G t p.1) k‖ ^ 2 ≤
        tW p.2 ^ s * ∑ c, trigNegSq s (interp (G t c)) := by
      intro t
      simp only [trigNegSq_interp]
      have hsingle : (tW (freqVec k) ^ s)⁻¹ * ‖dft (G t p.1) k‖ ^ 2 ≤
          ∑ c, ∑ k', (tW (freqVec k') ^ s)⁻¹ * ‖dft (G t c) k'‖ ^ 2 := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun c => ∑ k',
          (tW (freqVec k') ^ s)⁻¹ * ‖dft (G t c) k'‖ ^ 2) (fun c _ =>
            Finset.sum_nonneg fun k' _ => mul_nonneg (inv_nonneg.2
              (pow_nonneg (tW_pos _).le _)) (sq_nonneg _)) (Finset.mem_univ p.1))
        exact Finset.single_le_sum (f := fun k' =>
          (tW (freqVec k') ^ s)⁻¹ * ‖dft (G t p.1) k'‖ ^ 2) (fun k' _ =>
            mul_nonneg (inv_nonneg.2 (pow_nonneg (tW_pos _).le _)) (sq_nonneg _))
            (Finset.mem_univ k)
      rw [hk] at hsingle
      calc ‖dft (G t p.1) k‖ ^ 2
          = tW p.2 ^ s * ((tW p.2 ^ s)⁻¹ * ‖dft (G t p.1) k‖ ^ 2) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hsingle hpos.le
    have hRint : IntegrableOn (fun t => ∑ c, trigNegSq s (interp (G t c))) (Ioc 0 T) := by
      simp only [trigNegSq_interp]
      exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun k' _ =>
        (hgint c k').const_mul _
    rw [← integral_const_mul]
    exact integral_mono (hgint p.1 k) (hRint.const_mul _) hle
  · have hg : ∀ t, mFourierCoeff (⇑(interp (G t p.1))) p.2 = 0 := fun t =>
      mFourierCoeff_interp_of_not_mem _ _ hn
    simp only [hg, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    exact mul_nonneg hpos.le hRnn

end Budget

/-- **Grid Aubin–Lions–Simon theorem, coefficient form.**  Let `U m t c` be time-dependent
periodic grid arrays (`N m` points per axis, finitely many components `c`) with weak time
derivatives `G m t c` (`IsGridW12Rep`), bounded uniformly in `m` in `L²_t H¹_h`
(`∫₀ᵀ Σ_c (‖U‖_h² + Σ_i ‖D_i⁺U‖_h²) ≤ B`) and with interpolated time derivatives bounded in
`L²_t H^{-s}_x` (`∫₀ᵀ Σ_c ‖𝓘_h G‖²_{H^{-s}} ≤ B₁`).  Then the Fourier coefficients of the
interpolants `𝓘_h U` have a subsequence converging strongly in `L²_t ℓ²_{(c,n)}`. -/
theorem gridAubinLions_coeff {C : Type*} [Fintype C] {N : ℕ → ℕ} [∀ m, NeZero (N m)]
    {T : ℝ} (hT : 0 < T) (U G : ∀ m, ℝ → C → Grid (N m) → ℂ)
    (hW : ∀ m c, IsGridW12Rep T (fun t => U m t c) (fun t => G m t c)) (s : ℕ) {B B1 : ℝ}
    (hB : ∀ m, ∫ t in Ioc 0 T, ∑ c, (gridNormSq (U m t c) + coordForm (U m t c)) ≤ B)
    (hB1 : ∀ m, ∫ t in Ioc 0 T, ∑ c, trigNegSq s (interp (G m t c)) ≤ B1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c' : C × (Fin 3 → ℤ) → ℝ → ℂ,
      (∀ p, ContinuousOn (c' p) (Icc 0 T)) ∧
      (∀ m, Summable fun p : C × (Fin 3 → ℤ) =>
        ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U (φ m) t p.1))) p.2 - c' p t‖ ^ 2) ∧
      Tendsto (fun m => ∑' p : C × (Fin 3 → ℤ),
        ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U (φ m) t p.1))) p.2 - c' p t‖ ^ 2)
        atTop (𝓝 0) := by
  have hWc : ∀ m (p : C × (Fin 3 → ℤ)),
      IsW12Rep T (fun t => mFourierCoeff (⇑(interp (U m t p.1))) p.2)
        (fun t => mFourierCoeff (⇑(interp (G m t p.1))) p.2) := fun m p =>
    (hW m p.1).coeff p.2
  have h0 : ∀ m, ∑' p : C × (Fin 3 → ℤ), tW p.2 * ∫ t in Ioc 0 T,
      ‖mFourierCoeff (⇑(interp (U m t p.1))) p.2‖ ^ 2 ≤ 3 * B := fun m =>
    (coeff_energy_le (U m) (G m) (hW m)).2.trans (by linarith [hB m])
  have hB1nn : 0 ≤ B1 := le_trans (integral_nonneg fun t =>
    Finset.sum_nonneg fun c _ => trigNegSq_nonneg _ _) (hB1 0)
  have h1 : ∀ m (p : C × (Fin 3 → ℤ)), ∫ t in Ioc 0 T,
      ‖mFourierCoeff (⇑(interp (G m t p.1))) p.2‖ ^ 2 ≤ tW p.2 ^ s * B1 := fun m p =>
    (coeff_deriv_le (U m) (G m) (hW m) s p).trans
      (mul_le_mul_of_nonneg_left (hB1 m) (pow_nonneg (tW_pos _).le _))
  exact aubinLions_coefficients_continuous (ι := C × (Fin 3 → ℤ)) hT (fun p => tW p.2)
    (fun p => one_le_tW p.2) (fun R => finite_tW_le C R)
    (fun m p t => mFourierCoeff (⇑(interp (U m t p.1))) p.2)
    (fun m p t => mFourierCoeff (⇑(interp (G m t p.1))) p.2) hWc
    (fun m => (coeff_energy_le (U m) (G m) (hW m)).1) h0 (fun p => tW p.2 ^ s * B1) h1


/-! ### From coefficients to the space-time field: Parseval and Tonelli -/

section Field

/-- The space-time measure of the cylinder `(0,T] × 𝕋³` (Lebesgue measure in time, normalized
Haar measure on the unit torus). -/
def cylMeasure (T : ℝ) : Measure (ℝ × UnitAddTorus (Fin 3)) :=
  (volume.restrict (Ioc 0 T)).prod volume

instance (T : ℝ) : IsFiniteMeasure (cylMeasure T) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) := by constructor; simp
  unfold cylMeasure; infer_instance

/-- The space-time trigonometric interpolant `(t, x) ↦ 𝓘_h u(t)(x)` of a time-dependent grid
array. -/
def field (u : ℝ → Grid N → ℂ) : ℝ × UnitAddTorus (Fin 3) → ℂ := fun p => interp (u p.1) p.2

theorem field_eq_sum (u : ℝ → Grid N → ℂ) (p : ℝ × UnitAddTorus (Fin 3)) :
    field u p = ∑ k, dft (u p.1) k * mFourier (freqVec k) p.2 := by
  simp only [field, interp, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

theorem ae_cylMeasure_mem (T : ℝ) : ∀ᵐ p ∂cylMeasure T, p.1 ∈ Ioc 0 T :=
  (Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioc)

theorem norm_mFourier_apply (n : Fin 3 → ℤ) (x : UnitAddTorus (Fin 3)) :
    ‖mFourier n x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod]
  exact Finset.prod_eq_one fun i _ => by
    rw [fourier_apply]; exact Circle.norm_coe _

/-- The space-time interpolant of a grid array continuous on `[0,T]` is in `L²((0,T] × 𝕋³)`. -/
theorem memLp_field {T : ℝ} {u : ℝ → Grid N → ℂ} (hu : ContinuousOn u (Icc 0 T)) :
    MemLp (field u) 2 (cylMeasure T) := by
  have hdc : ∀ k, ContinuousOn (fun t => dft (u t) k) (Icc 0 T) := fun k =>
    (continuous_dft k).comp_continuousOn hu
  have hmeas : AEStronglyMeasurable (field u) (cylMeasure T) := by
    have : field u = fun p => ∑ k, dft (u p.1) k * mFourier (freqVec k) p.2 :=
      funext (field_eq_sum u)
    rw [this]
    refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (((hdc k).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc).comp_fst
    · exact ((mFourier (freqVec k)).continuous.comp continuous_snd).aestronglyMeasurable
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_finsetSum (Finset.univ : Finset (Grid N)) fun k _ => (hdc k).norm)
  refine MemLp.of_bound hmeas M ?_
  filter_upwards [ae_cylMeasure_mem T] with p hp
  rw [field_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  have := hM p.1 (Ioc_subset_Icc_self hp)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)] at this
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_mFourier_apply, mul_one]

/-- Parseval on the unit torus for a continuous function. -/
theorem integral_norm_sq_eq_tsum (f : C(UnitAddTorus (Fin 3), ℂ)) :
    ∫ x, ‖f x‖ ^ 2 = ∑' n, ‖mFourierCoeff (⇑f) n‖ ^ 2 := by
  have h := hasSum_sq_mFourierCoeff (f.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp] at h
  rw [h.tsum_eq]
  exact integral_congr_ae ((f.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)).mono fun x hx => by
    simp only [hx])

theorem mFourierCoeff_sub (f g : C(UnitAddTorus (Fin 3), ℂ)) (n : Fin 3 → ℤ) :
    mFourierCoeff (⇑(f - g)) n = mFourierCoeff (⇑f) n - mFourierCoeff (⇑g) n := by
  rw [← mFourierCoeff_toLp, ← mFourierCoeff_toLp f, ← mFourierCoeff_toLp g,
    ← mFourierBasis_repr, ← mFourierBasis_repr, ← mFourierBasis_repr, map_sub, map_sub]
  rfl


theorem continuousOn_coeff {s : Set ℝ} {u : ℝ → Grid N → ℂ} (hu : ContinuousOn u s)
    (n : Fin 3 → ℤ) : ContinuousOn (fun t => mFourierCoeff (⇑(interp (u t))) n) s := by
  simp only [mFourierCoeff_interp]
  refine continuousOn_finsetSum _ fun k _ => ?_
  by_cases hk : freqVec k = n
  · simp only [hk, ite_true]; exact (continuous_dft k).comp_continuousOn hu
  · simp only [hk, ite_false]; exact continuousOn_const

/-- **Parseval–Tonelli identity.**  For two grid arrays (possibly on different grids) continuous
on `[0,T]`, the `L²((0,T] × 𝕋³)` distance of their space-time interpolants equals the
`L²_t ℓ²_n` distance of their Fourier coefficients. -/
theorem integral_field_sub {T : ℝ} {N' : ℕ} [NeZero N'] {u : ℝ → Grid N → ℂ}
    {v : ℝ → Grid N' → ℂ} (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T)) :
    ∫ p, ‖field u p - field v p‖ ^ 2 ∂cylMeasure T =
      ∑' n, ∫ t in Ioc 0 T,
        ‖mFourierCoeff (⇑(interp (u t))) n - mFourierCoeff (⇑(interp (v t))) n‖ ^ 2 := by
  classical
  have hint : Integrable (fun p => ‖field u p - field v p‖ ^ 2) (cylMeasure T) :=
    ((memLp_field hu).sub (memLp_field hv)).norm.integrable_sq
  rw [cylMeasure, integral_prod _ hint]
  have hpt : ∀ t, ∫ x, ‖field u (t, x) - field v (t, x)‖ ^ 2 = ∑' n,
      ‖mFourierCoeff (⇑(interp (u t))) n - mFourierCoeff (⇑(interp (v t))) n‖ ^ 2 := by
    intro t
    have h := integral_norm_sq_eq_tsum (interp (u t) - interp (v t))
    simp only [mFourierCoeff_sub, ContinuousMap.sub_apply] at h
    exact h
  simp only [hpt]
  set S : Finset (Fin 3 → ℤ) :=
    (Finset.univ : Finset (Grid N)).image freqVec ∪ (Finset.univ : Finset (Grid N')).image freqVec
  have hz : ∀ t, ∀ n ∉ S,
      ‖mFourierCoeff (⇑(interp (u t))) n - mFourierCoeff (⇑(interp (v t))) n‖ ^ 2 = 0 := by
    intro t n hn
    have h1 : n ∉ Set.range (freqVec (N := N)) := by
      rintro ⟨k, rfl⟩
      exact hn (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
    have h2 : n ∉ Set.range (freqVec (N := N')) := by
      rintro ⟨k, rfl⟩
      exact hn (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
    rw [mFourierCoeff_interp_of_not_mem _ _ h1, mFourierCoeff_interp_of_not_mem _ _ h2]
    simp
  have hint' : ∀ n, IntegrableOn (fun t =>
      ‖mFourierCoeff (⇑(interp (u t))) n - mFourierCoeff (⇑(interp (v t))) n‖ ^ 2) (Ioc 0 T) :=
    fun n => integrableOn_of_continuousOn
      ((((continuousOn_coeff hu n).sub (continuousOn_coeff hv n)).norm).pow 2)
  have e : ∀ t, ∑' n,
      ‖mFourierCoeff (⇑(interp (u t))) n - mFourierCoeff (⇑(interp (v t))) n‖ ^ 2 =
      ∑ n ∈ S, ‖mFourierCoeff (⇑(interp (u t))) n - mFourierCoeff (⇑(interp (v t))) n‖ ^ 2 :=
    fun t => tsum_eq_sum (s := S) (hz t)
  simp only [e]
  rw [integral_finsetSum _ fun n _ => hint' n]
  refine (tsum_eq_sum (s := S) fun n hn => ?_).symm
  simp [hz _ n hn]

/-- `‖f‖²_{L²} = ∫ ‖f‖²` for the `L²` class of an `L²` function. -/
theorem norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  have e : ∀ a, ‖f a‖ ^ (2 : ℝ) = ‖f a‖ ^ 2 := fun a => Real.rpow_two _
  simp only [e]
  have hI : 0 ≤ ∫ a, ‖f a‖ ^ 2 ∂μ := integral_nonneg fun a => by positivity
  rw [ENNReal.toReal_ofReal (by positivity)]
  have := Real.rpow_inv_natCast_pow (n := 2) hI two_ne_zero
  simpa using this

/-- The elementary comparison behind the Cauchy property: for finitely supported coefficient
families `a, b` and any comparison family `c` (all continuous on `[0,T]`),
`Σ_n ∫|a_n - b_n|² ≤ 2 Σ_n ∫|a_n - c_n|² + 2 Σ_n ∫|b_n - c_n|²`. -/
theorem tsum_integral_sub_le {T : ℝ} (a b c : (Fin 3 → ℤ) → ℝ → ℂ)
    (ha : ∀ n, ContinuousOn (a n) (Icc 0 T)) (hb : ∀ n, ContinuousOn (b n) (Icc 0 T))
    (hc : ∀ n, ContinuousOn (c n) (Icc 0 T)) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ n ∉ S, ∀ t, a n t = 0 ∧ b n t = 0)
    (hsa : Summable fun n => ∫ t in Ioc 0 T, ‖a n t - c n t‖ ^ 2)
    (hsb : Summable fun n => ∫ t in Ioc 0 T, ‖b n t - c n t‖ ^ 2) :
    ∑' n, ∫ t in Ioc 0 T, ‖a n t - b n t‖ ^ 2 ≤
      2 * (∑' n, ∫ t in Ioc 0 T, ‖a n t - c n t‖ ^ 2) +
        2 * (∑' n, ∫ t in Ioc 0 T, ‖b n t - c n t‖ ^ 2) := by
  have hpt : ∀ n, ∫ t in Ioc 0 T, ‖a n t - b n t‖ ^ 2 ≤
      2 * (∫ t in Ioc 0 T, ‖a n t - c n t‖ ^ 2) + 2 * (∫ t in Ioc 0 T, ‖b n t - c n t‖ ^ 2) := by
    intro n
    have i1 : IntegrableOn (fun t => ‖a n t - b n t‖ ^ 2) (Ioc 0 T) :=
      integrableOn_of_continuousOn (((ha n).sub (hb n)).norm.pow 2)
    have i2 : IntegrableOn (fun t => ‖a n t - c n t‖ ^ 2) (Ioc 0 T) :=
      integrableOn_of_continuousOn (((ha n).sub (hc n)).norm.pow 2)
    have i3 : IntegrableOn (fun t => ‖b n t - c n t‖ ^ 2) (Ioc 0 T) :=
      integrableOn_of_continuousOn (((hb n).sub (hc n)).norm.pow 2)
    calc ∫ t in Ioc 0 T, ‖a n t - b n t‖ ^ 2
        ≤ ∫ t in Ioc 0 T, (2 * ‖a n t - c n t‖ ^ 2 + 2 * ‖b n t - c n t‖ ^ 2) := by
          refine integral_mono i1 ((i2.const_mul 2).add (i3.const_mul 2)) fun t => ?_
          have := norm_sub_sq_le_two (a n t - c n t) (b n t - c n t)
          simp only [sub_sub_sub_cancel_right] at this
          exact this
      _ = _ := by
          rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul,
            integral_const_mul]
  have hz : ∀ n ∉ S, ∫ t in Ioc 0 T, ‖a n t - b n t‖ ^ 2 = 0 := by
    intro n hn
    simp [(hS n hn _).1, (hS n hn _).2]
  have hsL : Summable fun n => ∫ t in Ioc 0 T, ‖a n t - b n t‖ ^ 2 :=
    summable_of_ne_finset_zero hz
  calc ∑' n, ∫ t in Ioc 0 T, ‖a n t - b n t‖ ^ 2
      ≤ ∑' n, (2 * (∫ t in Ioc 0 T, ‖a n t - c n t‖ ^ 2) +
          2 * (∫ t in Ioc 0 T, ‖b n t - c n t‖ ^ 2)) :=
        hsL.tsum_le_tsum hpt ((hsa.mul_left 2).add (hsb.mul_left 2))
    _ = _ := by
        rw [(hsa.mul_left 2).tsum_add (hsb.mul_left 2), tsum_mul_left, tsum_mul_left]

end Field

/-! ### The grid Aubin–Lions–Simon theorem -/

/-- **Grid Aubin–Lions–Simon theorem** (space-time form).  Let `U m t c` be time-dependent
periodic grid arrays (`N m` points per axis, arbitrary `N m`, finitely many components `c`)
with weak time derivatives `G m t c` (every grid value `W^{1,2}(0,T)`), bounded uniformly in `m`
in `L²_t H¹_h`:
`∫₀ᵀ Σ_c (‖U(t)‖_h² + Σ_i ‖D_i⁺U(t)‖_h²) dt ≤ B`, and whose interpolated time derivatives are
bounded in `L²_t H^{-s}_x`: `∫₀ᵀ Σ_c ‖𝓘_h G(t)‖²_{H^{-s}(𝕋³)} dt ≤ B₁`.  Then the space-time
trigonometric interpolants `(t,x) ↦ 𝓘_h U(t)(x)` are relatively compact in
`L²((0,T] × 𝕋³)`: a subsequence is Cauchy for the `L²` distance and converges in
`L²((0,T] × 𝕋³)` (each interpolant lies in `L²` by `memLp_field`). -/
theorem gridAubinLions {C : Type*} [Fintype C] {N : ℕ → ℕ} [∀ m, NeZero (N m)]
    {T : ℝ} (hT : 0 < T) (U G : ∀ m, ℝ → C → Grid (N m) → ℂ)
    (hW : ∀ m c, IsGridW12Rep T (fun t => U m t c) (fun t => G m t c)) (s : ℕ) {B B1 : ℝ}
    (hB : ∀ m, ∫ t in Ioc 0 T, ∑ c, (gridNormSq (U m t c) + coordForm (U m t c)) ≤ B)
    (hB1 : ∀ m, ∫ t in Ioc 0 T, ∑ c, trigNegSq s (interp (G m t c)) ≤ B1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ ε > 0, ∃ M, ∀ m ≥ M, ∀ m' ≥ M, ∀ c,
        ∫ p, ‖field (fun t => U (φ m) t c) p - field (fun t => U (φ m') t c) p‖ ^ 2
          ∂cylMeasure T < ε) ∧
      ∃ L : C → Lp ℂ 2 (cylMeasure T), ∀ c,
        Tendsto (fun m => (memLp_field (hW (φ m) c).continuousOn).toLp
          (field (fun t => U (φ m) t c))) atTop (𝓝 (L c)) := by
  classical
  obtain ⟨φ, hφ, c', hc'cont, hsum, hlim⟩ := gridAubinLions_coeff hT U G hW s hB hB1
  have hcont : ∀ m c, ContinuousOn (fun t => U m t c) (Icc 0 T) := fun m c =>
    (hW m c).continuousOn
  have hnn : ∀ m (p : C × (Fin 3 → ℤ)), 0 ≤
      ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U (φ m) t p.1))) p.2 - c' p t‖ ^ 2 :=
    fun m p => integral_nonneg fun _ => by positivity
  have hinj : ∀ c : C, Function.Injective fun n : Fin 3 → ℤ => (c, n) := fun c n n' h =>
    (Prod.mk.inj h).2
  -- comparison of one component with the full coefficient error
  have hcomp : ∀ m (c : C),
      (Summable fun n => ∫ t in Ioc 0 T,
        ‖mFourierCoeff (⇑(interp (U (φ m) t c))) n - c' (c, n) t‖ ^ 2) ∧
      ∑' n, ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U (φ m) t c))) n - c' (c, n) t‖ ^ 2 ≤
        ∑' p : C × (Fin 3 → ℤ),
          ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U (φ m) t p.1))) p.2 - c' p t‖ ^ 2 := by
    intro m c
    have hs : Summable fun n => ∫ t in Ioc 0 T,
        ‖mFourierCoeff (⇑(interp (U (φ m) t c))) n - c' (c, n) t‖ ^ 2 :=
      by
        have h := (hsum m).comp_injective (hinj c)
        exact h
    exact ⟨hs, hs.tsum_le_tsum_of_inj _ (hinj c) (fun p _ => hnn m p) (fun n => le_rfl)
      (hsum m)⟩
  have key : ∀ m m' c,
      ∫ p, ‖field (fun t => U (φ m) t c) p - field (fun t => U (φ m') t c) p‖ ^ 2
        ∂cylMeasure T ≤
        2 * (∑' p : C × (Fin 3 → ℤ),
          ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U (φ m) t p.1))) p.2 - c' p t‖ ^ 2) +
        2 * (∑' p : C × (Fin 3 → ℤ),
          ∫ t in Ioc 0 T, ‖mFourierCoeff (⇑(interp (U (φ m') t p.1))) p.2 - c' p t‖ ^ 2) := by
    intro m m' c
    rw [integral_field_sub (hcont (φ m) c) (hcont (φ m') c)]
    have hS : ∀ n ∉ (Finset.univ : Finset (Grid (N (φ m)))).image freqVec ∪
        (Finset.univ : Finset (Grid (N (φ m')))).image freqVec, ∀ t,
        mFourierCoeff (⇑(interp (U (φ m) t c))) n = 0 ∧
          mFourierCoeff (⇑(interp (U (φ m') t c))) n = 0 := by
      intro n hn t
      have h1 : n ∉ Set.range (freqVec (N := N (φ m))) := by
        rintro ⟨k, rfl⟩
        exact hn (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
      have h2 : n ∉ Set.range (freqVec (N := N (φ m'))) := by
        rintro ⟨k, rfl⟩
        exact hn (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
      exact ⟨mFourierCoeff_interp_of_not_mem _ _ h1, mFourierCoeff_interp_of_not_mem _ _ h2⟩
    have h := tsum_integral_sub_le (T := T)
      (fun n t => mFourierCoeff (⇑(interp (U (φ m) t c))) n)
      (fun n t => mFourierCoeff (⇑(interp (U (φ m') t c))) n) (fun n => c' (c, n))
      (fun n => continuousOn_coeff (hcont _ c) n) (fun n => continuousOn_coeff (hcont _ c) n)
      (fun n => hc'cont (c, n)) _ hS (hcomp m c).1 (hcomp m' c).1
    linarith [(hcomp m c).2, (hcomp m' c).2]
  have hcauchy : ∀ ε > 0, ∃ M, ∀ m ≥ M, ∀ m' ≥ M, ∀ c,
      ∫ p, ‖field (fun t => U (φ m) t c) p - field (fun t => U (φ m') t c) p‖ ^ 2
        ∂cylMeasure T < ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hlim (ε / 4) (by positivity)
    refine ⟨M, fun m hm m' hm' c => ?_⟩
    have h1 := hM m hm
    have h2 := hM m' hm'
    rw [Real.dist_eq, sub_zero] at h1 h2
    have := key m m' c
    have e1 := lt_of_le_of_lt (le_abs_self _) h1
    have e2 := lt_of_le_of_lt (le_abs_self _) h2
    linarith
  refine ⟨φ, hφ, hcauchy, ?_⟩
  have hL : ∀ c, CauchySeq fun m => (memLp_field (hW (φ m) c).continuousOn).toLp
      (field (fun t => U (φ m) t c)) := by
    intro c
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hcauchy (ε ^ 2) (by positivity)
    refine ⟨M, fun m hm m' hm' => ?_⟩
    rw [dist_eq_norm, ← MemLp.toLp_sub]
    have h := norm_toLp_sq ((memLp_field (hW (φ m) c).continuousOn).sub
      (memLp_field (hW (φ m') c).continuousOn))
    have hlt := hM m hm m' hm' c
    simp only [Pi.sub_apply] at h
    rw [← h] at hlt
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  exact ⟨fun c => Classical.choose (cauchySeq_tendsto_of_complete (hL c)),
    fun c => Classical.choose_spec (cauchySeq_tendsto_of_complete (hL c))⟩


/-- **Grid Aubin–Lions–Simon theorem** (limit form): under the hypotheses of `gridAubinLions`,
a subsequence of the space-time interpolants converges in `L²((0,T] × 𝕋³)` to limits `Ω c`:
`∫_{(0,T] × 𝕋³} |𝓘_h U_{φ m}(·, c) - Ω c|² → 0`. -/
theorem gridAubinLions_limit {C : Type*} [Fintype C] {N : ℕ → ℕ} [∀ m, NeZero (N m)]
    {T : ℝ} (hT : 0 < T) (U G : ∀ m, ℝ → C → Grid (N m) → ℂ)
    (hW : ∀ m c, IsGridW12Rep T (fun t => U m t c) (fun t => G m t c)) (s : ℕ) {B B1 : ℝ}
    (hB : ∀ m, ∫ t in Ioc 0 T, ∑ c, (gridNormSq (U m t c) + coordForm (U m t c)) ≤ B)
    (hB1 : ∀ m, ∫ t in Ioc 0 T, ∑ c, trigNegSq s (interp (G m t c)) ≤ B1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : C → ℝ × UnitAddTorus (Fin 3) → ℂ, ∀ c,
      MemLp (Ω c) 2 (cylMeasure T) ∧
      Tendsto (fun m => ∫ p, ‖field (fun t => U (φ m) t c) p - Ω c p‖ ^ 2 ∂cylMeasure T)
        atTop (𝓝 0) := by
  obtain ⟨φ, hφ, -, L, hL⟩ := gridAubinLions hT U G hW s hB hB1
  refine ⟨φ, hφ, fun c => ⇑(L c), fun c => ⟨Lp.memLp (L c), ?_⟩⟩
  have hm : ∀ m, MemLp (fun p => field (fun t => U (φ m) t c) p - (L c) p) 2 (cylMeasure T) :=
    fun m => (memLp_field (hW (φ m) c).continuousOn).sub (Lp.memLp (L c))
  have e : ∀ m, ∫ p, ‖field (fun t => U (φ m) t c) p - (L c) p‖ ^ 2 ∂cylMeasure T =
      ‖(memLp_field (hW (φ m) c).continuousOn).toLp (field (fun t => U (φ m) t c)) - L c‖ ^ 2 := by
    intro m
    rw [← norm_toLp_sq (hm m)]
    congr 2
    conv_rhs => rw [← Lp.toLp_coeFn (L c) (Lp.memLp (L c)), ← MemLp.toLp_sub]
    rfl
  simp only [e]
  have h0 := (tendsto_iff_norm_sub_tendsto_zero.1 (hL c)).pow 2
  simpa using h0

end Grid

end RenewalGeometry.GridAubinLions
