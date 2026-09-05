/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.AnytimeAudit

/-!
# Selection-safe adaptive coordinate audit — exact form
  (`thm:anytime-audit`)

Bounded intervention coordinates `X_t ∈ [0,1]` are sampled
predictably; coordinate `j` has mean `p_j`, sample count
`N_j(t)`, and empirical mean `p̂_j(t)`.  Via optional skipping,
the successive sampled values of coordinate `j` form a process
`Y j : ℕ → Ω → ℝ` strongly adapted to the coordinate's sampling
filtration whose increments have conditional mean `p j` — this
martingale property is exactly the predictable-sampling
hypothesis, and the empirical mean at any time with
`N_j(t) = k` is the mean of the first `k` sampled values.

This file proves the record's probabilistic layer exactly:

* `hasCondSubgaussianMGF_of_mem_Icc`: the **conditional
  Hoeffding lemma** — a bounded increment with vanishing
  conditional expectation is conditionally sub-Gaussian;
* `azuma_two_sided`: the **two-sided Azuma–Hoeffding bound**
  `P(kε ≤ |∑_{i<k}(Y_i − p)|) ≤ 2·exp(−2kε²)` for predictably
  sampled `[0,1]`-valued increments;
* `anytime_audit`: the **simultaneous confidence region** —
  with probability at least `1 − α`, for every coordinate `j`
  and every count `k ≥ 1`,
  `|p̂_j − p_j| ≤ √((2k)⁻¹·log(π²k²/(3αw_j)))`,
  by the exact Hoeffding calibration of the boxed radius, the
  Basel count ledger, the coordinate weight ledger, and the
  countable union bound.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace NCG
namespace AnytimeAudit

section CondHoeffding

variable {Ω : Type} {m mΩ : MeasurableSpace Ω}
  [StandardBorelSpace Ω] {μ : Measure Ω}

/-- **Conditional Hoeffding lemma**: a bounded random variable
with vanishing conditional expectation is conditionally
sub-Gaussian with the Hoeffding parameter. -/
theorem hasCondSubgaussianMGF_of_mem_Icc
    [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → ℝ}
    {a b : ℝ} (hXm : Measurable[mΩ] X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hce : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hXm.aemeasurable hb
  · have hint : Integrable X μ :=
      Integrable.of_mem_Icc (μ := μ) a b hXm.aemeasurable hb
    have h1 : ∀ᵐ ω' ∂(μ.trim hm),
        ∀ᵐ ω ∂(condExpKernel μ m ω'), X ω ∈ Set.Icc a b := by
      refine Measure.ae_ae_of_ae_comp ?_
      rw [condExpKernel_comp_trim hm]
      exact hb
    have hce_trim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
      StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
        stronglyMeasurable_condExp stronglyMeasurable_const
        hce
    have h2 : ∀ᵐ ω' ∂(μ.trim hm),
        ∫ y, X y ∂(condExpKernel μ m ω') = 0 := by
      have h3 := condExp_ae_eq_trim_integral_condExpKernel
        hm hint
      filter_upwards [h3, hce_trim] with ω' h3' hce'
      rw [← h3']
      exact hce'
    filter_upwards [h1, h2] with ω' hIcc hint0
    intro t
    have hprob : IsProbabilityMeasure
        ((condExpKernel μ m) ω') :=
      IsMarkovKernel.isProbabilityMeasure ω'
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hXm.aemeasurable hIcc hint0).mgf_le t

end CondHoeffding

variable {Ω : Type} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace Ω] {μ : Measure Ω}

/-- The Hoeffding parameter of a `[0,1]`-valued increment
centered at `q` is `4⁻¹`. -/
theorem hoeffding_param (q : ℝ) :
    ((‖(1 - q) - -q‖₊ / 2) ^ 2 : ℝ≥0) = 4⁻¹ := by
  rw [show (1 - q) - -q = (1:ℝ) from by ring, nnnorm_one,
    div_pow, one_pow]
  norm_num

/-- **Two-sided Azuma–Hoeffding** for predictably sampled
`[0,1]`-valued increments with conditional mean `q`:
`P(kε ≤ |∑_{i<k} (Y i − q)|) ≤ 2·exp(−2kε²)`. -/
theorem azuma_two_sided [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ) (q : ℝ)
    (h_adapted : ∀ i, StronglyMeasurable[ℱ i] (Y i))
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean0 : ∫ ω, Y 0 ω ∂μ = q)
    (h_mean : ∀ i, μ[Y (i + 1) | ℱ i] =ᵐ[μ] fun _ => q)
    (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | (k : ℝ) * ε
        ≤ |∑ i ∈ Finset.range k, (Y i ω - q)|}
      ≤ 2 * Real.exp (-2 * k * ε ^ 2) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hYmeas : ∀ i, Measurable (Y i) := fun i =>
    ((h_adapted i).mono (ℱ.le i)).measurable
  have hZbdd : ∀ i, ∀ᵐ ω ∂μ,
      Y i ω - q ∈ Set.Icc (-q) (1 - q) := by
    intro i
    filter_upwards [h_bdd i] with ω hω
    obtain ⟨h0, h1⟩ := hω
    exact ⟨by linarith, by linarith⟩
  have hZadapted : StronglyAdapted ℱ
      (fun i ω => Y i ω - q) := fun i =>
    (h_adapted i).sub stronglyMeasurable_const
  -- the centered start
  have h0 : HasSubgaussianMGF (fun ω => Y 0 ω - q)
      (4⁻¹ : ℝ≥0) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := fun ω => Y 0 ω - q) (a := -q) (b := 1 - q)
      ((hYmeas 0).sub measurable_const).aemeasurable
      (hZbdd 0) ?_
    · rwa [hoeffding_param q] at h
    · rw [integral_sub (Integrable.of_mem_Icc 0 1
        (hYmeas 0).aemeasurable (h_bdd 0))
        (integrable_const q), h_mean0]
      simp
  -- the centered conditionally sub-Gaussian increments
  have hcond : ∀ i, HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
      (fun ω => Y (i + 1) ω - q) (4⁻¹ : ℝ≥0) μ := by
    intro i
    have hce : μ[fun ω => Y (i + 1) ω - q | ℱ i]
        =ᵐ[μ] 0 := by
      have hsub := condExp_sub (μ := μ)
        (f := Y (i + 1)) (g := fun _ => q)
        (Integrable.of_mem_Icc 0 1
          (hYmeas (i + 1)).aemeasurable (h_bdd (i + 1)))
        (integrable_const q) (ℱ i)
      have hcq : μ[fun _ => q | ℱ i] = fun _ => q :=
        condExp_const (ℱ.le i) q
      filter_upwards [hsub, h_mean i] with ω hω hmω
      rw [Pi.zero_apply]
      have : (Y (i + 1) - fun _ => q) = fun ω =>
          Y (i + 1) ω - q := rfl
      rw [← this, hω, Pi.sub_apply, hmω, hcq]
      ring
    have h := hasCondSubgaussianMGF_of_mem_Icc (ℱ.le i)
      (X := fun ω => Y (i + 1) ω - q)
      (a := -q) (b := 1 - q)
      ((hYmeas (i + 1)).sub measurable_const)
      (hZbdd (i + 1)) hce
    rwa [hoeffding_param q] at h
  -- one-sided bounds
  have hε' : 0 ≤ (k : ℝ) * ε := by positivity
  have hsumc : ((∑ _i ∈ Finset.range k,
      (4⁻¹ : ℝ≥0) : ℝ≥0) : ℝ) = k / 4 := by
    rw [Finset.sum_const, Finset.card_range]
    push_cast
    ring
  have hexp : -((k : ℝ) * ε) ^ 2 / (2 * ((k : ℝ) / 4))
      = -2 * k * ε ^ 2 := by
    field_simp
    ring
  have hR := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (μ := μ) (Y := fun i ω => Y i ω - q)
    (cY := fun _ => (4⁻¹ : ℝ≥0)) (ℱ := ℱ)
    hZadapted h0 k (fun i _ => hcond i) hε'
  rw [hsumc, hexp] at hR
  have hL := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (μ := μ) (Y := fun i ω => -(Y i ω - q))
    (cY := fun _ => (4⁻¹ : ℝ≥0)) (ℱ := ℱ)
    (fun i => (hZadapted i).neg)
    (HasSubgaussianMGF.neg h0) k
    (fun i _ => Kernel.HasSubgaussianMGF.neg (hcond i)) hε'
  rw [hsumc, hexp] at hL
  -- two-sided union
  have hsub : {ω | (k : ℝ) * ε
      ≤ |∑ i ∈ Finset.range k, (Y i ω - q)|}
      ⊆ {ω | (k : ℝ) * ε
          ≤ ∑ i ∈ Finset.range k, (Y i ω - q)}
        ∪ {ω | (k : ℝ) * ε
            ≤ ∑ i ∈ Finset.range k, -(Y i ω - q)} := by
    intro ω hω
    have hω' : (k : ℝ) * ε
        ≤ |∑ i ∈ Finset.range k, (Y i ω - q)| := hω
    rcases le_abs.mp hω' with h | h
    · exact Set.mem_union_left _ h
    · refine Set.mem_union_right _ ?_
      rw [Set.mem_setOf_eq, Finset.sum_neg_distrib]
      exact h
  calc μ.real {ω | (k : ℝ) * ε
      ≤ |∑ i ∈ Finset.range k, (Y i ω - q)|}
      ≤ μ.real ({ω | (k : ℝ) * ε
          ≤ ∑ i ∈ Finset.range k, (Y i ω - q)}
        ∪ {ω | (k : ℝ) * ε
            ≤ ∑ i ∈ Finset.range k, -(Y i ω - q)}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | (k : ℝ) * ε
          ≤ ∑ i ∈ Finset.range k, (Y i ω - q)}
        + μ.real {ω | (k : ℝ) * ε
            ≤ ∑ i ∈ Finset.range k, -(Y i ω - q)} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * k * ε ^ 2) := by
        rw [two_mul]
        exact add_le_add hR hL

/-- **The boxed simultaneous confidence radius**
`√((2k)⁻¹·log(π²k²/(3αw)))`. -/
noncomputable def auditRadius (α w : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt ((2 * (k : ℝ))⁻¹
    * Real.log (Real.pi ^ 2 * (k : ℝ) ^ 2 / (3 * (α * w))))

theorem auditRadius_nonneg (α w : ℝ) (k : ℕ) :
    0 ≤ auditRadius α w k := Real.sqrt_nonneg _

/-- Single-coordinate calibrated bound: at count `k`, the
audited deviation event has probability at most
`6αw/(π²k²)`. -/
theorem audit_single_bound [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ) (q α w : ℝ)
    (h_adapted : ∀ i, StronglyMeasurable[ℱ i] (Y i))
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean0 : ∫ ω, Y 0 ω ∂μ = q)
    (h_mean : ∀ i, μ[Y (i + 1) | ℱ i] =ᵐ[μ] fun _ => q)
    (hα : 0 < α) (hα1 : α ≤ 1) (hw : 0 < w) (hw1 : w ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    μ.real {ω | auditRadius α w k
        < |(∑ i ∈ Finset.range k, Y i ω) / k - q|}
      ≤ 6 * (α * w) / (Real.pi ^ 2 * (k : ℝ) ^ 2) := by
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hπ3 : (3 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have haw0 : (0 : ℝ) < 3 * (α * w) :=
    mul_pos (by norm_num) (mul_pos hα hw)
  have hX1 : (1 : ℝ)
      ≤ Real.pi ^ 2 * (k : ℝ) ^ 2 / (3 * (α * w)) := by
    rw [le_div_iff₀ haw0, one_mul]
    have haw1 : α * w ≤ 1 :=
      mul_le_one₀ hα1 hw.le hw1
    nlinarith
  -- the event at fixed count is a two-sided Azuma event
  have hsub : {ω | auditRadius α w k
      < |(∑ i ∈ Finset.range k, Y i ω) / k - q|}
      ⊆ {ω | (k : ℝ) * auditRadius α w k
          ≤ |∑ i ∈ Finset.range k, (Y i ω - q)|} := by
    intro ω hω
    have hω' : auditRadius α w k
        < |(∑ i ∈ Finset.range k, Y i ω) / k - q| := hω
    have hquot : (∑ i ∈ Finset.range k, (Y i ω - q))
        / (k : ℝ)
        = (∑ i ∈ Finset.range k, Y i ω) / k - q := by
      rw [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, sub_div,
        mul_div_cancel_left₀ _ hk0]
    rw [← hquot, abs_div, abs_of_pos hkpos] at hω'
    have h2 := (lt_div_iff₀ hkpos).mp hω'
    have h3 : (k : ℝ) * auditRadius α w k
        ≤ |∑ i ∈ Finset.range k, (Y i ω - q)| := by
      rw [mul_comm]
      exact h2.le
    exact h3
  have hb := azuma_two_sided ℱ Y q h_adapted h_bdd h_mean0
    h_mean k hk (auditRadius_nonneg α w k)
  -- calibration of the radius
  have hcal : Real.exp (-2 * (k : ℝ)
      * (auditRadius α w k) ^ 2)
      = (Real.pi ^ 2 * (k : ℝ) ^ 2 / (3 * (α * w)))⁻¹ := by
    have h := NCG.confidence_radius_calibration (k : ℝ)
      (Real.pi ^ 2 * (k : ℝ) ^ 2 / (3 * (α * w)))
      hkpos hX1
    have hrs : auditRadius α w k
        = Real.sqrt ((2 * (k : ℝ))⁻¹
          * Real.log (Real.pi ^ 2 * (k : ℝ) ^ 2
            / (3 * (α * w)))) := rfl
    rw [← hrs] at h
    rw [show (-2 * (k : ℝ)) * (auditRadius α w k) ^ 2
      = (-(2 * (k : ℝ))) * (auditRadius α w k) ^ 2 from
        by ring]
    exact h
  calc μ.real {ω | auditRadius α w k
      < |(∑ i ∈ Finset.range k, Y i ω) / k - q|}
      ≤ μ.real {ω | (k : ℝ) * auditRadius α w k
          ≤ |∑ i ∈ Finset.range k, (Y i ω - q)|} :=
        measureReal_mono hsub
    _ ≤ 2 * Real.exp (-2 * (k : ℝ)
          * (auditRadius α w k) ^ 2) := hb
    _ = 6 * (α * w) / (Real.pi ^ 2 * (k : ℝ) ^ 2) := by
        rw [hcal, inv_div]
        ring

/-- **Selection-safe adaptive coordinate audit**: with
probability at least `1 − α`, simultaneously for every
coordinate `j` and every count `k ≥ 1`, the empirical mean of
the first `k` predictably sampled values of coordinate `j`
stays within the boxed radius
`√((2k)⁻¹·log(π²k²/(3αw_j)))` of the true mean `p j`. -/
theorem anytime_audit [IsProbabilityMeasure μ]
    {J : Type} [Fintype J]
    (ℱ : J → Filtration ℕ mΩ) (Y : J → ℕ → Ω → ℝ)
    (p w : J → ℝ) (α : ℝ)
    (h_adapted : ∀ j i, StronglyMeasurable[(ℱ j) i] (Y j i))
    (h_bdd : ∀ j i, ∀ᵐ ω ∂μ, Y j i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean0 : ∀ j, ∫ ω, Y j 0 ω ∂μ = p j)
    (h_mean : ∀ j i,
      μ[Y j (i + 1) | (ℱ j) i] =ᵐ[μ] fun _ => p j)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : ∀ j, 0 < w j) (hwsum : ∑ j, w j ≤ 1) :
    μ.real {ω | ∃ j, ∃ k, 1 ≤ k ∧ auditRadius α (w j) k
        < |(∑ i ∈ Finset.range k, Y j i ω) / k - p j|}
      ≤ α := by
  classical
  have hw1 : ∀ j, w j ≤ 1 := fun j =>
    le_trans (Finset.single_le_sum (f := w)
      (fun j _ => (hw j).le) (Finset.mem_univ j)) hwsum
  set B : J → ℕ → Set Ω := fun j k =>
    {ω | 1 ≤ k ∧ auditRadius α (w j) k
      < |(∑ i ∈ Finset.range k, Y j i ω) / k - p j|}
    with hB
  have hFeq : {ω | ∃ j, ∃ k, 1 ≤ k ∧ auditRadius α (w j) k
      < |(∑ i ∈ Finset.range k, Y j i ω) / k - p j|}
      = ⋃ jk : J × ℕ, B jk.1 jk.2 := by
    ext ω
    simp [hB, Set.mem_iUnion, Prod.exists]
  have hnn : ∀ (j : J) (k : ℕ),
      0 ≤ 6 * (α * w j) / (Real.pi ^ 2 * (k : ℝ) ^ 2) :=
    fun j k => div_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg hα.le (hw j).le)) (by positivity)
  have hbound : ∀ (j : J) (k : ℕ), μ (B j k)
      ≤ ENNReal.ofReal
        (6 * (α * w j) / (Real.pi ^ 2 * (k : ℝ) ^ 2)) := by
    intro j k
    rcases Nat.lt_or_ge k 1 with hk | hk
    · have hk0 : k = 0 := by omega
      subst hk0
      have hempty : B j 0 = ∅ := by
        ext ω
        simp [hB]
      rw [hempty]
      simp
    · have h1 := audit_single_bound (ℱ j) (Y j) (p j) α
        (w j) (h_adapted j) (h_bdd j) (h_mean0 j)
        (h_mean j) hα hα1 (hw j) (hw1 j) k hk
      have hsub : B j k ⊆ {ω | auditRadius α (w j) k
          < |(∑ i ∈ Finset.range k, Y j i ω) / k - p j|} :=
        fun ω hω => hω.2
      have h2 : μ.real (B j k)
          ≤ 6 * (α * w j) / (Real.pi ^ 2 * (k : ℝ) ^ 2) :=
        le_trans (measureReal_mono hsub) h1
      exact (ENNReal.le_ofReal_iff_toReal_le
        (measure_ne_top μ _) (hnn j k)).mpr h2
  have hbase : ∀ j : J, (∑' k : ℕ, ENNReal.ofReal
      (6 * (α * w j) / (Real.pi ^ 2 * (k : ℝ) ^ 2)))
      = ENNReal.ofReal (α * w j) := by
    intro j
    have hcongr : ∀ k : ℕ,
        6 * (α * w j) / (Real.pi ^ 2 * (k : ℝ) ^ 2)
        = (6 * (α * w j) / Real.pi ^ 2)
          * (1 / (k : ℝ) ^ 2) := by
      intro k
      rcases eq_or_ne ((k : ℝ)) 0 with h | h
      · rw [h]
        norm_num
      · field_simp
    have hsummable : Summable (fun k : ℕ =>
        6 * (α * w j) / (Real.pi ^ 2 * (k : ℝ) ^ 2)) := by
      refine Summable.congr ?_ fun k => (hcongr k).symm
      exact (Real.summable_one_div_nat_pow.mpr
        one_lt_two).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (hnn j) hsummable]
    congr 1
    rw [tsum_congr hcongr, tsum_mul_left, NCG.basel_budget]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hFeq]
  refine (ENNReal.le_ofReal_iff_toReal_le
    (measure_ne_top μ _) hα.le).mp ?_
  calc μ (⋃ jk : J × ℕ, B jk.1 jk.2)
      ≤ ∑' jk : J × ℕ, μ (B jk.1 jk.2) :=
        measure_iUnion_le _
    _ ≤ ∑' jk : J × ℕ, ENNReal.ofReal (6 * (α * w jk.1)
          / (Real.pi ^ 2 * (jk.2 : ℝ) ^ 2)) :=
        ENNReal.tsum_le_tsum fun jk => hbound jk.1 jk.2
    _ = ∑' j : J, ∑' k : ℕ, ENNReal.ofReal (6 * (α * w j)
          / (Real.pi ^ 2 * (k : ℝ) ^ 2)) :=
        ENNReal.tsum_prod (f := fun (j : J) (k : ℕ) =>
          ENNReal.ofReal (6 * (α * w j)
            / (Real.pi ^ 2 * (k : ℝ) ^ 2)))
    _ = ∑ j : J, ∑' k : ℕ, ENNReal.ofReal (6 * (α * w j)
          / (Real.pi ^ 2 * (k : ℝ) ^ 2)) :=
        tsum_fintype _
    _ = ∑ j : J, ENNReal.ofReal (α * w j) :=
        Finset.sum_congr rfl fun j _ => hbase j
    _ = ENNReal.ofReal (∑ j : J, α * w j) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ =>
          mul_nonneg hα.le (hw j).le).symm
    _ ≤ ENNReal.ofReal α := ENNReal.ofReal_le_ofReal
        (NCG.weight_budget w α hα.le hwsum)

end AnytimeAudit
end NCG
