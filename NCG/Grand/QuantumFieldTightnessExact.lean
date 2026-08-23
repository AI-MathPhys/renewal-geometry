/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.QuantumCylinderInverseLimitExact

/-!
# Absolute tightness of cylinder field laws

Machinery for `thm:SMST-quantum-tightness` (QRP.7–QRP.8): field laws `μ̂_X = (ι_X)_* μ_X` of
finite cylinders mapped into a field space `E`.

* `fieldLaw_tail_le` (**QRP.7, tail bound**): an exponential moment bound
  `∑ μ_X(ω) e^{α 𝒱(ι_X ω)} ≤ C` gives `μ̂_X {𝒱 > R} ≤ C e^{-α R}`;
* `isTightMeasureSet_fieldLaw` (**QRP.7, tightness**): with compact sublevel sets of `𝒱`,
  the family of field laws is tight;
* `isCompact_screened`: in a Hilbert space, the set of vectors of norm `≤ M` whose tails
  `‖(I - P_k) x‖ ≤ t_k` under finite-rank contractions `P_k` with `t_k → 0` is compact;
* `isTightMeasureSet_of_screen` (**QRP.8**): probability measures on a Hilbert space with
  uniformly bounded second moments and uniformly vanishing screen tails
  `sup_X ∫ ‖(I - P_k) φ‖² dμ̂_X → 0` form a tight family.
-/

open MeasureTheory Filter Topology Finset
open NCG.QuantumCylinderInverseLimit

namespace NCG
namespace QuantumFieldTightness

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Field laws and exponential moments -/

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The field law `(ι)_* μ` of a weighted finite cylinder. -/
noncomputable def fieldLaw {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (μ : Ω → ℝ) (ι : Ω → E) : Measure E :=
  (discrete μ).map ι

theorem fieldLaw_apply {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (μ : Ω → ℝ) (ι : Ω → E) {s : Set E} (hs : MeasurableSet s) :
    fieldLaw μ ι s = ∑ ω, ENNReal.ofReal (μ ω) * (ι ⁻¹' s).indicator 1 ω := by
  unfold fieldLaw
  rw [Measure.map_apply (Measurable.of_discrete) hs, discrete_apply _ (MeasurableSet.of_discrete)]

theorem isProbabilityMeasure_fieldLaw {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (h1 : ∑ ω, μ ω = 1) (ι : Ω → E) :
    IsProbabilityMeasure (fieldLaw μ ι) := by
  haveI := isProbabilityMeasure_discrete hμ h1
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete).aemeasurable

/-- The exponential moment `∑ μ(ω) e^{α 𝒱(ι ω)}`. -/
noncomputable def expMoment {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (ι : Ω → E) (V : E → ℝ) (α : ℝ) :
    ℝ :=
  ∑ ω, μ ω * Real.exp (α * V (ι ω))

/-- **(QRP.7, tail bound)**: `μ̂ {𝒱 > R} ≤ e^{-α R} ∑ μ(ω) e^{α 𝒱(ι ω)}`. -/
theorem fieldLaw_tail_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (ι : Ω → E) (V : E → ℝ) (hV : Measurable V) {α : ℝ}
    (hα : 0 ≤ α) (R : ℝ) :
    fieldLaw μ ι {x | R < V x} ≤ ENNReal.ofReal (expMoment μ ι V α * Real.exp (-(α * R))) := by
  rw [fieldLaw_apply μ ι (measurableSet_lt measurable_const hV)]
  have hsum : ∑ ω, ENNReal.ofReal (μ ω) * (ι ⁻¹' {x | R < V x}).indicator 1 ω
      = ENNReal.ofReal (∑ ω ∈ univ.filter (fun ω => R < V (ι ω)), μ ω) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun ω _ => hμ ω, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : R < V (ι ω) <;> simp [h]
  rw [hsum]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold expMoment
  rw [Finset.sum_mul]
  calc ∑ ω ∈ univ.filter (fun ω => R < V (ι ω)), μ ω
      ≤ ∑ ω ∈ univ.filter (fun ω => R < V (ι ω)),
          μ ω * Real.exp (α * V (ι ω)) * Real.exp (-(α * R)) := by
        refine Finset.sum_le_sum fun ω hω => ?_
        rw [Finset.mem_filter] at hω
        rw [mul_assoc, ← Real.exp_add]
        have : 0 ≤ α * V (ι ω) + -(α * R) := by nlinarith [hω.2]
        have := Real.one_le_exp this
        calc μ ω = μ ω * 1 := (mul_one _).symm
          _ ≤ μ ω * Real.exp (α * V (ι ω) + -(α * R)) :=
              mul_le_mul_of_nonneg_left this (hμ ω)
    _ ≤ ∑ ω, μ ω * Real.exp (α * V (ι ω)) * Real.exp (-(α * R)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun ω _ _ =>
          mul_nonneg (mul_nonneg (hμ ω) (Real.exp_pos _).le) (Real.exp_pos _).le

/-- A tail threshold making `C e^{-α R}` small. -/
theorem exists_tail_threshold {C α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ R : ℝ, C * Real.exp (-(α * R)) < ε := by
  have h : Tendsto (fun R : ℝ => C * Real.exp (-(α * R))) atTop (𝓝 (C * 0)) := by
    refine tendsto_const_nhds.mul ?_
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hα)
  rw [mul_zero] at h
  exact (h.eventually (gt_mem_nhds hε)).exists

/-- **(QRP.7, tightness)**: a uniform exponential moment bound with compact sublevel sets makes
the family of field laws tight. -/
theorem isTightMeasureSet_fieldLaw {X : Type*} {Ω : X → Type*} [∀ x, Fintype (Ω x)]
    [∀ x, MeasurableSpace (Ω x)] [∀ x, DiscreteMeasurableSpace (Ω x)] (μ : ∀ x, Ω x → ℝ)
    (hμ : ∀ x ω, 0 ≤ μ x ω) (ι : ∀ x, Ω x → E) (V : E → ℝ) (hV : Measurable V)
    (hcompact : ∀ R : ℝ, IsCompact {e | V e ≤ R}) {α : ℝ} (hα : 0 < α) {C : ℝ}
    (hC : ∀ x, expMoment (μ x) (ι x) V α ≤ C) :
    IsTightMeasureSet (Set.range fun x => fieldLaw (μ x) (ι x)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with hT | hT
  · exact ⟨{e | V e ≤ 0}, hcompact 0, fun _ _ => hT ▸ le_top⟩
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hT
  obtain ⟨R, hR⟩ := exists_tail_threshold (C := C) hα hε'
  refine ⟨{e | V e ≤ R}, hcompact R, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hcompl : {e | V e ≤ R}ᶜ = {e | R < V e} := by
    ext e
    simp
  rw [hcompl]
  refine (fieldLaw_tail_le (hμ x) (ι x) V hV hα.le R).trans ?_
  calc ENNReal.ofReal (expMoment (μ x) (ι x) V α * Real.exp (-(α * R)))
      ≤ ENNReal.ofReal (C * Real.exp (-(α * R))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le)
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hR.le
    _ = ε := ENNReal.ofReal_toReal hT

/-! ### Compact screens in a Hilbert space -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Compact screened set**: vectors of norm `≤ M` whose tails under finite-rank contractions
`P k` are at most `t k → 0` form a compact set. -/
theorem isCompact_screened (M : ℝ) (P : ℕ → H →L[ℝ] H)
    (hfin : ∀ k, FiniteDimensional ℝ (LinearMap.range (P k).toLinearMap))
    (hP : ∀ k x, ‖P k x‖ ≤ ‖x‖) (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) :
    IsCompact {x : H | ‖x‖ ≤ M ∧ ∀ k, ‖x - P k x‖ ≤ t k} := by
  refine isCompact_iff_totallyBounded_isComplete.2 ⟨?_, IsClosed.isComplete ?_⟩
  · rw [Metric.totallyBounded_iff]
    intro ε hε
    -- choose a screen with small tail
    obtain ⟨k, hk⟩ : ∃ k, t k < ε / 2 := by
      have := ht.eventually (gt_mem_nhds (half_pos hε))
      exact this.exists
    -- the screened ball is compact in the finite-dimensional range
    haveI := hfin k
    set S := LinearMap.range (P k).toLinearMap with hS
    have hball : IsCompact ((fun y : S => (y : H)) '' Metric.closedBall (0 : S) M) :=
      (isCompact_closedBall (0 : S) M).image continuous_subtype_val
    obtain ⟨net, hnet, hcover⟩ := Metric.totallyBounded_iff.1 hball.totallyBounded (ε / 2)
      (half_pos hε)
    refine ⟨net, hnet, fun x hx => ?_⟩
    obtain ⟨hxM, hxt⟩ := hx
    have hPx : P k x ∈ (fun y : S => (y : H)) '' Metric.closedBall (0 : S) M := by
      refine ⟨⟨P k x, LinearMap.mem_range_self _ x⟩, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖P k x‖ ≤ M
      exact (hP k x).trans hxM
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hPx)
    refine Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    rw [Metric.mem_ball] at hxy ⊢
    calc dist x y ≤ dist x (P k x) + dist (P k x) y := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_le_of_lt ?_ hxy
          rw [dist_eq_norm]
          exact (hxt k).trans hk.le
      _ = ε := add_halves ε
  · rw [Set.setOf_and, Set.setOf_forall]
    refine (isClosed_le continuous_norm continuous_const).inter (isClosed_iInter fun k => ?_)
    exact isClosed_le (continuous_norm.comp (continuous_id.sub (P k).continuous)) continuous_const

variable [MeasurableSpace H] [BorelSpace H]

/-- Markov's inequality for the squared norm of a vector-valued tail. -/
theorem measure_norm_gt_le {ν : Measure H} (f : H → H) (hf : Measurable f) {c : ℝ} (hc : 0 < c) :
    ν {x | c < ‖f x‖} ≤ (∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν) / ENNReal.ofReal (c ^ 2) := by
  have hmeas : AEMeasurable (fun x => ‖f x‖ₑ ^ 2) ν := (hf.enorm.pow_const 2).aemeasurable
  have h := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (c ^ 2))
  have hsub : {x | c < ‖f x‖} ⊆ {x | ENNReal.ofReal (c ^ 2) ≤ ‖f x‖ₑ ^ 2} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le hx.le 2)
  have hc' : ENNReal.ofReal (c ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  calc ENNReal.ofReal (c ^ 2) * ν {x | c < ‖f x‖}
      ≤ ENNReal.ofReal (c ^ 2) * ν {x | ENNReal.ofReal (c ^ 2) ≤ ‖f x‖ₑ ^ 2} := by
        gcongr
    _ ≤ _ := h


/-- Markov's inequality in multiplicative form at a real threshold. -/
theorem mul_measure_norm_gt_le {ν : Measure H} (f : H → H) (hf : Measurable f) {c : ℝ}
    (hc : 0 < c) :
    ENNReal.ofReal (c ^ 2) * ν {x | c < ‖f x‖} ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  have hmeas : AEMeasurable (fun x => ‖f x‖ₑ ^ 2) ν := (hf.enorm.pow_const 2).aemeasurable
  have h := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (c ^ 2))
  have hsub : {x | c < ‖f x‖} ⊆ {x | ENNReal.ofReal (c ^ 2) ≤ ‖f x‖ₑ ^ 2} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le hx.le 2)
  calc ENNReal.ofReal (c ^ 2) * ν {x | c < ‖f x‖}
      ≤ ENNReal.ofReal (c ^ 2) * ν {x | ENNReal.ofReal (c ^ 2) ≤ ‖f x‖ₑ ^ 2} := by
        gcongr
    _ ≤ _ := h

/-- The geometric threshold `2^{-j}` as an extended nonnegative real. -/
theorem ofReal_half_pow_sq (j : ℕ) :
    ENNReal.ofReal (((2⁻¹ : ℝ) ^ j) ^ 2) = ((2⁻¹ : ENNReal) ^ j) ^ 2 := by
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- **(QRP.8)**: probability measures on a Hilbert space with uniformly bounded second moments
and uniformly vanishing screen tails form a tight family. -/
theorem isTightMeasureSet_of_screen {X : Type*} (ν : X → Measure H)
    [∀ x, IsProbabilityMeasure (ν x)] (P : ℕ → H →L[ℝ] H)
    (hfin : ∀ k, FiniteDimensional ℝ (LinearMap.range (P k).toLinearMap))
    (hP : ∀ k x, ‖P k x‖ ≤ ‖x‖) {A : ENNReal} (hA : A ≠ ⊤)
    (hmom : ∀ x, ∫⁻ φ, ‖φ‖ₑ ^ 2 ∂(ν x) ≤ A)
    (hscreen : Tendsto (fun k => ⨆ x, ∫⁻ φ, ‖φ - P k φ‖ₑ ^ 2 ∂(ν x)) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range ν) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with hT | hT
  · exact ⟨∅, isCompact_empty, fun _ _ => hT ▸ le_top⟩
  -- the radius `M` controlling the bounded part
  have hε2 : (0 : ENNReal) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hε2T : ε / 2 ≠ ⊤ := ENNReal.div_ne_top hT (by norm_num)
  set e : ℝ := (ε / 2).toReal with he
  have he0 : 0 < e := ENNReal.toReal_pos hε2.ne' hε2T
  set M : ℝ := max 1 (A.toReal / e) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMA : A ≤ ENNReal.ofReal (M ^ 2) * (ε / 2) := by
    have h1 : A.toReal ≤ M ^ 2 * e := by
      have : A.toReal / e ≤ M := le_max_right _ _
      have h2 : A.toReal ≤ M * e := by
        rwa [div_le_iff₀ he0] at this
      have h3 : M * e ≤ M ^ 2 * e := by
        have : M ≤ M ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this he0.le
      exact h2.trans h3
    calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
      _ ≤ ENNReal.ofReal (M ^ 2 * e) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (M ^ 2) * (ε / 2) := by
          rw [ENNReal.ofReal_mul (by positivity), he, ENNReal.ofReal_toReal hε2T]
  have hbounded : ∀ x, ν x {φ | M < ‖φ‖} ≤ ε / 2 := by
    intro x
    have h := mul_measure_norm_gt_le (ν := ν x) id measurable_id hM0
    simp only [id] at h
    have hM2 : ENNReal.ofReal (M ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have h' := (h.trans (hmom x)).trans hMA
    rw [mul_comm, mul_comm (ENNReal.ofReal (M ^ 2))] at h'
    exact (ENNReal.mul_le_mul_iff_left hM2 ENNReal.ofReal_ne_top).mp h'
  -- the screens with geometric tails
  set q : ℕ → ENNReal := fun j => (2⁻¹ : ENNReal) ^ j with hq
  have hq0 : ∀ j, q j ≠ 0 := fun j => pow_ne_zero _ (by simp)
  have hqT : ∀ j, q j ≠ ⊤ := fun j => ENNReal.pow_ne_top (by simp)
  have hε4 : (0 : ENNReal) < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  have hchoose : ∀ j, ∃ k, ⨆ x, ∫⁻ φ, ‖φ - P k φ‖ₑ ^ 2 ∂(ν x) < q j ^ 2 * (ε / 4 * q j) := by
    intro j
    have hpos : (0 : ENNReal) < q j ^ 2 * (ε / 4 * q j) := by
      rw [pos_iff_ne_zero]
      exact mul_ne_zero (pow_ne_zero _ (hq0 j)) (mul_ne_zero hε4.ne' (hq0 j))
    exact (hscreen.eventually (gt_mem_nhds hpos)).exists
  choose k hk using hchoose
  have htail : ∀ j x, ν x {φ | (2⁻¹ : ℝ) ^ j < ‖φ - P (k j) φ‖} ≤ ε / 4 * q j := by
    intro j x
    have h := mul_measure_norm_gt_le (ν := ν x) (fun φ => φ - P (k j) φ)
      (continuous_id.sub (P (k j)).continuous).measurable (c := (2⁻¹ : ℝ) ^ j) (by positivity)
    rw [ofReal_half_pow_sq] at h
    have h2 : q j ^ 2 * ν x {φ | (2⁻¹ : ℝ) ^ j < ‖φ - P (k j) φ‖} ≤ q j ^ 2 * (ε / 4 * q j) :=
      h.trans ((le_iSup (fun x => ∫⁻ φ, ‖φ - P (k j) φ‖ₑ ^ 2 ∂(ν x)) x).trans (hk j).le)
    rw [mul_comm, mul_comm (q j ^ 2)] at h2
    exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero _ (hq0 j)) (ENNReal.pow_ne_top (hqT j))).mp h2
  -- the compact screened set
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨{φ | ‖φ‖ ≤ M ∧ ∀ j, ‖φ - P (k j) φ‖ ≤ (2⁻¹ : ℝ) ^ j},
    isCompact_screened M (fun j => P (k j)) (fun j => hfin (k j)) (fun j => hP (k j)) _ ht, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hsub : {φ | ‖φ‖ ≤ M ∧ ∀ j, ‖φ - P (k j) φ‖ ≤ (2⁻¹ : ℝ) ^ j}ᶜ ⊆
      {φ | M < ‖φ‖} ∪ ⋃ j, {φ | (2⁻¹ : ℝ) ^ j < ‖φ - P (k j) φ‖} := by
    intro φ hφ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_forall, not_le] at hφ
    by_cases hM' : M < ‖φ‖
    · exact Or.inl hM'
    · obtain ⟨j, hj⟩ := hφ (not_lt.mp hM')
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)
  calc ν x {φ | ‖φ‖ ≤ M ∧ ∀ j, ‖φ - P (k j) φ‖ ≤ (2⁻¹ : ℝ) ^ j}ᶜ
      ≤ ν x ({φ | M < ‖φ‖} ∪ ⋃ j, {φ | (2⁻¹ : ℝ) ^ j < ‖φ - P (k j) φ‖}) := measure_mono hsub
    _ ≤ ν x {φ | M < ‖φ‖} + ν x (⋃ j, {φ | (2⁻¹ : ℝ) ^ j < ‖φ - P (k j) φ‖}) :=
        measure_union_le _ _
    _ ≤ ε / 2 + ∑' j, ν x {φ | (2⁻¹ : ℝ) ^ j < ‖φ - P (k j) φ‖} :=
        add_le_add (hbounded x) (measure_iUnion_le _)
    _ ≤ ε / 2 + ∑' j, ε / 4 * q j := add_le_add le_rfl (ENNReal.tsum_le_tsum fun j => htail j x)
    _ = ε / 2 + ε / 2 := by
        rw [ENNReal.tsum_mul_left, hq, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
        congr 1
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_assoc, mul_comm ε 2,
          ← mul_assoc]
        congr 1
        rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
          mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    _ = ε := ENNReal.add_halves ε

end Hilbert

end QuantumFieldTightness
end NCG
