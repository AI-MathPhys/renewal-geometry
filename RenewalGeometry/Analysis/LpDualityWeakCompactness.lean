/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# `Lᵖ`–`L^q` duality and weak sequential compactness in `Lᵖ`, `1 < p < ∞`
  (infrastructure for `thm:supp-curvature-compactness`, emergent-spacetime manuscript)

For a finite measure `μ` and Hölder-conjugate exponents `1 < p, q < ∞`:

* `indicatorSignedMeasure`, `density`: a bounded functional `Λ` on `L^q(μ)` defines the signed
  measure `A ↦ Λ(1_A)`, absolutely continuous w.r.t. `μ`, with Radon–Nikodym density `g`;
* `apply_simpleFunc`, `apply_bounded`: `Λ t = ∫ t g` for simple and bounded measurable `t`;
* `eLpNorm_le_of_forall_bounded`: the dual characterization `‖g‖_p ≤ C` from
  `|∫ t g| ≤ C ‖t‖_q` on bounded tests (truncation argument);
* `exists_lpPairing_eq`: **Riesz representation of `(L^q)*`** — every `Λ` is integration against
  some `g ∈ Lᵖ` with `‖g‖_p ≤ ‖Λ‖` (not in Mathlib);
* `exists_subseq_tendsto_weak`: **weak sequential compactness of bounded sets of `Lᵖ`**
  (countably generated σ-algebra), via the sequential Banach–Alaoglu theorem in `(L^q)*` and the
  representation theorem;
* `exists_subseq_tendsto_weak_fun`, `exists_subseq_tendsto_weak_family`,
  `exists_subseq_tendsto_weak_family_vec`: function-level forms, simultaneous extraction for
  finite families, and values in a finite-dimensional real normed space.
-/

open MeasureTheory Filter Topology ENNReal
open scoped NNReal

noncomputable section

namespace RenewalGeometry.LpDuality

set_option linter.unusedSectionVars false

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

section SignedMeasure

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem indicatorConstLp_congr_set {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (h : s = t) (c : ℝ) :
    indicatorConstLp q hs hμs c = indicatorConstLp q ht hμt c := by
  subst h; rfl

theorem sum_indicatorConstLp_eq (f : ℕ → Set α) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) (s : Finset ℕ) :
    ∑ i ∈ s, indicatorConstLp q (hf i) (measure_ne_top μ (f i)) (1 : ℝ) =
      indicatorConstLp q (Finset.measurableSet_biUnion s fun i _ => hf i)
        (measure_ne_top μ _) (1 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, indicatorConstLp_congr_set _ MeasurableSet.empty _ (by simp)
      (by simp), indicatorConstLp_empty]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih]
    have hdis : Disjoint (f a) (⋃ i ∈ s, f i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hd (fun h => ha (h ▸ hi))
    rw [← indicatorConstLp_disjoint_union (hf a) (Finset.measurableSet_biUnion s fun i _ => hf i)
      (measure_ne_top μ _) (measure_ne_top μ _) hdis]
    exact indicatorConstLp_congr_set _ _ _ _ (Finset.set_biUnion_insert a s f).symm _

theorem hasSum_indicatorConstLp (hq : q ≠ ∞) (f : ℕ → Set α) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun i => indicatorConstLp q (hf i) (measure_ne_top μ (f i)) (1 : ℝ))
      (indicatorConstLp q (MeasurableSet.iUnion hf) (measure_ne_top μ _) (1 : ℝ)) := by
  show Tendsto _ _ _
  simp_rw [sum_indicatorConstLp_eq (q := q) f hf hd]
  apply tendsto_indicatorConstLp_set hq
  have hsub : ∀ s : Finset ℕ, (⋃ i ∈ s, f i) ⊆ ⋃ i, f i := fun s =>
    Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i
  have heq : ∀ s : Finset ℕ, μ (symmDiff (⋃ i ∈ s, f i) (⋃ i, f i)) =
      μ (⋃ i, f i) - ∑ i ∈ s, μ (f i) := by
    intro s
    rw [symmDiff_of_le (hsub s), measure_sdiff (hsub s)
      (Finset.measurableSet_biUnion s fun i _ => hf i).nullMeasurableSet (measure_ne_top μ _),
      measure_biUnion_finset (fun i _ j _ hij => hd hij) (fun i _ => hf i)]
  simp_rw [heq]
  have hsum : Tendsto (fun s : Finset ℕ => ∑ i ∈ s, μ (f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
    rw [measure_iUnion hd hf]
    exact ENNReal.summable.hasSum
  have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := μ (⋃ i, f i))) hsum
    (Or.inl (measure_ne_top μ _))
  change Tendsto _ atTop _
  simpa using this

open Classical in
/-- The signed measure `A ↦ Λ(1_A)` of a bounded functional on `L^q(μ)` (finite `μ`, `q < ∞`). -/
def indicatorSignedMeasure (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) : SignedMeasure α where
  measureOf' A := if hA : MeasurableSet A then
      Λ (indicatorConstLp q hA (measure_ne_top μ A) (1 : ℝ)) else 0
  empty' := by
    simp only [dite_eq_left MeasurableSet.empty, indicatorConstLp_empty, map_zero]
  not_measurable' A hA := by simp only [hA, dite_false]
  m_iUnion' f hf hd := by
    rw [dif_pos (MeasurableSet.iUnion hf)]
    have h := (hasSum_indicatorConstLp hq f hf hd).mapL Λ
    have heq : ∀ i, (if hA : MeasurableSet (f i) then
        Λ (indicatorConstLp q hA (measure_ne_top μ (f i)) (1 : ℝ)) else 0) =
        Λ (indicatorConstLp q (hf i) (measure_ne_top μ (f i)) (1 : ℝ)) := fun i => dif_pos (hf i)
    simp only [heq]
    exact h

open Classical in
theorem indicatorSignedMeasure_apply (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) {A : Set α}
    (hA : MeasurableSet A) :
    indicatorSignedMeasure hq Λ A = Λ (indicatorConstLp q hA (measure_ne_top μ A) (1 : ℝ)) := by
  change (if hA : MeasurableSet A then _ else _) = _
  rw [dif_pos hA]

theorem indicatorSignedMeasure_absolutelyContinuous (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) :
    indicatorSignedMeasure hq Λ ≪ᵥ μ.toENNRealVectorMeasure := by
  intro A hA0
  by_cases hA : MeasurableSet A
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hA0
    rw [indicatorSignedMeasure_apply hq Λ hA]
    have hz : indicatorConstLp q hA (measure_ne_top μ A) (1 : ℝ) = 0 := by
      rw [← norm_eq_zero, norm_indicatorConstLp (by
        exact (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne') hq]
      simp only [measureReal_def, hA0, ENNReal.toReal_zero, norm_one, one_mul]
      exact Real.zero_rpow (by
        have h1 : (1 : ℝ≥0∞) ≤ q := Fact.out
        have : 0 < q.toReal := ENNReal.toReal_pos
          (lt_of_lt_of_le zero_lt_one h1).ne' hq
        positivity)
    rw [hz, map_zero]
  · exact (indicatorSignedMeasure hq Λ).not_measurable hA

/-- The Radon–Nikodym density of `A ↦ Λ(1_A)`. -/
def density (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) : α → ℝ :=
  (indicatorSignedMeasure hq Λ).rnDeriv μ

theorem integrable_density (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) :
    Integrable (density hq Λ) μ :=
  SignedMeasure.integrable_rnDeriv _ _

theorem setIntegral_density (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) {A : Set α}
    (hA : MeasurableSet A) :
    ∫ x in A, density hq Λ x ∂μ = Λ (indicatorConstLp q hA (measure_ne_top μ A) (1 : ℝ)) := by
  rw [← indicatorSignedMeasure_apply hq Λ hA, ← withDensityᵥ_apply
    (integrable_density hq Λ) hA, density, SignedMeasure.withDensityᵥ_rnDeriv_eq _ _
    (indicatorSignedMeasure_absolutelyContinuous hq Λ)]

theorem indicatorConstLp_eq_smul_one {A : Set α} (hA : MeasurableSet A) (hμ : μ A ≠ ∞) (c : ℝ) :
    indicatorConstLp q hA hμ c = c • indicatorConstLp q hA hμ (1 : ℝ) := by
  ext1
  filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hA) (hμs := hμ) (c := c),
    Lp.coeFn_smul c (indicatorConstLp q hA hμ (1 : ℝ)),
    indicatorConstLp_coeFn (p := q) (hs := hA) (hμs := hμ) (c := (1 : ℝ))] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  by_cases hx : x ∈ A <;> simp [hx]

theorem apply_indicatorConstLp (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) {A : Set α}
    (hA : MeasurableSet A) (hμ : μ A ≠ ∞) (c : ℝ) :
    Λ (indicatorConstLp q hA hμ c) = ∫ x, A.indicator (fun _ => c) x * density hq Λ x ∂μ := by
  rw [indicatorConstLp_eq_smul_one, map_smul, smul_eq_mul, ← setIntegral_density hq Λ hA,
    ← integral_indicator hA, ← integral_const_mul]
  congr 1
  funext x
  by_cases hx : x ∈ A <;> simp [hx]

/-- On simple functions, `Λ` is integration against the density. -/
theorem apply_simpleFunc (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) (s : SimpleFunc α ℝ) :
    Λ ((s.memLp_of_isFiniteMeasure q μ).toLp s) = ∫ x, s x * density hq Λ x ∂μ := by
  induction s using SimpleFunc.induction with
  | const c hA =>
    have h1 : ((SimpleFunc.piecewise _ hA (SimpleFunc.const α c) (SimpleFunc.const α 0)).memLp_of_isFiniteMeasure q μ).toLp
        (SimpleFunc.piecewise _ hA (SimpleFunc.const α c) (SimpleFunc.const α 0)) =
        indicatorConstLp q hA (measure_ne_top μ _) c := by
      rw [indicatorConstLp]
      apply MemLp.toLp_congr
      refine Filter.Eventually.of_forall fun x => ?_
      simp [SimpleFunc.coe_piecewise, Set.piecewise, Set.indicator]
    rw [h1, apply_indicatorConstLp hq]
    congr 1
  | @add f g _ hf hg =>
    have h1 : ((f + g).memLp_of_isFiniteMeasure q μ).toLp ⇑(f + g) =
        (f.memLp_of_isFiniteMeasure q μ).toLp f + (g.memLp_of_isFiniteMeasure q μ).toLp g := by
      rw [← MemLp.toLp_add]
      rfl
    obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
    obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
    have hif : Integrable (fun x => f x * density hq Λ x) μ :=
      (integrable_density hq Λ).bdd_mul f.aestronglyMeasurable (Eventually.of_forall hCf)
    have hig : Integrable (fun x => g x * density hq Λ x) μ :=
      (integrable_density hq Λ).bdd_mul g.aestronglyMeasurable (Eventually.of_forall hCg)
    rw [h1, map_add, hf, hg, ← integral_add hif hig]
    congr 1
    funext x
    simp [add_mul]

end SignedMeasure

section NormBound

theorem abs_mul_abs_rpow_sub_two {P : ℝ} (hP : 1 < P) (y : ℝ) :
    |y * |y| ^ (P - 2)| = |y| ^ (P - 1) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
  by_cases hy : y = 0
  · simp [hy, Real.zero_rpow (show P - 1 ≠ 0 by linarith)]
  · have hpos : 0 < |y| := abs_pos.2 hy
    rw [show P - 1 = 1 + (P - 2) by ring, Real.rpow_add hpos, Real.rpow_one]

theorem mul_abs_rpow_sub_two_mul_self {P : ℝ} (hP : 1 < P) (y : ℝ) :
    y * |y| ^ (P - 2) * y = |y| ^ P := by
  by_cases hy : y = 0
  · simp [hy, Real.zero_rpow (show P ≠ 0 by linarith)]
  · have hpos : 0 < |y| := abs_pos.2 hy
    rw [show P = 2 + (P - 2) by ring, Real.rpow_add hpos, Real.rpow_two]
    rw [show 2 + (P - 2) - 2 = P - 2 by ring, sq_abs]
    ring

/-- **Dual norm bound.** If a strongly measurable `g` satisfies `|∫ t g| ≤ C ‖t‖_q` for every
bounded strongly measurable `t`, then `‖g‖_p ≤ C` (`p, q` Hölder conjugate, `1 < p < ∞`). -/
theorem eLpNorm_le_of_forall_bounded {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    (hq : q ≠ ∞) {g : α → ℝ} (hgm : StronglyMeasurable g) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ t : α → ℝ, StronglyMeasurable t → (∃ c, ∀ x, ‖t x‖ ≤ c) →
      |∫ x, t x * g x ∂μ| ≤ C * (eLpNorm t q μ).toReal) :
    eLpNorm g p μ ≤ ENNReal.ofReal C := by
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hP1 : 1 < p.toReal := hPQ.lt
  have hp0 : p ≠ 0 := ENNReal.HolderConjugate.ne_zero p q
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  let B : ℕ → Set α := fun K => {x | |g x| ≤ K}
  have hB : ∀ K, MeasurableSet (B K) := fun K =>
    measurableSet_le hgm.measurable.abs measurable_const
  let gK : ℕ → α → ℝ := fun K => (B K).indicator g
  have hgK_meas : ∀ K, StronglyMeasurable (gK K) := fun K => hgm.indicator (hB K)
  have hgK_bd : ∀ K x, ‖gK K x‖ ≤ K := by
    intro K x
    by_cases hx : x ∈ B K
    · simp only [gK, Set.indicator_of_mem hx, Real.norm_eq_abs]; exact hx
    · simp [gK, Set.indicator_of_notMem hx]
  have hbound : ∀ K, eLpNorm (gK K) p μ ≤ ENNReal.ofReal C := by
    intro K
    have hmem : MemLp (gK K) p μ :=
      MemLp.of_bound (hgK_meas K).aestronglyMeasurable K (Eventually.of_forall (hgK_bd K))
    let t : α → ℝ := fun x => gK K x * |gK K x| ^ (p.toReal - 2)
    have ht_meas : StronglyMeasurable t :=
      ((hgK_meas K).measurable.mul ((hgK_meas K).measurable.abs.pow_const _)).stronglyMeasurable
    have habs_t : ∀ x, |t x| = |gK K x| ^ (p.toReal - 1) := fun x =>
      abs_mul_abs_rpow_sub_two hP1 _
    have htg : ∀ x, t x * g x = |gK K x| ^ p.toReal := by
      intro x
      by_cases hx : x ∈ B K
      · have : gK K x = g x := Set.indicator_of_mem hx g
        simp only [t]
        rw [this]
        exact mul_abs_rpow_sub_two_mul_self hP1 _
      · have : gK K x = 0 := Set.indicator_of_notMem hx g
        simp only [t]
        rw [this]
        simp [Real.zero_rpow (show p.toReal ≠ 0 by linarith)]
    have ht_bd : ∀ x, ‖t x‖ ≤ (K : ℝ) ^ (p.toReal - 1) := fun x => by
      rw [Real.norm_eq_abs, habs_t]
      exact Real.rpow_le_rpow (abs_nonneg _) (by simpa using hgK_bd K x) (by linarith)
    have htmem : MemLp t q μ :=
      MemLp.of_bound ht_meas.aestronglyMeasurable _ (Eventually.of_forall ht_bd)
    set J := ∫ x, |gK K x| ^ p.toReal ∂μ with hJdef
    have hJ0 : 0 ≤ J := integral_nonneg fun x => by positivity
    have hnorm_g : eLpNorm (gK K) p μ = ENNReal.ofReal (J ^ p.toReal⁻¹) := by
      rw [hmem.eLpNorm_eq_integral_rpow_norm hp0 hp]
      simp only [Real.norm_eq_abs, J]
    have hnorm_t : (eLpNorm t q μ).toReal = J ^ q.toReal⁻¹ := by
      rw [htmem.eLpNorm_eq_integral_rpow_norm hq0 hq, ENNReal.toReal_ofReal (by
        exact Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)]
      congr 1
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      simp only [Real.norm_eq_abs]
      rw [habs_t, ← Real.rpow_mul (abs_nonneg _), hPQ.sub_one_mul_conj]
    have hkey := hbd t ht_meas ⟨_, ht_bd⟩
    have hint : ∫ x, t x * g x ∂μ = J := by
      simp only [htg, J]
    rw [hint, abs_of_nonneg hJ0, hnorm_t] at hkey
    rw [hnorm_g]
    apply ENNReal.ofReal_le_ofReal
    rcases hJ0.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow (inv_ne_zero hPQ.ne_zero)]; exact hC
    · have hsplit : J ^ p.toReal⁻¹ * J ^ q.toReal⁻¹ = J := by
        rw [← Real.rpow_add h, hPQ.inv_add_inv_eq_one, Real.rpow_one]
      have hpos : 0 < J ^ q.toReal⁻¹ := Real.rpow_pos_of_pos h _
      have : J ^ p.toReal⁻¹ * J ^ q.toReal⁻¹ ≤ C * J ^ q.toReal⁻¹ := hsplit.symm ▸ hkey
      exact le_of_mul_le_mul_right this hpos
  have hlim : ∀ x, Tendsto (fun K => gK K x) atTop (𝓝 (g x)) := by
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈|g x|⌉₊] with K hK
    have hx : x ∈ B K := by
      show |g x| ≤ (K : ℝ)
      exact (Nat.le_ceil _).trans (by exact_mod_cast hK)
    exact (Set.indicator_of_mem hx g).symm
  calc eLpNorm g p μ ≤ atTop.liminf (fun K => eLpNorm (gK K) p μ) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun K => (hgK_meas K).aestronglyMeasurable) g
          (Eventually.of_forall hlim)
    _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

end NormBound

section Representation

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- On bounded strongly measurable functions, `Λ` is integration against the density. -/
theorem apply_bounded (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) {t : α → ℝ}
    (ht : StronglyMeasurable t) {c : ℝ} (hc : 0 ≤ c) (hbd : ∀ x, ‖t x‖ ≤ c) :
    Λ ((MemLp.of_bound ht.aestronglyMeasurable c (Eventually.of_forall hbd)).toLp t) =
      ∫ x, t x * density hq Λ x ∂μ := by
  have htq := MemLp.of_bound (p := q) (μ := μ) ht.aestronglyMeasurable c (Eventually.of_forall hbd)
  let s : ℕ → SimpleFunc α ℝ := ht.approxBounded c
  have hs_bd : ∀ n x, ‖s n x‖ ≤ c := fun n x => ht.norm_approxBounded_le hc n x
  have hs_lim : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (t x)) := fun x =>
    ht.tendsto_approxBounded_of_norm_le (hbd x)
  have hq1 : 1 ≤ q := Fact.out
  have hui : UnifIntegrable (fun n => ⇑(s n)) q μ := by
    refine unifIntegrable_of hq1 hq (fun n => (s n).aestronglyMeasurable) fun ε _ => ?_
    refine ⟨c.toNNReal + 1, fun n => ?_⟩
    have hzero : {x | c.toNNReal + 1 ≤ ‖s n x‖₊}.indicator (s n) = 0 := by
      funext x
      apply Set.indicator_of_notMem
      simp only [Set.mem_setOf_eq, not_le]
      rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_add, NNReal.coe_one]
      linarith [hs_bd n x, Real.le_coe_toNNReal c]
    rw [hzero, eLpNorm_zero]
    exact zero_le
  have hLp : Tendsto (fun n => eLpNorm (⇑(s n) - t) q μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae hq1 hq (fun n => (s n).aestronglyMeasurable) htq hui
      (Eventually.of_forall hs_lim)
  have hconv : Tendsto (fun n => ((s n).memLp_of_isFiniteMeasure q μ).toLp (s n)) atTop
      (𝓝 (htq.toLp t)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hLp
  have h1 := (Λ.continuous.tendsto _).comp hconv
  have h1' : Tendsto (fun n => ∫ x, s n x * density hq Λ x ∂μ) atTop (𝓝 (Λ (htq.toLp t))) := by
    refine h1.congr fun n => ?_
    exact apply_simpleFunc hq Λ (s n)
  have h2 : Tendsto (fun n => ∫ x, s n x * density hq Λ x ∂μ) atTop
      (𝓝 (∫ x, t x * density hq Λ x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => c * ‖density hq Λ x‖)
      (fun n => (s n).aestronglyMeasurable.mul (integrable_density hq Λ).1)
      ((integrable_density hq Λ).norm.const_mul c)
      (fun n => Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hs_bd n x) (norm_nonneg _))
      (Eventually.of_forall fun x => (hs_lim x).mul_const _)
  exact tendsto_nhds_unique h1' h2

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderConjugate q]

/-- The density of `Λ` lies in `Lᵖ`, with `‖g‖_p ≤ ‖Λ‖`. -/
theorem eLpNorm_density_le (hp : p ≠ ∞) (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) :
    eLpNorm (density hq Λ) p μ ≤ ENNReal.ofReal ‖Λ‖ := by
  apply eLpNorm_le_of_forall_bounded (g := density hq Λ) hp hq
    (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable (norm_nonneg Λ)
  rintro t ht ⟨c, hc⟩
  have hc' : ∀ x, ‖t x‖ ≤ max c 0 := fun x => (hc x).trans (le_max_left _ _)
  rw [← apply_bounded hq Λ ht (le_max_right c 0) hc', ← Real.norm_eq_abs]
  refine (Λ.le_opNorm _).trans_eq ?_
  rw [Lp.norm_toLp]

theorem memLp_density (hp : p ≠ ∞) (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) :
    MemLp (density hq Λ) p μ :=
  ⟨(SignedMeasure.measurable_rnDeriv _ _).aestronglyMeasurable,
    (eLpNorm_density_le hp hq Λ).trans_lt ENNReal.ofReal_lt_top⟩

/-- **Riesz representation of `(L^q)*`** (finite measure, `1 < q < ∞`, `p` the conjugate
exponent): every bounded linear functional on `L^q(μ)` is integration against a unique-up-to-null
`g ∈ Lᵖ(μ)`, with `‖g‖_p ≤ ‖Λ‖`. -/
theorem exists_lpPairing_eq (hp : p ≠ ∞) (hq : q ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ q μ)) :
    ∃ g : Lp ℝ p μ, ‖g‖ ≤ ‖Λ‖ ∧ ∀ h : Lp ℝ q μ, Λ h = ∫ x, h x * g x ∂μ := by
  have hmem := memLp_density hp hq Λ
  refine ⟨hmem.toLp _, ?_, ?_⟩
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (eLpNorm_density_le hp hq Λ)
  · set g := hmem.toLp (density hq Λ)
    let L := ContinuousLinearMap.lpPairing μ q p (ContinuousLinearMap.mul ℝ ℝ)
    have hL : ∀ h, L h g = ∫ x, h x * g x ∂μ := fun h => by
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      rfl
    suffices ∀ h, Λ h = L h g by intro h; rw [this, hL]
    refine Lp.induction hq _ ?_ ?_ ?_
    · intro c A hA hμA
      rw [Lp.simpleFunc.coe_indicatorConst, hL, apply_indicatorConstLp hq Λ hA]
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hA) (hμs := hμA.ne) (c := c),
        hmem.coeFn_toLp] with x h1 h2
      rw [h1, h2]
    · intro f f' hf hf' _ h1 h2
      rw [map_add, h1, h2, map_add, ContinuousLinearMap.add_apply]
    · exact isClosed_eq Λ.continuous (L.continuous.clm_apply continuous_const)

end Representation

section WeakCompactness

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Hölder bound for the integral pairing of `L^q` and `Lᵖ`. -/
theorem norm_integral_mul_le (h : Lp ℝ q μ) (f : Lp ℝ p μ) :
    ‖∫ x, h x * f x ∂μ‖ ≤ ‖h‖ * ‖f‖ := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  have h1 : ∫ x, h x * f x ∂μ = ∫ x, B.holder 1 h f x ∂μ :=
    (integral_congr_ae (B.coeFn_holder (r := 1) h f)).symm
  rw [h1]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← L1.norm_eq_integral_norm]
  refine (B.norm_holder_apply_apply_le (r := 1) h f).trans ?_
  have := ContinuousLinearMap.opNorm_mul_le (𝕜 := ℝ) (R := ℝ)
  calc ‖B‖ * ‖h‖ * ‖f‖ ≤ 1 * ‖h‖ * ‖f‖ := by gcongr
    _ = ‖h‖ * ‖f‖ := by ring

/-- The functional `h ↦ ∫ h f` on `L^q` induced by `f ∈ Lᵖ`. -/
def pairingFunctional (f : Lp ℝ p μ) : StrongDual ℝ (Lp ℝ q μ) :=
  (ContinuousLinearMap.lpPairing μ q p (ContinuousLinearMap.mul ℝ ℝ)).flip f

theorem pairingFunctional_apply (f : Lp ℝ p μ) (h : Lp ℝ q μ) :
    pairingFunctional (q := q) f h = ∫ x, h x * f x ∂μ := by
  rw [pairingFunctional, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  rfl

theorem norm_pairingFunctional_le (f : Lp ℝ p μ) :
    ‖pairingFunctional (q := q) f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h => by
    rw [pairingFunctional_apply, mul_comm]
    exact norm_integral_mul_le h f

/-- **Weak sequential compactness of bounded sets of `Lᵖ(μ)`, `1 < p < ∞`.**  For a finite
measure on a countably generated σ-algebra, every sequence bounded by `C` in `Lᵖ` has a
subsequence converging weakly (against every `h ∈ L^q`, `1/p + 1/q = 1`) to some `g ∈ Lᵖ` with
`‖g‖_p ≤ C`. -/
theorem exists_subseq_tendsto_weak [MeasurableSpace.CountablyGenerated α] (hp : p ≠ ∞)
    (hq : q ≠ ∞) (f : ℕ → Lp ℝ p μ) {C : ℝ} (hC : ∀ n, ‖f n‖ ≤ C) :
    ∃ g : Lp ℝ p μ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ‖g‖ ≤ C ∧ ∀ h : Lp ℝ q μ,
      Tendsto (fun n => ∫ x, h x * f (φ n) x ∂μ) atTop (𝓝 (∫ x, h x * g x ∂μ)) := by
  have : Fact (q ≠ ∞) := ⟨hq⟩
  have hcpt := WeakDual.isSeqCompact_closedBall ℝ (Lp ℝ q μ) (0 : StrongDual ℝ (Lp ℝ q μ)) C
  let x : ℕ → WeakDual ℝ (Lp ℝ q μ) := fun n =>
    StrongDual.toWeakDual (pairingFunctional (q := q) (f n))
  have hx : ∀ n, x n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall
      (0 : StrongDual ℝ (Lp ℝ q μ)) C := by
    intro n
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, x,
      StrongDual.toStrongDual_toWeakDual]
    exact (norm_pairingFunctional_le (f n)).trans (hC n)
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hcpt hx
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at ha
  obtain ⟨g, hg, hrep⟩ := exists_lpPairing_eq (μ := μ) hp hq (WeakDual.toStrongDual a)
  refine ⟨g, φ, hφ, hg.trans ha, fun h => ?_⟩
  have hev := ((WeakDual.eval_continuous h).tendsto a).comp hlim
  rw [← WeakDual.toStrongDual_apply, hrep h] at hev
  refine hev.congr fun n => ?_
  simp only [Function.comp_apply, x, StrongDual.toWeakDual_apply, pairingFunctional_apply]

end WeakCompactness

section Families

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
  [MeasurableSpace.CountablyGenerated α]

/-- Function-level form of `exists_subseq_tendsto_weak`. -/
theorem exists_subseq_tendsto_weak_fun (hp : p ≠ ∞) (hq : q ≠ ∞) (f : ℕ → α → ℝ)
    (hf : ∀ n, MemLp (f n) p μ) {B : ℝ≥0∞} (hB : B ≠ ∞) (hbd : ∀ n, eLpNorm (f n) p μ ≤ B) :
    ∃ g : α → ℝ, MemLp g p μ ∧ eLpNorm g p μ ≤ B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ h : α → ℝ, MemLp h q μ →
        Tendsto (fun n => ∫ x, h x * f (φ n) x ∂μ) atTop (𝓝 (∫ x, h x * g x ∂μ)) := by
  obtain ⟨G, φ, hφ, hG, hlim⟩ := exists_subseq_tendsto_weak (μ := μ) hp hq
    (fun n => (hf n).toLp (f n)) (C := B.toReal)
    (fun n => by rw [Lp.norm_toLp]; exact ENNReal.toReal_mono hB (hbd n))
  refine ⟨G, Lp.memLp G, ?_, φ, hφ, fun h hh => ?_⟩
  · rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top G), ← ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (by rw [← Lp.norm_def]; exact hG)
  · have hl := hlim (hh.toLp h)
    have hlimit : ∫ x, (hh.toLp h) x * G x ∂μ = ∫ x, h x * G x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hh.coeFn_toLp] with x hx
      rw [hx]
    rw [hlimit] at hl
    refine hl.congr fun n => ?_
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp, (hf (φ n)).coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]

/-- Simultaneous weak extraction for a finite family of bounded real `Lᵖ` sequences. -/
theorem exists_subseq_tendsto_weak_family {ι : Type*} [Fintype ι] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : ι → ℕ → α → ℝ) (hf : ∀ i n, MemLp (f i n) p μ) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hbd : ∀ i n, eLpNorm (f i n) p μ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ι → α → ℝ, ∀ i, MemLp (g i) p μ ∧
      ∀ h : α → ℝ, MemLp h q μ →
        Tendsto (fun n => ∫ x, h x * f i (φ n) x ∂μ) atTop (𝓝 (∫ x, h x * g i x ∂μ)) := by
  classical
  suffices H : ∀ s : Finset ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ι → α → ℝ, ∀ i ∈ s,
      MemLp (g i) p μ ∧ ∀ h : α → ℝ, MemLp h q μ →
        Tendsto (fun n => ∫ x, h x * f i (φ n) x ∂μ) atTop (𝓝 (∫ x, h x * g i x ∂μ)) by
    obtain ⟨φ, hφ, g, hg⟩ := H Finset.univ
    exact ⟨φ, hφ, g, fun i => hg i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨φ, hφ, g, hg⟩ := ih
    obtain ⟨ga, hga, -, ψ, hψ, hlim⟩ := exists_subseq_tendsto_weak_fun hp hq
      (fun n => f a (φ n)) (fun n => hf a _) hB (fun n => hbd a _)
    refine ⟨φ ∘ ψ, hφ.comp hψ, Function.update g a ga, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · simp only [Function.update_self]
      exact ⟨hga, hlim⟩
    · have hne : i ≠ a := fun h => ha (h ▸ hi')
      simp only [Function.update_of_ne hne]
      exact ⟨(hg i hi').1, fun h hh => ((hg i hi').2 h hh).comp hψ.tendsto_atTop⟩

/-- Expansion of an `L^q`-weighted vector integral in a basis. -/
theorem integral_smul_eq_sum_basis {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {r : ℕ} (b : Module.Basis (Fin r) ℝ V) (h : α → ℝ) (u : α → V)
    (hint : ∀ j, Integrable (fun x => h x * b.coord j (u x)) μ) :
    ∫ x, h x • u x ∂μ = ∑ j, (∫ x, h x * b.coord j (u x) ∂μ) • b j := by
  have hpt : ∀ x, h x • u x = ∑ j, (h x * b.coord j (u x)) • b j := by
    intro x
    conv_lhs => rw [← b.sum_repr (u x), Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, Module.Basis.coord_apply]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ => (hint j).smul_const (b j)]
  simp_rw [integral_smul_const]

/-- **Weak sequential compactness for finite families of bounded `Lᵖ` sequences with values in a
finite-dimensional real normed space** (finite measure, countably generated σ-algebra,
`1 < p < ∞`): weak convergence means convergence of `∫ h • fₙ` for every scalar `h ∈ L^q`. -/
theorem exists_subseq_tendsto_weak_family_vec {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : ι → ℕ → α → V) (hf : ∀ i n, MemLp (f i n) p μ) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hbd : ∀ i n, eLpNorm (f i n) p μ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ι → α → V, ∀ i, MemLp (g i) p μ ∧
      ∀ h : α → ℝ, MemLp h q μ →
        Tendsto (fun n => ∫ x, h x • f i (φ n) x ∂μ) atTop (𝓝 (∫ x, h x • g i x ∂μ)) := by
  classical
  set r := Module.finrank ℝ V
  let b : Module.Basis (Fin r) ℝ V := Module.finBasis ℝ V
  let c : Fin r → V →L[ℝ] ℝ := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  have hc : ∀ j v, c j v = b.coord j v := fun j v => rfl
  set M : ℝ := ∑ j, ‖c j‖
  have hcM : ∀ j, ‖c j‖ ≤ M := fun j =>
    Finset.single_le_sum (f := fun j => ‖c j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  let F : ι × Fin r → ℕ → α → ℝ := fun ij n x => c ij.2 (f ij.1 n x)
  have hF : ∀ ij n, MemLp (F ij n) p μ := fun ij n => (hf ij.1 n).continuousLinearMap_comp _
  have hFbd : ∀ ij n, eLpNorm (F ij n) p μ ≤ ENNReal.ofReal M * B := by
    intro ij n
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := f ij.1 n) (c := M)
      (Eventually.of_forall fun x => ?_) p).trans ?_
    · exact (c ij.2).le_opNorm _ |>.trans (by gcongr; exact hcM ij.2)
    · gcongr; exact hbd ij.1 n
  obtain ⟨φ, hφ, G, hG⟩ := exists_subseq_tendsto_weak_family hp hq F hF
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) hFbd
  refine ⟨φ, hφ, fun i x => ∑ j, G (i, j) x • b j, fun i => ⟨?_, fun h hh => ?_⟩⟩
  · exact memLp_finsetSum _ fun j _ =>
      ((hG (i, j)).1.continuousLinearMap_comp
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (b j)) : _)
  · have hint : ∀ n j, Integrable (fun x => h x * b.coord j (f i (φ n) x)) μ := fun n j =>
      hh.integrable_mul (hF (i, j) (φ n))
    have hintG : ∀ j, Integrable (fun x => h x * b.coord j (∑ j', G (i, j') x • b j')) μ := by
      intro j
      have : (fun x => h x * b.coord j (∑ j', G (i, j') x • b j')) = fun x => h x * G (i, j) x := by
        funext x
        simp [Module.Basis.coord_apply, map_sum, Finsupp.single_apply]
      rw [this]
      exact hh.integrable_mul (hG (i, j)).1
    rw [integral_smul_eq_sum_basis b h _ hintG]
    simp_rw [integral_smul_eq_sum_basis b h _ (hint _)]
    refine tendsto_finset_sum _ fun j _ => Tendsto.smul_const ?_ (b j)
    have hlim := (hG (i, j)).2 h hh
    have : (fun x => h x * b.coord j (∑ j', G (i, j') x • b j')) = fun x => h x * G (i, j) x := by
      funext x
      simp [Module.Basis.coord_apply, map_sum, Finsupp.single_apply]
    rw [this]
    exact hlim

end Families

end RenewalGeometry.LpDuality
