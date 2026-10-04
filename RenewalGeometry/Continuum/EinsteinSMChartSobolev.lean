/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMReducedClosure
import RenewalGeometry.Analysis.SobolevBoxCrEmbedding

/-!
# Negative-Sobolev stress convergence (`cor:reduced-stress`, `cor:stress-topology`,
  Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMReducedStress.lean` / `EinsteinSMMainLimit.lean` (cylinder
`(0,T) × 𝕋³` lifted to `ℝ⁴` with spatially periodic fields and tests, trivialised bundles, slab
chart boxes `Q = (t₀,t₁) × (0,1)³`, dual norms rendered as uniform estimates
`|ℓ_h(v) - ℓ(v)| ≤ ε ‖v‖`).

## The `H^m_0` test norm and the chart embedding

* `hmNorm Q m f = (Σ_{j ≤ m} ∫_Q ‖D^j f‖²)^{1/2}`: the `H^m` norm on the chart box of a test
  section (classical derivatives `D^j f = iteratedFDeriv`, sup norm on `ℝ⁴`, operator norms; for
  compactly supported smooth tests this is the `H^m_0(K)` norm, `Q` being a fundamental domain of
  the slab containing the test region); `hmTestNorm` sums it over the five entries of a test tuple.
* **`exists_crNorm_le_hmNorm`, `exists_testNorm_le_hmTestNorm`** (the embedding
  `H^m_0(K) ↪ C^r(K)` for `m > r + 2` in four dimensions): `‖v‖_{C^r} ≤ C ‖v‖_{H^m}` for every
  physical test of every region `K` whose time support lies in `(t₀,t₁)`, through
  `SobolevBoxCr.exists_slab_cr_bound` (rescaling and periodisation in time, `H^m(𝕋⁴) ⊂ C^r`).

## Corollaries

* `operationalStress_dual_bound`: unit-ball convergence of the operational stress implies the
  `ε ‖v‖` form (homogeneity), and hence convergence in the dual of every test norm dominating
  the `C^{r₀}` norm;
* **`reduced_stress_negSobolev`** (`cor:reduced-stress`, all clauses): along the subsequence of
  `reduced_closure`, strong `L¹` convergence of the Yang–Mills and Higgs stresses; convergence of
  the complete matter metric first variation in the dual `C^r` norm for every `r ≥ 1` and in
  `H^{-m}` for every integer `m > 4` (with `r = 2`); the operational stress converges to
  `T^SM dV_g` in `(𝒱_K^{r₀})^*` and in `H^{-m}` for every `m > r₀ + 2`;
* **`stress_topology_screen`** (`cor:stress-topology`, route (C4a), unconditional) and
  **`stress_topology`** (the certificate as stated; route (C4b) through the hypothesis of
  `main_limit`, i.e. the conclusion of `prop:dirac-stability`): along every strong-packet
  subsequence furnished by `thm:main-limit` (`main_limit_screen`, `main_limit`), the operational
  stress converges to `T^SM dV_g` in `(𝒱_K^{r₀})^*`, in distributions (each fixed test), and in
  `H^{-m}` for every integer `m > r₀ + 2` on each fixed compact test region.  The proof uses the
  proved reduced continuity (`StrongPacketOn.toReduced`, `matterMetricVariation_dual_tendsto`)
  and sectorwise consistency, not the Lipschitz estimate of `prop:variation-continuity`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace StressTopology

/-! ### The `H^m` test norm -/

section HmNorm

variable {T : ℝ}

/-- **The `H^m(Q)` norm** `(Σ_{j ≤ m} ∫_Q ‖D^j f‖²)^{1/2}` of a section on a chart box. -/
def hmNorm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (Q : ChartBox T) (m : ℕ)
    (f : E4 → F) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (m + 1), ∫ x in Q.set, ‖iteratedFDeriv ℝ j f x‖ ^ 2)

theorem hmNorm_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (Q : ChartBox T)
    (m : ℕ) (f : E4 → F) : 0 ≤ hmNorm Q m f := Real.sqrt_nonneg _

/-- **The `H^m` test norm** of a tuple `v = (k, a, η_H, η_Ψ, η_Ψ̄)`: the sum of the `H^m(Q)` norms
of its entries. -/
def hmTestNorm {C : Type} [Fintype C] (Q : ChartBox T) (m : ℕ) (v : FieldTuple C) : ℝ :=
  hmNorm Q m v.e + hmNorm Q m v.A + hmNorm Q m v.H + hmNorm Q m v.Ψ + hmNorm Q m v.Ψb

theorem hmTestNorm_nonneg {C : Type} [Fintype C] (Q : ChartBox T) (m : ℕ) (v : FieldTuple C) :
    0 ≤ hmTestNorm Q m v := by
  unfold hmTestNorm
  have := hmNorm_nonneg Q m v.e; have := hmNorm_nonneg Q m v.A
  have := hmNorm_nonneg Q m v.H; have := hmNorm_nonneg Q m v.Ψ
  have := hmNorm_nonneg Q m v.Ψb
  linarith

theorem slabChart_set_eq {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    (slabChart t₀ t₁ h0 h01 h1 (T := T)).set = SobolevBoxCr.slabBox (0 : Fin 4) t₀ t₁ := by
  ext x
  rw [mem_slabChart]
  simp only [SobolevBoxCr.slabBox, Set.mem_pi, mem_univ, true_implies, SobolevBoxCr.slabLo,
    SobolevBoxCr.slabHi]
  constructor
  · rintro ⟨ht, hs⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ht
    · simpa [Fin.succ_ne_zero] using hs j
  · intro h
    exact ⟨by simpa using h 0, fun j => by simpa [Fin.succ_ne_zero] using h j.succ⟩

/-- A compact test region inside `(t₀,t₁) × 𝕋³` has time support in some `[a,b] ⊂ (t₀,t₁)`. -/
theorem exists_time_Icc {K : CylRegion T} {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) :
    ∃ a b, t₀ < a ∧ b < t₁ ∧ ∀ p ∈ K.carrier, p.1 ∈ Icc a b := by
  set S := Prod.fst '' K.carrier
  have hS : IsCompact S := K.isCompact.image continuous_fst
  rcases S.eq_empty_or_nonempty with he | hne
  · refine ⟨(t₀ + t₁) / 2, (t₀ + t₁) / 2, by linarith, by linarith, fun p hp => ?_⟩
    exact absurd (he ▸ mem_image_of_mem Prod.fst hp : p.1 ∈ (∅ : Set ℝ)) (notMem_empty _)
  · obtain ⟨a, ha, hamin⟩ := hS.exists_isLeast hne
    obtain ⟨b, hb, hbmax⟩ := hS.exists_isGreatest hne
    obtain ⟨pa, hpa, rfl⟩ := ha
    obtain ⟨pb, hpb, rfl⟩ := hb
    exact ⟨pa.1, pb.1, (hK pa hpa).1, (hK pb hpb).2, fun p hp =>
      ⟨hamin (mem_image_of_mem _ hp), hbmax (mem_image_of_mem _ hp)⟩⟩

theorem cylTest_eq_zero_of_notMem_Icc {K : CylRegion T} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E4 → F} (hf : IsCylTest K f) {a b : ℝ}
    (hab : ∀ p ∈ K.carrier, p.1 ∈ Icc a b) (x : E4) (hx : x 0 ∉ Icc a b) : f x = 0 := by
  by_contra h
  exact hx (hab _ (hf.support (subset_tsupport f h)))

theorem cylTest_periodic_int {K : CylRegion T} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E4 → F} (hf : IsCylTest K f) (n : Fin 4 → ℤ) (hn : n 0 = 0)
    (x : E4) : f (x + fun i => (n i : ℝ)) = f x := by
  have e : (fun i => (n i : ℝ)) = spatialShift (fun j => n j.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hn]
    · simp
  rw [e]
  exact hf.periodic _ x

/-- **The chart Sobolev embedding `H^m_0(K) ↪ C^r(K)`, `m > r + 2` (four dimensions)**, for one
entry: there is `C` (depending on the chart and the fibre) with `‖f‖_{C^r} ≤ C ‖f‖_{H^m(Q)}` for
every smooth spatially periodic section supported in any region `K` whose time support lies in
`(t₀,t₁)`. -/
theorem exists_crNorm_le_hmNorm (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {r m : ℕ} (hrm : r + 2 < m) :
    ∃ C, 0 ≤ C ∧ ∀ (K : CylRegion T), (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) →
      ∀ f : E4 → F, IsCylTest K f → crNorm r f ≤ C * hmNorm (slabChart t₀ t₁ h0 h01 h1) m f := by
  have hj : ∀ j : ℕ, ∃ C, 0 ≤ C ∧ (j ≤ r → ∀ f : E4 → F, ContDiff ℝ ∞ f →
      (∀ n : Fin 4 → ℤ, n 0 = 0 → ∀ x, f (x + fun i => (n i : ℝ)) = f x) →
      ∀ a b, t₀ < a → b < t₁ → (∀ x : E4, x 0 ∉ Icc a b → f x = 0) →
      ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C * Real.sqrt
        ((∫ y in SobolevBoxCr.slabBox (0 : Fin 4) t₀ t₁, ‖f y‖ ^ 2) +
          ∫ y in SobolevBoxCr.slabBox (0 : Fin 4) t₀ t₁, ‖iteratedFDeriv ℝ m f y‖ ^ 2)) := by
    intro j
    by_cases hjr : j ≤ r
    · have hm : (Fintype.card (Fin 4) : ℝ) / 2 + j < m := by
        have : (j : ℝ) ≤ r := by exact_mod_cast hjr
        have h2 : ((r + 2 : ℕ) : ℝ) < m := by exact_mod_cast hrm
        simp only [Fintype.card_fin]; push_cast at h2; linarith
      obtain ⟨C, hC0, hC⟩ := SobolevBoxCr.exists_slab_cr_bound F (0 : Fin 4) h01 hm
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hjr⟩
  choose C hC0 hC using hj
  refine ⟨∑ j ∈ Finset.range (r + 1), C j, Finset.sum_nonneg fun j _ => hC0 j,
    fun K hK f hf => ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := exists_time_Icc h01 hK
  have hS : Real.sqrt ((∫ y in SobolevBoxCr.slabBox (0 : Fin 4) t₀ t₁, ‖f y‖ ^ 2) +
      ∫ y in SobolevBoxCr.slabBox (0 : Fin 4) t₀ t₁, ‖iteratedFDeriv ℝ m f y‖ ^ 2) ≤
      hmNorm (slabChart t₀ t₁ h0 h01 h1) m f := by
    unfold hmNorm
    rw [slabChart_set_eq]
    refine Real.sqrt_le_sqrt ?_
    have hm0 : 0 ≠ m := by omega
    have hsub : ({0, m} : Finset ℕ) ⊆ Finset.range (m + 1) := by
      intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
      setIntegral_nonneg (SobolevBoxCr.measurableSet_slabBox _ _ _) fun _ _ => sq_nonneg _)
    rw [Finset.sum_pair hm0]
    simp only [norm_iteratedFDeriv_zero]
  unfold crNorm
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ciSup_le fun x => ?_
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact (hC j hjr f hf.smooth (cylTest_periodic_int hf) a b ha hb (cylTest_eq_zero_of_notMem_Icc hf hab) x).trans
    (mul_le_mul_of_nonneg_left hS (hC0 j))

/-- **`‖v‖_{C^r} ≤ C ‖v‖_{H^m}` on physical tests, `m > r + 2`** (the embedding
`H^m_0(K) ↪ C^r(K)` of `cor:stress-topology`, applied entrywise): one constant for every region
`K` whose time support lies in `(t₀,t₁)`. -/
theorem exists_testNorm_le_hmTestNorm (C : Type) [Fintype C] {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {r m : ℕ} (hrm : r + 2 < m) :
    ∃ Cq, 0 ≤ Cq ∧ ∀ (left : C → Bool) (K : CylRegion T), (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) →
      ∀ v : CrTest left r K, ‖v‖ ≤ Cq * hmTestNorm (slabChart t₀ t₁ h0 h01 h1) m v.val := by
  obtain ⟨C1, h1C, hC1⟩ := exists_crNorm_le_hmNorm CoframeFibre h0 h01 h1 hrm
  obtain ⟨C2, h2C, hC2⟩ := exists_crNorm_le_hmNorm ConnFibre h0 h01 h1 hrm
  obtain ⟨C3, h3C, hC3⟩ := exists_crNorm_le_hmNorm HiggsFibre h0 h01 h1 hrm
  obtain ⟨C4, h4C, hC4⟩ := exists_crNorm_le_hmNorm (SpinorFibre C) h0 h01 h1 hrm
  refine ⟨C1 + C2 + C3 + C4, by positivity, fun left K hK v => ?_⟩
  obtain ⟨m1, m2, m3, m4, m5, -⟩ := v.val_mem
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have b1 := hC1 K hK _ m1; have b2 := hC2 K hK _ m2; have b3 := hC3 K hK _ m3
  have b4 := hC4 K hK _ m4; have b5 := hC4 K hK _ m5
  have n1 := hmNorm_nonneg Q m v.val.e; have n2 := hmNorm_nonneg Q m v.val.A
  have n3 := hmNorm_nonneg Q m v.val.H; have n4 := hmNorm_nonneg Q m v.val.Ψ
  have n5 := hmNorm_nonneg Q m v.val.Ψb
  rw [CrTest.norm_def, testNorm, hmTestNorm]
  nlinarith [mul_nonneg h2C n1, mul_nonneg h3C n1, mul_nonneg h4C n1,
    mul_nonneg h1C n2, mul_nonneg h3C n2, mul_nonneg h4C n2,
    mul_nonneg h1C n3, mul_nonneg h2C n3, mul_nonneg h4C n3,
    mul_nonneg h1C n4, mul_nonneg h2C n4, mul_nonneg h3C n4,
    mul_nonneg h1C n5, mul_nonneg h2C n5, mul_nonneg h3C n5]

/-- **Non-vacuity of the chart embedding**: the nonzero metric bump test `bumpTest` on
`K = [T/4, 3T/4] × 𝕋³` satisfies the hypotheses of `exists_testNorm_le_hmTestNorm` on the chart
`(T/8, 7T/8) × (0,1)³`, and its `H^m` test norm is positive. -/
theorem hmTestNorm_bumpTest_pos (hT : 0 < T) (C : Type) [Fintype C] (left : C → Bool)
    {r m : ℕ} (hrm : r + 2 < m) :
    0 < hmTestNorm (slabChart (T / 8) (7 * T / 8) (by positivity) (by linarith) (by linarith)
      (T := T)) m (bumpTest (C := C) hT left r).val := by
  obtain ⟨Cq, hCq0, hCq⟩ := exists_testNorm_le_hmTestNorm C (T := T) (t₀ := T / 8)
    (t₁ := 7 * T / 8) (by positivity) (by linarith) (by linarith) hrm
  have hK : ∀ p ∈ (middleRegion T hT).carrier, p.1 ∈ Ioo (T / 8) (7 * T / 8) := by
    rintro ⟨t, y⟩ ⟨⟨h1, h2⟩, -⟩
    exact ⟨by linarith, by linarith⟩
  have h := hCq left (middleRegion T hT) hK (bumpTest hT left r)
  have hpos := norm_bumpTest_pos (C := C) hT left r
  have hnn := hmTestNorm_nonneg (slabChart (T / 8) (7 * T / 8) (by positivity) (by linarith)
    (by linarith) (T := T)) m (bumpTest (C := C) hT left r).val
  by_contra hle
  push Not at hle
  have h0 := le_antisymm hle hnn
  rw [h0, mul_zero] at h
  linarith

end HmNorm

/-! ### Dual convergence of the matter metric variation and of the operational stress

The two statements below re-prove `EinsteinSM.matterMetricVariation_dual_tendsto` and
`EinsteinSM.operationalStress_tendsto` of `EinsteinSMReducedStress.lean` from the same library
lemmas (`smVariation_dual_tendsto`, the consistency defect), so that this file does not import
`EinsteinSMReducedStress.lean` (which cannot be imported together with
`EinsteinSMCertificatePacket.lean`, both declaring `ReducedConvergence.of_subseq`). -/

section Operational

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec) {r : ℕ} {K : CylRegion T}

theorem crNorm_zero_fun' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℕ) :
    crNorm r (0 : E4 → F) = 0 := by
  simp [crNorm]

omit [Fintype Ysec] in
theorem norm_metricTest_le' (v : CrTest FC.left r K) : ‖metricTest FC v‖ ≤ ‖v‖ := by
  rw [CrTest.norm_def, CrTest.norm_def]
  change crNorm r v.val.e + crNorm r (0 : E4 → ConnFibre) + crNorm r (0 : E4 → HiggsFibre) +
    crNorm r (0 : E4 → SpinorFibre FC.C) + crNorm r (0 : E4 → SpinorFibre FC.C) ≤ _
  simp only [crNorm_zero_fun', add_zero, testNorm]
  have := crNorm_nonneg r v.val.A; have := crNorm_nonneg r v.val.H
  have := crNorm_nonneg r v.val.Ψ; have := crNorm_nonneg r v.val.Ψb
  linarith

omit [Fintype Ysec] in
theorem metricTest_smul (c : ℝ) (v : CrTest FC.left r K) :
    metricTest FC (c • v) = c • metricTest FC v := by
  apply CrTest.val_injective
  rw [CrTest.val_smul]
  change FieldTuple.mk (c • v.val).e 0 0 0 0 = c • FieldTuple.mk v.val.e 0 0 0 0
  simp [FieldTuple.mk, FieldTuple.e]

/-- **Dual `C^r` convergence of the complete matter metric first variation** under reduced
convergence on a slab chart containing the time support of `K` (the dual clause of
`cor:reduced-stress`; same statement as `EinsteinSM.matterMetricVariation_dual_tendsto`). -/
theorem matterMetric_dual_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁)
    (h1 : t₁ < T) (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T FC.left} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    {L : LimitFields FC.C}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest FC.left r K,
      |-2 * firstVariation T FC (θ n) .standardModel (z n).z (metricTest FC v).val -
        stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  filter_upwards [smVariation_dual_tendsto FC h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp))
    hr hRC hyL hy0 (half_pos hε)] with n hn v
  have h := (hn (metricTest FC v)).trans
    (mul_le_mul_of_nonneg_left (norm_metricTest_le' FC v) (half_pos hε).le)
  unfold stressDistribution
  rw [show -2 * firstVariation T FC (θ n) .standardModel (z n).z (metricTest FC v).val -
      -2 * smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L (metricTest FC v) =
      -2 * (firstVariation T FC (θ n) .standardModel (z n).z (metricTest FC v).val -
        smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L (metricTest FC v)) by ring,
    abs_mul]
  norm_num
  linarith

/-- The operational stress functional `v ↦ -2 D𝒮_{SM,h}(z_h^d)[𝓘_h(k,0,0,0,0)]` minus the limit
`T^SM dV_g`. -/
def opStressDefect (reg : RegulatorSequence T FC) (n : ℕ) (Q : ChartBox T) (L : LimitFields FC.C)
    (θ₀ : CoefficientBank Ysec) (v : CrTest FC.left reg.r0 K) : ℝ :=
  -2 * reg.finiteSectorVariation n .standardModel (reg.lift n K (metricTest FC v)) -
    stressDistribution FC θ₀ Q L v

theorem opStressDefect_smul (reg : RegulatorSequence T FC) (n : ℕ) (Q : ChartBox T)
    (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) (c : ℝ) (v : CrTest FC.left reg.r0 K) :
    opStressDefect FC reg n Q L θ₀ (c • v) = c * opStressDefect FC reg n Q L θ₀ v := by
  unfold opStressDefect stressDistribution
  rw [metricTest_smul, smLimitVariation_smul]
  have e : reg.lift n K (c • metricTest FC v : CrTest FC.left reg.r0 K) =
      c • reg.lift n K (metricTest FC v) := map_smul (reg.lift n K) c _
  rw [e]
  simp only [RegulatorSequence.finiteSectorVariation, map_smul, smul_eq_mul]
  ring

/-- **The operational stress converges in `(𝒱_K^{r₀})^*`** (uniformly on the unit ball), from the
dual convergence of the matter metric first variation and sectorwise consistency `c_h(K) → 0`
(same statement as `EinsteinSM.operationalStress_tendsto`). -/
theorem operational_unit_tendsto (reg : RegulatorSequence T FC) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) (hcons : reg.FirstVariationConsistent) (Q : ChartBox T)
    (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec)
    (hconv : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
      |-2 * firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
          (metricTest FC v).val - stressDistribution FC θ₀ Q L v| ≤ ε * ‖v‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K, ‖v‖ ≤ 1 →
      |opStressDefect FC reg (σ k) Q L θ₀ v| ≤ ε := by
  have hc := ((hcons K).comp hσ).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr
    (by positivity : 0 < ε / 4)))
  filter_upwards [hconv (ε / 2) (half_pos hε), hc] with k hk hck v hv
  have hmv : ‖metricTest FC v‖ ≤ 1 := (norm_metricTest_le' FC v).trans hv
  have hmv' : testNorm reg.r0 (metricTest FC v : ↥(testSubmodule FC.left K)).1 ≤ 1 := hmv
  have hb : ENNReal.ofReal |reg.finiteSectorVariation (σ k) .standardModel
      (reg.lift (σ k) K (metricTest FC v)) - firstVariation T FC (reg.bank (σ k)) .standardModel
        (reg.fields (σ k)).z (metricTest FC v).val| ≤ reg.consistencyDefect (σ k) K := by
    unfold RegulatorSequence.consistencyDefect
    refine le_trans ?_ (Finset.single_le_sum (f := fun b : Sector => ⨆ (w : ↥(testSubmodule
      FC.left K)) (_ : testNorm reg.r0 w.1 ≤ 1), ENNReal.ofReal |reg.finiteSectorVariation (σ k) b
        (reg.lift (σ k) K w) - firstVariation T FC (reg.bank (σ k)) b (reg.fields (σ k)).z w.1|)
      (fun _ _ => zero_le) (Finset.mem_univ Sector.standardModel))
    exact le_iSup₂ (f := fun (w : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 w.1 ≤ 1) =>
      ENNReal.ofReal |reg.finiteSectorVariation (σ k) .standardModel (reg.lift (σ k) K w) -
        firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z w.1|)
      (metricTest FC v : ↥(testSubmodule FC.left K)) hmv'
  have e1 := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < ε / 4)).mp (hb.trans_lt hck)
  have e2 := (hk v).trans (mul_le_of_le_one_right (half_pos hε).le hv)
  unfold opStressDefect
  have := abs_sub_le (-2 * reg.finiteSectorVariation (σ k) .standardModel
      (reg.lift (σ k) K (metricTest FC v)))
    (-2 * firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
      (metricTest FC v).val) (stressDistribution FC θ₀ Q L v)
  have e3 : |-2 * reg.finiteSectorVariation (σ k) .standardModel
      (reg.lift (σ k) K (metricTest FC v)) - -2 * firstVariation T FC (reg.bank (σ k))
        .standardModel (reg.fields (σ k)).z (metricTest FC v).val| =
      2 * |reg.finiteSectorVariation (σ k) .standardModel (reg.lift (σ k) K (metricTest FC v)) -
        firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
          (metricTest FC v).val| := by
    rw [show -2 * reg.finiteSectorVariation (σ k) .standardModel
        (reg.lift (σ k) K (metricTest FC v)) - -2 * firstVariation T FC (reg.bank (σ k))
          .standardModel (reg.fields (σ k)).z (metricTest FC v).val =
        -2 * (reg.finiteSectorVariation (σ k) .standardModel (reg.lift (σ k) K (metricTest FC v)) -
          firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
            (metricTest FC v).val) by ring, abs_mul]
    norm_num
  linarith

/-- A homogeneous functional bounded by `ε` on the unit ball is bounded by `ε ‖v‖`. -/
theorem abs_le_mul_norm_of_unit {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ℓ : V → ℝ) (hhom : ∀ (c : ℝ) v, ℓ (c • v) = c * ℓ v) {ε : ℝ}
    (h : ∀ v, ‖v‖ ≤ 1 → |ℓ v| ≤ ε) (v : V) : |ℓ v| ≤ ε * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · have := hhom 0 0; rw [zero_smul, zero_mul] at this; rw [this]; simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hw : ‖‖v‖⁻¹ • v‖ ≤ 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := h _ hw
    rw [hhom, abs_mul, abs_inv, abs_of_pos hn] at h1
    calc |ℓ v| = ‖v‖ * (‖v‖⁻¹ * |ℓ v|) := by field_simp
      _ ≤ ‖v‖ * ε := mul_le_mul_of_nonneg_left h1 hn.le
      _ = ε * ‖v‖ := mul_comm _ _

/-- **Operational stress, `ε ‖v‖` form and transfer to any dominating test norm `q`**
(`‖v‖_{C^{r₀}} ≤ C_q q(v)`; for `q = ‖·‖_{H^m}`, `m > r₀ + 2`, this is the `H^{-m}` convergence). -/
theorem operational_dual_bound (reg : RegulatorSequence T FC) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) (hcons : reg.FirstVariationConsistent) (Q : ChartBox T)
    (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec)
    (hconv : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
      |-2 * firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
          (metricTest FC v).val - stressDistribution FC θ₀ Q L v| ≤ ε * ‖v‖)
    (q : CrTest FC.left reg.r0 K → ℝ) (hq0 : ∀ v, 0 ≤ q v) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hq : ∀ v, ‖v‖ ≤ Cq * q v) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
      |opStressDefect FC reg (σ k) Q L θ₀ v| ≤ ε * ‖v‖ ∧
        |opStressDefect FC reg (σ k) Q L θ₀ v| ≤ ε * q v := by
  filter_upwards [operational_unit_tendsto FC reg hσ hcons Q L θ₀ hconv
    (by positivity : 0 < ε / (Cq + 1))] with k hk v
  have hb := abs_le_mul_norm_of_unit (opStressDefect FC reg (σ k) Q L θ₀)
    (opStressDefect_smul FC reg (σ k) Q L θ₀) hk v
  have hn := norm_nonneg v
  have hdiv : ε / (Cq + 1) ≤ ε := div_le_self hε.le (by linarith)
  refine ⟨hb.trans (mul_le_mul_of_nonneg_right hdiv hn), ?_⟩
  have hqv : 0 ≤ q v := hq0 v
  calc |opStressDefect FC reg (σ k) Q L θ₀ v| ≤ ε / (Cq + 1) * ‖v‖ := hb
    _ ≤ ε / (Cq + 1) * (Cq * q v) := mul_le_mul_of_nonneg_left (hq v) (by positivity)
    _ ≤ ε * q v := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hqv
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- **Transfer of dual convergence to a dominating test norm** (for `q = ‖·‖_{H^m}` the `H^{-m}`
convergence): `|ℓ_n v - ℓ v| ≤ ε ‖v‖` eventually for every `ε` implies the same with `q(v)`. -/
theorem dual_transfer_q (q : CrTest FC.left r K → ℝ) (hq0 : ∀ v, 0 ≤ q v) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hq : ∀ v, ‖v‖ ≤ Cq * q v) (ℓ : ℕ → CrTest FC.left r K → ℝ) (ℓ₀ : CrTest FC.left r K → ℝ)
    (h : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v, |ℓ n v - ℓ₀ v| ≤ ε * ‖v‖) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v, |ℓ n v - ℓ₀ v| ≤ ε * q v := by
  intro ε hε
  filter_upwards [h (ε / (Cq + 1)) (by positivity)] with n hn v
  have hqv : 0 ≤ q v := hq0 v
  calc |ℓ n v - ℓ₀ v| ≤ ε / (Cq + 1) * ‖v‖ := hn v
    _ ≤ ε / (Cq + 1) * (Cq * q v) := mul_le_mul_of_nonneg_left (hq v) (by positivity)
    _ ≤ ε * q v := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hqv
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

end Operational

end StressTopology
end EinsteinSM
end RenewalGeometry
