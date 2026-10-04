/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMMainLimit
import RenewalGeometry.Continuum.EinsteinSMChartSobolev

/-!
# Distributional and negative-Sobolev stress convergence (`cor:stress-topology`,
  Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMMainLimit.lean` and `EinsteinSMChartSobolev.lean`.

`cor:stress-topology`: assume sectorwise consistency (`eq:C1-consistency`); along every
strong-packet subsequence furnished by `thm:main-limit`, the operational stress
`⟨T_h, k⟩ = -2 D𝒮_{SM,h}(z_h^d)[𝓘_h(k,0,0,0,0)]` converges to `T^SM dV_g` in distributions, and on
each fixed compact test region in `H^{-m}` for every integer `m > r₀ + 2`.

* `stress_topology_of_packet`: along any subsequence with strong-packet convergence (coframe chart
  condition, compact banks, Yukawa continuity, consistency), on every test region `K` with time
  support in `(t₀,t₁)`: convergence in `(𝒱_K^{r₀})^*` (`ε ‖v‖` form), in distributions (each test
  `v`), and in `H^{-m}` (`ε ‖v‖_{H^m}`) for every `m > r₀ + 2`.  The route: strong packet ⇒
  reduced convergence (`StrongPacketOn.toReduced`), the proved reduced continuity of the matter
  metric variation, consistency, homogeneity, and the chart embedding `H^m_0 ↪ C^{r₀}`
  (`exists_testNorm_le_hmTestNorm`).  The Lipschitz estimate of `prop:variation-continuity` is
  not used.
* **`stress_topology_screen`**: instantiated with the subsequences of `main_limit_screen`
  (`thm:main-limit`, route (C4a), unconditional).
* **`stress_topology`**: instantiated with the subsequences of `main_limit` (the certificate as
  stated, (C4a) or (C4b)); its hypothesis `hdirac` is the conclusion of `prop:dirac-stability` on
  the (C4b) charts, exactly as in `main_limit`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace StressTopology

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **Stress topology along a strong-packet subsequence.** -/
theorem stress_topology_of_packet (reg : RegulatorSequence T FC)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, reg.bank n ∈ P)
    (hcons : reg.FirstVariationConsistent) (hyuk : FC.YukawaContinuous) {σ : ℕ → ℕ}
    (hσ : StrictMono σ) {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hSP : StrongPacket (fun k => reg.fields (σ k)) (fun k => reg.bank (σ k)) L θ₀) :
    ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) →
      (∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
        |opStressDefect FC reg (σ k) (slabChart t₀ t₁ h0 h01 h1) L θ₀ v| ≤ ε * ‖v‖) ∧
      (∀ v : CrTest FC.left reg.r0 K,
        Tendsto (fun k => -2 * reg.finiteSectorVariation (σ k) .standardModel
          (reg.lift (σ k) K (metricTest FC v))) atTop
          (𝓝 (stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v))) ∧
      (∀ m : ℕ, reg.r0 + 2 < m → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
        ∀ v : CrTest FC.left reg.r0 K,
          |opStressDefect FC reg (σ k) (slabChart t₀ t₁ h0 h01 h1) L θ₀ v| ≤
            ε * hmTestNorm (slabChart t₀ t₁ h0 h01 h1) m v.val) := by
  intro K t₀ t₁ h0 h01 h1 hK
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  obtain ⟨P, hP, hθP⟩ := hbank
  obtain ⟨Ke, hKe, hKn⟩ := hch Q
  have hRC : ReducedConvergence Q (fun k => reg.fields (σ k)) (fun k => reg.bank (σ k)) L θ₀ :=
    (hSP.local_conv Q).toReduced ⟨Ke, hKe, fun k => hKn _⟩ ⟨P, hP, fun k => hθP _⟩
      hSP.bank_tendsto
  obtain ⟨hyL, hy0⟩ := hyuk _ _ hRC.bank_tendsto
  have hr0 : 1 ≤ reg.r0 := le_trans (by norm_num) reg.four_le_r0
  have hdual : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
      |-2 * firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z
          (metricTest FC v).val - stressDistribution FC θ₀ Q L v| ≤ ε * ‖v‖ :=
    fun ε hε => matterMetric_dual_tendsto FC h0 h01 h1 hK hr0 hRC hyL hy0 hε
  have hop : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
      |opStressDefect FC reg (σ k) Q L θ₀ v| ≤ ε * ‖v‖ := fun ε hε => by
    filter_upwards [operational_dual_bound FC reg hσ.tendsto_atTop hcons Q L θ₀ hdual
      (fun v => ‖v‖) (fun v => norm_nonneg v) zero_le_one (fun v => by rw [one_mul]) hε]
      with k hk v
    exact (hk v).1
  refine ⟨hop, fun v => ?_, fun m hm ε hε => ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hop (ε / (‖v‖ + 1)) (by positivity)] with k hk
    have h := hk v
    rw [Real.dist_eq]
    unfold opStressDefect at h
    have hv := norm_nonneg v
    calc _ ≤ ε / (‖v‖ + 1) * ‖v‖ := h
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  · obtain ⟨Cq, hCq0, hCq⟩ := exists_testNorm_le_hmTestNorm FC.C h0 h01 h1 (r := reg.r0)
      (m := m) hm
    filter_upwards [operational_dual_bound FC reg hσ.tendsto_atTop hcons Q L θ₀ hdual
      (fun v : CrTest FC.left reg.r0 K => hmTestNorm Q m v.val)
      (fun v => hmTestNorm_nonneg Q m v.val) hCq0 (hCq FC.left K hK) hε] with k hk v
    exact (hk v).2

/-- **`cor:stress-topology`, route (C4a)** (unconditional): under the hypotheses of
`main_limit_screen` (`thm:main-limit`, spinor screen route on every chart box), every cutoff
subsequence has a further subsequence furnished by `thm:main-limit` (strong packet, convergence of
the first variations, `eq:main-stationary`, `eq:Einstein-SM`) along which the operational stress
converges to `T^SM dV_g` in `(𝒱_K^{r₀})^*`, in distributions, and in `H^{-m}` for every integer
`m > r₀ + 2` on every fixed compact test region. -/
theorem stress_topology_screen (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hroute : ∀ Q : ChartBox T, SpinorScreenRoute Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      θ₀ ∈ physicalBanks ∧
      StrongPacket (fun k => reg.fields (ns (ψ k))) (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      FirstVariationsConverge FC reg.r0 (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ ∧
      ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) →
        (∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
          |opStressDefect FC reg (ns (ψ k)) (slabChart t₀ t₁ h0 h01 h1) L θ₀ v| ≤ ε * ‖v‖) ∧
        (∀ v : CrTest FC.left reg.r0 K,
          Tendsto (fun k => -2 * reg.finiteSectorVariation (ns (ψ k)) .standardModel
            (reg.lift (ns (ψ k)) K (metricTest FC v))) atTop
            (𝓝 (stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v))) ∧
        (∀ m : ℕ, reg.r0 + 2 < m → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
          ∀ v : CrTest FC.left reg.r0 K,
            |opStressDefect FC reg (ns (ψ k)) (slabChart t₀ t₁ h0 h01 h1) L θ₀ v| ≤
              ε * hmTestNorm (slabChart t₀ t₁ h0 h01 h1) m v.val) := by
  obtain ⟨ψ, hψ, L, θ₀, h1, h2, h3, h4, h5⟩ := main_limit_screen hT reg hcert hch hroute hcons
    hsrc hvan hyuk ns hns
  exact ⟨ψ, hψ, L, θ₀, h1, h2, h3, h4, h5, stress_topology_of_packet (σ := fun k => ns (ψ k))
    reg hch (hcert (midChart hT)).bank_compact hcons hyuk (hns.comp hψ) h2⟩

/-- **`cor:stress-topology`, the certificate as stated** (route (C4a) or (C4b) on each chart box):
the same conclusions along the subsequences furnished by `main_limit`, whose hypothesis `hdirac`
(the conclusion of `prop:dirac-stability` on the (C4b) charts) is inherited. -/
theorem stress_topology (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hdirac : ∀ Q : ChartBox T, DiracStabilityRoute Q reg.fields → SpinorH1Cauchy Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      θ₀ ∈ physicalBanks ∧
      StrongPacket (fun k => reg.fields (ns (ψ k))) (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      FirstVariationsConverge FC reg.r0 (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ ∧
      ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) →
        (∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
          |opStressDefect FC reg (ns (ψ k)) (slabChart t₀ t₁ h0 h01 h1) L θ₀ v| ≤ ε * ‖v‖) ∧
        (∀ v : CrTest FC.left reg.r0 K,
          Tendsto (fun k => -2 * reg.finiteSectorVariation (ns (ψ k)) .standardModel
            (reg.lift (ns (ψ k)) K (metricTest FC v))) atTop
            (𝓝 (stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v))) ∧
        (∀ m : ℕ, reg.r0 + 2 < m → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
          ∀ v : CrTest FC.left reg.r0 K,
            |opStressDefect FC reg (ns (ψ k)) (slabChart t₀ t₁ h0 h01 h1) L θ₀ v| ≤
              ε * hmTestNorm (slabChart t₀ t₁ h0 h01 h1) m v.val) := by
  obtain ⟨ψ, hψ, L, θ₀, h1, h2, h3, h4, h5⟩ := main_limit hT reg hcert hch hdirac hcons
    hsrc hvan hyuk ns hns
  exact ⟨ψ, hψ, L, θ₀, h1, h2, h3, h4, h5, stress_topology_of_packet (σ := fun k => ns (ψ k))
    reg hch (hcert (midChart hT)).bank_compact hcons hyuk (hns.comp hψ) h2⟩

/-- **Non-vacuity of `cor:stress-topology`** (route (C4a)): the flat regulator satisfies every
hypothesis of `stress_topology_screen`. -/
example (hT : 0 < T) :=
  stress_topology_screen hT (flatRegulator T) (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) (flatRegulator_spinorScreenRoute T)
    (flatRegulator_consistent hT) flatRegulator_sourceBounds (fun K => by simp)
    (trivialCarrier_yukawaContinuous Unit) id strictMono_id

/-- **Non-vacuity of `stress_topology`** (with the route-(C4b) hypothesis). -/
example (hT : 0 < T) :=
  stress_topology hT (flatRegulator T) (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) (fun Q _ => flatRegulator_spinorH1Cauchy Q)
    (flatRegulator_consistent hT) flatRegulator_sourceBounds (fun K => by simp)
    (trivialCarrier_yukawaContinuous Unit) id strictMono_id

end StressTopology
end EinsteinSM
end RenewalGeometry
