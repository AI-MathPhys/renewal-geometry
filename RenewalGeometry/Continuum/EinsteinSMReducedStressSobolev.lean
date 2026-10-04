/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMReducedStress
import RenewalGeometry.Continuum.EinsteinSMChartSobolev

/-!
# `cor:reduced-stress`, all clauses (Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMReducedStress.lean` (slab charts `Q = (t₀,t₁) × (0,1)³`, trivialised
bundles, dual norms rendered as `|ℓ_h(v) - ℓ(v)| ≤ ε ‖v‖` eventually; `H^{-m}` convergence rendered
as the same estimate with the `H^m` test norm `hmTestNorm Q m` of `EinsteinSMChartSobolev.lean`
on a fixed compact test region `K` with time support in `(t₀,t₁)`).

**`reduced_stress_negSobolev`**: along a subsequence of `thm:reduced-closure` (`reduced_stress`):
(i) the Yang–Mills and Higgs stress densities converge strongly in `L¹`; (ii) the complete matter
metric first variation (`T^SM dV_g`, spin-connection chain included) converges in the dual `C^r`
test norm for every `r ≥ 1` (the manuscript states `r ≥ 2`); (iii) it converges in `H^{-m}` for
every integer `m > 4` (from (ii) with `r = 2` and the chart embedding `H^m_0(K) ↪ C²(K)`,
`exists_testNorm_le_hmTestNorm`); (iv) the operational stress
`⟨T_h, k⟩ = -2 D𝒮_{SM,h}(z_h^d)[𝓘_h(k,0,0,0,0)]` converges to `T^SM dV_g` in `(𝒱_K^{r₀})^*` and in
`H^{-m}` for every integer `m > r₀ + 2` (sectorwise consistency `eq:C1-consistency`).  Fermionic
stress: no `L¹` claim, as in the manuscript.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace StressTopology

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **`cor:reduced-stress`** (all clauses; see the module docstring). -/
theorem reduced_stress_negSobolev (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesReducedCertificate Q)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k)))
          (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
        RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
          (fun k x => ymStress (reg.bank (ns (ψ k))) (redJet (reg.fields (ns (ψ k))).z x))
          (fun x => ymStress θ₀ (limitJet L x)) ∧
        RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
          (fun k x => higgsStress (reg.bank (ns (ψ k))) (redJet (reg.fields (ns (ψ k))).z x))
          (fun x => higgsStress θ₀ (limitJet L x))) ∧
      (∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) →
        (∀ r : ℕ, 1 ≤ r → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left r K,
          |-2 * firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
              (reg.fields (ns (ψ k))).z (metricTest FC v).val -
            stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v| ≤ ε * ‖v‖) ∧
        (∀ m : ℕ, 4 < m → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left 2 K,
          |-2 * firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
              (reg.fields (ns (ψ k))).z (metricTest FC v).val -
            stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v| ≤
            ε * hmTestNorm (slabChart t₀ t₁ h0 h01 h1) m v.val) ∧
        (∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
          |opStressDefect FC reg (ns (ψ k)) (slabChart t₀ t₁ h0 h01 h1) L θ₀ v| ≤ ε * ‖v‖) ∧
        (∀ m : ℕ, reg.r0 + 2 < m → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
          ∀ v : CrTest FC.left reg.r0 K,
            |opStressDefect FC reg (ns (ψ k)) (slabChart t₀ t₁ h0 h01 h1) L θ₀ v| ≤
              ε * hmTestNorm (slabChart t₀ t₁ h0 h01 h1) m v.val)) := by
  obtain ⟨ψ, hψ, L, θ₀, hall, -⟩ := reduced_stress hT reg hcert hcons hstat hyuk ns hns
  refine ⟨ψ, hψ, L, θ₀, hall, fun K t₀ t₁ h0 h01 h1 hK => ?_⟩
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hRC := (hall t₀ t₁ h0 h01 h1).1
  obtain ⟨hyL, hy0⟩ := hyuk _ _ hRC.bank_tendsto
  have hdual : ∀ r : ℕ, 1 ≤ r → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left r K,
      |-2 * firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
          (reg.fields (ns (ψ k))).z (metricTest FC v).val -
        stressDistribution FC θ₀ Q L v| ≤ ε * ‖v‖ :=
    fun r hr ε hε => matterMetric_dual_tendsto FC h0 h01 h1 hK hr hRC hyL hy0 hε
  have hr0 : 1 ≤ reg.r0 := le_trans (by norm_num) reg.four_le_r0
  have hσ : Tendsto (fun k => ns (ψ k)) atTop atTop := (hns.comp hψ).tendsto_atTop
  refine ⟨hdual, fun m hm => ?_, fun ε hε => ?_, fun m hm => ?_⟩
  · obtain ⟨Cq, hCq0, hCq⟩ := exists_testNorm_le_hmTestNorm FC.C h0 h01 h1 (r := 2) (m := m)
      (by omega)
    exact dual_transfer_q FC (fun v : CrTest FC.left 2 K => hmTestNorm Q m v.val)
      (fun v => hmTestNorm_nonneg Q m v.val) hCq0 (hCq FC.left K hK) _ _ (hdual 2 (by norm_num))
  · filter_upwards [operational_dual_bound FC reg hσ hcons Q L θ₀ (hdual reg.r0 hr0)
      (fun v => ‖v‖) (fun v => norm_nonneg v) zero_le_one (fun v => by rw [one_mul]) hε]
      with k hk v
    exact (hk v).1
  · obtain ⟨Cq, hCq0, hCq⟩ := exists_testNorm_le_hmTestNorm FC.C h0 h01 h1 (r := reg.r0) (m := m)
      hm
    intro ε hε
    filter_upwards [operational_dual_bound FC reg hσ hcons Q L θ₀ (hdual reg.r0 hr0)
      (fun v : CrTest FC.left reg.r0 K => hmTestNorm Q m v.val)
      (fun v => hmTestNorm_nonneg Q m v.val) hCq0 (hCq FC.left K hK) hε] with k hk v
    exact (hk v).2

/-- **Non-vacuity of `cor:reduced-stress`**: the flat regulator satisfies every hypothesis. -/
example (hT : 0 < T) :=
  reduced_stress_negSobolev hT (flatRegulator T) (fun Q => flatRegulator_reducedCertificate T Q)
    (flatRegulator_consistent hT) flatRegulator_stationary (trivialCarrier_yukawaContinuous Unit)
    id strictMono_id

end StressTopology
end EinsteinSM
end RenewalGeometry
