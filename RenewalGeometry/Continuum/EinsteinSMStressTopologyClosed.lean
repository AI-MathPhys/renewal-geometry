/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMStressTopology
import RenewalGeometry.Continuum.EinsteinSMDiracStability

/-!
# `cor:stress-topology`, closed (Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMStressTopology.lean`.

* **`stress_topology_closed`**: `cor:stress-topology` under exactly the hypotheses of
  `main_limit_closed` (`thm:main-limit`, the compactness certificate as stated, route (C4a) or
  (C4b) on each chart box).  The route-(C4b) hypothesis `hdirac` of `stress_topology` is
  discharged by `prop:dirac-stability` (`DiracStab.diracRoute_spinorH1Cauchy`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace StressTopology

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **`cor:stress-topology` (closed)**: assume the hypotheses of `thm:main-limit` (the classical
compactness certificate on every chart box with route (C4a) or (C4b), the coframe chart condition,
sectorwise consistency `eq:C1-consistency`, the source bounds with vanishing source residual,
Yukawa continuity).  Every cutoff subsequence has a further subsequence furnished by
`thm:main-limit` (strong packet, convergence of the first variations, `eq:main-stationary`,
`eq:Einstein-SM`) along which the operational stress
`⟨T_h, k⟩ = -2 D𝒮_{SM,h}[𝓘_h(k,0,0,0,0)]` converges to `T^SM dV_g` in `(𝒱_K^{r₀})^*`, in
distributions, and in `H^{-m}` for every integer `m > r₀ + 2` on every fixed compact test region.
Route (C4b) is discharged by `prop:dirac-stability`. -/
theorem stress_topology_closed (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
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
              ε * hmTestNorm (slabChart t₀ t₁ h0 h01 h1) m v.val) :=
  stress_topology hT reg hcert hch (fun Q h => DiracStab.diracRoute_spinorH1Cauchy Q h) hcons
    hsrc hvan hyuk ns hns

/-- **Non-vacuity of `stress_topology_closed`**: the flat regulator satisfies every hypothesis. -/
example (hT : 0 < T) :=
  stress_topology_closed hT (flatRegulator T) (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) (flatRegulator_consistent hT) flatRegulator_sourceBounds
    (fun K => by simp) (trivialCarrier_yukawaContinuous Unit) id strictMono_id

end StressTopology
end EinsteinSM
end RenewalGeometry
