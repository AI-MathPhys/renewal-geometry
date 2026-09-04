/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCInitialMixtureExact
import NCG.Grand.MetzlerPerronExponentExact

/-!
# The SCGF of the genuine finite-CTMC additive path observable

The finite-time Feynman--Kac identity transfers the proved Perron asymptotic
to the actual stochastic exponential moment. Positive escape rates and
irreducibility of the tilted Metzler matrix are explicit hypotheses here.
-/

open Filter Topology

namespace NCG.FiniteCTMCPathSCGF

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCFeynmanKacPathMoment
open FiniteCTMCInitialMixture MetzlerExponentialPositivity MetzlerPerronExponent
open PerronSCGFSandwich

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The scaled log of the genuine exponential path moment converges to the
canonical Perron exponent, for any nonzero nonnegative initial distribution. -/
theorem tendsto_scaled_log_pathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hpne : ∃ x, 0 < p x)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hirr : IsIrreducibleMetzler (tilt L v g k)) :
    Tendsto
      (fun T : ℝ => Real.log (pathMoment x₀ p L hL hescape v g k T (fun _ => 1)) / T)
      atTop (𝓝 (exponent (tilt L v g k))) := by
  letI : Nonempty S := ⟨x₀⟩
  apply (tiltedGenerator_SCGLimit_eq_exponent L hL v g k hirr p hp hpne).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [pathMoment_eq_exponentialEntry_pairing L hL hescape x₀ p hp v g k T
    (fun _ => 1) hT]
  rfl

/-- Probability normalization supplies the nonzero initial weight required
by Perron asymptotics; no full-support assumption is needed. -/
theorem tendsto_scaled_log_pathMoment_of_probability
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hirr : IsIrreducibleMetzler (tilt L v g k)) :
    Tendsto
      (fun T : ℝ => Real.log (pathMoment x₀ p L hL hescape v g k T (fun _ => 1)) / T)
      atTop (𝓝 (exponent (tilt L v g k))) := by
  apply tendsto_scaled_log_pathMoment L hL hescape x₀ p hp _ v g k hirr
  by_contra! hn
  have hz : ∀ x, p x = 0 := fun x => le_antisymm (hn x) (hp x)
  simp [hz] at hsum

end

end NCG.FiniteCTMCPathSCGF
