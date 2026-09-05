/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Almost-sure convergence of empirical second moments

Upgrade of `cor:self-averaged-flat` (flagship) / `thm:self-averaging`
(lorentzian track): the earlier record proves the concentration
mechanism for pairwise **uncorrelated** reset fluctuations at the
variance level.  Here the almost-sure statement itself is proved for
pairwise **independent identically distributed** direction sequences,
via Etemadi's strong law of large numbers
(`ProbabilityTheory.strong_law_ae`):

* `empirical_second_moment_strong_law` — for a pairwise independent
  identically distributed sequence of bounded direction vectors
  `θ_a : Ω → (Fin 3 → ℝ)`, almost surely every entry of the empirical
  second moment `n⁻¹ ∑_{a<n} θ_a θ_aᵀ` converges to the entry of the
  limit moment `M_* = 𝔼[θ₀ θ₀ᵀ]`.

Together with the proved Lipschitz symbol dependence and band-limited
convergence (`quadratic_form_lipschitz`, `band_symbol_bound`), this
turns moment concentration into operator convergence along almost
every realization, which is the manuscript's corollary in the
i.i.d. phase.  The general stationary-**ergodic** form needs the
pointwise Birkhoff theorem, which Mathlib does not yet provide (only
the von Neumann mean ergodic theorem); that generalization remains a
noted step.
-/

namespace NCG

open Filter Function MeasureTheory ProbabilityTheory

/-- **Almost-sure empirical second moments** (`cor:self-averaged-flat`,
i.i.d. phase): for a pairwise independent identically distributed
sequence of measurable direction vectors, almost surely every entry
of the empirical second moment converges to the corresponding entry
of `𝔼[θ₀ θ₀ᵀ]`. -/
theorem empirical_second_moment_strong_law
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (θ : ℕ → Ω → Fin 3 → ℝ)
    (hmeas : ∀ a, Measurable (θ a))
    (hindep : Pairwise ((IndepFun · · μ) on θ))
    (hident : ∀ a, IdentDistrib (θ a) (θ 0) μ μ)
    (hbound : ∀ a ω i, |θ a ω i| ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ i j : Fin 3,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          ∑ a ∈ Finset.range n, θ a ω i * θ a ω j)
        atTop (nhds (μ[fun ω => θ 0 ω i * θ 0 ω j])) := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  -- the entry sequence `X a ω = θ_a(ω)_i θ_a(ω)_j`
  set X : ℕ → Ω → ℝ := fun a ω => θ a ω i * θ a ω j with hX
  have hφmeas : Measurable fun v : Fin 3 → ℝ => v i * v j :=
    (measurable_pi_apply i).mul (measurable_pi_apply j)
  have hXmeas : ∀ a, Measurable (X a) :=
    fun a => hφmeas.comp (hmeas a)
  -- integrability from the direction bound
  have hXbound : ∀ a ω, ‖X a ω‖ ≤ 1 := by
    intro a ω
    rw [hX, Real.norm_eq_abs, abs_mul]
    calc |θ a ω i| * |θ a ω j| ≤ 1 * 1 :=
        mul_le_mul (hbound a ω i) (hbound a ω j)
          (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hint : Integrable (X 0) μ := by
    refine ⟨(hXmeas 0).aestronglyMeasurable, ?_⟩
    refine MeasureTheory.HasFiniteIntegral.of_bounded (C := 1) ?_
    exact ae_of_all _ fun ω => hXbound 0 ω
  -- independence and identical distribution pass through the entries
  have hXindep : Pairwise ((IndepFun · · μ) on X) := by
    intro a b hab
    exact (hindep hab).comp hφmeas hφmeas
  have hXident : ∀ a, IdentDistrib (X a) (X 0) μ μ :=
    fun a => (hident a).comp hφmeas
  -- Etemadi's strong law
  have hlln := strong_law_ae X hint hXindep hXident
  filter_upwards [hlln] with ω hω
  simpa [smul_eq_mul] using hω

end NCG
