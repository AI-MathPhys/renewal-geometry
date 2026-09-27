/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.A3DiscreteUnitBallCompactnessExact

/-!
# Almost-everywhere gradient bounds for Lipschitz limits

Paper `predictive_spectral_geometry`, label `lem:supp-A3-compactness`, the
`W^{1,∞}` identification.  Rademacher's theorem
(`LipschitzWith.ae_differentiableAt`) together with the derivative bound of a
Lipschitz map (`HasFDerivAt.le_of_lipschitz`) gives, for every `K`-Lipschitz
`F` on a finite-dimensional space, `|∇F| ≤ K` almost everywhere
(`ae_differentiableAt_and_norm_fderiv_le`).  A `K`-Lipschitz limit of any
sequence is again `K`-Lipschitz (`lipschitzWith_of_tendsto_pointwise`), so the
same bound holds for the limit.

Applied to the anchored `A₃` discrete unit-ball sequences of
`A3DiscreteUnitBallCompactnessExact`, the uniform limit on every closed ball
extends (McShane) to an `18`-Lipschitz `F` on the whole space with
`|∇F| ≤ 18` almost everywhere (`a3_limit_ae_gradient_bound`).  The sharp
constant `1` of `eq:supp-A3-limit-Lip` is not obtained here: it needs the
weak-* passage of the twelve root difference quotients and the tight-frame
identity, which the library does not yet have.
-/

open Filter MeasureTheory
open scoped Topology NNReal

namespace RenewalGeometry.LipschitzLimitGradientBound

section general

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Rademacher with the Lipschitz gradient bound.** A `K`-Lipschitz map on a
finite-dimensional real space is differentiable almost everywhere (for any
additive Haar measure) with `‖fderiv F x‖ ≤ K`. -/
theorem ae_differentiableAt_and_norm_fderiv_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : ℝ≥0} {f : E → F} (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ K := by
  filter_upwards [hf.ae_differentiableAt (μ := μ)] with x hx
  exact ⟨hx, hx.hasFDerivAt.le_of_lipschitz hf⟩

end general

section limits

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]

/-- A pointwise limit of `K`-Lipschitz maps is `K`-Lipschitz. -/
theorem lipschitzWith_of_tendsto_pointwise {K : ℝ≥0} {f : ℕ → α → β} {g : α → β}
    (hf : ∀ n, LipschitzWith K (f n)) (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    LipschitzWith K g := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hdist : Tendsto (fun n => dist (f n x) (f n y)) atTop (𝓝 (dist (g x) (g y))) :=
    (hlim x).dist (hlim y)
  exact le_of_tendsto hdist (Eventually.of_forall fun n => (hf n).dist_le_mul x y)

end limits

section a3

open A3FiniteDifferenceConsistency A3PeriodicGraphSampling FiniteWeightedGraphHodgeDirac
open A3DiscreteUnitBallCompactness

/-- **`lem:supp-A3-compactness`, Rademacher upgrade (constant 18).** For anchored
discrete unit-ball sequences on the `A₃` graphs, the exact Euclidean extensions
have, on every closed ball, a uniformly convergent subsequence whose limit is the
restriction of an `18`-Lipschitz `F : Space → ℝ` with `‖∇F‖ ≤ 18` almost
everywhere. -/
theorem a3_limit_ae_gradient_bound
    (f : (n : ℕ) → Vertex (n + 1) → ℝ)
    (hf : ∀ n, graphLipschitz (mass (n + 1)) (conductance (n + 1)) (f n) ≤ 1)
    (hzero : ∀ n, f n 0 = 0) (R : ℝ) :
    ∃ G : ℕ → Space → ℝ,
      (∀ n, LipschitzWith 18 (G n)) ∧
      (∀ n x, G n (point (n + 1) x) = f n x) ∧
      ∃ F : Space → ℝ, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ LipschitzWith 18 F ∧
        TendstoUniformly (fun n (x : Metric.closedBall (0 : Space) R) => G (φ n) x)
          (fun x => F x) atTop ∧
        ∀ᵐ x ∂(volume : Measure Space), DifferentiableAt ℝ F x ∧ ‖fderiv ℝ F x‖ ≤ 18 := by
  obtain ⟨G, hLip, heq, -, g, φ, hφ, hg, -, hconv⟩ :=
    exists_uniformly_convergent_extensions_on_ball f hf hzero R
  -- transport the ball limit to a function on `Space`, Lipschitz on the ball
  classical
  let g' : Space → ℝ := fun x =>
    if h : x ∈ Metric.closedBall (0 : Space) R then g ⟨x, h⟩ else 0
  have hg' : LipschitzOnWith 18 g' (Metric.closedBall (0 : Space) R) := by
    intro x hx y hy
    simp only [g', hx, hy, dite_true]
    exact hg.edist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨F, hF, hFeq⟩ := hg'.extend_real
  refine ⟨G, hLip, heq, F, φ, hφ, hF, ?_, ae_differentiableAt_and_norm_fderiv_le volume hF⟩
  have hFg : (fun x : Metric.closedBall (0 : Space) R => F x) = g := by
    funext x
    rw [← hFeq x.property]
    simp only [g', x.property, dite_true]
  rw [hFg]
  exact hconv

end a3

end RenewalGeometry.LipschitzLimitGradientBound
