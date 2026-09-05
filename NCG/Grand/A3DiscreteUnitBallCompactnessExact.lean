/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3DiscreteLipschitzExtensionExact
import NCG.Grand.UniformLipschitzSubsequenceCompactnessExact

/-!
# Compact subsequences of anchored A3 graph unit-ball observables

Every sequence of anchored discrete unit-ball functions has exact Euclidean
extensions and, on each fixed closed ball, a uniformly convergent subsequence
with an eighteen-Lipschitz limit. Neither extension nor compactness is assumed.
The sharp one-Lipschitz identification remains a separate energy-limit theorem.
-/

open Filter
open scoped Topology

namespace NCG.A3DiscreteUnitBallCompactness

open A3FiniteDifferenceConsistency A3PeriodicGraphSampling
open FiniteWeightedGraphHodgeDirac A3DiscreteLipschitzExtension
open UniformLipschitzSubsequenceCompactness

noncomputable section

theorem exists_uniformly_convergent_extensions_on_ball
    (f : (n : ℕ) → Vertex (n + 1) → ℝ)
    (hf : ∀ n, graphLipschitz (mass (n + 1)) (conductance (n + 1)) (f n) ≤ 1)
    (hzero : ∀ n, f n 0 = 0) (R : ℝ) :
    ∃ G : ℕ → Space → ℝ,
      (∀ n, LipschitzWith 18 (G n)) ∧
      (∀ n x, G n (point (n + 1) x) = f n x) ∧
      (∀ n, G n 0 = 0) ∧
      ∃ g : Metric.closedBall (0 : Space) R → ℝ, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ LipschitzWith 18 g ∧
        (∀ x, |g x| ≤ 18 * R) ∧
        TendstoUniformly (fun n (x : Metric.closedBall (0 : Space) R) => G (φ n) x)
          g atTop := by
  choose G hLip heq hGzero hbound using fun n =>
    exists_anchored_lipschitz_extension (n + 1) (f n) (hf n) (hzero n)
  have hrestricted (n : ℕ) :
      LipschitzWith 18 (fun x : Metric.closedBall (0 : Space) R => G n x) := by
    simpa only [mul_one, Function.comp_def] using
      (hLip n).comp (LipschitzWith.subtype_val (Metric.closedBall (0 : Space) R))
  have hrestricted_bound (n : ℕ) (x : Metric.closedBall (0 : Space) R) :
      |G n x| ≤ 18 * R := by
    apply (hbound n x).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  obtain ⟨g, φ, hφ, hg, hgBound, hconv⟩ := exists_uniformly_convergent_subsequence
    (fun n (x : Metric.closedBall (0 : Space) R) => G n x) 18 (18 * R)
      hrestricted hrestricted_bound
  exact ⟨G, hLip, heq, hGzero, g, φ, hφ, hg, hgBound, hconv⟩

end

end NCG.A3DiscreteUnitBallCompactness
