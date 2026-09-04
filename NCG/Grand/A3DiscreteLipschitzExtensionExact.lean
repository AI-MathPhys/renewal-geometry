/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.A3DiscreteUnitBallEquicontinuityExact

/-!
# Uniform Lipschitz extensions of arbitrary A3 discrete observables

The commutator unit ball admits real-valued Euclidean extensions with a
single Lipschitz constant at all mesh sizes. Normalization at the zero
vertex gives a uniform linear-growth bound on every extension.
-/

namespace NCG.A3DiscreteLipschitzExtension

open A3FiniteDifferenceConsistency A3PeriodicGraphSampling
open A3DiscreteUnitBallEquicontinuity FiniteWeightedGraphHodgeDirac

noncomputable section

theorem exists_lipschitz_extension
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) :
    ∃ g : Space → ℝ, LipschitzWith 18 g ∧ ∀ x, g (point d x) = f x := by
  classical
  let F : Space → ℝ := fun p => f (Function.invFun (point d) p)
  have hF (x : Vertex d) : F (point d x) = f x := by
    dsimp only [F]
    rw [Function.leftInverse_invFun (point_injective d)]
  have hLip : LipschitzOnWith 18 F (Set.range (point d)) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hF, hF]
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using
      abs_difference_le_eighteen_norm d f hf y x
  obtain ⟨g, hg, heq⟩ := hLip.extend_real
  refine ⟨g, hg, fun x => ?_⟩
  rw [← heq (Set.mem_range_self x), hF]

theorem point_zero (d : ℕ) : point d (0 : Vertex d) = 0 := by
  simp [point, LatticeGridSampling.embed]

/-- Anchored unit-ball functions have uniformly bounded extensions on each fixed ball. -/
theorem exists_anchored_lipschitz_extension
    (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (hzero : f 0 = 0) :
    ∃ g : Space → ℝ, LipschitzWith 18 g ∧ (∀ x, g (point d x) = f x) ∧
      g 0 = 0 ∧ ∀ p, |g p| ≤ 18 * ‖p‖ := by
  obtain ⟨g, hg, heq⟩ := exists_lipschitz_extension d f hf
  have hgzero : g 0 = 0 := by simpa only [point_zero, hzero] using heq 0
  refine ⟨g, hg, heq, hgzero, fun p => ?_⟩
  simpa only [Real.dist_eq, hgzero, sub_zero, dist_zero_right, Real.norm_eq_abs,
    NNReal.coe_ofNat] using
    hg.dist_le_mul p 0

end

end NCG.A3DiscreteLipschitzExtension
