/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalSpectralIsolation
import Mathlib.Topology.DiscreteSubset

/-!
# Finiteness of compact-normal spectrum away from zero

The nonzero spectrum of a compact normal operator is discrete, and the whole spectrum is compact.
Consequently only finitely many spectral points can remain outside any fixed neighborhood of zero.
This is the finiteness input needed to turn pointwise spectral inclusion into one uniform late-stage
statement.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A compact normal operator has only finitely many spectral points whose norm is bounded below
by a positive constant. -/
theorem finite_spectrum_norm_ge_of_compact_of_isStarNormal
    (T : H →L[ℂ] H) (hcompact : IsCompactOperator (T : H → H))
    (hnormal : IsStarNormal T) (r : ℝ) (hr : 0 < r) :
    Set.Finite {z ∈ spectrum ℂ T | r ≤ ‖z‖} := by
  let S : Set ℂ := {z ∈ spectrum ℂ T | r ≤ ‖z‖}
  have hScompact : IsCompact S := by
    exact (spectrum.isCompact T).inter_right
      (isClosed_le continuous_const continuous_norm)
  have hSdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      exact (not_le_of_gt hr) (by simpa using hz.2)
    obtain ⟨ε, hε, hisolated⟩ :=
      exists_isolatedInBall_of_compact_of_isStarNormal T hcompact hnormal z hz0
    refine ⟨Metric.ball z ε, Metric.isOpen_ball, ?_⟩
    ext w
    constructor
    · rintro ⟨hwball, hwS⟩
      have hwz : w = z :=
        hisolated w hwS.1 (Metric.mem_ball.mp hwball)
      simp [hwz]
    · intro hw
      have hwz : w = z := by simpa using hw
      subst w
      exact ⟨Metric.mem_ball_self hε, hz⟩
  exact hScompact.finite hSdiscrete

end NCG.ResolventStability
