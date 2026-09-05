/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TargetRelativeFiniteTimeExact
import NCG.Grand.RelationValuedLimitExact

/-!
# Target-relative weak Einstein--matter response

The weak matter and Einstein equations are represented here by genuine
continuous linear residual functionals on the response carrier.  Vanishing of
their finite-regulator evaluations passes to the completed finite-time trace at
the declared dense query times.
-/

open Filter Topology

noncomputable section

namespace NCG.TargetRelativeEinsteinMatter

open NCG.ResponseThreadCompletion

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [CompleteSpace K]

/-- A finite-time response satisfying every declared weak matter and Einstein
identity as an equality in the continuous dual. -/
structure WeakResponse (Y : Thread K)
    (matterResidual einsteinResidual : ℕ → K →L[ℝ] ℝ)
    (matterTime einsteinTime : ℕ → ℝ) where
  trace : ℝ → K
  trace_eq_limit : trace = limitTrace Y
  continuous : ContinuousOn trace (Set.Icc 0 Y.T)
  continuation_modulus : ∀ t ∈ Set.Icc 0 Y.T, ∀ s ∈ Set.Icc 0 Y.T,
    dist (trace t) (trace s) ≤ Y.ω |t - s|
  matter_identity : ∀ r, matterResidual r (trace (matterTime r)) = 0
  einstein_identity : ∀ r, einsteinResidual r (trace (einsteinTime r)) = 0

/-- **Target-relative finite-time Einstein--matter response.**  A projectively
Cauchy response thread with vanishing finite weak residuals has at least one
completed response satisfying all weak matter and Einstein identities. -/
theorem target_relative_finite_time_einstein_matter_response
    (Y : Thread K)
    (matterResidual einsteinResidual : ℕ → K →L[ℝ] ℝ)
    (matterTime einsteinTime : ℕ → ℝ)
    (matterDepth einsteinDepth : ℕ → ℕ)
    (hmatterTime : ∀ r, matterTime r ∈ Y.D (matterDepth r))
    (heinsteinTime : ∀ r, einsteinTime r ∈ Y.D (einsteinDepth r))
    (hmatter : ∀ r, Tendsto
      (fun m => matterResidual r (Y.y m (matterTime r))) atTop (𝓝 0))
    (heinstein : ∀ r, Tendsto
      (fun m => einsteinResidual r (Y.y m (einsteinTime r))) atTop (𝓝 0)) :
    Nonempty (WeakResponse Y matterResidual einsteinResidual
      matterTime einsteinTime) := by
  have hmatterLimit : ∀ r,
      matterResidual r (limitTrace Y (matterTime r)) = 0 := by
    intro r
    have h := cylinder_limit Y
      (fun z : Fin 1 → K => matterResidual r (z 0))
      ((matterResidual r).continuous.comp (continuous_apply 0))
      (fun _ : Fin 1 => matterTime r) (matterDepth r)
      (fun _ => hmatterTime r) (by simpa using hmatter r)
    simpa using h
  have heinsteinLimit : ∀ r,
      einsteinResidual r (limitTrace Y (einsteinTime r)) = 0 := by
    intro r
    have h := cylinder_limit Y
      (fun z : Fin 1 → K => einsteinResidual r (z 0))
      ((einsteinResidual r).continuous.comp (continuous_apply 0))
      (fun _ : Fin 1 => einsteinTime r) (einsteinDepth r)
      (fun _ => heinsteinTime r) (by simpa using heinstein r)
    simpa using h
  exact ⟨{
    trace := limitTrace Y
    trace_eq_limit := rfl
    continuous := limitTrace_continuousOn Y
    continuation_modulus := fun _ ht _ hs => limitTrace_modulus Y ht hs
    matter_identity := hmatterLimit
    einstein_identity := heinsteinLimit }⟩

end NCG.TargetRelativeEinsteinMatter
