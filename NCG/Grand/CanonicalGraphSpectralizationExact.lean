/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StationaryGraphSpectralizationExact
import NCG.Grand.A3DeSitterConnesConvergenceExact

/-!
# Canonical graph Hodge--Dirac spectralization: complete manuscript theorem

This entry point assembles SP.17--SP.20 from their independently proved
finite and continuum components. In particular, the flat distance is the
actual lattice quotient metric and the time-dependent graph distance is
the actual commutator supremum for the curved masses and conductances.
-/

open Matrix Filter Set
open scoped Topology Matrix.Norms.L2Operator

namespace NCG.CanonicalGraphSpectralization

open FiniteWeightedGraphHodgeDirac StationaryFluxAdjoint WeightedGraphOrthonormalCoordinates
open StationaryGraphSpectralization A3FiniteDifferenceConsistency A3FlatTorusMetric
open A3ConnesFlatUniformConvergence A3DeSitterConnesConvergence

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All conclusions of the manuscript's canonical graph spectralization theorem. -/
structure SpectralizationConclusion (mass : V → ℝ) (k : V → V → ℝ) : Prop where
  weightedAdjoint : ∀ f g,
    weightedPairing mass f (rateGenerator k g) =
      weightedPairing mass (fluxGenerator mass (fun x y => mass y * k y x) f) g
  squareBlocks :
    let c := symmetrizedConductance (fun x y => mass x * k x y)
    dirac mass c * dirac mass c = fromBlocks
      ((differential mass c)ᵀ * differential mass c) 0 0
      (differential mass c * (differential mass c)ᵀ)
  squareCoordinates : ∀ f,
    let c := symmetrizedConductance (fun x y => mass x * k x y)
    ((differential mass c)ᵀ * differential mass c).mulVec (vertexCoordinates mass f) =
      vertexCoordinates mass (fun x =>
        -(rateGenerator k f x + fluxGenerator mass (fun x y => mass y * k y x) f x))
  commutatorEnergy : ∀ f,
    let c := symmetrizedConductance (fun x y => mass x * k x y)
    graphLipschitz mass c f ^ 2 =
      ‖fun x => (1 / mass x) * ∑ y, c x y * |f y - f x| ^ 2‖
  constantKernel : ∀ f,
    graphLipschitz mass (symmetrizedConductance (fun x y => mass x * k x y)) f = 0 ↔
      ∃ a : ℝ, ∀ x, f x = a
  flatConvergence : Tendsto distanceError atTop (𝓝 0)
  sliceSeminorm : ∀ (d : ℕ) [NeZero d] (H t : ℝ) (f : A3PeriodicGraphSampling.Vertex d → ℝ),
    graphLipschitz (scaledMass (Real.exp (H * t)) (A3PeriodicGraphSampling.mass d))
      (scaledConductance (Real.exp (H * t)) (A3PeriodicGraphSampling.conductance d)) f =
        Real.exp (-H * t) * graphLipschitz (A3PeriodicGraphSampling.mass d)
          (A3PeriodicGraphSampling.conductance d) f
  sliceDistance : ∀ (d : ℕ) [NeZero d] (H t : ℝ) (x y : A3PeriodicGraphSampling.Vertex d),
    sliceConnesDistance d H t x y = Real.exp (H * t) *
      FiniteConnesDistanceAttainment.connesDistance (A3PeriodicGraphSampling.mass d)
        (A3PeriodicGraphSampling.conductance d) x y
  compactSliceConvergence : ∀ (H : ℝ) (K : Set ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ K, ∀ x y : A3PeriodicGraphSampling.Vertex (n + 1),
      |sliceConnesDistance (n + 1) H t x y -
        sliceFlatDistance H t (A3PeriodicGraphSampling.point (n + 1) x)
          (A3PeriodicGraphSampling.point (n + 1) y)| < ε

/-- Full SP.17--SP.20, with no supplied continuum limit or spectral certificate. -/
theorem canonical_graph_spectralization
    (mass : V → ℝ) (k : V → V → ℝ) (hmass : ∀ x, 0 < mass x)
    (hk : ∀ x y, 0 ≤ k x y)
    (hstationary : ∀ x, ∑ y, mass x * k x y = ∑ y, mass y * k y x)
    (hconnected : ConductanceConnected (symmetrizedConductance (fun x y => mass x * k x y))) :
    SpectralizationConclusion mass k where
  weightedAdjoint := stationary_rate_adjoint mass k hmass hstationary
  squareBlocks := dirac_square_zeroForm_block mass _
  squareCoordinates := stationary_rate_dirac_square mass k hmass hk
  commutatorEnergy := stationary_rate_commutator_energy mass k hmass hk
  constantKernel := connected_commutator_kernel mass _ hmass hconnected
  flatConvergence := tendsto_distanceError_zero
  sliceSeminorm := slice_graphLipschitz_eq
  sliceDistance := sliceConnesDistance_eq
  compactSliceConvergence := eventually_uniform_slice_distance_error

end

end NCG.CanonicalGraphSpectralization
