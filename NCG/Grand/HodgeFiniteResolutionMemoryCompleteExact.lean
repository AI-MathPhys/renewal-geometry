/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteResolutionMemoryExact
import NCG.Grand.HodgeFeedbackSpectralReduction

/-!
# Hodge-to-Hankel finite-resolution memory closure

This file closes the bridge in `cor:finite-resolution-memory`.  The Hodge
min--max injection bounds the loaded low spectral carrier by a spatial Weyl
screen.  That derived rank bound is then fed into the exact Hankel splitting,
which gives the declared/innovation/tail profile and rules out an amorphous
fixed-resolution memory branch.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace NCG.HankelFeedback

variable {H₀ L : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [MeasurableSpace H₀] [BorelSpace H₀] [SecondCountableTopology H₀]
  [FiniteDimensional ℝ H₀]
  [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

/-- The exact data needed to connect a Hodge-dominated loaded transient to
its finite spatial counting screen.  Its fields are the formal counterparts
of `H_X >= c_H Delta_X^sp - C_H I`, the min--max high-mode separation, and
the operational spatial Weyl count. -/
structure HodgeLoadedTransientProfile (W : Splitting H₀) where
  spatialLow : H₀ →ₗ[ℝ] L
  spatialEnergy : H₀ → ℝ
  cH : ℝ
  CH : ℝ
  CW : ℝ
  cH_pos : 0 < cH
  hodgeLow : ∀ u : LinearMap.range W.P.toLinearMap,
    cH * spatialEnergy u - CH * ‖(u : H₀)‖ ^ 2
      ≤ W.R * ‖(u : H₀)‖ ^ 2
  spatialHigh : ∀ v : H₀, spatialLow v = 0 → v ≠ 0 →
    ((W.R + CH) / cH) * ‖v‖ ^ 2 < spatialEnergy v
  spatialWeylCount : (Module.finrank ℝ L : ℝ) ≤
    CW * W.R ^ ((3 : ℝ) / 2)

variable {W : Splitting H₀} (P : HodgeLoadedTransientProfile (L := L) W)

/-- The Hodge min--max comparison and the spatial Weyl law give the required
rank bound for the loaded low-energy screen. -/
theorem loadedScreen_rank_le :
    (Module.finrank ℝ (LinearMap.range W.P.toLinearMap) : ℝ) ≤
      P.CW * W.R ^ ((3 : ℝ) / 2) := by
  exact (Nat.cast_le.mpr (hodge_low_mode_finrank_le
    (LinearMap.range W.P.toLinearMap) P.spatialLow P.spatialEnergy
    W.R P.cH P.CH P.cH_pos P.hodgeLow P.spatialHigh)).trans
      P.spatialWeylCount

/-- Source and dynamic-containment residuals jointly decide whether a low
mode belongs to the declared physical carrier. -/
theorem source_dynamic_residuals_iff_declared
    (Dsource Ddynamic : Submodule ℝ (Lp H₀ 2 halfLine))
    [Dsource.HasOrthogonalProjection] [Ddynamic.HasOrthogonalProjection]
    {v : Lp H₀ 2 halfLine} (hv : v ∈ lowRange W) :
    (v - Dsource.starProjection v = 0 ∧
      v - Ddynamic.starProjection v = 0) ↔
      v ∈ declaredPart W (Dsource ⊓ Ddynamic) := by
  rw [low_mode_declared_iff W Dsource hv,
    low_mode_declared_iff W Ddynamic hv]
  simp only [declaredPart, Submodule.mem_inf]
  aesop

/-- Complete finite-resolution memory conclusion.  Every output splits into
declared low modes, canonical finite innovations, and the controlled
high-energy tail; simultaneously the two innovation ranks obey the spatial
`R^(3/2)` count, the tail converges in operator norm, and the full memory is
compact. -/
theorem hodge_finite_resolution_memory
    (D : Submodule ℝ (Lp H₀ 2 halfLine)) :
    (∀ f : Lp H₀ 2 halfLine,
      ∃ d ∈ declaredPart W D, ∃ i ∈ innovations W D,
        hankel W.fullScreen f = d + i + hankel W.highScreen f ∧
          ‖hankel W.highScreen f‖ ≤
            W.b * W.c / (2 * W.R) * ‖f‖) ∧
    (Module.finrank ℝ (lowRange W) : ℝ) ≤
      P.CW * W.R ^ ((3 : ℝ) / 2) ∧
    (Module.finrank ℝ (innovations W D) : ℝ) ≤
      P.CW * W.R ^ ((3 : ℝ) / 2) ∧
    ‖hankel W.fullScreen - hankel W.lowScreen‖ ≤
      W.b * W.c / (2 * W.R) ∧
    IsCompactOperator (hankel W.fullScreen) := by
  refine ⟨memory_profile W D, ?_⟩
  exact no_amorphous_branch W (loadedScreen_rank_le P) D

end NCG.HankelFeedback
