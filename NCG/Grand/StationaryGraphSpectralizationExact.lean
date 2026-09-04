/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StationaryFluxAdjointExact

/-!
# Canonical finite stationary graph spectralization

This API takes the original positive masses, nonnegative renewal rates and
stationarity equation. The reversed flux is proved to be the weighted
adjoint; the actual matrix square, energy formula and constant kernel then
follow without a spectral certificate supplied as a hypothesis.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace NCG.StationaryGraphSpectralization

open StationaryFluxAdjoint WeightedGraphOrthonormalCoordinates FiniteWeightedGraphHodgeDirac

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def rateGenerator (k : V → V → ℝ) (f : V → ℝ) : V → ℝ :=
  fun x => ∑ y, k x y * (f y - f x)

theorem fluxGenerator_mass_mul_rate_eq
    (mass : V → ℝ) (k : V → V → ℝ) (hmass : ∀ x, 0 < mass x) (f : V → ℝ) :
    fluxGenerator mass (fun x y => mass x * k x y) f = rateGenerator k f := by
  funext x
  unfold fluxGenerator rateGenerator
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [(hmass x).ne']

theorem stationary_rate_adjoint
    (mass : V → ℝ) (k : V → V → ℝ) (hmass : ∀ x, 0 < mass x)
    (hstationary : ∀ x, ∑ y, mass x * k x y = ∑ y, mass y * k y x)
    (f g : V → ℝ) :
    weightedPairing mass f (rateGenerator k g) =
      weightedPairing mass (fluxGenerator mass (fun x y => mass y * k y x) f) g := by
  rw [← fluxGenerator_mass_mul_rate_eq mass k hmass]
  exact stationary_flux_adjoint mass (fun x y => mass x * k x y) hmass hstationary f g

theorem stationary_rate_dirac_square
    (mass : V → ℝ) (k : V → V → ℝ) (hmass : ∀ x, 0 < mass x)
    (hk : ∀ x y, 0 ≤ k x y) (f : V → ℝ) :
    let c := symmetrizedConductance (fun x y => mass x * k x y)
    ((differential mass c)ᵀ * differential mass c).mulVec (vertexCoordinates mass f) =
      vertexCoordinates mass (fun x =>
        -(rateGenerator k f x + fluxGenerator mass (fun x y => mass y * k y x) f x)) := by
  dsimp only
  rw [← fluxGenerator_mass_mul_rate_eq mass k hmass]
  exact hodgeLaplacian_eq_negative_flux_sum mass (fun x y => mass x * k x y)
    hmass (fun x y => mul_nonneg (hmass x).le (hk x y)) f

theorem stationary_rate_commutator_energy
    (mass : V → ℝ) (k : V → V → ℝ) (hmass : ∀ x, 0 < mass x)
    (hk : ∀ x y, 0 ≤ k x y) (f : V → ℝ) :
    let c := symmetrizedConductance (fun x y => mass x * k x y)
    graphLipschitz mass c f ^ 2 =
      ‖fun x => (1 / mass x) * ∑ y, c x y * |f y - f x| ^ 2‖ := by
  dsimp only
  rw [graphLipschitz, norm_sq_dirac_commutator]
  congr 1
  funext x
  have hc : ∀ x y, 0 ≤ symmetrizedConductance (fun x y => mass x * k x y) x y :=
    fun x y => div_nonneg
      (add_nonneg (mul_nonneg (hmass x).le (hk x y))
        (mul_nonneg (hmass y).le (hk y x))) (by norm_num)
  rw [localEnergy_eq_conductance_formula mass _ f hmass hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [sq_abs]
  ring

theorem connected_commutator_kernel
    (mass : V → ℝ) (c : V → V → ℝ) (hmass : ∀ x, 0 < mass x)
    (hconnected : ConductanceConnected c) (f : V → ℝ) :
    graphLipschitz mass c f = 0 ↔ ∃ a : ℝ, ∀ x, f x = a := by
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    have hf : f = 0 := Subsingleton.elim _ _
    simp [hf, graphLipschitz, representation, vertexRepresentation, edgeRepresentation]
  | inr h =>
    letI := h
    exact dirac_commutator_norm_eq_zero_iff_constant mass c f hmass hconnected

end

end NCG.StationaryGraphSpectralization
