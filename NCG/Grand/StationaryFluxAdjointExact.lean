/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WeightedGraphHodgeLaplacianCoordinatesExact
import Mathlib

/-!
# Stationary flux reversal is the weighted generator adjoint

For positive vertex masses and balanced directed flux, transposing the flux
gives the actual adjoint under the weighted inner product. Symmetrizing this
generator produces conductance `(q(x,y)+q(y,x))/2`, linking the matrix Hodge
Laplacian to the symmetric part of the original stationary generator.
-/

open Matrix
open scoped BigOperators

namespace NCG.StationaryFluxAdjoint

open StationaryWeightedGraphGenerator WeightedGraphHodgeLaplacianCoordinates
open WeightedGraphOrthonormalCoordinates FiniteWeightedGraphHodgeDirac

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def fluxGenerator (mass : V → ℝ) (q : V → V → ℝ) (f : V → ℝ) : V → ℝ :=
  fun x => (∑ y, q x y * (f y - f x)) / mass x

def weightedPairing (mass : V → ℝ) (f g : V → ℝ) : ℝ := ∑ x, mass x * f x * g x

def symmetrizedConductance (q : V → V → ℝ) (x y : V) : ℝ := (q x y + q y x) / 2

theorem weightedPairing_fluxGenerator
    (mass : V → ℝ) (q : V → V → ℝ) (hmass : ∀ x, 0 < mass x) (f g : V → ℝ) :
    weightedPairing mass f (fluxGenerator mass q g) =
      ∑ x, ∑ y, q x y * f x * (g y - g x) := by
  unfold weightedPairing fluxGenerator
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [(hmass x).ne']

/-- Balance supplies precisely the diagonal identity needed for the adjoint. -/
theorem stationary_flux_adjoint
    (mass : V → ℝ) (q : V → V → ℝ) (hmass : ∀ x, 0 < mass x)
    (hbalance : ∀ x, ∑ y, q x y = ∑ y, q y x) (f g : V → ℝ) :
    weightedPairing mass f (fluxGenerator mass q g) =
      weightedPairing mass (fluxGenerator mass (fun x y => q y x) f) g := by
  have hcomm : weightedPairing mass (fluxGenerator mass (fun x y => q y x) f) g =
      weightedPairing mass g (fluxGenerator mass (fun x y => q y x) f) := by
    unfold weightedPairing
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hcomm, weightedPairing_fluxGenerator mass q hmass,
    weightedPairing_fluxGenerator mass (fun x y => q y x) hmass]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  · apply Finset.sum_congr rfl
    intro x _
    simp only [← Finset.sum_mul]
    rw [hbalance x]
    ring

theorem symmetric_generator_eq_average
    (mass : V → ℝ) (q : V → V → ℝ) (f : V → ℝ) :
    symmetricRateGenerator mass (symmetrizedConductance q) f =
      fun x => (fluxGenerator mass q f x + fluxGenerator mass (fun x y => q y x) f x) / 2 := by
  funext x
  unfold symmetricRateGenerator symmetrizedConductance fluxGenerator
  rw [← add_div, ← Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The actual orthonormal-coordinate Dirac square equals minus the sum of
the original flux generator and its weighted adjoint under stationarity. -/
theorem hodgeLaplacian_eq_negative_flux_sum
    (mass : V → ℝ) (q : V → V → ℝ) (hmass : ∀ x, 0 < mass x)
    (hq : ∀ x y, 0 ≤ q x y) (f : V → ℝ) :
    ((differential mass (symmetrizedConductance q))ᵀ *
      differential mass (symmetrizedConductance q)).mulVec (vertexCoordinates mass f) =
      vertexCoordinates mass (fun x =>
        -(fluxGenerator mass q f x + fluxGenerator mass (fun x y => q y x) f x)) := by
  rw [hodgeLaplacian_mulVec_vertexCoordinates mass (symmetrizedConductance q) hmass
    (fun x y => div_nonneg (add_nonneg (hq x y) (hq y x)) (by norm_num))
    (fun x y => by simp [symmetrizedConductance, add_comm]),
    symmetric_generator_eq_average]
  congr 1
  funext x
  ring

end

end NCG.StationaryFluxAdjoint
