/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AtlasIsoperimetry
import NCG.Grand.OperationalSobolevWeylFiniteGraph

/-!
# Renewal-native spatial positive screen

Exact composition of the coordinate/atlas cut certificate with the
operational Sobolev--Weyl theorem.
-/

open scoped BigOperators

noncomputable section

namespace NCG
namespace FiniteWeightedGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : FiniteWeightedGraph V)

/-- Common output of either the Cartesian or robust-atlas branch. -/
structure SpatialCutMargin (h : ℝ) where
  constant : ℝ
  constant_pos : 0 < constant
  cut : ∀ A : Finset V,
    constant * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^
        ((2 : ℝ) / 3) ≤ h * finiteCutCapacity G.conductance A

/-- The complete finite spatial screen promised by the manuscript
corollary. -/
structure RenewalSpatialPositiveScreen (I D h Vstar : ℝ) where
  sobolev : ∀ f : V → ℝ, (∑ v, G.mass v * f v = 0) →
    ∑ v, G.mass v * f v ^ 6 ≤
      ((128 * D / I ^ 2) * finiteSpatialEnergy G.conductance f) ^ 3
  poincareConstant : ℝ
  poincare : ∀ f : V → ℝ, (∑ v, G.mass v * f v = 0) →
    ∑ v, G.mass v * f v ^ 2 ≤
      poincareConstant * finiteSpatialEnergy G.conductance f
  spectralFloor : ℝ
  spectralFloor_pos : 0 < spectralFloor
  eigenvalue_floor : ∀ j, 0 < G.eigenvalue j → spectralFloor ≤ G.eigenvalue j
  counting : ∀ R, 0 < R →
    (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
      1 + 4 * Real.exp (3 / 2) * Vstar *
        ((128 * D / I ^ 2) * R) ^ ((3 : ℝ) / 2)
  tail : ∀ (f : V → ℝ) (R : ℝ), 0 < R →
    ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
        G.spectralCoefficient f j ^ 2 ≤
      R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2

/-- A regulator-uniform coordinate or atlas cut margin supplies the physical
Poincaré floor, dimension-three Weyl counting, and exhaustive finite-rank
spectral screens. -/
theorem renewalSpatialPositiveScreen
    (D h Vstar : ℝ) (hD : 0 < D) (hh : 0 < h) (hVstar : 0 < Vstar)
    (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (M : G.SpatialCutMargin h) :
    ∃ S : G.RenewalSpatialPositiveScreen M.constant D h Vstar,
      S.poincareConstant =
          128 * D * Vstar ^ ((2 : ℝ) / 3) / M.constant ^ 2 ∧
      S.spectralFloor =
          M.constant ^ 2 / (128 * D * Vstar ^ ((2 : ℝ) / 3)) := by
  let CP : ℝ := 128 * D * Vstar ^ ((2 : ℝ) / 3) / M.constant ^ 2
  let floor : ℝ := M.constant ^ 2 /
    (128 * D * Vstar ^ ((2 : ℝ) / 3))
  refine ⟨{
    sobolev := ?_
    poincareConstant := CP
    poincare := ?_
    spectralFloor := floor
    spectralFloor_pos := ?_
    eigenvalue_floor := ?_
    counting := ?_
    tail := ?_ }, rfl, rfl⟩
  · intro f hmean
    have h := finite_meanZero_L6_sobolev G.mass
      (fun v => (G.mass_pos v).le) G.conductance G.conductance_nonneg
      G.conductance_symm f hmean M.constant D h M.constant_pos hD.le hh
      hdegree M.cut
    simpa using h
  · intro f hmean
    exact finite_meanZero_poincare G.mass (fun v => (G.mass_pos v).le)
      G.conductance G.conductance_nonneg G.conductance_symm f hmean
      M.constant D h Vstar M.constant_pos hD.le hh hVstar.le hvolume
      hdegree M.cut
  · unfold floor
    exact div_pos (sq_pos_of_pos M.constant_pos)
      (mul_pos (mul_pos (by norm_num) hD)
        (Real.rpow_pos_of_pos hVstar _))
  · intro j hj
    unfold floor
    exact G.positiveEigenvalue_floor M.constant D h Vstar M.constant_pos hD
      hh hVstar hvolume hdegree M.cut j hj
  · intro R hR
    exact G.eigenvalueCount_bound M.constant D h Vstar R M.constant_pos
      hD.le hh hVstar.le hvolume hR hdegree M.cut
  · intro f R hR
    exact G.eigenfunction_spectralTail_bound f R hR

end FiniteWeightedGraph
end NCG
