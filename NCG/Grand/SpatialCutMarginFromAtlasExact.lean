/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RenewalSpatialPositiveScreen

/-!
# Spatial cut margins from coordinate and robust-atlas certificates

This closes the constructor gap in `cor:renewal-spatial-positive-screen`:
the coordinate mixed-fiber and protected-atlas outputs are converted to the
`SpatialCutMargin` consumed by the already compiled Sobolev--Weyl screen.
-/

open Finset

noncomputable section

namespace NCG
namespace FiniteWeightedGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : FiniteWeightedGraph V)

/-- The quantitative output of the protected Cartesian branch before its
conversion to the physical cut margin. -/
structure CartesianMixedFiberCertificate (h : ℝ) where
  cminus : ℝ
  mplus : ℝ
  delta : ℝ
  cminus_pos : 0 < cminus
  mplus_pos : 0 < mplus
  delta_pos : 0 < delta
  mixedFiber : ∀ B : Finset V, ∃ cardSmall : ℝ,
    0 ≤ cardSmall ∧
    min (∑ v ∈ B, G.mass v) (∑ v ∈ Bᶜ, G.mass v) ≤
      mplus * h ^ 3 * cardSmall ∧
    cminus * h * (delta * cardSmall ^ ((2 : ℝ) / 3)) ≤
      finiteCutCapacity G.conductance B

/-- The mixed-fiber certificate constructs the exact `SpatialCutMargin` used
by the renewal screen theorem. -/
def spatialCutMargin_of_cartesian
    (h : ℝ) (hh : 0 < h) (C : G.CartesianMixedFiberCertificate h) :
    G.SpatialCutMargin h where
  constant := C.cminus * C.delta / C.mplus ^ ((2 : ℝ) / 3)
  constant_pos := by
    exact div_pos (mul_pos C.cminus_pos C.delta_pos)
      (Real.rpow_pos_of_pos C.mplus_pos _)
  cut := by
    intro B
    obtain ⟨cardSmall, hcard, hmass, hmixed⟩ := C.mixedFiber B
    exact cartesian_cut_bound_of_mixedFibers cardSmall
      (min (∑ v ∈ B, G.mass v) (∑ v ∈ Bᶜ, G.mass v))
      (finiteCutCapacity G.conductance B) h C.cminus C.mplus C.delta
      hh C.cminus_pos.le C.mplus_pos C.delta_pos.le hcard
      (le_min
        (Finset.sum_nonneg fun v _ => (G.mass_pos v).le)
        (Finset.sum_nonneg fun v _ => (G.mass_pos v).le))
      hmass hmixed

/-- Raw protected-atlas data, uniformly for every endpoint cut.  Its fields
are precisely the hypotheses of `protected_atlas_cut_bound`; notably, no
global cut margin is assumed. -/
structure RobustAtlasCertificate
    (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (h : ℝ) where
  I0 : ℝ
  Jstar : ℝ
  eta : ℝ
  vstar : ℝ
  Vstar : ℝ
  I0_pos : 0 < I0
  Jstar_pos : 0 < Jstar
  eta_pos : 0 < eta
  eta_lt_half : eta < 1 / 2
  vstar_pos : 0 < vstar
  Vstar_pos : 0 < Vstar
  chartMass : ι → ℝ
  insideMass : Finset V → ι → ℝ
  localCut : Finset V → ι → ℝ
  interfaceCut : Finset V → ι → ι → ℝ
  adjacent : ι → ι → Prop
  chartMass_lower : ∀ a, vstar ≤ chartMass a
  chartMass_sum : G.volume = ∑ a, chartMass a
  volume_le : G.volume ≤ Vstar
  inside_nonneg : ∀ B a, 0 ≤ insideMass B a
  inside_le : ∀ B a, insideMass B a ≤ chartMass a
  inside_sum : ∀ B,
    min (∑ v ∈ B, G.mass v) (∑ v ∈ Bᶜ, G.mass v) =
      ∑ a, insideMass B a
  local_bound : ∀ B a,
    I0 * min (insideMass B a) (chartMass a - insideMass B a) ^
        ((2 : ℝ) / 3) ≤ localCut B a
  local_aggregate : ∀ B,
    ∑ a, localCut B a ≤ h * finiteCutCapacity G.conductance B
  nerve_connected : NerveCutConnected adjacent
  interface_bound : ∀ B a b, adjacent a b →
    eta * chartMass a ≤ insideMass B a →
    insideMass B b ≤ (1 - eta) * chartMass b →
    Jstar ≤ interfaceCut B a b
  interface_global : ∀ B a b,
    interfaceCut B a b ≤ h * finiteCutCapacity G.conductance B

theorem cutMass_add_compl (B : Finset V) :
    (∑ v ∈ B, G.mass v) + (∑ v ∈ Bᶜ, G.mass v) = G.volume := by
  have hp := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset V) (fun v => v ∈ B) G.mass
  have hB : Finset.univ.filter (fun v => v ∈ B) = B := by ext v; simp
  have hBc : Finset.univ.filter (fun v => ¬ v ∈ B) = Bᶜ := by ext v; simp
  rw [hB, hBc] at hp
  exact hp

/-- The protected-atlas scalar theorem constructs the same concrete cut
margin object as the coordinate branch. -/
def spatialCutMargin_of_robustAtlas
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (h : ℝ) (A : G.RobustAtlasCertificate ι h) :
    G.SpatialCutMargin h where
  constant := min
    (A.I0 * (2 * A.eta * A.vstar / A.Vstar) ^ ((2 : ℝ) / 3))
    (A.Jstar * (2 / A.Vstar) ^ ((2 : ℝ) / 3))
  constant_pos := atlas_floor_positive A.I0 A.Jstar A.eta A.vstar A.Vstar
    A.I0_pos A.Jstar_pos A.eta_pos A.vstar_pos A.Vstar_pos
  cut := by
    intro B
    have hpart := G.cutMass_add_compl B
    have hglobalHalf :
        min (∑ v ∈ B, G.mass v) (∑ v ∈ Bᶜ, G.mass v) ≤
          G.volume / 2 := by
      have hleft := min_le_left
        (∑ v ∈ B, G.mass v) (∑ v ∈ Bᶜ, G.mass v)
      have hright := min_le_right
        (∑ v ∈ B, G.mass v) (∑ v ∈ Bᶜ, G.mass v)
      linarith
    exact protected_atlas_cut_bound A.chartMass (A.insideMass B)
      (A.localCut B) (A.interfaceCut B) A.adjacent G.volume
      (min (∑ v ∈ B, G.mass v) (∑ v ∈ Bᶜ, G.mass v))
      (h * finiteCutCapacity G.conductance B)
      A.I0 A.Jstar A.eta A.vstar A.Vstar A.eta_pos A.eta_lt_half
      A.vstar_pos A.Vstar_pos A.I0_pos.le A.Jstar_pos.le
      A.chartMass_lower (A.inside_nonneg B) (A.inside_le B)
      A.chartMass_sum (A.inside_sum B) A.volume_le hglobalHalf
      (A.local_bound B) (A.local_aggregate B) A.nerve_connected
      (A.interface_bound B) (A.interface_global B)

/-- Either protected spatial branch now produces the complete renewal-native
positive screen, with no separately supplied `SpatialCutMargin`. -/
theorem renewalSpatialPositiveScreen_of_coordinate_or_atlas
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (D h Vstar : ℝ) (hD : 0 < D) (hh : 0 < h) (hVstar : 0 < Vstar)
    (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (branch : G.CartesianMixedFiberCertificate h ⊕
      G.RobustAtlasCertificate ι h) :
    ∃ M : G.SpatialCutMargin h,
      ∃ S : G.RenewalSpatialPositiveScreen M.constant D h Vstar,
        S.poincareConstant =
            128 * D * Vstar ^ ((2 : ℝ) / 3) / M.constant ^ 2 ∧
        S.spectralFloor =
            M.constant ^ 2 / (128 * D * Vstar ^ ((2 : ℝ) / 3)) := by
  let M : G.SpatialCutMargin h := match branch with
    | Sum.inl C => G.spatialCutMargin_of_cartesian h hh C
    | Sum.inr A => G.spatialCutMargin_of_robustAtlas h A
  obtain ⟨S, hP, hfloor⟩ := G.renewalSpatialPositiveScreen
    D h Vstar hD hh hVstar hvolume hdegree M
  exact ⟨M, S, hP, hfloor⟩

end FiniteWeightedGraph
end NCG


