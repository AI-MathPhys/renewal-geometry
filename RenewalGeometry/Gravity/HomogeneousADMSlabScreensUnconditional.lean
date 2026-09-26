/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HomogeneousADMPacketDerivedExact
import RenewalGeometry.DiscreteAnalysis.TorusCoordinateIsoperimetryExact

/-!
# Unconditional slab screens of the de Sitter and flat renewal vacua
  (`thm:supp-desitter-adm`, `thm:supp-flat-vacuum`, emergent-spacetime supplement)

The coordinate-grid edge-isoperimetric inequality is now a theorem
(`TorusCoordinateIsoperimetry.coordinateGridIsoperimetry`, constant `c₀ = 1/32`),
so the slab-uniformity clause of `thm:supp-desitter-adm` closes with no
remaining hypothesis:

* `desitter_slab_screens_unconditional` — on every compact slab `|t| ≤ T` the
  time-`t` spatial graph of the de Sitter regulator (mass `e^{3Ht}h³`, rate
  `e^{-2Ht}/(8h²)`) satisfies the cut inequality with constant
  `1/(256 e^{HT})`, the spectral floor `poincareConstant e^{-HT} e^{HT} (1/32)`,
  the Weyl count with `weylConstant e^{-HT} e^{HT} (1/32)`, and the
  compact-screen tail bound, uniformly in `h = 1/d` and `t`;
* `desitter_adm_packet_full` — the full statement of `thm:supp-desitter-adm`:
  the boxed ADM packet `eq:supp-desitter-adm`, the conductance
  `eq:supp-desitter-conductance`, and the uniform slab screens;
* `flat_slab_screens_unconditional` — the flat regulator (`a = 1`) satisfies the
  same screens with `a₋ = a₊ = 1`, for every mesh.
-/

open scoped BigOperators

namespace RenewalGeometry.HomogeneousADMPacket

open RelationalDeSitterBranch A3PeriodicScreens TorusCoordinateIsoperimetry

/-- `thm:supp-desitter-adm`, slab clause, unconditional: on `|t| ≤ T` the cut,
Poincaré, Weyl and compact-screen constants of the time-`t` de Sitter spatial
graph depend only on `H T`, uniformly in the mesh `h = 1/d` and in `t`. -/
theorem desitter_slab_screens_unconditional (H T : ℝ) (hH : 0 ≤ H)
    (d : ℕ) [NeZero d] (t : ℝ) (ht : |t| ≤ T) :
    let a := Real.exp (H * t)
    let hapos : 0 < a := Real.exp_pos _
    let G := scaledGraph d a hapos
    (∀ A : Finset (A3PeriodicGraphSampling.Vertex d), 0 < A.card →
      2 * A.card ≤ d ^ 3 →
      1 / (256 * Real.exp (H * T)) * (∑ v ∈ A, G.mass v) ^ ((2 : ℝ) / 3) ≤
        A3PeriodicGraphSampling.mesh d * finiteCutCapacity G.conductance A) ∧
    (∀ j, 0 < G.eigenvalue j →
      poincareConstant (Real.exp (-H * T)) (Real.exp (H * T)) (1 / 32) ≤
        G.eigenvalue j) ∧
    (∀ R : ℝ, 0 < R →
      (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
        weylConstant (Real.exp (-H * T)) (Real.exp (H * T)) (1 / 32) *
          (1 + R ^ ((3 : ℝ) / 2))) ∧
    (∀ (f : A3PeriodicGraphSampling.Vertex d → ℝ) (R : ℝ), 0 < R →
      ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
          G.spectralCoefficient f j ^ 2 ≤
        R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2) := by
  intro a hapos G
  have h := desitter_slab_screens H T (1 / 32) hH (by norm_num) d
    (coordinateGridIsoperimetry d) t ht
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, h2, h3, h4⟩
  intro A hA hhalf
  have := h1 A hA hhalf
  have heq : (1 : ℝ) / 32 / (8 * Real.exp (H * T)) = 1 / (256 * Real.exp (H * T)) := by
    field_simp; ring
  rwa [heq] at this

/-- **`thm:supp-desitter-adm`** in full: for every `h ≠ 0` and `t` the boxed ADM
packet `𝓑_h(t) = e^{-2Ht} I`, `ϱ_h(t) = e^{3Ht}`, `g_h(t) = e^{2Ht} I`,
`N_h(t) = 1`, `β_h(t) = 0`, the edge conductance `e^{Ht} h / 8`, and, on every
compact slab `|t| ≤ T`, cut / Poincaré / counting / compact-screen constants
uniform in the mesh `h = 1/d` and in `t` (explicit: `1/(256 e^{HT})`,
`poincareConstant e^{-HT} e^{HT} (1/32)`, `weylConstant e^{-HT} e^{HT} (1/32)`). -/
theorem desitter_adm_packet_full (H : ℝ) (hH : 0 ≤ H) :
    (∀ (h t : ℝ), h ≠ 0 →
      predictableBracket H h t = Real.exp (-2 * H * t) • 1 ∧
      speedDensity H t = Real.exp (3 * H * t) ∧
      admMetric (predictableBracket H h t) (speedDensity H t) =
        Real.exp (2 * H * t) • 1 ∧
      admLapse (predictableBracket H h t) (speedDensity H t) = 1 ∧
      predictableDrift (fun _ => rootRate H h t) h = 0 ∧
      vertexMass H h t * rootRate H h t = Real.exp (H * t) * h / 8) ∧
    (∀ (T : ℝ) (d : ℕ) [NeZero d] (t : ℝ), |t| ≤ T →
      let G := scaledGraph d (Real.exp (H * t)) (Real.exp_pos _)
      (∀ v, vertexMass H (A3PeriodicGraphSampling.mesh d) t = G.mass v) ∧
      rootRate H (A3PeriodicGraphSampling.mesh d) t =
        scaledRate d (Real.exp (H * t)) ∧
      (∀ A : Finset (A3PeriodicGraphSampling.Vertex d), 0 < A.card →
        2 * A.card ≤ d ^ 3 →
        1 / (256 * Real.exp (H * T)) * (∑ v ∈ A, G.mass v) ^ ((2 : ℝ) / 3) ≤
          A3PeriodicGraphSampling.mesh d * finiteCutCapacity G.conductance A) ∧
      (∀ j, 0 < G.eigenvalue j →
        poincareConstant (Real.exp (-H * T)) (Real.exp (H * T)) (1 / 32) ≤
          G.eigenvalue j) ∧
      (∀ R : ℝ, 0 < R →
        (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
          weylConstant (Real.exp (-H * T)) (Real.exp (H * T)) (1 / 32) *
            (1 + R ^ ((3 : ℝ) / 2))) ∧
      (∀ (f : A3PeriodicGraphSampling.Vertex d → ℝ) (R : ℝ), 0 < R →
        ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
            G.spectralCoefficient f j ^ 2 ≤
          R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2)) := by
  refine ⟨fun h t hh => desitter_adm_packet H h t hh, ?_⟩
  intro T d _ t ht G
  obtain ⟨hmass, hrate⟩ := desitter_mass_rate_scaled H t d
  obtain ⟨h1, h2, h3, h4⟩ := desitter_slab_screens_unconditional H T hH d t ht
  exact ⟨hmass, hrate, h1, h2, h3, h4⟩

/-- The flat regulator (`a = 1`, `H = 0`) has the same uniform screens for every
mesh, with `a₋ = a₊ = 1`: cut constant `1/256`. -/
theorem flat_slab_screens_unconditional (d : ℕ) [NeZero d] :
    let G := scaledGraph d 1 one_pos
    (∀ A : Finset (A3PeriodicGraphSampling.Vertex d), 0 < A.card →
      2 * A.card ≤ d ^ 3 →
      1 / 256 * (∑ v ∈ A, G.mass v) ^ ((2 : ℝ) / 3) ≤
        A3PeriodicGraphSampling.mesh d * finiteCutCapacity G.conductance A) ∧
    (∀ j, 0 < G.eigenvalue j → poincareConstant 1 1 (1 / 32) ≤ G.eigenvalue j) ∧
    (∀ R : ℝ, 0 < R →
      (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
        weylConstant 1 1 (1 / 32) * (1 + R ^ ((3 : ℝ) / 2))) ∧
    (∀ (f : A3PeriodicGraphSampling.Vertex d → ℝ) (R : ℝ), 0 < R →
      ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
          G.spectralCoefficient f j ^ 2 ≤
        R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2) := by
  intro G
  have h := periodic_screens_unconditional d 1 1 1 one_pos le_rfl le_rfl
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, h2, h3, h4⟩
  intro A hA hhalf
  simpa using h1 A hA hhalf

end RenewalGeometry.HomogeneousADMPacket
