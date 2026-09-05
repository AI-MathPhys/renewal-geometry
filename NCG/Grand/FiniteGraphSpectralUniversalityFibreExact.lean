/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CycleProjector

/-!
# Finite graph spectral universality fibre

This file proves the finite algebraic and entropy content of
`thm:GT-NCG-graph-fibre`.  For a connected oriented incidence matrix, the
stationary circulation fibre is the open conductance box inside the cycle
kernel.  Its underlying linear dimension is the first Betti number, it is
trivial exactly at the connected tree cardinality, and the stationary entropy
production is nonnegative with unique zero at equilibrium.
-/

open Matrix Finset

namespace NCG
namespace FiniteGraphSpectralUniversalityFibre

variable {V E : Type*} [Fintype V] [Fintype E]

/-- A real current obeys the oriented stationarity equation for a complex
incidence matrix. -/
def IsStationaryCurrent (B : Matrix V E ℂ) (j : E → ℝ) : Prop :=
  B *ᵥ (fun e => (j e : ℂ)) = 0

/-- The same-spectralization circulation fibre: stationary currents strictly
inside the two directed conductance bounds. -/
def GraphSpectralFibre (B : Matrix V E ℂ) (c : E → ℝ) : Set (E → ℝ) :=
  {j | IsStationaryCurrent B j ∧ ∀ e, |j e| < c e}

def forwardFlux (c j : E → ℝ) (e : E) : ℝ := c e + j e
def reverseFlux (c j : E → ℝ) (e : E) : ℝ := c e - j e

/-- The renewal rate obtained from a directed stationary flux and the mass at
its tail vertex.  This is formula (SP.23) of the manuscript. -/
noncomputable def forwardRate (m : V → ℝ) (tail : E → V)
    (c j : E → ℝ) (e : E) : ℝ :=
  (c e + j e) / m (tail e)

/-- The oppositely directed renewal rate, based at the head vertex. -/
noncomputable def reverseRate (m : V → ℝ) (head : E → V)
    (c j : E → ℝ) (e : E) : ℝ :=
  (c e - j e) / m (head e)

theorem forwardRate_eq_flux_div_mass (m : V → ℝ) (tail : E → V)
    (c j : E → ℝ) (e : E) :
    forwardRate m tail c j e = forwardFlux c j e / m (tail e) := rfl

theorem reverseRate_eq_flux_div_mass (m : V → ℝ) (head : E → V)
    (c j : E → ℝ) (e : E) :
    reverseRate m head c j e = reverseFlux c j e / m (head e) := rfl

/-- The strict current box is exactly positivity of both directed fluxes. -/
theorem abs_lt_conductance_iff_flux_pos (c j : E → ℝ) (e : E) :
    |j e| < c e ↔ 0 < forwardFlux c j e ∧ 0 < reverseFlux c j e := by
  simp only [forwardFlux, reverseFlux, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Symmetrizing the two directed fluxes recovers the fixed conductance, so
the spectral Hodge--Dirac data is independent of the circulation. -/
theorem symmetricFlux_eq_conductance (c j : E → ℝ) (e : E) :
    (forwardFlux c j e + reverseFlux c j e) / 2 = c e := by
  simp [forwardFlux, reverseFlux]

/-- Antisymmetrizing the two directed fluxes recovers the current.  Together
with `symmetricFlux_eq_conductance`, this gives uniqueness of the symmetric /
antisymmetric flux decomposition used in the converse direction of (SP.22). -/
theorem antisymmetricFlux_eq_current (c j : E → ℝ) (e : E) :
    (forwardFlux c j e - reverseFlux c j e) / 2 = j e := by
  simp [forwardFlux, reverseFlux]

/-- Edge contribution to steady entropy production. -/
noncomputable def entropyEdge (c j : ℝ) : ℝ :=
  2 * j * Real.log ((c + j) / (c - j))

/-- Inside a positive conductance box, an edge entropy contribution is
strictly positive exactly for a nonzero circulation. -/
theorem entropyEdge_pos_iff {c j : ℝ} (hc : 0 < c) (hj : |j| < c) :
    0 < entropyEdge c j ↔ j ≠ 0 := by
  constructor
  · intro h h0
    subst j
    simp [entropyEdge] at h
  · intro hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hnum : 0 < c + j := by
        have := (abs_lt.mp hj).1
        linarith
      have hden : 0 < c - j := by linarith
      have hratioPos : 0 < (c + j) / (c - j) := div_pos hnum hden
      have hratioLt : (c + j) / (c - j) < 1 := (div_lt_one hden).mpr (by linarith)
      have hlog : Real.log ((c + j) / (c - j)) < 0 :=
        Real.log_neg hratioPos hratioLt
      unfold entropyEdge
      exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by norm_num) hneg) hlog
    · have hnum : 0 < c + j := by linarith
      have hden : 0 < c - j := by
        have := (abs_lt.mp hj).2
        linarith
      have hratio : 1 < (c + j) / (c - j) := (one_lt_div hden).mpr (by linarith)
      have hlog : 0 < Real.log ((c + j) / (c - j)) := Real.log_pos hratio
      unfold entropyEdge
      positivity

theorem entropyEdge_nonneg {c j : ℝ} (hc : 0 < c) (hj : |j| < c) :
    0 ≤ entropyEdge c j := by
  by_cases h0 : j = 0
  · simp [h0, entropyEdge]
  · exact (entropyEdge_pos_iff hc hj).2 h0 |>.le

/-- Steady entropy production of a finite circulation. -/
noncomputable def entropyProduction (c j : E → ℝ) : ℝ :=
  ∑ e, entropyEdge (c e) (j e)

/-- Entropy production vanishes only at the equilibrium current. -/
theorem entropyProduction_eq_zero_iff (c j : E → ℝ)
    (hc : ∀ e, 0 < c e) (hj : ∀ e, |j e| < c e) :
    entropyProduction c j = 0 ↔ j = 0 := by
  classical
  unfold entropyProduction
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h
      funext e
      by_contra hne
      have hp := (entropyEdge_pos_iff (hc e) (hj e)).2 hne
      exact hp.ne' (h e (Finset.mem_univ e))
    · rintro rfl e he
      simp [entropyEdge]
  · intro e he
    exact entropyEdge_nonneg (hc e) (hj e)

/-- Every nonzero admissible current has entropy production different from
the equilibrium member of the same spectral fibre. -/
theorem entropyProduction_ne_equilibrium (c j : E → ℝ)
    (hc : ∀ e, 0 < c e) (hj : ∀ e, |j e| < c e) (hne : j ≠ 0) :
    entropyProduction c j ≠ entropyProduction c 0 := by
  have hnonzero : entropyProduction c j ≠ 0 := by
    intro hzero
    exact hne ((entropyProduction_eq_zero_iff c j hc hj).mp hzero)
  simpa [entropyProduction, entropyEdge] using hnonzero

/-- The zero current always belongs to a strictly positive conductance fibre. -/
theorem zero_mem_fibre (B : Matrix V E ℂ) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) : (0 : E → ℝ) ∈ GraphSpectralFibre B c := by
  constructor
  · unfold IsStationaryCurrent
    ext v
    simp [Matrix.mulVec]
  · intro e
    simpa using hc e

/-- Connected incidence gives the cycle-space dimension
`|E|-|V|+1`. -/
theorem cycleKernel_finrank {B : Matrix V E ℂ} [Nonempty V]
    (hconnected : IsConnectedIncidence B) :
    Module.finrank ℂ (LinearMap.ker B.mulVecLin) =
      Fintype.card E + 1 - Fintype.card V := by
  classical
  obtain ⟨G, hG, hP2, hPH, hBP, hfix, hdim, hdim'⟩ :=
    exact_harmonic_cycle_projector B hconnected
  exact hdim'

/-- For a connected incidence matrix, the cycle fibre has zero underlying
linear dimension exactly at the tree cardinality `|E|+1=|V|`. -/
theorem cycleKernel_finrank_eq_zero_iff_treeCard {B : Matrix V E ℂ}
    [Nonempty V] (hconnected : IsConnectedIncidence B) :
    Module.finrank ℂ (LinearMap.ker B.mulVecLin) = 0 ↔
      Fintype.card E + 1 = Fintype.card V := by
  classical
  have hdim := cycleKernel_finrank hconnected
  have hrank := connectedIncidence_rank B hconnected
  have hrankLe : Matrix.rank B ≤ Fintype.card E := Matrix.rank_le_card_width B
  omega

/-- **`thm:GT-NCG-graph-fibre`.**  The fibre is the strict conductance box in
the stationary cycle kernel; its dimension is the first Betti number and it is
trivial exactly for a connected tree.  Entropy production varies away from
equilibrium and has unique zero at the zero circulation. -/
theorem graph_spectral_universality_fibre (B : Matrix V E ℂ) [Nonempty V]
    (hconnected : IsConnectedIncidence B) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) :
    Module.finrank ℂ (LinearMap.ker B.mulVecLin) =
        Fintype.card E + 1 - Fintype.card V ∧
      (Module.finrank ℂ (LinearMap.ker B.mulVecLin) = 0 ↔
        Fintype.card E + 1 = Fintype.card V) ∧
      (0 : E → ℝ) ∈ GraphSpectralFibre B c ∧
      (∀ j ∈ GraphSpectralFibre B c,
        entropyProduction c j = 0 ↔ j = 0) := by
  refine ⟨cycleKernel_finrank hconnected,
    cycleKernel_finrank_eq_zero_iff_treeCard hconnected,
    zero_mem_fibre B c hc, ?_⟩
  intro j hj
  exact entropyProduction_eq_zero_iff c j hc hj.2

end FiniteGraphSpectralUniversalityFibre
end NCG
