/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteConnesDistanceAttainmentExact

/-!
# Metric laws and unconditional scaling of finite Connes distance

All variational suprema are the actual commutator suprema. Connectedness
supplies attainment internally, so neither the metric laws nor homogeneous
scaling require an optimizer as a hypothesis.
-/

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace NCG.FiniteConnesDistanceMetric

open FiniteWeightedGraphHodgeDirac FiniteConnesDistanceAttainment

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem abs_sub_le_connesDistance
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance)
    (f : V → ℝ) (hf : graphLipschitz mass conductance f ≤ 1) :
    |f x - f y| ≤ connesDistance mass conductance x y :=
  (connesDistance_isGreatest mass conductance x y hmass hconnected).2 ⟨f, hf, rfl⟩

theorem connesDistance_nonneg
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    0 ≤ connesDistance mass conductance x y :=
  (connesDistance_isGreatest mass conductance x y hmass hconnected).2
    (zero_mem_distanceValues mass conductance x y)

theorem connesDistance_self
    (mass : V → ℝ) (conductance : V → V → ℝ) (x : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    connesDistance mass conductance x x = 0 := by
  obtain ⟨f, hf, hdist⟩ := exists_connesDistance_optimizer mass conductance x x hmass hconnected
  simpa using hdist

theorem connesDistance_comm
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V) :
    connesDistance mass conductance x y = connesDistance mass conductance y x := by
  have hvalues : distanceValues mass conductance x y = distanceValues mass conductance y x := by
    ext r
    simp only [distanceValues, mem_setOf_eq, abs_sub_comm]
  exact congrArg sSup hvalues

theorem connesDistance_triangle
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y z : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    connesDistance mass conductance x z ≤
      connesDistance mass conductance x y + connesDistance mass conductance y z := by
  obtain ⟨f, hf, hdist⟩ := exists_connesDistance_optimizer mass conductance x z hmass hconnected
  rw [hdist]
  exact (abs_sub_le (f x) (f y) (f z)).trans
    (add_le_add (abs_sub_le_connesDistance mass conductance x y hmass hconnected f hf)
      (abs_sub_le_connesDistance mass conductance y z hmass hconnected f hf))

theorem connesDistance_pos_of_ne
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance)
    (hxy : x ≠ y) : 0 < connesDistance mass conductance x y := by
  let f : V → ℝ := fun z => if z = x then 1 else 0
  let L := graphLipschitz mass conductance f
  have hL : 0 ≤ L := norm_nonneg _
  have hden : 0 < L + 1 := by linarith
  have hfeasible : graphLipschitz mass conductance ((L + 1)⁻¹ • f) ≤ 1 := by
    rw [graphLipschitz_smul, abs_of_pos (inv_pos.mpr hden)]
    change (L + 1)⁻¹ * L ≤ 1
    rw [← div_eq_inv_mul]
    exact (div_le_one hden).mpr (by linarith)
  have hbound := abs_sub_le_connesDistance mass conductance x y hmass hconnected
    ((L + 1)⁻¹ • f) hfeasible
  have hvalue : |((L + 1)⁻¹ • f) x - ((L + 1)⁻¹ • f) y| = (L + 1)⁻¹ := by
    simp [f, Ne.symm hxy, abs_of_pos (inv_pos.mpr hden)]
  rw [hvalue] at hbound
  exact (inv_pos.mpr hden).trans_le hbound

theorem connesDistance_eq_zero_iff
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    connesDistance mass conductance x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    have := connesDistance_pos_of_ne mass conductance x y hmass hconnected hxy
    linarith
  · rintro rfl
    exact connesDistance_self mass conductance x hmass hconnected

/-- Homogeneous distance scaling without a supplied maximizer. -/
theorem connesDistance_scaled
    (a : ℝ) (ha : 0 < a) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (hconnected : ConductanceConnected conductance) (x y : V) :
    connesDistance (scaledMass a mass) (scaledConductance a conductance) x y =
      a * connesDistance mass conductance x y :=
  (connesDistance_scaled_isGreatest a ha mass conductance hmass hc x y _
    (connesDistance_isGreatest mass conductance x y hmass hconnected)).csSup_eq

theorem deSitter_connesDistance
    (H t : ℝ) (mass : V → ℝ) (conductance : V → V → ℝ)
    (hmass : ∀ x, 0 < mass x) (hc : ∀ x y, 0 ≤ conductance x y)
    (hconnected : ConductanceConnected conductance) (x y : V) :
    connesDistance (scaledMass (Real.exp (H * t)) mass)
        (scaledConductance (Real.exp (H * t)) conductance) x y =
      Real.exp (H * t) * connesDistance mass conductance x y :=
  connesDistance_scaled _ (Real.exp_pos _) mass conductance hmass hc hconnected x y

end

end NCG.FiniteConnesDistanceMetric
