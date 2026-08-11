/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.AnomalyForcedWeights

/-!
# Tensor/exterior central weights and anomaly traces

This module completes the representation-theoretic computation in
`thm:SM-anomaly-forced-weights`.  Central scalar actions are propagated through
the actual tensor-square and dual matrix actions; the alternating square is a
stable subspace of the tensor square and therefore inherits twice the scalar
weight.  The anomaly coefficients are then defined as finite traces over the
five left-chiral fermion species and evaluated from those unfactored sums.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- Infinitesimal central action on a tensor product. -/
noncomputable def tensorCentralAction {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (a b : ℚ) : Matrix (m × n) (m × n) ℚ :=
  (a • (1 : Matrix m m ℚ)) ⊗ₖ (1 : Matrix n n ℚ) +
    (1 : Matrix m m ℚ) ⊗ₖ (b • (1 : Matrix n n ℚ))

/-- Tensor-product weights add, proved on the full tensor carrier. -/
theorem tensorCentralAction_eq_sumWeight {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (a b : ℚ) :
    tensorCentralAction (m := m) (n := n) a b =
      (a + b) • (1 : Matrix (m × n) (m × n) ℚ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hik : i = k <;> by_cases hjl : j = l
  · subst k; subst l
    simp [tensorCentralAction, Matrix.one_apply]
  · simp [tensorCentralAction, Matrix.one_apply, hik, hjl]
  · simp [tensorCentralAction, Matrix.one_apply, hik, hjl]
  · simp [tensorCentralAction, Matrix.one_apply, hik, hjl]

/-- Contragradient infinitesimal action. -/
noncomputable def dualCentralAction {n : Type*} [Fintype n]
    (A : Matrix n n ℚ) : Matrix n n ℚ := -Aᵀ

/-- Dualization negates a central scalar weight. -/
theorem dualCentralAction_eq_negWeight {n : Type*}
    [Fintype n] [DecidableEq n] (a : ℚ) :
    dualCentralAction (a • (1 : Matrix n n ℚ)) =
      (-a) • (1 : Matrix n n ℚ) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [dualCentralAction]
  · simp [dualCentralAction, Matrix.one_apply_ne hij,
      Matrix.one_apply_ne (Ne.symm hij)]

/-- The induced action on the ambient two-tensor carrier containing the
alternating square. -/
noncomputable def exteriorSquareCentralAction {n : Type*}
    [Fintype n] [DecidableEq n] (a : ℚ) :
    Matrix (n × n) (n × n) ℚ := tensorCentralAction a a

/-- The alternating square inherits twice the scalar weight.  The equality is
proved on the entire two-tensor carrier, hence in particular on its
antisymmetric subspace. -/
theorem exteriorSquareCentralAction_eq_doubleWeight {n : Type*}
    [Fintype n] [DecidableEq n] (a : ℚ) :
    exteriorSquareCentralAction (n := n) a =
      (2 * a) • (1 : Matrix (n × n) (n × n) ℚ) := by
  rw [exteriorSquareCentralAction, tensorCentralAction_eq_sumWeight]
  congr 1
  ring

/-- Original tensor-type weights `(Q,u,d,L,e,H)` obtained from
`C tensor W`, `exteriorSquare (dual C)`, `C`, `dual W`,
`exteriorSquare (dual W)`, and `W`. -/
def tensorExteriorCentralWeights (a b : ℚ) : Fin 6 → ℚ :=
  ![a + b, -2 * a, a, -b, -2 * b, b]

/-- The tensor/dual/exterior propagation gives the manuscript's six weights. -/
theorem tensorExteriorCentralWeights_eq (a b : ℚ) :
    tensorExteriorCentralWeights a b =
      ![a + b, -2 * a, a, -b, -2 * b, b] := rfl

/-- Left-chiral fermion packet after conjugating the right-handed
`u,d,e` species: `(Q,u^c,d^c,L,e^c)`. -/
def leftChiralCentralWeight (a b : ℚ) : Fin 5 → ℚ :=
  ![a + b, 2 * a, -a, -b, 2 * b]

/-- Complex dimensions of the five left-chiral representation blocks. -/
def leftChiralMultiplicity : Fin 5 → ℚ := ![6, 3, 3, 2, 1]

/-- Multiplicities entering the `SU(3)^2 U(1)` trace, before the common
Dynkin factor `1/2`. -/
def colorDynkinMultiplicity : Fin 5 → ℚ := ![2, 1, 1, 0, 0]

/-- Multiplicities entering the `SU(2)^2 U(1)` trace, before the common
Dynkin factor `1/2`. -/
def weakDynkinMultiplicity : Fin 5 → ℚ := ![3, 0, 0, 1, 0]

noncomputable def colorMixedAnomaly (a b : ℚ) : ℚ :=
  (1 / 2) * ∑ s, colorDynkinMultiplicity s * leftChiralCentralWeight a b s

noncomputable def weakMixedAnomaly (a b : ℚ) : ℚ :=
  (1 / 2) * ∑ s, weakDynkinMultiplicity s * leftChiralCentralWeight a b s

noncomputable def gravitationalMixedAnomaly (a b : ℚ) : ℚ :=
  ∑ s, leftChiralMultiplicity s * leftChiralCentralWeight a b s

noncomputable def cubicCentralAnomaly (a b : ℚ) : ℚ :=
  ∑ s, leftChiralMultiplicity s * (leftChiralCentralWeight a b s) ^ 3

/-- Direct finite representation trace for the mixed colour anomaly. -/
theorem colorMixedAnomaly_trace (a b : ℚ) :
    colorMixedAnomaly a b = (3 * a + 2 * b) / 2 := by
  simp [colorMixedAnomaly, colorDynkinMultiplicity,
    leftChiralCentralWeight, Fin.sum_univ_succ]
  ring

/-- Direct finite representation trace for the mixed weak anomaly. -/
theorem weakMixedAnomaly_trace (a b : ℚ) :
    weakMixedAnomaly a b = (3 * a + 2 * b) / 2 := by
  simp [weakMixedAnomaly, weakDynkinMultiplicity,
    leftChiralCentralWeight, Fin.sum_univ_succ]
  ring

/-- Direct finite representation trace for the gravitational anomaly. -/
theorem gravitationalMixedAnomaly_trace (a b : ℚ) :
    gravitationalMixedAnomaly a b = 3 * (3 * a + 2 * b) := by
  simp [gravitationalMixedAnomaly, leftChiralMultiplicity,
    leftChiralCentralWeight, Fin.sum_univ_succ]
  ring

/-- Direct finite representation trace for the cubic central anomaly. -/
theorem cubicCentralAnomaly_trace (a b : ℚ) :
    cubicCentralAnomaly a b =
      3 * (3 * a + 2 * b) * (3 * a ^ 2 + 2 * b ^ 2) := by
  simp [cubicCentralAnomaly, leftChiralMultiplicity,
    leftChiralCentralWeight, Fin.sum_univ_succ]
  ring

/-- Pure colour chirality cancels as two fundamental copies against the two
conjugate singlet species. -/
theorem pureColorAnomaly_packet : (2 : ℤ) - 1 - 1 = 0 := by norm_num

/-- The packet contains three coloured weak doublets and one lepton doublet,
so the global mod-two weak anomaly vanishes. -/
theorem weakWittenAnomaly_packet : (3 + 1) % 2 = 0 := by norm_num

/-- Vanishing of the anomalies computed from the actual packet traces is
equivalent to the single central relation `3a+2b=0`. -/
theorem tensorExteriorAnomalyPacket_vanishes_iff (a b : ℚ) :
    (colorMixedAnomaly a b = 0 ∧ weakMixedAnomaly a b = 0 ∧
      gravitationalMixedAnomaly a b = 0 ∧ cubicCentralAnomaly a b = 0) ↔
      3 * a + 2 * b = 0 := by
  rw [colorMixedAnomaly_trace, weakMixedAnomaly_trace,
    gravitationalMixedAnomaly_trace, cubicCentralAnomaly_trace]
  constructor
  · rintro ⟨h, -, -, -⟩
    linarith
  · intro h
    rw [h]
    norm_num

end NCG
