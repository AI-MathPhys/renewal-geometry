/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Unitality and stationarity (`lem:unital-stationary`)

For a linear map `Φ` on `M_n(ℂ)` with trace adjoint `Φ_*`
(characterised by `Tr(Φ_*(x)·y) = Tr(x·Φ(y))`):

* `Φ(1) = 1` iff `Φ_*` is trace preserving;
* `Φ_*(ρ) = ρ` iff the functional `a ↦ Tr(ρ·a)` is `Φ`-invariant.

Both directions follow from nondegeneracy of the trace pairing
(`trace_pairing_left_cancel`).
-/

namespace NCG

open Matrix

variable {n : ℕ}

/-- Nondegeneracy of the trace pairing: matrices with the same traces
against every test matrix are equal. -/
theorem trace_pairing_left_cancel {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ x : Matrix (Fin n) (Fin n) ℂ,
      (x * A).trace = (x * B).trace) : A = B := by
  have hval : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n),
      (Matrix.single j i (1 : ℂ) * M).trace = M i j := by
    intro M i j
    simp only [Matrix.trace, Matrix.diag]
    rw [Finset.sum_eq_single j]
    · rw [Matrix.single_mul_apply_same, one_mul]
    · intro k _ hkj
      rw [Matrix.single_mul_apply_of_ne (h := hkj)]
    · intro habs
      exact absurd (Finset.mem_univ j) habs
  ext i j
  have h1 := h (Matrix.single j i 1)
  rw [hval A i j, hval B i j] at h1
  exact h1

variable (Φ Φstar :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)

/-- **Lemma `lem:unital-stationary` (unitality)**: given the trace
adjoint pairing, `Φ` is unital iff `Φ_*` is trace preserving. -/
theorem unital_iff_trace_preserving
    (hadj : ∀ x y, (Φstar x * y).trace = (x * Φ y).trace) :
    Φ 1 = 1 ↔ ∀ x, (Φstar x).trace = x.trace := by
  constructor
  · intro h1 x
    have h2 := hadj x 1
    rw [mul_one, h1, mul_one] at h2
    exact h2
  · intro h
    refine trace_pairing_left_cancel fun x => ?_
    have h2 := hadj x 1
    rw [mul_one] at h2
    rw [← h2, h x, mul_one]

/-- **Lemma `lem:unital-stationary` (stationarity)**: `Φ_*(ρ) = ρ`
iff the state functional `a ↦ Tr(ρ a)` is invariant under `Φ`. -/
theorem stationary_iff_invariant_state
    (hadj : ∀ x y, (Φstar x * y).trace = (x * Φ y).trace)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Φstar ρ = ρ ↔ ∀ a, (ρ * Φ a).trace = (ρ * a).trace := by
  constructor
  · intro h a
    rw [← hadj ρ a, h]
  · intro h
    refine trace_pairing_left_cancel fun x => ?_
    rw [Matrix.trace_mul_comm x (Φstar ρ), hadj ρ x, h x,
      Matrix.trace_mul_comm ρ x]

end NCG
