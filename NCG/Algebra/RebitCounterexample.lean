/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The rebit parallel counterexample

Covers `prop:rebit-parallel-counterexample` from
`manuscripts/renewal_emergence/renewal_emergence.tex`: in finite-dimensional **real** quantum
theory there are channels `T₊ ≡₁ T₋` with `T₊ ≢∥ T₋` — ordinary
process reduction need not be monoidal.

The channels are `T₊ = id` and `T₋ = transpose` on the rebit algebra
`M₂(ℝ)`.  Every rebit state and effect is a **symmetric** real
matrix, and the transpose fixes symmetric matrices, so `T₊` and `T₋`
agree on every single-system preparation and give identical outcome
weights against every effect (`transpose_eq_id_on_states`,
`transpose_single_system_weights`) — they are ordinarily
operationally equivalent.  But their extensions by the identity on a
second rebit (`realAmpliate`, the partial transpose) **differ on the
maximally entangled real state** `Ω = ψψᵀ`, `ψ = |00⟩ + |11⟩`:
the ampliated outputs are distinct positive matrices
(`ampliate_transpose_ne_ampliate_id`), and an explicit matrix-unit
effect assigns them different weights
(`ampliate_transpose_weight_ne`), so `T₊ ≢∥ T₋`.
-/

namespace NCG

open Matrix

/-- The rebit transpose channel `T₋`. -/
def transposeMap : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ]
    Matrix (Fin 2) (Fin 2) ℝ where
  toFun X := Xᵀ
  map_add' X Y := Matrix.transpose_add X Y
  map_smul' c X := Matrix.transpose_smul c X

@[simp] theorem transposeMap_apply (X : Matrix (Fin 2) (Fin 2) ℝ)
    (i j : Fin 2) : transposeMap X i j = X j i := rfl

/-- The extension of a rebit map by the identity on a second rebit
(the real ampliation `id ⊗ Φ` in product indices). -/
def realAmpliate
    (Φ : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ →ₗ[ℝ]
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ where
  toFun X := Matrix.of fun p q =>
    Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2
  map_add' X Y := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    change Φ (Matrix.of fun i j => (X + Y) (p1, i) (q1, j)) p2 q2
      = Φ (Matrix.of fun i j => X (p1, i) (q1, j)) p2 q2
        + Φ (Matrix.of fun i j => Y (p1, i) (q1, j)) p2 q2
    have h1 : (Matrix.of fun i j => (X + Y) (p1, i) (q1, j))
        = (Matrix.of fun i j => X (p1, i) (q1, j))
          + Matrix.of fun i j => Y (p1, i) (q1, j) := by
      ext i j
      simp [Matrix.add_apply]
    rw [h1, map_add, Matrix.add_apply]
  map_smul' c X := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    change Φ (Matrix.of fun i j => (c • X) (p1, i) (q1, j)) p2 q2
      = (c • Φ (Matrix.of fun i j => X (p1, i) (q1, j))) p2 q2
    have h1 : (Matrix.of fun i j => (c • X) (p1, i) (q1, j))
        = c • Matrix.of fun i j => X (p1, i) (q1, j) := by
      ext i j
      simp [Matrix.smul_apply]
    rw [h1, map_smul]

@[simp] theorem realAmpliate_apply
    (Φ : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (p q : Fin 2 × Fin 2) :
    realAmpliate Φ X p q
      = Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2 := rfl

/-- Ampliating the identity channel does nothing. -/
theorem realAmpliate_id (X : Matrix (Fin 2 × Fin 2)
    (Fin 2 × Fin 2) ℝ) :
    realAmpliate LinearMap.id X = X := by
  ext p q
  simp only [realAmpliate_apply, LinearMap.id_coe, id_eq,
    Matrix.of_apply]

/-- **Single-system agreement**: the transpose channel fixes every
symmetric matrix, hence every rebit state and effect. -/
theorem transpose_eq_id_on_states
    (ρ : Matrix (Fin 2) (Fin 2) ℝ) (hρ : ρ.IsSymm) :
    transposeMap ρ = ρ := hρ

/-- **Single-system agreement (weights)**: `T₊` and `T₋` give the
same outcome weight to every rebit preparation against every
effect. -/
theorem transpose_single_system_weights
    (ρ Eff : Matrix (Fin 2) (Fin 2) ℝ) (hρ : ρ.IsSymm) :
    (Eff * transposeMap ρ).trace = (Eff * ρ).trace := by
  rw [transpose_eq_id_on_states ρ hρ]

/-- The maximally entangled real unit vector `ψ = |00⟩ + |11⟩`. -/
def entangledVec : Fin 2 × Fin 2 → ℝ :=
  fun p => if p.1 = p.2 then 1 else 0

/-- The maximally entangled real state `Ω = ψψᵀ`. -/
def entangledState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  vecMulVec entangledVec entangledVec

theorem entangledState_posSemidef : entangledState.PosSemidef := by
  have hstar : star entangledVec = entangledVec := by
    funext p
    simp [entangledVec]
  have h1 : entangledState
      = vecMulVec entangledVec (star entangledVec) := by
    rw [entangledState, hstar]
  rw [h1]
  exact Matrix.posSemidef_vecMulVec_self_star entangledVec

/-- **Parallel disagreement (matrix form)**: the ampliations of `T₋`
and `T₊` differ on the maximally entangled real state. -/
theorem ampliate_transpose_ne_ampliate_id :
    realAmpliate transposeMap entangledState
      ≠ realAmpliate LinearMap.id entangledState := by
  intro heq
  have h1 := congrFun (congrFun heq ((0 : Fin 2), (0 : Fin 2)))
    ((1 : Fin 2), (1 : Fin 2))
  rw [realAmpliate_id] at h1
  simp only [realAmpliate_apply, transposeMap_apply,
    Matrix.of_apply] at h1
  rw [show entangledState ((0 : Fin 2), (1 : Fin 2))
      ((1 : Fin 2), (0 : Fin 2)) = 0 by
    simp [entangledState, vecMulVec_apply, entangledVec]] at h1
  rw [show entangledState ((0 : Fin 2), (0 : Fin 2))
      ((1 : Fin 2), (1 : Fin 2)) = 1 by
    simp [entangledState, vecMulVec_apply, entangledVec]] at h1
  norm_num at h1

/-- Trace pairing against a matrix unit reads off an entry. -/
theorem trace_single_mul {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) (M : Matrix n n ℝ) :
    (Matrix.single j i (1 : ℝ) * M).trace = M i j := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.single_mul_apply_same, one_mul]
  · intro k _ hkj
    rw [Matrix.single_mul_apply_of_ne (h := hkj)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **Proposition `prop:rebit-parallel-counterexample`**: `T₊ = id`
and `T₋ = transpose` on the rebit agree on every single-system
preparation and effect (`≡₁`), yet an explicit effect distinguishes
their ampliations on the entangled real state (`≢∥`). -/
theorem rebit_parallel_counterexample :
    (∀ ρ Eff : Matrix (Fin 2) (Fin 2) ℝ, ρ.IsSymm →
      (Eff * transposeMap ρ).trace = (Eff * ρ).trace)
    ∧ entangledState.PosSemidef
    ∧ ∃ Eff : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ,
        (Eff * realAmpliate transposeMap entangledState).trace
          ≠ (Eff * realAmpliate LinearMap.id entangledState).trace
    := by
  refine ⟨fun ρ Eff hρ =>
    transpose_single_system_weights ρ Eff hρ,
    entangledState_posSemidef, ?_⟩
  refine ⟨Matrix.single ((1 : Fin 2), (1 : Fin 2))
    ((0 : Fin 2), (0 : Fin 2)) 1, ?_⟩
  rw [trace_single_mul, trace_single_mul, realAmpliate_id]
  simp only [realAmpliate_apply, transposeMap_apply,
    Matrix.of_apply]
  rw [show entangledState ((0 : Fin 2), (1 : Fin 2))
      ((1 : Fin 2), (0 : Fin 2)) = 0 by
    simp [entangledState, vecMulVec_apply, entangledVec]]
  rw [show entangledState ((0 : Fin 2), (0 : Fin 2))
      ((1 : Fin 2), (1 : Fin 2)) = 1 by
    simp [entangledState, vecMulVec_apply, entangledVec]]
  norm_num

end NCG
