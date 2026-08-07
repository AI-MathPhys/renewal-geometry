/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact harmonic cycle projector
  (`thm:cycle-projector`, Gran-Tensor manuscript)

* `cycle_projector`: for any Hermitian Penrose inverse `G` of
  the vertex Laplacian `∂∂ᴴ`, the boxed operator
  `Π_cyc = I_E - ∂ᴴG∂` is the orthogonal projection onto the
  cycle space `H₁(Γ;ℂ) = Ker ∂`: idempotent, Hermitian, kills
  under `∂`, and fixes the kernel pointwise; and rank–nullity
  gives `dim H₁ + (|V| - 1) = |E|` under the connected-graph
  rank `rank ∂ = |V| - 1`.

Rendering disclosed: `(∂∂ᴴ)†` is rendered by an arbitrary
Hermitian matrix `G` with the Penrose identities (existence of
the Moore–Penrose inverse of the Hermitian Laplacian by the
spectral theorem is not re-derived); the key range identity
`∂∂ᴴG∂ = ∂` is obtained by `MMᴴ = 0` cancellation, with no
diagonalization.  The dimension clause is stated in
subtraction-free form; that a connected graph's boundary has
rank `|V| - 1` is the manuscript's graph-theory bookkeeping.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:cycle-projector`: `Π_cyc = I - ∂ᴴ(∂∂ᴴ)†∂` is the
orthogonal projection onto the cycle space, with the
rank–nullity cycle dimension. -/
theorem cycle_projector {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E]
    (dl : Matrix V E ℂ) (G : Matrix V V ℂ) (hG : Gᴴ = G)
    (h1 : dl * dlᴴ * G * (dl * dlᴴ) = dl * dlᴴ)
    (h2 : G * (dl * dlᴴ) * G = G) :
    ((1 - dlᴴ * G * dl) * (1 - dlᴴ * G * dl)
        = 1 - dlᴴ * G * dl)
    ∧ (1 - dlᴴ * G * dl)ᴴ = 1 - dlᴴ * G * dl
    ∧ dl * (1 - dlᴴ * G * dl) = 0
    ∧ (∀ x : E → ℂ, dl *ᵥ x = 0
        → (1 - dlᴴ * G * dl) *ᵥ x = x)
    ∧ (Matrix.rank dl = Fintype.card V - 1 →
        Module.finrank ℂ (LinearMap.ker dl.mulVecLin)
          + (Fintype.card V - 1) = Fintype.card E) := by
  have h1' : dl * (dlᴴ * (G * (dl * dlᴴ))) = dl * dlᴴ := by
    have h := h1
    simp only [Matrix.mul_assoc] at h
    exact h
  have hrange : dl * dlᴴ * G * dl = dl := by
    set M := dl * dlᴴ * G * dl - dl with hM
    have hMhval : Mᴴ = dlᴴ * Gᴴ * (dl * dlᴴ) - dlᴴ := by
      rw [hM]
      simp only [Matrix.conjTranspose_sub,
        Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      congr 1
      simp only [Matrix.mul_assoc]
    have e1 : (dl * dlᴴ * G * dl) * (dlᴴ * Gᴴ * (dl * dlᴴ))
        = dl * dlᴴ := by
      rw [hG]
      simp only [Matrix.mul_assoc]
      rw [h1', h1']
    have e2 : dl * (dlᴴ * Gᴴ * (dl * dlᴴ)) = dl * dlᴴ := by
      rw [hG]
      simp only [Matrix.mul_assoc]
      rw [h1']
    have e3 : (dl * dlᴴ * G * dl) * dlᴴ = dl * dlᴴ := by
      simp only [Matrix.mul_assoc]
      rw [h1']
    have hMM : M * Mᴴ = 0 := by
      rw [hMhval, hM, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, e1, e2, e3]
      abel
    have hMh0 : Mᴴ = 0 := by
      apply Matrix.conjTranspose_mul_self_eq_zero.mp
      rw [Matrix.conjTranspose_conjTranspose]
      exact hMM
    have hM0 : M = 0 := by
      have h := congrArg Matrix.conjTranspose hMh0
      simpa using h
    have hsub : dl * dlᴴ * G * dl - dl = 0 := by
      rw [← hM]
      exact hM0
    exact sub_eq_zero.mp hsub
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hcore : dlᴴ * G * dl * (dlᴴ * G * dl)
        = dlᴴ * G * dl := by
      calc dlᴴ * G * dl * (dlᴴ * G * dl)
          = dlᴴ * (G * (dl * dlᴴ) * G) * dl := by
            simp only [Matrix.mul_assoc]
        _ = dlᴴ * G * dl := by rw [h2]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [hcore]
    abel
  · simp only [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hG]
    congr 1
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_sub, Matrix.mul_one,
      show dl * (dlᴴ * G * dl) = dl * dlᴴ * G * dl by
        simp only [Matrix.mul_assoc],
      hrange, sub_self]
  · intro x hx
    rw [Matrix.sub_mulVec, Matrix.one_mulVec,
      show (dlᴴ * G * dl) *ᵥ x = dlᴴ *ᵥ (G *ᵥ (dl *ᵥ x)) by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc],
      hx]
    simp
  · intro hrank
    have h := LinearMap.finrank_range_add_finrank_ker
      dl.mulVecLin
    rw [Module.finrank_pi] at h
    have hr : Matrix.rank dl
        = Module.finrank ℂ (LinearMap.range dl.mulVecLin) :=
      rfl
    omega

end NCG
