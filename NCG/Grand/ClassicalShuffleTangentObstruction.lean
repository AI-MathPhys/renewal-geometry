/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Classical reversible shuffles are orthogonal to Hamiltonian tangents

Inverse-paired permutation channels are self-adjoint on coefficient space,
whereas Hamiltonian derivations are skew-adjoint.  This file proves the finite
Frobenius orthogonality and the resulting zero Hamiltonian projection.
-/

namespace NCG

open Matrix

/-- Matrix of a permutation acting on a finite coefficient basis. -/
def shufflePermutationMatrix {ι : Type*} [DecidableEq ι]
    (σ : Equiv.Perm ι) : Matrix ι ι ℝ :=
  fun i j => if i = σ j then 1 else 0

/-- Transposition replaces a permutation by its inverse. -/
theorem shufflePermutationMatrix_transpose {ι : Type*} [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    (shufflePermutationMatrix σ)ᵀ = shufflePermutationMatrix σ.symm := by
  ext i j
  simp only [Matrix.transpose_apply, shufflePermutationMatrix]
  by_cases h : j = σ i
  · rw [if_pos h]
    have : i = σ.symm j := by simpa using congrArg σ.symm h.symm
    rw [if_pos this]
  · rw [if_neg h]
    have : i ≠ σ.symm j := by
      intro hi
      apply h
      simpa [hi]
    rw [if_neg this]

/-- Frobenius pairing on real superoperator matrices. -/
noncomputable def superFrobeniusInner {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Squared Frobenius norm of a real superoperator matrix. -/
noncomputable def superFrobeniusSq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) : ℝ :=
  superFrobeniusInner A A

/-- A symmetric superoperator is Frobenius-orthogonal to every skew-symmetric
superoperator. -/
theorem symmetric_skew_superoperator_orthogonal {ι : Type*} [Fintype ι]
    (S C : Matrix ι ι ℝ) (hS : Sᵀ = S) (hC : Cᵀ = -C) :
    superFrobeniusInner C S = 0 := by
  have hswap : superFrobeniusInner C S =
      superFrobeniusInner Cᵀ Sᵀ := by
    simp only [superFrobeniusInner, Matrix.transpose_apply]
    rw [Finset.sum_comm]
  rw [hC, hS] at hswap
  have hneg : superFrobeniusInner (-C) S =
      -superFrobeniusInner C S := by
    simp [superFrobeniusInner, Finset.sum_neg_distrib]
  rw [hneg] at hswap
  linarith

/-- An inverse-paired random permutation channel. -/
noncomputable def inversePairedShuffle {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (w : Ω → ℝ) (σ : Ω → Equiv.Perm ι) : Matrix ι ι ℝ :=
  ∑ ω, w ω • shufflePermutationMatrix (σ ω)

/-- Equal weights on inverse pairs make the shuffle channel self-adjoint. -/
theorem inversePairedShuffle_symmetric {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (pair : Equiv.Perm Ω) (w : Ω → ℝ) (σ : Ω → Equiv.Perm ι)
    (_hpair : ∀ ω, pair (pair ω) = ω)
    (hw : ∀ ω, w (pair ω) = w ω)
    (hσ : ∀ ω, σ (pair ω) = (σ ω).symm) :
    (inversePairedShuffle w σ)ᵀ = inversePairedShuffle w σ := by
  rw [inversePairedShuffle, Matrix.transpose_sum]
  simp_rw [Matrix.transpose_smul, shufflePermutationMatrix_transpose]
  have hreindex := Equiv.sum_comp pair
    (fun ω => w ω • shufflePermutationMatrix (σ ω))
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro ω _
  rw [hw, hσ]

/-- Orthogonal projection coefficients onto a supplied Hamiltonian-derivation
basis.  For a skew-adjoint basis this is the canonical Hamiltonian component
up to its positive Gram normalization. -/
noncomputable def hamiltonianProjection {α ι : Type*}
    [Fintype α] [Fintype ι]
    (C : α → Matrix ι ι ℝ) (S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑ a, (superFrobeniusInner (C a) S) • C a

/-- `thm:SMST-classical-shuffle-obstruction`: an inverse-paired shuffle minus
the identity is symmetric, hence its Hamiltonian projection is zero and its
Hamiltonian residual retains its full squared norm. -/
theorem classical_shuffle_tangent_obstruction {Ω α ι : Type*}
    [Fintype Ω] [Fintype α] [Fintype ι] [DecidableEq ι]
    (pair : Equiv.Perm Ω) (w : Ω → ℝ) (σ : Ω → Equiv.Perm ι)
    (C : α → Matrix ι ι ℝ)
    (hpair : ∀ ω, pair (pair ω) = ω)
    (hw : ∀ ω, w (pair ω) = w ω)
    (hσ : ∀ ω, σ (pair ω) = (σ ω).symm)
    (hC : ∀ a, (C a)ᵀ = -(C a)) :
    let S := inversePairedShuffle w σ - 1
    hamiltonianProjection C S = 0
      ∧ superFrobeniusSq (S - hamiltonianProjection C S)
        = superFrobeniusSq S := by
  dsimp only
  have hΨ := inversePairedShuffle_symmetric pair w σ hpair hw hσ
  have hS : (inversePairedShuffle w σ - 1)ᵀ =
      inversePairedShuffle w σ - 1 := by
    rw [Matrix.transpose_sub, hΨ, Matrix.transpose_one]
  have hcoeff : ∀ a,
      superFrobeniusInner (C a) (inversePairedShuffle w σ - 1) = 0 :=
    fun a => symmetric_skew_superoperator_orthogonal _ _ hS (hC a)
  have hproj : hamiltonianProjection C (inversePairedShuffle w σ - 1) = 0 := by
    simp [hamiltonianProjection, hcoeff]
  rw [hproj, sub_zero]
  exact ⟨rfl, rfl⟩

end NCG
