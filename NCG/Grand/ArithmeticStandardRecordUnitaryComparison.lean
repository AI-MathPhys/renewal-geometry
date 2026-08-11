/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ArStandardComparison
import NCG.Grand.ExactSourceSchurResidual

/-!
# Unitary comparison of standard and record arithmetic carriers

The carriers in this file are genuinely separate finite types.  An endpoint
label equivalence produces the canonical unitary; all operators, sources,
word Grams, and transfer panels are then transported across it.  The common
source Moore--Penrose residual is also proved to vanish.
-/

open Matrix

namespace NCG

/-- Matrix of the endpoint-label equivalence from a standard carrier `s` to a
record carrier `r`. -/
def endpointLabelUnitary {s r : Type*} [Fintype s] [Fintype r]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r) : Matrix r s ℂ :=
  Matrix.of fun i j => if i = e j then 1 else 0

theorem endpointLabelUnitary_mulVec
    {s r : Type*} [Fintype s] [Fintype r]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r) (x : s → ℂ) :
    endpointLabelUnitary e *ᵥ x = fun i => x (e.symm i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, endpointLabelUnitary, Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm i)]
  · simp
  · intro j _ hj
    have hneq : i ≠ e j := by
      intro h
      apply hj
      apply e.injective
      simpa using h.symm
    simp [hneq]
  · simp

theorem endpointLabelUnitary_conjTranspose_mul
    {s r : Type*} [Fintype s] [Fintype r]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r) :
    (endpointLabelUnitary e)ᴴ * endpointLabelUnitary e = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    endpointLabelUnitary, Matrix.of_apply]
  rw [Finset.sum_eq_single (e i)]
  · by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  · intro k _ hk
    have hki : k ≠ e i := hk
    simp [hki]
  · simp

theorem endpointLabelUnitary_mul_conjTranspose
    {s r : Type*} [Fintype s] [Fintype r]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r) :
    endpointLabelUnitary e * (endpointLabelUnitary e)ᴴ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    endpointLabelUnitary, Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm i)]
  · by_cases hij : i = j
    · subst j
      simp
    · have hsymm : e.symm i ≠ e.symm j := by
        exact fun h => hij (e.symm.injective h)
      simp [hij, Ne.symm hij, Matrix.one_apply]
  · intro k _ hk
    have hki : k ≠ e.symm i := hk
    have hneq : i ≠ e k := by
      intro h
      apply hki
      apply e.injective
      simpa using h.symm
    simp [hneq]
  · simp

/-- Transport a standard arithmetic operator to the record carrier. -/
def endpointTransport {s r : Type*} [Fintype s] [Fintype r]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r)
    (A : Matrix s s ℂ) : Matrix r r ℂ :=
  endpointLabelUnitary e * A * (endpointLabelUnitary e)ᴴ

/-- The canonical endpoint unitary intertwines every transported operator. -/
theorem endpointLabelUnitary_intertwines
    {s r : Type*} [Fintype s] [Fintype r]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r)
    (A : Matrix s s ℂ) :
    endpointLabelUnitary e * A =
      endpointTransport e A * endpointLabelUnitary e := by
  unfold endpointTransport
  rw [Matrix.mul_assoc, Matrix.mul_assoc,
    endpointLabelUnitary_conjTranspose_mul, Matrix.mul_one]

/-- Transport preserves every source Gram. -/
theorem endpointLabelUnitary_sourceGram
    {s r k : Type*} [Fintype s] [Fintype r] [Fintype k]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r)
    (S : Matrix s k ℂ) :
    (endpointLabelUnitary e * S)ᴴ * (endpointLabelUnitary e * S) = Sᴴ * S := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (endpointLabelUnitary e)ᴴ,
    endpointLabelUnitary_conjTranspose_mul, Matrix.one_mul]

/-- Transport preserves every finite transfer panel `Soutᴴ A Sin`. -/
theorem endpointLabelUnitary_transferPanel
    {s r kin kout : Type*} [Fintype s] [Fintype r]
    [Fintype kin] [Fintype kout] [DecidableEq s] [DecidableEq r]
    (e : s ≃ r) (A : Matrix s s ℂ)
    (Sin : Matrix s kin ℂ) (Sout : Matrix s kout ℂ) :
    (endpointLabelUnitary e * Sout)ᴴ * endpointTransport e A *
        (endpointLabelUnitary e * Sin) = Soutᴴ * A * Sin := by
  rw [Matrix.conjTranspose_mul]
  unfold endpointTransport
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (endpointLabelUnitary e)ᴴ,
    endpointLabelUnitary_conjTranspose_mul, Matrix.one_mul,
    ← Matrix.mul_assoc (endpointLabelUnitary e)ᴴ,
    endpointLabelUnitary_conjTranspose_mul, Matrix.one_mul]

/-- Once the standard source is transported, both mutual Moore--Penrose Schur
residuals are the same expression `G - G Gdag G` and vanish. -/
theorem transportedStandardSource_mutualSchurResiduals
    {s r k : Type*} [Fintype s] [Fintype r] [Fintype k]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r)
    (Sstd : Matrix s k ℂ) (Gdag : Matrix k k ℂ)
    (hPenrose : (Sstdᴴ * Sstd) * Gdag * (Sstdᴴ * Sstd) = Sstdᴴ * Sstd) :
    let Scan := endpointLabelUnitary e * Sstd
    (Scanᴴ * Scan - Scanᴴ * Scan * Gdag * (Sstdᴴ * Sstd) = 0)
      ∧ (Sstdᴴ * Sstd - Sstdᴴ * Sstd * Gdag * (Scanᴴ * Scan) = 0) := by
  dsimp only
  rw [endpointLabelUnitary_sourceGram]
  constructor <;> rw [hPenrose, sub_self]

/-- Exact separate-carrier content of `thm:ar-standard-comparison`. -/
theorem arithmeticStandardRecord_unitaryComparison
    {s r k : Type*} [Fintype s] [Fintype r] [Fintype k]
    [DecidableEq s] [DecidableEq r] (e : s ≃ r)
    (Sstd : Matrix s k ℂ) :
    let U := endpointLabelUnitary e
    let Scan := U * Sstd
    Uᴴ * U = 1 ∧ U * Uᴴ = 1
      ∧ Scanᴴ * Scan = Sstdᴴ * Sstd
      ∧ ∀ A : Matrix s s ℂ,
          U * A = endpointTransport e A * U := by
  dsimp only
  exact ⟨endpointLabelUnitary_conjTranspose_mul e,
    endpointLabelUnitary_mul_conjTranspose e,
    endpointLabelUnitary_sourceGram e Sstd,
    endpointLabelUnitary_intertwines e⟩

end NCG
