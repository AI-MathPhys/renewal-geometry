/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Graded monoidal CAR packet
  (`thm:SMST-monoidal-CAR`, Gran-Tensor manuscript)

* `monoidal_car`: from the polar relations of the parity-cell
  corner (`f² = 0`, `fᴴf = P_R`, `ffᴴ = P_L`, `πf = -fπ`,
  `π² = 1`), the two-slot operators `b₁† = f⊗I`, `b₂† = π⊗f`
  satisfy the boxed canonical anticommutation relations
  `{bᵢ, bⱼ†} = δᵢⱼI`, `{bᵢ, bⱼ} = {bᵢ†, bⱼ†} = 0`.

Rendering disclosed: the exterior-algebra occupation basis, the
four incidence rows, and the two-slot Pythagorean/provenance
decompositions are the manuscript's packaging over the source
Schur formula (`thm:joint-source-short`, proved) and the CAR
identities proved here.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- `thm:SMST-monoidal-CAR`: the boxed CAR identities. -/
theorem monoidal_car {d : Type*} [Fintype d] [DecidableEq d]
    (f π PL PR : Matrix d d ℂ)
    (hf2 : f * f = 0) (hffH : f * fᴴ = PL) (hfHf : fᴴ * f = PR)
    (hsum : PL + PR = 1) (hπH : πᴴ = π) (hπ2 : π * π = 1)
    (hanti : π * f = -(f * π)) :
    ((fᴴ ⊗ₖ (1 : Matrix d d ℂ)) * (f ⊗ₖ 1)
        + (f ⊗ₖ 1) * (fᴴ ⊗ₖ (1 : Matrix d d ℂ)) = 1)
    ∧ ((π ⊗ₖ fᴴ) * (π ⊗ₖ f) + (π ⊗ₖ f) * (π ⊗ₖ fᴴ) = 1)
    ∧ ((fᴴ ⊗ₖ (1 : Matrix d d ℂ)) * (π ⊗ₖ f)
        + (π ⊗ₖ f) * (fᴴ ⊗ₖ (1 : Matrix d d ℂ)) = 0)
    ∧ ((f ⊗ₖ (1 : Matrix d d ℂ)) * (π ⊗ₖ f)
        + (π ⊗ₖ f) * (f ⊗ₖ (1 : Matrix d d ℂ)) = 0)
    ∧ ((fᴴ ⊗ₖ (1 : Matrix d d ℂ))
          * (fᴴ ⊗ₖ (1 : Matrix d d ℂ)) = 0)
    ∧ ((π ⊗ₖ fᴴ) * (π ⊗ₖ fᴴ) = 0) := by
  have hfH2 : fᴴ * fᴴ = 0 := by
    have := congrArg Matrix.conjTranspose hf2
    rwa [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_zero] at this
  have hantiH : π * fᴴ = -(fᴴ * π) := by
    have h := congrArg Matrix.conjTranspose hanti
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_mul, hπH] at h
    -- h : fᴴ * π = -(π * fᴴ)
    rw [h, neg_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hfHf, hffH, Matrix.one_mul]
    rw [show (PR ⊗ₖ (1 : Matrix d d ℂ))
        + (PL ⊗ₖ (1 : Matrix d d ℂ))
        = (PR + PL) ⊗ₖ (1 : Matrix d d ℂ) from by
      rw [Matrix.add_kronecker]]
    rw [show PR + PL = 1 from by rw [add_comm]; exact hsum]
    rw [Matrix.one_kronecker_one]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hπ2, hfHf, hffH]
    rw [show ((1 : Matrix d d ℂ) ⊗ₖ PR)
        + ((1 : Matrix d d ℂ) ⊗ₖ PL)
        = (1 : Matrix d d ℂ) ⊗ₖ (PR + PL) from by
      rw [Matrix.kronecker_add]]
    rw [show PR + PL = 1 from by rw [add_comm]; exact hsum]
    rw [Matrix.one_kronecker_one]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, hantiH]
    rw [show ((fᴴ * π) ⊗ₖ f) + (-(fᴴ * π)) ⊗ₖ f = 0 from by
      rw [← Matrix.add_kronecker, add_neg_cancel,
        Matrix.zero_kronecker]]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, hanti]
    rw [show ((f * π) ⊗ₖ f) + (-(f * π)) ⊗ₖ f = 0 from by
      rw [← Matrix.add_kronecker, add_neg_cancel,
        Matrix.zero_kronecker]]
  · rw [← Matrix.mul_kronecker_mul, hfH2, Matrix.one_mul,
      Matrix.zero_kronecker]
  · rw [← Matrix.mul_kronecker_mul, hπ2, hfH2,
      Matrix.kronecker_zero]

end NCG
