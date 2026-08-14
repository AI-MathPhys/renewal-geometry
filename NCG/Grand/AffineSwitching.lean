/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Neutral pair–switching incidence compiler
  (`thm:affine-switching-incidence`,
  Gran-Tensor manuscript)

* `affine_switching_incidence`: the boxed AFF.1 — with
  `P_sw = S(S*S)⁻¹S*` the switching-history projection
  (hermitian idempotent), the parity-given-switching
  innovation `𝕀_{par|sw} = N*(1-P_sw)N` is positive
  semidefinite, and it vanishes exactly when
  `(1-P_sw)N = 0`, i.e. exactly when the complete neutral
  pair synthesis lies in the switching source range — the
  zero-innovation branch on which alone the characteristic
  switching connection may control the neutral pair
  source.

* `affine_parity_line_scalar`: after compression to one
  final parity line, every quadratic action is a scalar
  multiple of the squared endpoint — a quadratic form on a
  one-dimensional carrier has the form `q(x) = q(1)x²` —
  so it supplies no new parity mechanism.

The rank of the innovation counting the minimum missing
switching/occurrence source dimension, and the
identification of `S_sw` with the actual divisor, Vaughan,
or switching-history synthesis, are the manuscript's
arithmetic layer.  The full-rank normal matrix renders the
pseudoinverse of the degenerate bank.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false in
/-- `thm:affine-switching-incidence` (AFF.1). -/
theorem affine_switching_incidence {n m k : Type}
    [Fintype n] [Fintype m] [Fintype k] [DecidableEq n]
    [DecidableEq m]
    (S : Matrix n m ℂ) (Np : Matrix n k ℂ)
    [Invertible (Sᴴ * S)] :
    -- the boxed positive innovation
    (Npᴴ * (1 - S * ((Sᴴ * S)⁻¹ * Sᴴ)) * Np).PosSemidef
    -- vanishing exactly on the zero-innovation branch
    ∧ (Npᴴ * (1 - S * ((Sᴴ * S)⁻¹ * Sᴴ)) * Np = 0
        ↔ (1 - S * ((Sᴴ * S)⁻¹ * Sᴴ)) * Np = 0) := by
  set P := S * ((Sᴴ * S)⁻¹ * Sᴴ) with hP
  have hSSH : (Sᴴ * S)ᴴ = Sᴴ * S := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hSSinvH : ((Sᴴ * S)⁻¹)ᴴ = (Sᴴ * S)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hSSH]
  have hPH : Pᴴ = P := by
    rw [hP, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hSSinvH,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hPP : P * P = P := by
    rw [hP]
    calc S * ((Sᴴ * S)⁻¹ * Sᴴ)
          * (S * ((Sᴴ * S)⁻¹ * Sᴴ))
        = S * ((Sᴴ * S)⁻¹ * ((Sᴴ * S)
            * ((Sᴴ * S)⁻¹ * Sᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = S * ((Sᴴ * S)⁻¹ * Sᴴ) := by
          rw [Matrix.mul_inv_cancel_left_of_invertible]
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  have hidem : (1 - P) * ((1 - P) * Np) = (1 - P) * Np := by
    rw [← Matrix.mul_assoc, h1P]
  have hfact : Npᴴ * (1 - P) * Np
      = ((1 - P) * Np)ᴴ * ((1 - P) * Np) := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPH,
      Matrix.mul_assoc Npᴴ (1 - P) Np, ← hidem,
      ← Matrix.mul_assoc, hidem]
  constructor
  · rw [hfact]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [hfact]
    exact Matrix.conjTranspose_mul_self_eq_zero

/-- One-line parity compression: a quadratic action on a
one-dimensional carrier is a scalar multiple of the
squared endpoint. -/
theorem affine_parity_line_scalar (q : ℝ → ℝ)
    (hq : ∀ c x : ℝ, q (c * x) = c ^ 2 * q x) :
    ∀ x : ℝ, q x = q 1 * x ^ 2 := by
  intro x
  have h := hq x 1
  rw [mul_one] at h
  rw [h]
  ring

end NCG
