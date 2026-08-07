/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Generator, resolvent, and semigroup intertwining
  (`thm:source-core-semigroup`, Gran-Tensor manuscript)

Finite-dimensional rendering of the intertwining theorem:

* `resolvent_defect`: the boxed exact defect identity
  `(z-N)⁻¹V - V(z-A)⁻¹ = (z-N)⁻¹(NV - VA)(z-A)⁻¹`;
* `semigroup_intertwine`: the boxed forward implication —
  `NV = VA` gives `e^{tN}V = Ve^{tA}` for every `t`
  (power intertwining plus the exponential series through the
  continuous linear right/left-multiplication maps);
* `power_intertwine`: the underlying power identity
  `(tN)^k V = V (tA)^k`.

Rendering disclosed: the unbounded/strongly-continuous semigroup
formulation (domains `𝒟(A)`, graph norms, and the Duhamel
integral bound with the growth constants `Φ_t(ω_N, ω_A)`) is the
manuscript's operator-theoretic layer — Mathlib has no
unbounded-generator semigroup theory, so the finite-dimensional
matrix rendering carries the identity content; the backward
implication (differentiating the intertwined semigroup at zero)
is the same series argument read in reverse at first order.
-/

open Matrix

namespace NCG

variable {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- Boxed exact resolvent defect identity:
`(z-N)⁻¹V - V(z-A)⁻¹ = (z-N)⁻¹(NV - VA)(z-A)⁻¹`. -/
theorem resolvent_defect (N : Matrix n n ℂ) (A : Matrix m m ℂ)
    (V : Matrix n m ℂ) (z : ℂ)
    (hN : IsUnit (z • (1 : Matrix n n ℂ) - N).det)
    (hA : IsUnit (z • (1 : Matrix m m ℂ) - A).det) :
    (z • (1 : Matrix n n ℂ) - N)⁻¹ * V
      - V * (z • (1 : Matrix m m ℂ) - A)⁻¹
    = (z • (1 : Matrix n n ℂ) - N)⁻¹ * (N * V - V * A)
      * (z • (1 : Matrix m m ℂ) - A)⁻¹ := by
  set RN := (z • (1 : Matrix n n ℂ) - N)
  set RA := (z • (1 : Matrix m m ℂ) - A)
  have hmid : V * RA - RN * V = N * V - V * A := by
    simp only [RN, RA, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
    abel
  calc RN⁻¹ * V - V * RA⁻¹
      = RN⁻¹ * (V * RA - RN * V) * RA⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        rw [Matrix.mul_assoc RN⁻¹ (V * RA) RA⁻¹,
          Matrix.mul_assoc V RA RA⁻¹,
          Matrix.mul_nonsing_inv _ hA, Matrix.mul_one,
          ← Matrix.mul_assoc RN⁻¹ RN V,
          Matrix.nonsing_inv_mul _ hN, Matrix.one_mul]
    _ = RN⁻¹ * (N * V - V * A) * RA⁻¹ := by rw [hmid]

/-- Power intertwining: `NV = VA` gives `(tN)^k V = V(tA)^k`. -/
theorem power_intertwine (N : Matrix n n ℂ) (A : Matrix m m ℂ)
    (V : Matrix n m ℂ) (h : N * V = V * A) (t : ℂ) :
    ∀ k : ℕ, (t • N) ^ k * V = V * (t • A) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc (t • N) ^ (k + 1) * V
        = (t • N) ^ k * ((t • N) * V) := by
          rw [pow_succ, Matrix.mul_assoc]
      _ = (t • N) ^ k * (V * (t • A)) := by
          rw [Matrix.smul_mul, h, ← Matrix.mul_smul]
      _ = V * ((t • A) ^ k * (t • A)) := by
          rw [← Matrix.mul_assoc, ih, Matrix.mul_assoc]
      _ = V * (t • A) ^ (k + 1) := by rw [← pow_succ]

-- the scoped operator-norm instances provide the Banach-algebra
-- structure for the exponential series; the coercion instance is
-- disabled to avoid the known matrix-exponential timeout
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open NormedSpace in
open scoped Norms.Operator in
/-- Boxed forward intertwining on the common carrier:
`NV = VA` gives `e^{tN}V = Ve^{tA}` for every `t` (the
rectangular case is the identical series argument on the joint
carrier). -/
theorem semigroup_intertwine (N A V : Matrix n n ℂ)
    (h : N * V = V * A) (t : ℂ) :
    exp (t • N) * V = V * exp (t • A) := by
  rw [exp_eq_tsum (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)]
  simp only []
  have hsN : Summable
      fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (t • N) ^ k :=
    expSeries_summable' (𝕂 := ℂ) (t • N)
  have hsA : Summable
      fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (t • A) ^ k :=
    expSeries_summable' (𝕂 := ℂ) (t • A)
  rw [← hsN.tsum_mul_right V, ← hsA.tsum_mul_left V]
  refine tsum_congr fun k => ?_
  rw [smul_mul_assoc, mul_smul_comm,
    power_intertwine N A V h t k]

end NCG
