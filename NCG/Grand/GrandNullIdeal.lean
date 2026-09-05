/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The contextual null ideal and record-sink nullity
  (`lem:contextual-null-ideal`, `thm:record-sink-nullity`,
   Gran-Tensor manuscript)

* `contextual_null_ideal`: the set of contextually null
  coefficients — those whose every two-sided word insertion has
  vanishing future-Gram expectation `tr(G·x a y) = 0` — is
  closed under addition, scalars, two-sided multiplication, and
  the involution (for a Hermitian future Gram): a two-sided
  `*`-ideal;
* `record_sink_nullity`: with the sink decomposition
  `P + Q = 1`, a future map killing the transient sector
  (`CQ = 0`) factors through the record-forgetting compression
  (`C = CP`), kills the transient inclusion (`CJ = 0` for
  `QJ = J`), and has the boxed vanishing leakage Gram
  `𝔾_rec = J*C*CJ = 0`.

Rendering disclosed: the null set is rendered on the
future-Gram contextual functionals; the free word-algebra
quotient framing and the cutoff compatibility of the transient
ideals are the manuscript's remaining bookkeeping.
-/

open Matrix

namespace NCG

/-- `lem:contextual-null-ideal`: contextual nullity is a
two-sided `*`-ideal. -/
theorem contextual_null_ideal {n : Type*} [Fintype n]
    (G : Matrix n n ℂ) (hG : Gᴴ = G) :
    (∀ a b : Matrix n n ℂ,
      (∀ x y, (G * (x * a * y)).trace = 0) →
      (∀ x y, (G * (x * b * y)).trace = 0) →
      ∀ x y, (G * (x * (a + b) * y)).trace = 0)
    ∧ (∀ (c : ℂ) (a : Matrix n n ℂ),
      (∀ x y, (G * (x * a * y)).trace = 0) →
      ∀ x y, (G * (x * (c • a) * y)).trace = 0)
    ∧ (∀ (a z : Matrix n n ℂ),
      (∀ x y, (G * (x * a * y)).trace = 0) →
      (∀ x y, (G * (x * (z * a) * y)).trace = 0)
      ∧ (∀ x y, (G * (x * (a * z) * y)).trace = 0))
    ∧ (∀ a : Matrix n n ℂ,
      (∀ x y, (G * (x * a * y)).trace = 0) →
      ∀ x y, (G * (x * aᴴ * y)).trace = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b ha hb x y
    rw [show x * (a + b) * y = x * a * y + x * b * y from by
      rw [Matrix.mul_add, Matrix.add_mul]]
    rw [Matrix.mul_add, Matrix.trace_add, ha x y, hb x y,
      add_zero]
  · intro c a ha x y
    rw [show x * (c • a) * y = c • (x * a * y) from by
      rw [Matrix.mul_smul, Matrix.smul_mul]]
    rw [Matrix.mul_smul, Matrix.trace_smul, ha x y, smul_zero]
  · intro a z ha
    constructor
    · intro x y
      rw [show x * (z * a) * y = (x * z) * a * y from by
        simp only [Matrix.mul_assoc]]
      exact ha (x * z) y
    · intro x y
      rw [show x * (a * z) * y = x * a * (z * y) from by
        simp only [Matrix.mul_assoc]]
      exact ha x (z * y)
  · intro a ha x y
    have h2 := ha yᴴ xᴴ
    have h3 : (G * (x * aᴴ * y)).trace
        = star ((G * (yᴴ * a * xᴴ)).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
        hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_conjTranspose,
        Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [h3, h2, star_zero]

/-- `thm:record-sink-nullity`: a transient-killing future map
factors through the record-forgetting compression and has zero
leakage Gram. -/
theorem record_sink_nullity {t h e : Type*} [Fintype t]
    [DecidableEq t] [Fintype h]
    (C : Matrix h t ℂ) (P Q : Matrix t t ℂ) (J : Matrix t e ℂ)
    (hPQ : P + Q = 1) (hCQ : C * Q = 0) (hQJ : Q * J = J) :
    (C = C * P)
    ∧ (C * J = 0)
    ∧ (Jᴴ * (Cᴴ * C) * J = 0) := by
  have hfact : C = C * P := by
    calc C = C * (1 : Matrix t t ℂ) := (Matrix.mul_one C).symm
      _ = C * (P + Q) := by rw [hPQ]
      _ = C * P + C * Q := by rw [Matrix.mul_add]
      _ = C * P := by rw [hCQ, add_zero]
  have hCJ : C * J = 0 := by
    calc C * J = C * (Q * J) := by rw [hQJ]
      _ = (C * Q) * J := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hCQ, Matrix.zero_mul]
  refine ⟨hfact, hCJ, ?_⟩
  rw [show Jᴴ * (Cᴴ * C) * J = (C * J)ᴴ * (C * J) from by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]]
  rw [hCJ, Matrix.conjTranspose_zero, Matrix.zero_mul]

end NCG
