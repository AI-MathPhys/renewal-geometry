/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Capacity–affinity factorization of positive branch weights

Covers `thm:affinity-conductance` from `manuscripts/renewal_emergence/renewal_emergence.tex`: on a
bidirected edge set with reversal `e ↦ ē` and positive branch
capacities `q`, the symmetric capacity `c_e = √(q_e q_ē)` and the
antisymmetric affinity `A_q(e) = log(q_e / q_ē)` give the boxed
factorization

`q_e = c_e · exp(A_q(e)/2)`,

and this is the unique factorization of `q` into a symmetric positive
part and an antisymmetric exponent.
-/

namespace NCG.Upstream

variable {E : Type*} (bar : E → E) (q : E → ℝ)

/-- **Theorem `thm:affinity-conductance` (capacity)**: the symmetric
positive capacity `c_e = √(q_e q_ē)`. -/
noncomputable def capacity (e : E) : ℝ := Real.sqrt (q e * q (bar e))

/-- **Theorem `thm:affinity-conductance` (affinity)**: the
antisymmetric affinity `A_q(e) = log(q_e / q_ē)`. -/
noncomputable def edgeAffinity (e : E) : ℝ := Real.log (q e / q (bar e))

variable (hbar : ∀ e, bar (bar e) = e) (hq : ∀ e, 0 < q e)

include hbar in
/-- **`thm:affinity-conductance`**: the capacity is symmetric under
edge reversal. -/
theorem capacity_symm (e : E) :
    capacity bar q (bar e) = capacity bar q e := by
  unfold capacity
  rw [hbar, mul_comm]

include hbar in
/-- **`thm:affinity-conductance`**: the affinity is antisymmetric
under edge reversal. -/
theorem edgeAffinity_antisymm (e : E) :
    edgeAffinity bar q (bar e) = -(edgeAffinity bar q e) := by
  unfold edgeAffinity
  rw [hbar, ← Real.log_inv, inv_div]

include hq in
/-- **`thm:affinity-conductance`**: the capacity is strictly
positive. -/
theorem capacity_pos (e : E) : 0 < capacity bar q e :=
  Real.sqrt_pos.mpr (mul_pos (hq e) (hq (bar e)))

private theorem sqrt_eq_exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, mul_one_div]

include hq in
/-- **Theorem `thm:affinity-conductance` (boxed identity)**:
`q_e = c_e · exp(A_q(e)/2)`. -/
theorem capacity_factorization (e : E) :
    q e = capacity bar q e * Real.exp (edgeAffinity bar q e / 2) := by
  have hle := hq e
  have hlb := hq (bar e)
  unfold capacity edgeAffinity
  rw [sqrt_eq_exp_half_log (mul_pos hle hlb), ← Real.exp_add,
    Real.log_mul hle.ne' hlb.ne', Real.log_div hle.ne' hlb.ne',
    show (Real.log (q e) + Real.log (q (bar e))) / 2
        + (Real.log (q e) - Real.log (q (bar e))) / 2
      = Real.log (q e) from by ring,
    Real.exp_log hle]

include hbar hq in
/-- **Theorem `thm:affinity-conductance` (uniqueness)**: any
factorization `q_e = c_e · exp(A_e/2)` with `c` symmetric positive and
`A` antisymmetric coincides with the canonical capacity/affinity
pair. -/
theorem capacity_factorization_unique (c A : E → ℝ)
    (hcpos : ∀ e, 0 < c e) (hcsymm : ∀ e, c (bar e) = c e)
    (hAanti : ∀ e, A (bar e) = -(A e))
    (hfact : ∀ e, q e = c e * Real.exp (A e / 2)) :
    (∀ e, c e = capacity bar q e) ∧
      (∀ e, A e = edgeAffinity bar q e) := by
  have hc : ∀ e, c e = capacity bar q e := by
    intro e
    have h1 : q e * q (bar e) = c e * c e := by
      rw [hfact e, hfact (bar e), hcsymm e, hAanti e]
      calc c e * Real.exp (A e / 2) * (c e * Real.exp (-(A e) / 2))
          = c e * c e * Real.exp (A e / 2 + -(A e) / 2) := by
            rw [Real.exp_add]; ring
        _ = c e * c e := by
            rw [show A e / 2 + -(A e) / 2 = 0 from by ring,
              Real.exp_zero, mul_one]
    unfold capacity
    rw [h1, Real.sqrt_mul_self (hcpos e).le]
  refine ⟨hc, fun e => ?_⟩
  have h2 : Real.exp (A e / 2) = q e / c e := by
    rw [hfact e, mul_comm (c e), mul_div_assoc,
      div_self (hcpos e).ne', mul_one]
  have h3 : A e = 2 * Real.log (q e / c e) := by
    have h := congrArg Real.log h2
    rw [Real.log_exp] at h
    linarith
  have h4 : Real.log (capacity bar q e)
      = (Real.log (q e) + Real.log (q (bar e))) / 2 := by
    unfold capacity
    rw [sqrt_eq_exp_half_log (mul_pos (hq e) (hq (bar e))),
      Real.log_exp, Real.log_mul (hq e).ne' (hq (bar e)).ne']
  rw [h3, hc e]
  unfold edgeAffinity
  rw [Real.log_div (hq e).ne' (capacity_pos bar q hq e).ne',
    Real.log_div (hq e).ne' (hq (bar e)).ne', h4]
  ring

end NCG.Upstream
