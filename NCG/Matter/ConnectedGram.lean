/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Connected-Gram commutant rigidity and the commutative trap
(SM_emergence, Phase 2)

* `commute_diagonal_offdiag_zero`, `diag_commute_connected_constant`,
  `simple_spectrum_connected_commutant` —
  `thm:simple-spectrum-connected-gram-main`: if `H_u` has simple
  spectrum and the support graph of `H_d` (in the `H_u` eigenbasis)
  is connected, then `{H_u, H_d}' = ℂ·I`: anything commuting with a
  simple-spectrum diagonal is diagonal, and commuting with a
  connected off-diagonal pattern forces the diagonal to be constant
  along edges, hence constant.  This is the mechanism behind
  `cor:finite-incidence-commutant-main`;
* `diagonal_commute` — `thm:v4-commutative-trap-current` (core): any
  two operators diagonal in the same character basis commute, so a
  strictly democratic `V₄`-equivariant inventory gives
  `[Y_uY_u†, Y_dY_d†] = 0` and cannot produce CKM mixing or CP.
-/

namespace NCG

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Commuting with a simple-spectrum diagonal forces off-diagonal
entries to vanish. -/
theorem commute_diagonal_offdiag_zero (d : n → ℂ)
    (hd : Function.Injective d) (X : Matrix n n ℂ)
    (hX : X * Matrix.diagonal d = Matrix.diagonal d * X)
    {i j : n} (hij : i ≠ j) : X i j = 0 := by
  have h := congrFun (congrFun hX i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hne : d j ≠ d i := fun hEq => hij (hd hEq).symm
  have h2 : X i j * (d j - d i) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3) hne

/-- A diagonal commuting with a connected support pattern is
constant along the connectivity relation. -/
theorem diag_commute_connected_constant (x : n → ℂ)
    (Hd : Matrix n n ℂ)
    (hcomm : Matrix.diagonal x * Hd = Hd * Matrix.diagonal x)
    {i j : n}
    (hconn : Relation.ReflTransGen
      (fun a b => Hd a b ≠ 0 ∨ Hd b a ≠ 0) i j) :
    x i = x j := by
  have hkey : ∀ p q : n, Hd p q ≠ 0 → x p = x q := by
    intro p q hpq
    have h := congrFun (congrFun hcomm p) q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    have h2 : Hd p q * (x p - x q) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hpq
    · exact sub_eq_zero.mp h3
  induction hconn with
  | refl => rfl
  | tail _ hedge ih =>
    rename_i b c _
    rcases hedge with h | h
    · rw [ih]
      exact hkey b c h
    · rw [ih]
      exact (hkey c b h).symm

/-- `thm:simple-spectrum-connected-gram-main`: if `H_u = diag d` has
simple spectrum and the nonzero support graph of `H_d` is connected,
then any `X` commuting with both is a scalar,
`{H_u, H_d}' = ℂ·I`. -/
theorem simple_spectrum_connected_commutant [Nonempty n]
    (d : n → ℂ) (hd : Function.Injective d) (Hd : Matrix n n ℂ)
    (hconn : ∀ i j : n, Relation.ReflTransGen
      (fun a b => Hd a b ≠ 0 ∨ Hd b a ≠ 0) i j)
    (X : Matrix n n ℂ)
    (hXu : X * Matrix.diagonal d = Matrix.diagonal d * X)
    (hXd : X * Hd = Hd * X) :
    X = X (Classical.arbitrary n) (Classical.arbitrary n) • 1 := by
  set i0 := Classical.arbitrary n with hi0
  have hdiag : X = Matrix.diagonal (fun i => X i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact commute_diagonal_offdiag_zero d hd X hXu hij
  have hXd' : Matrix.diagonal (fun i => X i i) * Hd
      = Hd * Matrix.diagonal (fun i => X i i) := by
    rw [← hdiag]
    exact hXd
  have hconst : ∀ i, X i i = X i0 i0 := by
    intro i
    exact diag_commute_connected_constant (fun i => X i i) Hd hXd'
      (hconn i i0)
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact hconst i
  · rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul,
      mul_zero]
    exact commute_diagonal_offdiag_zero d hd X hXu hij

/-- `thm:v4-commutative-trap-current` (core): operators diagonal in
the same character basis commute — a strictly democratic
`V₄`-equivariant inventory is commutative,
`[Y_uY_u†, Y_dY_d†] = 0`, and cannot produce nontrivial CKM mixing
or physical quark CP. -/
theorem diagonal_commute (u v : n → ℂ) :
    Matrix.diagonal u * Matrix.diagonal v
      = Matrix.diagonal v * Matrix.diagonal u := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end NCG
