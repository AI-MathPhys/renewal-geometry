/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Dimension selection: access efficiency, complexity gap, isotropy blindness

Kinematic dimension-selection results of the manuscript's `3+1` chapter:

* **Access efficiency** (`def:access-efficiency`,
  `thm:access-efficiency-selection`): the functional `η(m) = m / 2^m` —
  isotropically accessible directions per primitive Clifford revision
  mode — satisfies `η(1) = η(2) = 1/2`, is strictly decreasing from `m = 2`
  on, and among spatially nondegenerate ranks `m ≥ 3` is uniquely maximised
  at `m = 3`.  Once spatial nondegeneracy excludes the one-axis endpoint,
  the efficiency functional selects the `3+1` endpoint.

* **Primitive complexity gap** (`lem:complexity-gap`): each step
  `m ↦ m + 2` through the odd ranks multiplies the primitive
  revision-algebra dimension `dim Cl_{m+1} = 2^{m+1}` by four.

* **Isotropy is dimension-blind** (`thm:isotropy-dimension-blind`): the
  cross-polytope frame `{±e₁, …, ±e_d}` with equal weights has second
  moment `(1/d)·I` in *every* dimension `d`, so isotropic self-averaging
  is available at every rank and cannot by itself select `d = 3`.  This is
  the no-go that makes the selection principles genuinely conditional.
-/

namespace NCG

/-! ### Access efficiency -/

/-- The **primitive access efficiency** `η(m) = m / 2^m`
(Definition `def:access-efficiency`): minimal isotropic access count `2m`
divided by the primitive revision cost `2^{m+1}`. -/
def accessEfficiency (m : ℕ) : ℚ :=
  (m : ℚ) / 2 ^ m

@[simp]
theorem accessEfficiency_one : accessEfficiency 1 = 1 / 2 := by
  norm_num [accessEfficiency]

@[simp]
theorem accessEfficiency_two : accessEfficiency 2 = 1 / 2 := by
  norm_num [accessEfficiency]

@[simp]
theorem accessEfficiency_three : accessEfficiency 3 = 3 / 8 := by
  norm_num [accessEfficiency]

/-- The unconstrained maximum of the efficiency is the spatially degenerate
one-axis endpoint: `η(3) < η(1)` (Remark `rem:efficiency-honest` (a)). -/
theorem accessEfficiency_three_lt_one :
    accessEfficiency 3 < accessEfficiency 1 := by
  norm_num [accessEfficiency]

/-- `η` is strictly decreasing from `m = 2` on:
`η(m+1) < η(m)` for `m ≥ 2` (Theorem `thm:access-efficiency-selection`
(i)). -/
theorem accessEfficiency_succ_lt {m : ℕ} (hm : 2 ≤ m) :
    accessEfficiency (m + 1) < accessEfficiency m := by
  have hp : (0 : ℚ) < 2 ^ m := by positivity
  have hp' : (0 : ℚ) < 2 ^ (m + 1) := by positivity
  rw [accessEfficiency, accessEfficiency, div_lt_div_iff₀ hp' hp]
  rw [pow_succ]
  have hnat : m + 1 < 2 * m := by omega
  have hq : (m : ℚ) + 1 < 2 * m := by exact_mod_cast hnat
  push_cast
  nlinarith [hp]

/-- Strict monotone comparison across the tail: `η(k) < η(m)` whenever
`2 ≤ m < k`. -/
theorem accessEfficiency_lt {m k : ℕ} (hm : 2 ≤ m) (hmk : m < k) :
    accessEfficiency k < accessEfficiency m := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmk with h | h
      · exact lt_trans (accessEfficiency_succ_lt (by omega)) (ih h)
      · subst h
        exact accessEfficiency_succ_lt hm

/-- **Theorem `thm:access-efficiency-selection`** (ii): among spatially
nondegenerate ranks `m ≥ 3`, the efficiency is maximised at `m = 3`. -/
theorem accessEfficiency_le_three {m : ℕ} (h3 : 3 ≤ m) :
    accessEfficiency m ≤ accessEfficiency 3 := by
  rcases eq_or_lt_of_le h3 with h | h
  · rw [← h]
  · exact (accessEfficiency_lt (by norm_num) h).le

/-- **Theorem `thm:access-efficiency-selection`** (iii): the maximiser is
unique — `η(m) = η(3)` forces `m = 3` among ranks `m ≥ 3`.  Higher odd
primitive endpoints (`d = 5, 7, …`) remain algebraically admissible
(`prop:primitive-all-odd`) but strictly less efficient. -/
theorem accessEfficiency_eq_three_iff {m : ℕ} (h3 : 3 ≤ m) :
    accessEfficiency m = accessEfficiency 3 ↔ m = 3 := by
  constructor
  · intro h
    by_contra hne
    have hlt : 3 < m := lt_of_le_of_ne h3 (Ne.symm hne)
    exact absurd h (ne_of_lt (accessEfficiency_lt (by norm_num) hlt))
  · intro h
    rw [h]

/-! ### The primitive complexity gap -/

/-- **Lemma `lem:complexity-gap`**: the primitive revision cost
`dim Cl_{m+1} = 2^{m+1}` quadruples with each step through the odd spatial
ranks: `2^{(m+2)+1} = 4 · 2^{m+1}`. -/
theorem revisionCost_step (m : ℕ) :
    2 ^ (m + 2 + 1) = 4 * 2 ^ (m + 1) := by
  rw [pow_add 2 (m + 1) 2]
  ring

/-! ### Isotropy is dimension-blind -/

open Matrix

/-- The standard-basis outer products sum to the identity:
`∑ᵢ eᵢ eᵢᵀ = I`. -/
theorem sum_outer_single (d : ℕ) :
    (∑ i : Fin d, vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i 1))
      = (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext j k
  simp only [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Matrix.one_apply]
  simp [Finset.sum_ite_eq]

/-- **Theorem `thm:isotropy-dimension-blind`**: the cross-polytope reset
frame `{±e₁, …, ±e_d}` with equal weights `1/(2d)` has second moment
`(1/d)·I` in every dimension `d ≥ 1`.  Isotropic self-averaging is
therefore available at every spatial rank: it cannot imply interference
closure, and cannot by itself select `d = 3` among the odd primitive
endpoints. -/
theorem crossPolytope_second_moment {d : ℕ} (hd : 0 < d) :
    ((∑ i : Fin d, (2 * (d : ℝ))⁻¹
        • vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i 1))
      + ∑ i : Fin d, (2 * (d : ℝ))⁻¹
        • vecMulVec (-Pi.single i (1 : ℝ)) (-Pi.single i 1))
      = ((d : ℝ))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hneg : ∀ i : Fin d,
      vecMulVec (-Pi.single i (1 : ℝ)) (-Pi.single i 1)
        = vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i 1) := by
    intro i
    ext j k
    simp [vecMulVec_apply]
  simp_rw [hneg]
  rw [← Finset.smul_sum, sum_outer_single, ← add_smul]
  congr 1
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  field_simp
  ring

end NCG
