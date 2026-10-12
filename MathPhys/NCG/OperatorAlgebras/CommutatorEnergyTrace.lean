/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Commutator energy as a Frobenius trace

Split out of `MathPhys.Commutant.GrandInterface2` (Gran-Tensor manuscript,
`thm:SMST-commutant-audit`); pure finite-dimensional matrix algebra.

* `trace_conj_self_re`: `Re tr(Mᴴ M) = Σ |M_ij|²`;
* `trace_conj_self_re_eq_zero`: `Re tr(Mᴴ M) = 0 ↔ M = 0`;
* `commutant_audit`: the commutator energy `Σ_j ‖[c_j, X]‖²_F` vanishes exactly on
  the commutant, is blind to any commuting component (`[c_j, X] = [c_j, X - P]`),
  so a spectral-gap bound on `X - P` transfers to the rigidity estimate on `X`.
-/

open Matrix

namespace MathPhys

/-- Real part of `tr(Mᴴ M)` as a sum of entry norms. -/
lemma trace_conj_self_re {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) :
    ((Mᴴ * M).trace).re
      = ∑ j, ∑ i, Complex.normSq (M i j) := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm,
    Complex.mul_conj, Complex.ofReal_re]

/-- `tr(Mᴴ M).re = 0` iff `M = 0`. -/
lemma trace_conj_self_re_eq_zero {m n : Type*}
    [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    ((Mᴴ * M).trace).re = 0 ↔ M = 0 := by
  rw [trace_conj_self_re]
  constructor
  · intro h0
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ =>
        Complex.normSq_nonneg _).mp h0 j (Finset.mem_univ j)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Complex.normSq_nonneg _).mp hj i (Finset.mem_univ i)
    simpa using Complex.normSq_eq_zero.mp hi
  · intro h
    rw [h]
    simp

/-- `thm:SMST-commutant-audit`: the commutator energy vanishes
exactly on the commutant, is blind to any commuting component,
and the displayed spectral-gap bound transfers to the boxed
rigidity estimate. -/
theorem commutant_audit {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (X P : Matrix n n ℂ)
    (hP : ∀ j, c j * P = P * c j) :
    ((∑ j, (((c j * X - X * c j)ᴴ
        * (c j * X - X * c j)).trace).re) = 0
      ↔ ∀ j, c j * X = X * c j)
    ∧ (∀ j, c j * X - X * c j
        = c j * (X - P) - (X - P) * c j)
    ∧ (∀ lam : ℝ,
        lam * (((X - P)ᴴ * (X - P)).trace).re
          ≤ (∑ j, (((c j * (X - P) - (X - P) * c j)ᴴ
              * (c j * (X - P) - (X - P) * c j)).trace).re)
        → lam * (((X - P)ᴴ * (X - P)).trace).re
          ≤ (∑ j, (((c j * X - X * c j)ᴴ
              * (c j * X - X * c j)).trace).re)) := by
  have hblind : ∀ j, c j * X - X * c j
      = c j * (X - P) - (X - P) * c j := by
    intro j
    rw [Matrix.mul_sub, Matrix.sub_mul, hP j]
    abel
  refine ⟨?_, hblind, ?_⟩
  · constructor
    · intro h0 j
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        fun j _ => by
          rw [trace_conj_self_re]
          exact Finset.sum_nonneg fun a _ =>
            Finset.sum_nonneg fun b _ =>
              Complex.normSq_nonneg _).mp h0 j
        (Finset.mem_univ j)
      have := (trace_conj_self_re_eq_zero _).mp hterm
      have hsub := sub_eq_zero.mp this
      exact hsub
    · intro hcomm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [show c j * X - X * c j = 0 from by
        rw [hcomm j, sub_self]]
      simp
  · intro lam hgap
    refine le_trans hgap (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [← hblind j]

end MathPhys
