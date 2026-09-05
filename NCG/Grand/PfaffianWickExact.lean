/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteGrassmannWickExteriorExact
import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite Majorana Pfaffian Wick theorem

The combinatorial core of `thm:SMQG-Pfaffian-Wick`.  A Pfaffian is defined by
its signed first-row recursion.  A finite Majorana Gaussian is characterized
by the same Wick recursion, vacuum normalization, skew covariance, and odd
moment vanishing.  Strong induction proves that every even moment is the
Pfaffian of its two-point word matrix.

The final theorem keeps the manuscript's polarization firewall explicit: a
physically supplied conversion of an even-word kernel to an exterior compound
is an input.  Only after that input does positive-semidefinite one-particle
data imply positivity of the represented word kernel.
-/

open Matrix Finset
open scoped Matrix

noncomputable section

namespace NCG
namespace PfaffianWick

/-- Signed first-row Pfaffian recursion for a finite ordered word.  The sign
is fixed by the list order, which is the formal Berezin-order convention. -/
def pfaffian {V : Type*} (B : V → V → ℂ) : List V → ℂ
  | [] => 1
  | x :: xs =>
      ∑ j : Fin xs.length,
        (-1 : ℂ) ^ j.1 * B x (xs.get j) * pfaffian B (xs.eraseIdx j.1)
termination_by xs => xs.length
decreasing_by
  have hle : (xs.eraseIdx j.1).length ≤ xs.length :=
    le_trans (Nat.le_succ _) (List.length_eraseIdx_add_one j.isLt).le
  exact lt_of_le_of_lt hle (Nat.lt_succ_self _)

@[simp] theorem pfaffian_nil {V : Type*} (B : V → V → ℂ) :
    pfaffian B [] = 1 := by
  rw [pfaffian]

theorem pfaffian_cons {V : Type*} (B : V → V → ℂ) (x : V) (xs : List V) :
    pfaffian B (x :: xs) =
      ∑ j : Fin xs.length,
        (-1 : ℂ) ^ j.1 * B x (xs.get j) * pfaffian B (xs.eraseIdx j.1) := by
  rw [pfaffian]

/-- A normalized finite Majorana Gaussian specified by its exact Wick
recursion.  `odd` records the parity symmetry that kills odd words. -/
structure MajoranaGaussian (V : Type*) where
  covariance : V → V → ℂ
  covariance_skew : ∀ v w, covariance v w = -covariance w v
  moment : List V → ℂ
  vacuum : moment [] = 1
  wick_even : ∀ (x : V) (xs : List V), Even (x :: xs).length →
    moment (x :: xs) =
      ∑ j : Fin xs.length,
        (-1 : ℂ) ^ j.1 * covariance x (xs.get j) *
          moment (xs.eraseIdx j.1)
  odd : ∀ xs : List V, Odd xs.length → moment xs = 0

/-- The ordered word matrix whose Pfaffian appears in the Majorana Wick
formula. -/
def wordMatrix {V : Type*} (B : V → V → ℂ) {n : ℕ}
    (v : Fin n → V) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => B (v i) (v j)

/-- Pfaffian of the covariance word matrix, with the order supplied by
`Fin n`. -/
def wordPfaffian {V : Type*} (B : V → V → ℂ) {n : ℕ}
    (v : Fin n → V) : ℂ :=
  pfaffian B (List.ofFn v)

/-- Uniqueness of the even Wick recursion: every normalized Majorana Gaussian
moment is the signed recursive Pfaffian. -/
theorem moment_eq_pfaffian_of_even {V : Type*} (G : MajoranaGaussian V)
    (xs : List V) (heven : Even xs.length) :
    G.moment xs = pfaffian G.covariance xs := by
  cases xs with
  | nil =>
      simp [G.vacuum]
  | cons x tail =>
      rw [G.wick_even x tail heven, pfaffian_cons]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply moment_eq_pfaffian_of_even G
      rw [List.length_eraseIdx_of_lt j.isLt]
      rcases heven with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      simp only [List.length_cons] at hk
      omega
termination_by xs.length
decreasing_by
  subst xs
  have hle : (tail.eraseIdx j.1).length ≤ tail.length :=
    le_trans (Nat.le_succ _) (List.length_eraseIdx_add_one j.isLt).le
  exact lt_of_le_of_lt hle (Nat.lt_succ_self _)

/-- **Pfaffian Wick formula (QG.65).** -/
theorem even_majorana_moment_eq_wordPfaffian {V : Type*}
    (G : MajoranaGaussian V) (r : ℕ) (v : Fin (2 * r) → V) :
    G.moment (List.ofFn v) = wordPfaffian G.covariance v := by
  apply moment_eq_pfaffian_of_even G
  simpa using even_two_mul r

/-- Odd Majorana moments vanish. -/
theorem odd_majorana_moment_eq_zero {V : Type*}
    (G : MajoranaGaussian V) (r : ℕ) (v : Fin (2 * r + 1) → V) :
    G.moment (List.ofFn v) = 0 := by
  apply G.odd
  simpa using odd_two_mul_add_one r

open scoped ComplexOrder in
/-- A physically supplied compatible complex polarization identifies an
even-word kernel with a congruence of the corresponding exterior compound.
Positive one-particle covariance then makes that represented word kernel
positive semidefinite. -/
theorem polarized_evenWordKernel_posSemidef
    {d r : ℕ} {W : Type*} [Finite W]
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosSemidef)
    (U : Matrix (FiniteCompoundMatrixExteriorPower.GradeIdx (2 * r) d) W ℂ)
    (K : Matrix W W ℂ)
    (hpolarization :
      K = Uᴴ * FiniteCompoundMatrixExteriorPower.cmpd (2 * r) P * U) :
    K.PosSemidef := by
  rw [hpolarization]
  exact (FiniteCompoundMatrixExteriorPower.cmpd_posSemidef hP).conjTranspose_mul_mul_same U

/-- Consolidated exact certificate for `thm:SMQG-Pfaffian-Wick`: all even
moments are Pfaffians, all odd moments vanish, and every physically polarized
even-word kernel inherits exterior positivity. -/
theorem pfaffian_Wick_theorem {V : Type*} (G : MajoranaGaussian V) :
    (∀ (r : ℕ) (v : Fin (2 * r) → V),
      G.moment (List.ofFn v) = wordPfaffian G.covariance v) ∧
    (∀ (r : ℕ) (v : Fin (2 * r + 1) → V),
      G.moment (List.ofFn v) = 0) :=
  ⟨even_majorana_moment_eq_wordPfaffian G,
    odd_majorana_moment_eq_zero G⟩

end PfaffianWick
end NCG
