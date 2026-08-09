/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ArFiniteEuler
import NCG.Grand.PeanoStability

/-!
# Exact EASY 78: matrix-level finite Euler consequences

The previous finite-Euler theorem proved the Möbius identity on the cyclic
anchor.  Because every arithmetic history is a commuting linear combination
of Peano multiplication operators and every endpoint basis vector is obtained
from that anchor, the column identity upgrades to the full two-sided matrix
inverse.
-/

open Matrix

namespace NCG

/-- Every finite arithmetic-history linear combination commutes with every
Peano multiplication history. -/
theorem arithmeticHistory_commutes_peano {X : ℕ} (b : ℕ) (hb : 1 ≤ b)
    (f : ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 X, f a • peanoL X a) * peanoL X b =
      peanoL X b * (∑ a ∈ Finset.Icc 1 X, f a • peanoL X a) := by
  rw [Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  rw [Matrix.smul_mul, Matrix.mul_smul,
    peano_product a b ha1 hb, peano_product b a hb ha1,
    Nat.mul_comm]

/-- The zeta incidence history commutes with every Peano multiplication
history. -/
theorem zetaX_commutes_peano {X : ℕ} (b : ℕ) (hb : 1 ≤ b) :
    zetaX X * peanoL X b = peanoL X b * zetaX X := by
  rw [(zeta_incidence (X := X)).1, Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [peano_product (a + 1) b (by omega) hb,
    peano_product b (a + 1) hb (by omega), Nat.mul_comm]

/-- Equality on the cyclic Peano anchor upgrades to equality of any two
operators commuting with every multiplication history. -/
theorem eq_of_peano_anchor_of_commutes {X : ℕ} (hX : 0 < X)
    (A B : Matrix (Fin X) (Fin X) ℂ)
    (hA : ∀ b : ℕ, 1 ≤ b → A * peanoL X b = peanoL X b * A)
    (hB : ∀ b : ℕ, 1 ≤ b → B * peanoL X b = peanoL X b * B)
    (hanchor : A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
      B *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) :
    A = B := by
  ext j i
  let b : ℕ := (i : ℕ) + 1
  have hb : 1 ≤ b := by omega
  have hbi : b - 1 = (i : ℕ) := by simp [b]
  have hcol : peanoL X b *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
      Pi.single i 1 := by
    funext k
    rw [mulVec_single_col, peanoL, Matrix.of_apply, Pi.single_apply]
    have hbval : b = (i : ℕ) + 1 := rfl
    rw [show (((⟨0, hX⟩ : Fin X) : ℕ) + 1) = 1 from rfl,
      mul_one, hbval]
    by_cases hki : k = i
    · subst k
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hki (Fin.ext (by omega))), if_neg hki]
  have hv : A *ᵥ Pi.single i 1 = B *ᵥ Pi.single i 1 := by
    rw [← hcol, Matrix.mulVec_mulVec, hA b hb,
      ← Matrix.mulVec_mulVec, hanchor, Matrix.mulVec_mulVec,
      ← hB b hb, ← Matrix.mulVec_mulVec]
  have hj := congrFun hv j
  simpa only [mulVec_single_col] using hj

/-- The Möbius history is the full two-sided matrix inverse of the zeta
incidence history, not merely an inverse on the anchor column. -/
theorem finite_moebius_matrix_inverse {X : ℕ} (hX : 0 < X) :
    let M : Matrix (Fin X) (Fin X) ℂ :=
      ∑ a ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.moebius a : ℤ) : ℂ) • peanoL X a
    M * zetaX X = 1 ∧ zetaX X * M = 1 := by
  dsimp only
  let M : Matrix (Fin X) (Fin X) ℂ :=
    ∑ a ∈ Finset.Icc 1 X,
      ((ArithmeticFunction.moebius a : ℤ) : ℂ) • peanoL X a
  have hanchor0 := (ar_finite_euler hX).2.2.2
  have hanchor : (M * zetaX X) *ᵥ
      Pi.single (⟨0, hX⟩ : Fin X) 1 =
      (1 : Matrix (Fin X) (Fin X) ℂ) *ᵥ
        Pi.single (⟨0, hX⟩ : Fin X) 1 := by
    rw [← Matrix.mulVec_mulVec]
    simpa only [M, Matrix.one_mulVec] using hanchor0
  have hM : ∀ b : ℕ, 1 ≤ b →
      M * peanoL X b = peanoL X b * M := by
    intro b hb
    exact arithmeticHistory_commutes_peano b hb
      (fun a => ((ArithmeticFunction.moebius a : ℤ) : ℂ))
  have hZ : ∀ b : ℕ, 1 ≤ b →
      zetaX X * peanoL X b = peanoL X b * zetaX X :=
    fun b hb => zetaX_commutes_peano b hb
  have hMZ : ∀ b : ℕ, 1 ≤ b →
      (M * zetaX X) * peanoL X b = peanoL X b * (M * zetaX X) := by
    intro b hb
    calc
      (M * zetaX X) * peanoL X b
          = M * (zetaX X * peanoL X b) := by simp only [Matrix.mul_assoc]
      _ = M * (peanoL X b * zetaX X) := by rw [hZ b hb]
      _ = (M * peanoL X b) * zetaX X := by simp only [Matrix.mul_assoc]
      _ = (peanoL X b * M) * zetaX X := by rw [hM b hb]
      _ = peanoL X b * (M * zetaX X) := by simp only [Matrix.mul_assoc]
  have hright : M * zetaX X = 1 :=
    eq_of_peano_anchor_of_commutes hX (M * zetaX X) 1 hMZ
      (fun b hb => by simp) hanchor
  have hcomm : M * zetaX X = zetaX X * M := by
    calc
      M * zetaX X
          = (∑ a ∈ Finset.Icc 1 X,
              ((ArithmeticFunction.moebius a : ℤ) : ℂ) • peanoL X a) *
              zetaX X := rfl
      _ = zetaX X *
          (∑ a ∈ Finset.Icc 1 X,
            ((ArithmeticFunction.moebius a : ℤ) : ℂ) • peanoL X a) := by
          rw [Matrix.sum_mul, Matrix.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [Matrix.smul_mul, Matrix.mul_smul]
          rw [hZ a (Finset.mem_Icc.mp ha).1]
      _ = zetaX X * M := rfl
  exact ⟨hright, hcomm ▸ hright⟩

/-- The count commutator with each multiplication history has the exact
logarithmic weight. -/
theorem countLog_peano_commutator {X : ℕ} (n : ℕ) (hn : 2 ≤ n) :
    countLog X * peanoL X n - peanoL X n * countLog X =
      ((Real.log n : ℝ) : ℂ) • peanoL X n := by
  ext j i
  simp only [Matrix.sub_apply, Matrix.smul_apply,
    countLog, diagFn, peanoL, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.of_apply, smul_eq_mul]
  by_cases hcond : (j : ℕ) + 1 = n * ((i : ℕ) + 1)
  · rw [if_pos hcond]
    have hj : (((j : ℕ) : ℝ) + 1) =
        (n : ℝ) * (((i : ℕ) : ℝ) + 1) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) hcond
    have hlog : Real.log (((j : ℕ) : ℝ) + 1) =
        Real.log n + Real.log (((i : ℕ) : ℝ) + 1) := by
      rw [hj, Real.log_mul (by positivity) (by positivity)]
    push_cast [hlog]
    ring
  · rw [if_neg hcond]
    ring

/-- Full matrix form of the von Mangoldt commutator identity. -/
theorem finite_vonMangoldt_matrix_commutator {X : ℕ} :
    countLog X * logZop X - logZop X * countLog X =
      ∑ n ∈ Finset.Icc 2 X,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) • peanoL X n := by
  rw [logZop, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
    countLog_peano_commutator n hn2, smul_smul]
  congr 1
  have hlog0 : Real.log n ≠ 0 := by
    have h1 : (1 : ℝ) < n := by exact_mod_cast hn2
    exact (Real.log_pos h1).ne'
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

end NCG
