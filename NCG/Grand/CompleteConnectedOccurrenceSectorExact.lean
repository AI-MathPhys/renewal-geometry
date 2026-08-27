/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTHoeffdingShort
import NCG.Grand.GTSourceVariance

/-!
# Exact product-connected and occurrence sectors

This instantiates the abstract connected projection with the actual Hoeffding
all-support tensor power and proves the orthogonal Gram split asserted by
`thm:GT-complete-connected-sector`.
-/

open Matrix Finset

namespace NCG

/-- The tensor power of a Hermitian matrix is Hermitian. -/
theorem tensorPow_conjTranspose {n : Type} [Fintype n]
    (t : ℕ) (Q : Matrix n n ℂ) (hQ : Qᴴ = Q) :
    (tensorPow t (fun _ => Q))ᴴ = tensorPow t (fun _ => Q) := by
  ext x y
  simp only [Matrix.conjTranspose_apply, tensorPow, Matrix.of_apply]
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hentry := congrFun (congrFun hQ (x i)) (y i)
  simpa [Matrix.conjTranspose_apply] using hentry

/-- `thm:GT-complete-connected-sector`, with `Q^{tensor t}` instantiated by
the exact Hoeffding all-support projector. -/
theorem complete_connected_occurrence_sector_exact
    {n a e : Type} [Fintype n] [Fintype a]
    [DecidableEq n] [DecidableEq a]
    (t : ℕ) (P Q : Matrix n n ℂ)
    (hPQ1 : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hPP : P * P = P) (hQQ : Q * Q = Q) (hQH : Qᴴ = Q)
    (U : Matrix a (Fin t → n) ℂ) (hU : Uᴴ * U = 1)
    (Z : Matrix a e ℂ) :
    let Qtop := tensorPow t (fun _ => Q)
    let Pconn := U * Qtop * Uᴴ
    let Pocc := (1 : Matrix a a ℂ) - U * Uᴴ
    let Cfull := Pconn + Pocc
    Cfullᴴ = Cfull
      ∧ Cfull * Cfull = Cfull
      ∧ Pconn * Pocc = 0
      ∧ Pocc * Pconn = 0
      ∧ Zᴴ * Cfull * Z = Zᴴ * Pconn * Z + Zᴴ * Pocc * Z
      ∧ (∀ S : Finset (Fin t), S ≠ univ →
        Cfull * (U * tensorPow t (fun i => if i ∈ S then Q else P) * Uᴴ) = 0) := by
  dsimp only
  let Qtop : Matrix (Fin t → n) (Fin t → n) ℂ := tensorPow t (fun _ => Q)
  have hQtopH : Qtopᴴ = Qtop := tensorPow_conjTranspose t Q hQH
  have hhoe := gt_hoeffding_short t P Q hPQ1 hPQ hQP hPP hQQ
  have hQtop2 : Qtop * Qtop = Qtop := by
    dsimp [Qtop]
    rw [tensorPow_mul]
    congr 1
    funext i
    exact hQQ
  have hbase := gt_complete_connected_sector U Qtop 0 hU hQtopH hQtop2
  have hcan : ∀ {b : Type} [Fintype b] (X : Matrix (Fin t → n) b ℂ),
      Uᴴ * (U * X) = X := by
    intro b _ X
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  refine ⟨hbase.1, hbase.2.1, ?_, ?_, ?_, ?_⟩
  · calc
      (U * Qtop * Uᴴ) * (1 - U * Uᴴ)
          = U * Qtop * (Uᴴ - Uᴴ * (U * Uᴴ)) := by
              simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by
          rw [hcan Uᴴ, sub_self]
          simp
  · calc
      (1 - U * Uᴴ) * (U * Qtop * Uᴴ)
          = U * Qtop * Uᴴ - U * (Uᴴ * (U * (Qtop * Uᴴ))) := by
              simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hcan (Qtop * Uᴴ)]; simp only [Matrix.mul_assoc, sub_self]
  · simp only [Matrix.mul_add, Matrix.add_mul]
  · intro S hS
    have hPiOrth : Qtop * tensorPow t (fun i => if i ∈ S then Q else P) = 0 := by
      simpa [Qtop] using hhoe.2.2.1 univ S hS.symm
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hcan]
    rw [← Matrix.mul_assoc Qtop
      (tensorPow t (fun i => if i ∈ S then Q else P)) Uᴴ, hPiOrth,
      Matrix.zero_mul, Matrix.mul_zero]
    abel

end NCG
