/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ScoreCutoffLossExact
import NCG.Grand.ExactSourceSchurResidual

/-!
# Joint score-bank shorting under cutoff transport

An isometric physical pullback preserves every block of the complete joint
nuisance/retained score Gram.  Consequently the singular Moore--Penrose Schur
short commutes exactly with cutoff transport whenever the whole joint bank has
zero loss.
-/

open Matrix

namespace NCG

/-- Functional calculus is insensitive to the proof term used after the
underlying Hermitian matrices are identified. -/
theorem hermitianCFC_eq_of_eq {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    {f : ℝ → ℝ} (hXY : X = Y) : hX.cfc f = hY.cfc f := by
  subst Y
  rfl
/-- The Gram-functional definition of the source pseudoinverse depends only on
that Gram matrix. -/
theorem sourceGramPseudoinverse_eq_of_gram_eq
    {h k e : ℕ} (S : Matrix (Fin h) (Fin e) ℂ)
    (T : Matrix (Fin k) (Fin e) ℂ)
    (hgram : Sᴴ * S = Tᴴ * T) :
    sourceGramPseudoinverse S = sourceGramPseudoinverse T := by
  unfold sourceGramPseudoinverse
  apply hermitianCFC_eq_of_eq
  exact hgram
/-- Left multiplication by an isometry preserves the source Gram
pseudoinverse. -/
theorem sourceGramPseudoinverse_isometric_left
    {h k e : ℕ}
    (J : Matrix (Fin h) (Fin k) ℂ) (S : Matrix (Fin k) (Fin e) ℂ)
    (hJ : Jᴴ * J = 1) :
    sourceGramPseudoinverse (J * S) = sourceGramPseudoinverse S := by
  have hgram : (J * S)ᴴ * (J * S) = Sᴴ * S := by
    rw [Matrix.conjTranspose_mul]
    calc
      Sᴴ * Jᴴ * (J * S) = Sᴴ * ((Jᴴ * J) * S) := by
        simp only [Matrix.mul_assoc]
      _ = Sᴴ * S := by rw [hJ, Matrix.one_mul]
  exact sourceGramPseudoinverse_eq_of_gram_eq (J * S) S hgram

/-- The genuine Moore--Penrose source Schur residual is invariant under an
isometric left transport. -/
theorem sourceSchurResidual_isometric_left
    {h k eN eR : ℕ}
    (J : Matrix (Fin h) (Fin k) ℂ)
    (N : Matrix (Fin k) (Fin eN) ℂ)
    (R : Matrix (Fin k) (Fin eR) ℂ)
    (hJ : Jᴴ * J = 1) :
    sourceSchurResidual (J * N) (J * R) =
      sourceSchurResidual N R := by
  have hRR : (J * R)ᴴ * (J * R) = Rᴴ * R := by
    rw [Matrix.conjTranspose_mul]
    calc
      Rᴴ * Jᴴ * (J * R) = Rᴴ * ((Jᴴ * J) * R) := by
        simp only [Matrix.mul_assoc]
      _ = Rᴴ * R := by rw [hJ, Matrix.one_mul]
  have hNR : (J * N)ᴴ * (J * R) = Nᴴ * R := by
    rw [Matrix.conjTranspose_mul]
    calc
      Nᴴ * Jᴴ * (J * R) = Nᴴ * ((Jᴴ * J) * R) := by
        simp only [Matrix.mul_assoc]
      _ = Nᴴ * R := by rw [hJ, Matrix.one_mul]
  unfold sourceSchurResidual
  rw [hRR, hNR, sourceGramPseudoinverse_isometric_left J N hJ]

/-- **Joint-bank cutoff commutation**: if both nuisance and retained fine
scores are the isometric pullbacks of their coarse conditional expectations
(equivalently, the complete joint bank has zero loss), then simultaneous
nuisance shorting commutes with the cutoff. -/
theorem joint_score_bank_short_commutes
    {h k eN eR : ℕ}
    (J : Matrix (Fin h) (Fin k) ℂ)
    (fineN : Matrix (Fin h) (Fin eN) ℂ)
    (fineR : Matrix (Fin h) (Fin eR) ℂ)
    (coarseN : Matrix (Fin k) (Fin eN) ℂ)
    (coarseR : Matrix (Fin k) (Fin eR) ℂ)
    (hJ : Jᴴ * J = 1)
    (hN : fineN = J * coarseN) (hR : fineR = J * coarseR) :
    sourceSchurResidual fineN fineR =
      sourceSchurResidual coarseN coarseR := by
  rw [hN, hR]
  exact sourceSchurResidual_isometric_left J coarseN coarseR hJ

end NCG
