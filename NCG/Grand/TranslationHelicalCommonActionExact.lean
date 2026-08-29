/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NSTranslationHelical
import NCG.Grand.CanonicalInteriorBoundaryMinimum

/-!
# Translation--helical common-action handoff, exact singular form

This module removes the two interfaces left in `NSTranslationHelical`:

* the translation short uses the genuine Moore--Penrose projection, so the
  translation bank need not have full column rank;
* the surviving helical source is decomposed by the canonical attained
  minimum for `A = L + DᴴD`, including its exact Pythagoras identity.

The closed obstruction is the intersection of the selected screen `Q` with
the kernel of `A`.  Commutation with the support projection is precisely the
finite reducing-screen condition used in the manuscript.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option maxHeartbeats 800000

namespace NCG
namespace TranslationHelicalCommonActionExact

open GeometricThresholdBank SourceCoercivityInfluence PsdBlockSchur
open CanonicalInteriorBoundaryMinimum

variable {n tr hel b : Type*}
  [Fintype n] [Fintype tr] [Fintype hel] [Fintype b]
  [DecidableEq n] [DecidableEq tr] [DecidableEq hel] [DecidableEq b]

/-- Orthogonal projection onto the range of the translation source. -/
noncomputable def translationProjection (D : Matrix n tr ℂ) : Matrix n n ℂ :=
  D * pinv (Matrix.posSemidef_conjTranspose_mul_self D).1 * Dᴴ

/-- Helical innovation after shorting the translation range. -/
noncomputable def helicalResidual (D : Matrix n tr ℂ) (Dh : Matrix n hel ℂ) :
    Matrix n hel ℂ :=
  (1 - translationProjection D) * Dh

theorem translationProjection_isHermitian (D : Matrix n tr ℂ) :
    (translationProjection D).IsHermitian := by
  unfold translationProjection
  exact Matrix.isHermitian_mul_mul_conjTranspose D
    (pinv_isHermitian (Matrix.posSemidef_conjTranspose_mul_self D).1)

theorem translationProjection_idempotent (D : Matrix n tr ℂ) :
    translationProjection D * translationProjection D = translationProjection D := by
  let A := Dᴴ * D
  let G := pinv (Matrix.posSemidef_conjTranspose_mul_self D).1
  have hGAG : G * A * G = G :=
    pinv_mul_self_mul_pinv (Matrix.posSemidef_conjTranspose_mul_self D).1
  change (D * G * Dᴴ) * (D * G * Dᴴ) = D * G * Dᴴ
  calc
    (D * G * Dᴴ) * (D * G * Dᴴ) = D * (G * A * G) * Dᴴ := by
      simp only [A, Matrix.mul_assoc]
    _ = D * G * Dᴴ := by rw [hGAG]

theorem helicalResidual_gram_zero_iff
    (D : Matrix n tr ℂ) (Dh : Matrix n hel ℂ) :
    Dhᴴ * (1 - translationProjection D) * Dh = 0 ↔
      helicalResidual D Dh = 0 := by
  let P := translationProjection D
  have hPH : Pᴴ = P := (translationProjection_isHermitian D).eq
  have hP2 : P * P = P := translationProjection_idempotent D
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hP2]
    abel
  have hfactor : Dhᴴ * (1 - P) * Dh =
      ((1 - P) * Dh)ᴴ * ((1 - P) * Dh) := by
    rw [Matrix.conjTranspose_mul, hQH]
    simp only [Matrix.mul_assoc]
    symm
    rw [← Matrix.mul_assoc (1 - P) (1 - P) Dh, hQ2]
  rw [hfactor, Matrix.conjTranspose_mul_self_eq_zero]
  rfl

/-- Closed obstruction inside the selected screen. -/
noncomputable def closedObstruction
    (L : Matrix n n ℂ) (Dz : Matrix b n ℂ) (hL : L.PosSemidef)
    (Q : Matrix n n ℂ) : Matrix n n ℂ :=
  Q * (1 - supportProj (action_posSemidef L Dz hL).1)

/-- Surviving helical source after removing the closed obstruction. -/
noncomputable def survivingSource
    (Dtr : Matrix n tr ℂ) (Dh : Matrix n hel ℂ)
    (L : Matrix n n ℂ) (Dz : Matrix b n ℂ) (hL : L.PosSemidef)
    (Q : Matrix n n ℂ) : Matrix n hel ℂ :=
  (Q - closedObstruction L Dz hL Q) * helicalResidual Dtr Dh

theorem closedObstruction_isHermitian_idempotent
    (L : Matrix n n ℂ) (Dz : Matrix b n ℂ) (hL : L.PosSemidef)
    (Q : Matrix n n ℂ) (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q)
    (hcomm : Q * supportProj (action_posSemidef L Dz hL).1 =
      supportProj (action_posSemidef L Dz hL).1 * Q) :
    (closedObstruction L Dz hL Q)ᴴ = closedObstruction L Dz hL Q ∧
      closedObstruction L Dz hL Q * closedObstruction L Dz hL Q =
        closedObstruction L Dz hL Q := by
  let P := supportProj (action_posSemidef L Dz hL).1
  have hPH : Pᴴ = P := (supportProj_posSemidef
    (action_posSemidef L Dz hL).1).1.eq
  have hP2 : P * P = P := supportProj_idem
    (action_posSemidef L Dz hL).1
  have hQcomm : Q * (1 - P) = (1 - P) * Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hcomm]
  have h1P2 : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hP2]
    abel
  constructor
  · unfold closedObstruction
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPH, hQH, hQcomm]
  · unfold closedObstruction
    change (Q * (1 - P)) * (Q * (1 - P)) = Q * (1 - P)
    calc
      (Q * (1 - P)) * (Q * (1 - P))
          = Q * (((1 - P) * Q) * (1 - P)) := by
              simp only [Matrix.mul_assoc]
      _ = Q * ((Q * (1 - P)) * (1 - P)) := by rw [← hQcomm]
      _ = (Q * Q) * ((1 - P) * (1 - P)) := by
              simp only [Matrix.mul_assoc]
      _ = Q * (1 - P) := by rw [hQ2, h1P2]

/-- Pure matrix algebra behind support of the surviving source.  Factoring
this lemma keeps the spectral proof opaque during the final assembly. -/
theorem supported_after_closed_obstruction
    (A G P Q : Matrix n n ℂ) (R : Matrix n hel ℂ)
    (hAG : A * G = P) (hP2 : P * P = P)
    (hcomm : Q * P = P * Q) :
    A * G * ((Q - Q * (1 - P)) * R) =
      (Q - Q * (1 - P)) * R := by
  have hshort : Q - Q * (1 - P) = P * Q := by
    simp only [Matrix.mul_sub, Matrix.mul_one]
    rw [hcomm]
    abel
  rw [hAG, hshort]
  simp only [← Matrix.mul_assoc, hP2]

/-- **`thm:NS-translation-helical-handoff`, exact finite singular form.**
The theorem includes exact translation routing, the closed obstruction,
positive Moore--Penrose cost, and the attained canonical decomposition with
Pythagoras for every competing interior--boundary pair. -/
theorem translation_helical_common_action_exact
    (Dtr : Matrix n tr ℂ) (Dh : Matrix n hel ℂ)
    (L : Matrix n n ℂ) (Dz : Matrix b n ℂ) (hL : L.PosSemidef)
    (Q : Matrix n n ℂ) (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q)
    (hcomm : Q * supportProj (action_posSemidef L Dz hL).1 =
      supportProj (action_posSemidef L Dz hL).1 * Q) :
    (Dhᴴ * (1 - translationProjection Dtr) * Dh = 0 ↔
      helicalResidual Dtr Dh = 0) ∧
    ((helicalResidual Dtr Dh)ᴴ *
      (closedObstruction L Dz hL Q * Q) * helicalResidual Dtr Dh).PosSemidef ∧
    let S := survivingSource Dtr Dh L Dz hL Q
    (Sᴴ * pinv (action_posSemidef L Dz hL).1 * S).PosSemidef ∧
    (∀ c : hel → ℂ,
      let s := S *ᵥ c
      (synthesis L Dz)ᴴ *ᵥ minimizer L Dz hL s = s ∧
      star (minimizer L Dz hL s) ⬝ᵥ minimizer L Dz hL s =
        star c ⬝ᵥ ((Sᴴ * pinv (action_posSemidef L Dz hL).1 * S) *ᵥ c) ∧
      ∀ y : (n ⊕ b) → ℂ, (synthesis L Dz)ᴴ *ᵥ y = s →
        star y ⬝ᵥ y =
          star (minimizer L Dz hL s) ⬝ᵥ minimizer L Dz hL s +
          star (y - minimizer L Dz hL s) ⬝ᵥ
            (y - minimizer L Dz hL s)) := by
  let P := supportProj (action_posSemidef L Dz hL).1
  let P0 := closedObstruction L Dz hL Q
  let R := helicalResidual Dtr Dh
  have hP0 := closedObstruction_isHermitian_idempotent
    L Dz hL Q hQH hQ2 hcomm
  have hP0psd : P0.PosSemidef := by
    rw [show P0 = P0ᴴ * P0 by rw [hP0.1, hP0.2]]
    exact Matrix.posSemidef_conjTranspose_mul_self P0
  have hQcomm : Q * (1 - P) = (1 - P) * Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hcomm]
  have hP0Q : P0 * Q = P0 := by
    change (Q * (1 - P)) * Q = Q * (1 - P)
    calc
      (Q * (1 - P)) * Q = Q * ((1 - P) * Q) := Matrix.mul_assoc _ _ _
      _ = Q * (Q * (1 - P)) := by rw [← hQcomm]
      _ = (Q * Q) * (1 - P) := (Matrix.mul_assoc _ _ _).symm
      _ = Q * (1 - P) := by rw [hQ2]
  have hObs : (Rᴴ * (P0 * Q) * R).PosSemidef := by
    rw [hP0Q]
    exact hP0psd.conjTranspose_mul_mul_same R
  let S := survivingSource Dtr Dh L Dz hL Q
  have hCost : (Sᴴ * pinv (action_posSemidef L Dz hL).1 * S).PosSemidef :=
    (pinv_posSemidef (action_posSemidef L Dz hL).1).conjTranspose_mul_mul_same S
  refine ⟨helicalResidual_gram_zero_iff Dtr Dh, hObs, hCost, ?_⟩
  intro c
  dsimp only
  let s := S *ᵥ c
  have hS : action L Dz * pinv (action_posSemidef L Dz hL).1 * S = S :=
    by
      change action L Dz * pinv (action_posSemidef L Dz hL).1 *
          ((Q - Q * (1 - supportProj (action_posSemidef L Dz hL).1)) *
            helicalResidual Dtr Dh) =
        (Q - Q * (1 - supportProj (action_posSemidef L Dz hL).1)) *
          helicalResidual Dtr Dh
      exact supported_after_closed_obstruction
        (action L Dz) (pinv (action_posSemidef L Dz hL).1)
        (supportProj (action_posSemidef L Dz hL).1) Q
        (helicalResidual Dtr Dh)
        (mul_pinv_eq_supportProj (action_posSemidef L Dz hL).1)
        (supportProj_idem (action_posSemidef L Dz hL).1) hcomm
  have hs : action L Dz *ᵥ
      (pinv (action_posSemidef L Dz hL).1 *ᵥ s) = s := by
    change action L Dz *ᵥ
      (pinv (action_posSemidef L Dz hL).1 *ᵥ (S *ᵥ c)) = S *ᵥ c
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hS]
  obtain ⟨hfeas, henergy, hpyth⟩ :=
    canonical_interior_boundary_minimum L Dz hL s hs
  refine ⟨hfeas, ?_, hpyth⟩
  rw [henergy]
  change star (S *ᵥ c) ⬝ᵥ
      (pinv (action_posSemidef L Dz hL).1 *ᵥ (S *ᵥ c)) =
    star c ⬝ᵥ
      ((Sᴴ * pinv (action_posSemidef L Dz hL).1 * S) *ᵥ c)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end TranslationHelicalCommonActionExact
end NCG
