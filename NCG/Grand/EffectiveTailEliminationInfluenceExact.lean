/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTEffectiveShort
import NCG.Grand.TargetShortInfluenceExact
import NCG.Grand.GRHRestoringShortExact

/-!
# Exact influence preservation under positive tail elimination

This file completes the singular Moore--Penrose part of
`thm:GT-effective-action`.  For a positive block action

`L = [[A, B], [Bᴴ, C]] ⪰ 0`,  `C ≻ 0`,

the effective head action is the Schur complement
`S = A - B C⁻¹ Bᴴ ⪰ 0`.  If a head source `E` is supported on the range of
`S`, then its zero-extended source `Ê = (E,0)` is supported on the range of
`L`, and the Moore--Penrose quadratic influence is preserved exactly:

`Êᴴ L† Ê = Eᴴ S† E`.

Together with `NCG.gt_effective_action` and
`NCG.modulated_renewal_schur_mori`, this gives the kernel graph, completion
of the square, variational elimination, and exact singular influence claim
of the manuscript theorem.
-/

open Matrix NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace EffectiveTailEliminationInfluence

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {P Q K : Type} [Fintype P] [Fintype Q] [Fintype K]
  [DecidableEq P] [DecidableEq Q]

/-- The Schur effective action obtained by eliminating the tail block. -/
noncomputable abbrev effectiveAction (A : Matrix P P ℂ) (B : Matrix P Q ℂ)
    (C : Matrix Q Q ℂ) : Matrix P P ℂ :=
  A - B * C⁻¹ * Bᴴ

/-- A source supported on the head block, extended by zero to the full
head--tail space. -/
abbrev embeddedHeadSource (E : Matrix P K ℂ) : Matrix (P ⊕ Q) K ℂ :=
  Matrix.fromRows E 0

/-- Positivity of the full block action and positive definiteness of the
eliminated tail imply positivity of the effective action. -/
theorem effectiveAction_posSemidef {A : Matrix P P ℂ} {B : Matrix P Q ℂ}
    {C : Matrix Q Q ℂ} (hL : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (hC : C.PosDef) : (effectiveAction A B C).PosSemidef := by
  have hS := TargetShortInfluence.protectedShort_posSemidef hL
  unfold TargetShortInfluence.protectedShort at hS
  have hp : pinv (TargetShortInfluence.left_posSemidef hL).1 = C⁻¹ := by
    exact (Matrix.inv_eq_left_inv (GRHRestoringShort.pinv_mul_self hC)).symm
  rw [hp] at hS
  exact hS

/-- The exact Moore--Penrose influence identity after eliminating a positive
tail.  The range hypothesis is written as the canonical projector equation
`S S† E = E`, which is equivalent to `Ran E ⊆ Ran S` in finite dimensions. -/
theorem embedded_pinv_influence_eq {A : Matrix P P ℂ} {B : Matrix P Q ℂ}
    {C : Matrix Q Q ℂ} (hL : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (hC : C.PosDef) (E : Matrix P K ℂ)
    (hE : effectiveAction A B C
      * pinv (effectiveAction_posSemidef hL hC).1 * E = E) :
    (embeddedHeadSource (Q := Q) E)ᴴ
        * (pinv hL.1 * embeddedHeadSource (Q := Q) E)
      = Eᴴ * (pinv (effectiveAction_posSemidef hL hC).1 * E) := by
  letI := hC.isUnit.invertible
  let L : Matrix (P ⊕ Q) (P ⊕ Q) ℂ := Matrix.fromBlocks A B Bᴴ C
  let S : Matrix P P ℂ := effectiveAction A B C
  have hS : S.PosSemidef := effectiveAction_posSemidef hL hC
  let X : Matrix P K ℂ := pinv hS.1 * E
  let Y : Matrix Q K ℂ := -(C⁻¹ * (Bᴴ * X))
  let Z : Matrix (P ⊕ Q) K ℂ := Matrix.fromRows X Y
  let Ehat : Matrix (P ⊕ Q) K ℂ := embeddedHeadSource (Q := Q) E

  have hLX : L * Z = Ehat := by
    dsimp only [L, Z, Ehat, embeddedHeadSource]
    rw [Matrix.fromBlocks_mul_fromRows]
    congr 1
    · change A * X + B * Y = E
      dsimp only [Y]
      rw [Matrix.mul_neg, ← sub_eq_add_neg]
      change A * X - B * (C⁻¹ * (Bᴴ * X)) = E
      calc
        A * X - B * (C⁻¹ * (Bᴴ * X))
            = S * X := by
                simp only [S, effectiveAction, Matrix.sub_mul, Matrix.mul_assoc]
        _ = E := by
          change effectiveAction A B C
              * (pinv (effectiveAction_posSemidef hL hC).1 * E) = E
          simpa only [Matrix.mul_assoc] using hE
    · change Bᴴ * X + C * Y = 0
      dsimp only [Y]
      rw [Matrix.mul_neg, ← Matrix.mul_assoc C C⁻¹,
        Matrix.mul_inv_of_invertible, Matrix.one_mul]
      abel

  have hPL : supportProj hL.1 * L = L := by
    have h := congrArg Matrix.conjTranspose (mul_supportProj hL)
    simpa only [L, Matrix.conjTranspose_mul, hL.1.eq,
      (supportProj_posSemidef hL.1).1.eq] using h

  let W : Matrix (P ⊕ Q) K ℂ := pinv hL.1 * Ehat
  have hLW : L * W = Ehat := by
    calc
      L * W = supportProj hL.1 * Ehat := by
        dsimp only [W]
        rw [← Matrix.mul_assoc, mul_pinv_eq_supportProj]
      _ = supportProj hL.1 * (L * Z) := by rw [hLX]
      _ = Ehat := by rw [← Matrix.mul_assoc, hPL, hLX]

  have horth : Ehatᴴ * (W - Z) = 0 := by
    rw [← hLX, Matrix.conjTranspose_mul, hL.1.eq,
      Matrix.mul_assoc, Matrix.mul_sub, hLW, hLX, sub_self,
      Matrix.mul_zero]

  have hEW : Ehatᴴ * W = Ehatᴴ * Z := by
    rw [Matrix.mul_sub] at horth
    exact sub_eq_zero.mp horth

  calc
    (embeddedHeadSource (Q := Q) E)ᴴ
          * (pinv hL.1 * embeddedHeadSource (Q := Q) E)
        = Ehatᴴ * W := by rfl
    _ = Ehatᴴ * Z := hEW
    _ = Eᴴ * (pinv hS.1 * E) := by
      dsimp only [Ehat, Z, embeddedHeadSource]
      rw [
        Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
        Matrix.fromCols_mul_fromRows]
      simp [X]
    _ = Eᴴ * (pinv (effectiveAction_posSemidef hL hC).1 * E) := by
      rfl

/-- Bundled form of `thm:GT-effective-action`: the effective action is PSD,
the homogeneous kernel is the compensation graph, and every range-supported
head source has exactly the same pseudoinverse influence before and after
tail elimination. -/
theorem effective_action_full {A : Matrix P P ℂ} {B : Matrix P Q ℂ}
    {C : Matrix Q Q ℂ} (hL : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (hC : C.PosDef) :
    (effectiveAction A B C).PosSemidef
      ∧ (∀ (X : Matrix P K ℂ) (Y : Matrix Q K ℂ),
          (A * X + B * Y = 0 ∧ Bᴴ * X + C * Y = 0)
            ↔ (effectiveAction A B C * X = 0
              ∧ Y = -(C⁻¹ * (Bᴴ * X))))
      ∧ (∀ E : Matrix P K ℂ,
          effectiveAction A B C
              * pinv (effectiveAction_posSemidef hL hC).1 * E = E →
          (embeddedHeadSource (Q := Q) E)ᴴ
              * (pinv hL.1 * embeddedHeadSource (Q := Q) E)
            = Eᴴ * (pinv (effectiveAction_posSemidef hL hC).1 * E)) := by
  letI := hC.isUnit.invertible
  refine ⟨effectiveAction_posSemidef hL hC, ?_, ?_⟩
  · exact (gt_effective_action (m := K) A B C).1
  · intro E hE
    exact embedded_pinv_influence_eq hL hC E hE

end EffectiveTailEliminationInfluence
end NCG
