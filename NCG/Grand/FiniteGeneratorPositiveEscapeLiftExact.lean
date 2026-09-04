/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCPathLikelihoodExact
import NCG.Grand.CanonicalFiniteRateFibreRefresh
import NCG.Grand.FiniteHeatBathDobrushin

/-!
# A positive-escape lift of every finite generator

Add an independent unit-rate two-state clock. Forgetting the clock preserves
the original dynamics, including absorbing states, while every lifted state
has positive escape rate. Clock-only flips carry zero jump reward. The
protected tilt therefore commutes with this construction exactly.
-/

open Matrix Finset
open scoped BigOperators

namespace NCG.FiniteGeneratorPositiveEscapeLift

open DrivenProcess DrivenProcess.FinitePath

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Add the independent unit-rate Boolean flip generator to a finite matrix. -/
def clockLift (A : Matrix S S ℝ) : Matrix (Bool × S) (Bool × S) ℝ :=
  fun x y => (if x.1 = y.1 then A x.2 y.2 else 0) +
    (if x.2 = y.2 then if x.1 = y.1 then -1 else 1 else 0)

/-- Functions on the physical state ignore the auxiliary clock. -/
def liftFunction (f : S → ℝ) : Bool × S → ℝ := fun x => f x.2

/-- Only visible changes of physical state receive jump rewards. -/
def liftJumpReward (g : S → S → ℝ) : (Bool × S) → (Bool × S) → ℝ :=
  fun x y => if x.2 = y.2 then 0 else g x.2 y.2

/-- The Boolean clock does not change the action on physical functions. -/
theorem clockLift_mulVec_liftFunction (A : Matrix S S ℝ) (f : S → ℝ) :
    (clockLift A).mulVec (liftFunction f) = liftFunction (A.mulVec f) := by
  ext ⟨b, i⟩
  cases b <;>
    simp [clockLift, liftFunction, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fintype.sum_bool, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq'] <;> ring

/-- Every finite generator lifts to a genuine finite generator. -/
theorem clockLift_isGenerator (L : Matrix S S ℝ) (hL : IsGenerator L) :
    IsGenerator (clockLift L) where
  offDiag_nonneg := by
    rintro ⟨b, i⟩ ⟨c, j⟩ hne
    by_cases hbc : b = c <;> by_cases hij : i = j
    · exact False.elim (hne (Prod.ext hbc hij))
    · simpa [clockLift, hbc, hij] using hL.offDiag_nonneg i j hij
    · simp [clockLift, hbc, hij]
    · simp [clockLift, hbc, hij]
  row_sum := by
    intro x
    have h := congrFun (clockLift_mulVec_liftFunction L (fun _ => 1)) x
    simpa [Matrix.mulVec, dotProduct, liftFunction, hL.row_sum] using h

/-- The clock adds exactly one to every physical escape rate. -/
theorem escapeRate_clockLift (L : Matrix S S ℝ) (hL : IsGenerator L) (x : Bool × S) :
    escapeRate (clockLift L) x = escapeRate L x.2 + 1 := by
  have hdiag := diagonal_eq_neg_escapeRate (clockLift_isGenerator L hL) x
  have hbase := diagonal_eq_neg_escapeRate hL x.2
  simp only [clockLift, ite_true] at hdiag
  linarith

/-- Strict positivity is automatic, even for absorbing and singleton generators. -/
theorem escapeRate_clockLift_pos (L : Matrix S S ℝ) (hL : IsGenerator L) (x : Bool × S) :
    0 < escapeRate (clockLift L) x := by
  rw [escapeRate_clockLift L hL x]
  have hnonneg : 0 ≤ escapeRate L x.2 := by
    apply Finset.sum_nonneg
    intro y hy
    exact hL.offDiag_nonneg x.2 y (Finset.ne_of_mem_erase hy).symm
  linarith

/-- Taking a protected state/jump tilt commutes exactly with the clock lift. -/
theorem tilt_clockLift (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    tilt (clockLift L) (liftFunction v) (liftJumpReward g) k = clockLift (tilt L v g k) := by
  ext ⟨b, i⟩ ⟨c, j⟩
  by_cases hbc : b = c <;> by_cases hij : i = j <;>
    simp [tilt, clockLift, liftFunction, liftJumpReward, Prod.mk.injEq, hbc, hij] <;> ring

/-- Deterministic record that forgets the auxiliary clock. -/
def physicalRecord : Matrix (Bool × S) S ℝ := fun x j => if x.2 = j then 1 else 0

theorem physicalRecord_mulVec (f : S → ℝ) :
    (physicalRecord (S := S)).mulVec f = liftFunction f := by
  ext x
  simp [physicalRecord, Matrix.mulVec, dotProduct, liftFunction]

/-- Exact rectangular generator intertwining for the physical record. -/
theorem clockLift_mul_physicalRecord (A : Matrix S S ℝ) :
    (clockLift A * physicalRecord (S := S) : Matrix (Bool × S) S ℝ) =
      (physicalRecord (S := S) * A : Matrix (Bool × S) S ℝ) := by
  ext ⟨b, i⟩ j
  cases b <;>
    simp [clockLift, physicalRecord, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq'] <;> ring

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open scoped Matrix.Norms.Operator in
/-- Forgetting the clock intertwines the exact matrix exponentials. -/
theorem exponentialEntry_clockLift_intertwines (A : Matrix S S ℝ) (t : ℝ) :
    (Matrix.of (Matrix.exponentialEntry (t • clockLift A)) *
      physicalRecord (S := S) : Matrix (Bool × S) S ℝ) =
      (physicalRecord (S := S) * Matrix.of (Matrix.exponentialEntry (t • A)) :
        Matrix (Bool × S) S ℝ) := by
  have h := CanonicalFiniteRateFibreRefresh.exp_intertwine_rect
    (clockLift A) A (physicalRecord (S := S)) (clockLift_mul_physicalRecord A) t
  have hLift : Matrix.of (Matrix.exponentialEntry (t • clockLift A)) = NormedSpace.exp (t • clockLift A) := by
    ext i j
    exact FiniteHeatBathDobrushin.exponentialEntry_eq_exp_apply _ i j
  have hBase : Matrix.of (Matrix.exponentialEntry (t • A)) = NormedSpace.exp (t • A) := by
    ext i j
    exact FiniteHeatBathDobrushin.exponentialEntry_eq_exp_apply _ i j
  simpa only [hLift, hBase] using h

/-- The lifted semigroup acts on physical terminal functions by the original semigroup. -/
theorem exponentialEntry_clockLift_mulVec (A : Matrix S S ℝ) (t : ℝ) (f : S → ℝ) :
    Matrix.mulVec (Matrix.exponentialEntry (t • clockLift A)) (liftFunction f) =
      liftFunction (Matrix.mulVec (Matrix.exponentialEntry (t • A)) f) := by
  calc
    Matrix.mulVec (Matrix.exponentialEntry (t • clockLift A)) (liftFunction f) =
        Matrix.mulVec (Matrix.of (Matrix.exponentialEntry (t • clockLift A)) *
          physicalRecord (S := S) : Matrix (Bool × S) S ℝ) f := by
      rw [← Matrix.mulVec_mulVec, physicalRecord_mulVec]
      rfl
    _ = Matrix.mulVec (physicalRecord (S := S) *
        Matrix.of (Matrix.exponentialEntry (t • A)) : Matrix (Bool × S) S ℝ) f := by
      rw [exponentialEntry_clockLift_intertwines]
    _ = liftFunction (Matrix.mulVec (Matrix.exponentialEntry (t • A)) f) := by
      rw [← Matrix.mulVec_mulVec, physicalRecord_mulVec]
      rfl

end

end NCG.FiniteGeneratorPositiveEscapeLift
