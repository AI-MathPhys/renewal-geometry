/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFeynmanKacCompilerExact

/-!
# Feynman--Kac uniqueness on physical nonnegative time

The physical path moment is only required to solve its backward equation on
`[0, infinity)`, with the right derivative at zero. No differentiability or
artificial extension of the stochastic process to negative time is assumed.
-/

open Matrix Set
open scoped Matrix.Norms.Operator

namespace NCG.NonnegativeTimeFeynmanKac

open FiniteFeynmanKacBackwardEquation FiniteCTMCFeynmanKacCompiler
open DrivenProcess DrivenProcess.FinitePath

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Matrix flow uniqueness with derivatives only on the physical half-line. -/
theorem eq_exp_mul_initial_of_hasDerivWithinAt_nonnegative
    (X Y0 : Matrix S S ℝ) (Y : ℝ → Matrix S S ℝ)
    (hY : ∀ t, 0 ≤ t → HasDerivWithinAt Y (X * Y t) (Ici 0) t)
    (h0 : Y 0 = Y0) (t : ℝ) (ht : 0 ≤ t) :
    Y t = NormedSpace.exp (t • X) * Y0 := by
  let Z := fun s : ℝ => NormedSpace.exp ((-s) • X) * Y s
  have hE : ∀ u : ℝ,
      HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s) • X))
        (-(NormedSpace.exp ((-u) • X) * X)) u := by
    intro u
    have h := (hasDerivAt_exp_smul_const X (-u)).scomp u (hasDerivAt_neg' (x := u))
    rw [neg_one_smul] at h
    exact h
  have hZ : ∀ u, 0 ≤ u → HasDerivWithinAt Z 0 (Ici 0) u := by
    intro u hu
    have h := (hE u).hasDerivWithinAt.mul (hY u hu)
    have heq : -(NormedSpace.exp ((-u) • X) * X) * Y u +
        NormedSpace.exp ((-u) • X) * (X * Y u) = 0 := by
      rw [Matrix.neg_mul, Matrix.mul_assoc]
      exact neg_add_cancel _
    exact h.congr_deriv heq
  have hZD : DifferentiableOn ℝ Z (Ici 0) := fun u hu => (hZ u hu).differentiableWithinAt
  have hZzero : ∀ u ∈ Ici (0 : ℝ), fderivWithin ℝ Z (Ici 0) u = 0 := by
    intro u hu
    simpa using (hZ u hu).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Ici 0 u hu)
  have hconst : Z t = Z 0 := (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero
    hZD hZzero ht (Set.self_mem_Ici : (0 : ℝ) ∈ Ici 0)
  change NormedSpace.exp ((-t) • X) * Y t = NormedSpace.exp ((-0) • X) * Y 0 at hconst
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, h0] at hconst
  have hinv : NormedSpace.exp (t • X) * NormedSpace.exp ((-t) • X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _
      (((Commute.refl X).smul_left t).smul_right (-t)),
      ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  calc
    Y t = 1 * Y t := (Matrix.one_mul _).symm
    _ = (NormedSpace.exp (t • X) * NormedSpace.exp ((-t) • X)) * Y t := by rw [hinv]
    _ = NormedSpace.exp (t • X) * Y0 := by rw [Matrix.mul_assoc, hconst]

/-- The finite backward equation determines the matrix-exponential solution
on nonnegative time, requiring only a right derivative at the origin. -/
theorem eq_exponentialEntry_mulVec_of_backwardEquation_nonnegative
    [Nonempty S] (B : Matrix S S ℝ) (f : S → ℝ) (F : ℝ → S → ℝ)
    (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (B.mulVec (F t)) (Ici 0) t)
    (h0 : F 0 = f) (t : ℝ) (ht : 0 ≤ t) :
    F t = Matrix.mulVec (Matrix.exponentialEntry (t • B)) f := by
  let j0 : S := Classical.choice inferInstance
  let Y := fun u => singleColumn j0 (F u)
  have hY : ∀ u, 0 ≤ u → HasDerivWithinAt Y (B * Y u) (Ici 0) u := by
    intro u hu
    have h := (singleColumnCLM j0).hasFDerivAt.comp_hasDerivWithinAt u (hF u hu)
    change HasDerivWithinAt (fun s => singleColumn j0 (F s))
      (singleColumn j0 (B.mulVec (F u))) (Ici 0) u at h
    change HasDerivWithinAt (fun s => singleColumn j0 (F s))
      (B * singleColumn j0 (F u)) (Ici 0) u
    rw [mul_singleColumn]
    exact h
  have hY0 : Y 0 = singleColumn j0 f := by simp only [Y, h0]
  have hmatrix := eq_exp_mul_initial_of_hasDerivWithinAt_nonnegative
    B (singleColumn j0 f) Y hY hY0 t ht
  have hexponential : Matrix.exponentialEntry (t • B) = NormedSpace.exp (t • B) := by
    ext i j
    exact FiniteHeatBathDobrushin.exponentialEntry_eq_exp_apply (t • B) i j
  rw [hexponential]
  rw [mul_singleColumn] at hmatrix
  funext i
  have hi := congrFun (congrFun hmatrix i) j0
  simpa [Y, singleColumn] using hi

/-- Correctly scoped compiler for the actual finite-CTMC path expectation. -/
theorem eq_exponentialEntry_mulVec_of_firstJumpConditioning_nonnegative
    [Nonempty S] (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hescape : ∀ x, 0 < escapeRate L x) (f : S → ℝ) (F : ℝ → S → ℝ)
    (hF : ∀ t, 0 ≤ t →
      HasDerivWithinAt F (firstJumpDerivative L v g k F t) (Ici 0) t)
    (h0 : F 0 = f) (t : ℝ) (ht : 0 ≤ t) :
    F t = Matrix.mulVec (Matrix.exponentialEntry (t • tilt L v g k)) f := by
  apply eq_exponentialEntry_mulVec_of_backwardEquation_nonnegative
    (tilt L v g k) f F _ h0 t ht
  intro u hu
  rw [← firstJumpDerivative_eq_tilt_mulVec L v g k hescape F u]
  exact hF u hu

end

end NCG.NonnegativeTimeFeynmanKac
