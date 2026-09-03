/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHeatBathDobrushin

/-!
# Exact finite Feynman--Kac backward-equation uniqueness

Conditioning a finite-state continuous-time path law on its first jump gives a
backward linear ODE.  This file closes the deterministic half of that argument:
every differentiable vector-valued solution of `F' = B F`, with terminal
initial value `f`, is exactly `exp(tB) f`.  The proof embeds a vector as one
matrix column and uses an integrating factor, so it does not assume an ODE
solver or semigroup representation.
-/

open Matrix
open scoped Matrix.Norms.Operator

noncomputable section

namespace NCG.FiniteFeynmanKacBackwardEquation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Embed a vector as a selected column of a square matrix. -/
def singleColumn (j0 : S) (f : S → ℝ) : Matrix S S ℝ :=
  fun i j => if j = j0 then f i else 0

/-- Left matrix multiplication acts on the selected column by `mulVec`. -/
theorem mul_singleColumn (B : Matrix S S ℝ) (j0 : S) (f : S → ℝ) :
    B * singleColumn j0 f = singleColumn j0 (B.mulVec f) := by
  ext i j
  by_cases hj : j = j0
  · subst j
    simp [singleColumn, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp [singleColumn, Matrix.mul_apply, hj]

/-- The selected-column embedding as a continuous linear map. -/
noncomputable def singleColumnCLM (j0 : S) :
    (S → ℝ) →L[ℝ] Matrix S S ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := singleColumn j0
      map_add' := by
        intro f g
        ext i j
        by_cases hj : j = j0 <;> simp [singleColumn, hj]
      map_smul' := by
        intro c f
        ext i j
        simp [singleColumn] }

@[simp] theorem singleColumnCLM_apply (j0 : S) (f : S → ℝ) :
    singleColumnCLM j0 f = singleColumn j0 f := rfl

/-- Uniqueness of a matrix-valued left linear flow with arbitrary initial
matrix: `Y' = X Y`, `Y(0)=Y0` implies `Y(t)=exp(tX)Y0`. -/
theorem eq_exp_mul_initial_of_hasDerivAt
    (X Y0 : Matrix S S ℝ) (Y : ℝ → Matrix S S ℝ)
    (hY : ∀ t, HasDerivAt Y (X * Y t) t)
    (h0 : Y 0 = Y0) (t : ℝ) :
    Y t = NormedSpace.exp (t • X) * Y0 := by
  have hE : ∀ u : ℝ,
      HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s) • X))
        (-(NormedSpace.exp ((-u) • X) * X)) u := by
    intro u
    have h :=
      (hasDerivAt_exp_smul_const X (-u)).scomp u
        (hasDerivAt_neg' (x := u))
    rw [neg_one_smul] at h
    exact h
  have hZ : ∀ u,
      HasDerivAt
        (fun s => NormedSpace.exp ((-s) • X) * Y s) 0 u := by
    intro u
    have h := (hE u).mul (hY u)
    have heq :
        -(NormedSpace.exp ((-u) • X) * X) * Y u +
            NormedSpace.exp ((-u) • X) * (X * Y u) = 0 := by
      rw [Matrix.neg_mul, Matrix.mul_assoc]
      exact neg_add_cancel _
    exact h.congr_deriv heq
  have hconst := is_const_of_deriv_eq_zero
    (fun u => (hZ u).differentiableAt) (fun u => (hZ u).deriv) t 0
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero,
    Matrix.one_mul, h0] at hconst
  have hinv :
      NormedSpace.exp (t • X) * NormedSpace.exp ((-t) • X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _
      (((Commute.refl X).smul_left t).smul_right (-t)),
      ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  calc
    Y t = 1 * Y t := (Matrix.one_mul _).symm
    _ = (NormedSpace.exp (t • X) *
          NormedSpace.exp ((-t) • X)) * Y t := by rw [hinv]
    _ = NormedSpace.exp (t • X) *
          (NormedSpace.exp ((-t) • X) * Y t) := by
            rw [Matrix.mul_assoc]
    _ = NormedSpace.exp (t • X) * Y0 := by rw [hconst]

/-- **Backward Feynman--Kac uniqueness.**  Any differentiable finite-state
backward solution with `F(0)=f` is the coordinatewise matrix exponential
applied to `f`. -/
theorem eq_exponentialEntry_mulVec_of_backwardEquation
    [Nonempty S] (B : Matrix S S ℝ) (f : S → ℝ)
    (F : ℝ → S → ℝ)
    (hF : ∀ t, HasDerivAt F (B.mulVec (F t)) t)
    (h0 : F 0 = f) (t : ℝ) :
    F t = Matrix.mulVec (Matrix.exponentialEntry (t • B)) f := by
  let j0 : S := Classical.choice inferInstance
  let Y : ℝ → Matrix S S ℝ := fun u => singleColumn j0 (F u)
  have hY : ∀ u, HasDerivAt Y (B * Y u) u := by
    intro u
    have h := (singleColumnCLM j0).hasFDerivAt.comp_hasDerivAt u (hF u)
    change HasDerivAt (fun s => singleColumn j0 (F s))
      (singleColumn j0 (B.mulVec (F u))) u at h
    change HasDerivAt (fun s => singleColumn j0 (F s))
      (B * singleColumn j0 (F u)) u
    rw [mul_singleColumn]
    exact h
  have hY0 : Y 0 = singleColumn j0 f := by
    simp only [Y, h0]
  have hmatrix := eq_exp_mul_initial_of_hasDerivAt B
    (singleColumn j0 f) Y hY hY0 t
  have hexponential :
      Matrix.exponentialEntry (t • B) = NormedSpace.exp (t • B) := by
    ext i j
    exact FiniteHeatBathDobrushin.exponentialEntry_eq_exp_apply
      (t • B) i j
  rw [hexponential]
  rw [mul_singleColumn] at hmatrix
  funext i
  have hi := congrFun (congrFun hmatrix i) j0
  simpa [Y, singleColumn] using hi

/-- The exponential formula itself satisfies the finite backward equation and
initial condition.  Combined with the preceding theorem this is existence and
uniqueness of the deterministic Feynman--Kac evolution. -/
theorem exponentialEntry_backwardEquation_unique
    [Nonempty S] (B : Matrix S S ℝ) (f : S → ℝ)
    (F : ℝ → S → ℝ)
    (hF : ∀ t, HasDerivAt F (B.mulVec (F t)) t)
    (h0 : F 0 = f) :
    F = fun t => Matrix.mulVec (Matrix.exponentialEntry (t • B)) f := by
  funext t
  exact eq_exponentialEntry_mulVec_of_backwardEquation B f F hF h0 t

end NCG.FiniteFeynmanKacBackwardEquation
