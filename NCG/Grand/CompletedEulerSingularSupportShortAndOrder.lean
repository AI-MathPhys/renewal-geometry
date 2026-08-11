/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.GRHEulerShort
import NCG.Grand.RelativeMetricSupportDensity

/-!
# Completed--Euler short on a singular source support

This file removes the invertibility restriction from the completed--Euler
comparison.  It combines the canonical source-Gram Moore--Penrose inverse with
the support-relative metric density and proves the manuscript's exact
Pythagoras, kernel-inclusion order criterion, and sharp positive bridge defect.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG
namespace CompletedEulerSingularSupport

open RelativeMetricSupportDensity

/-- Literal inclusion of coefficient-form kernels. -/
def KernelIncluded {n : Type*} [Fintype n]
    (M E : Matrix n n ℂ) : Prop :=
  ∀ x : n → ℂ, M *ᵥ x = 0 → E *ᵥ x = 0

set_option maxHeartbeats 800000 in
-- Expanding the support projection into pointwise kernel identities is elaboration-intensive.
/-- For positive forms, inclusion of kernels is exactly support of the second
form on the support projection of the first. -/
theorem kernelIncluded_iff_supported {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef) :
    KernelIncluded M E ↔ E = D.Q * E * D.Q := by
  have hsource := source_supported D
  constructor
  · intro hker
    let K : Matrix n n ℂ := 1 - D.Q
    have hMK : M * K = 0 := by
      dsimp only [K]
      rw [Matrix.mul_sub, Matrix.mul_one, hsource.2, sub_self]
    have hEK : E * K = 0 := by
      ext i j
      have hv : M *ᵥ (K *ᵥ Pi.single j 1) = 0 := by
        calc
          M *ᵥ (K *ᵥ Pi.single j 1) =
              (M * K) *ᵥ Pi.single j 1 :=
            Matrix.mulVec_mulVec _ M K
          _ = 0 := by rw [hMK, Matrix.zero_mulVec]
      have hz := hker (K *ᵥ Pi.single j 1) hv
      calc
        (E * K) i j = ((E * K) *ᵥ Pi.single j 1) i := by
          simp [Matrix.mulVec, Matrix.mul_apply]
        _ = (E *ᵥ (K *ᵥ Pi.single j 1)) i := by
          rw [Matrix.mulVec_mulVec]
        _ = 0 := congrFun hz i
    have hKE : K * E = 0 := by
      have hKstar : Kᴴ = K := by
        dsimp only [K]
        exact complement_star D
      have hc := congrArg Matrix.conjTranspose hEK
      simpa only [Matrix.conjTranspose_mul, hKstar,
        hE.isHermitian.eq, Matrix.conjTranspose_zero] using hc
    dsimp only [K] at hEK hKE
    rw [Matrix.mul_sub, Matrix.mul_one] at hEK
    rw [Matrix.sub_mul, Matrix.one_mul] at hKE
    have hEQ : E * D.Q = E := (sub_eq_zero.mp hEK).symm
    have hQE : D.Q * E = E := (sub_eq_zero.mp hKE).symm
    calc
      E = D.Q * E := hQE.symm
      _ = D.Q * E * D.Q := by rw [Matrix.mul_assoc, hEQ]
  · intro hsupp x hMx
    have hAx : D.A *ᵥ x = 0 := by
      apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero D.A x).mp
      rw [D.A_star, D.A_sq]
      exact hMx
    have hQx : D.Q *ᵥ x = 0 := by
      calc
        D.Q *ᵥ x = (D.R * D.A) *ᵥ x := by rw [D.R_mul_A]
        _ = D.R *ᵥ (D.A *ᵥ x) := (Matrix.mulVec_mulVec x D.R D.A).symm
        _ = 0 := by rw [hAx, Matrix.mulVec_zero]
    calc
      E *ᵥ x = (D.Q * E * D.Q) *ᵥ x := by rw [← hsupp]
      _ = D.Q *ᵥ (E *ᵥ (D.Q *ᵥ x)) := by
        rw [Matrix.mul_assoc]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hQx, Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- The reduced completed-to-Euler coefficient map. -/
noncomputable def reducedEulerCoefficient {h m e : ℕ}
    (A : Matrix (Fin h) (Fin m) ℂ) (S : Matrix (Fin h) (Fin e) ℂ) :
    Matrix (Fin m) (Fin e) ℂ :=
  sourceGramPseudoinverse A * (Aᴴ * S)

/-- Singular Moore--Penrose Pythagoras for the completed and Euler source
metrics. -/
theorem completedEuler_pseudoinverse_pythagoras {h m e : ℕ}
    (A : Matrix (Fin h) (Fin m) ℂ) (S : Matrix (Fin h) (Fin e) ℂ) :
    let M := Aᴴ * A
    let E := Sᴴ * S
    let B := Aᴴ * S
    let C := reducedEulerCoefficient A S
    let R := sourceSchurResidual A S
    R = E - Bᴴ * sourceGramPseudoinverse A * B
      ∧ R.PosSemidef
      ∧ (R = 0 ↔ SourceRangeIncluded S A)
      ∧ E = Cᴴ * M * C + R := by
  dsimp only [reducedEulerCoefficient, sourceSchurResidual]
  let M : Matrix (Fin m) (Fin m) ℂ := Aᴴ * A
  let J : Matrix (Fin m) (Fin m) ℂ := sourceGramPseudoinverse A
  obtain ⟨hJstar, _, hJMJ, _, _, _⟩ :=
    sourceGramPseudoinverse_projection A
  have hCgram :
      (J * (Aᴴ * S))ᴴ * M * (J * (Aᴴ * S)) =
        (Aᴴ * S)ᴴ * J * (Aᴴ * S) := by
    rw [Matrix.conjTranspose_mul, hJstar]
    calc
      (Aᴴ * S)ᴴ * J * M * (J * (Aᴴ * S)) =
          (Aᴴ * S)ᴴ * ((J * M * J) * (Aᴴ * S)) := by
        simp only [Matrix.mul_assoc]
      _ = (Aᴴ * S)ᴴ * J * (Aᴴ * S) := by
        rw [show J * M * J = J by simpa only [J, M] using hJMJ]
        simp only [Matrix.mul_assoc]
  refine ⟨rfl, sourceSchurResidual_posSemidef A S,
    sourceSchurResidual_eq_zero_iff_rangeIncluded A S, ?_⟩
  rw [hCgram]
  abel

/-- The support-relative completed--Euler density. -/
def completedEulerRelativeDensity {n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix n n ℂ} (D : SupportData M)
    (E : Matrix n n ℂ) : Matrix n n ℂ :=
  relativeDensity D E

/-- The sharp multiplicative bridge defect `eta^+ = (||H||-1)_+`. -/
noncomputable def completedEulerBridgeDefect {n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix n n ℂ} (D : SupportData M)
    (E : Matrix n n ℂ) : ℝ :=
  max (‖completedEulerRelativeDensity D E‖ - 1) 0

/-- Exact order criterion on a possibly singular completed-source support. -/
theorem completedEuler_order_iff_kernel_and_relativeDensity {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef) :
    (M - E).PosSemidef ↔
      KernelIncluded M E ∧ ‖completedEulerRelativeDensity D E‖ ≤ 1 := by
  rw [show M - E = (1 : ℂ) • M - E by simp]
  rw [unit_domination_iff_kernelDefect_and_norm D hE]
  rw [kernelDefect_eq_zero_iff_supported D hE,
    ← kernelIncluded_iff_supported D hE]
  rfl

/-- On the finite-domination branch, the positive-part defect vanishes
exactly at completed--Euler order. -/
theorem completedEulerBridgeDefect_eq_zero_iff_order {n : Type*}
    [Fintype n] [DecidableEq n] {M E : Matrix n n ℂ}
    (D : SupportData M) (hE : E.PosSemidef)
    (hker : KernelIncluded M E) :
    completedEulerBridgeDefect D E = 0 ↔ (M - E).PosSemidef := by
  rw [completedEuler_order_iff_kernel_and_relativeDensity D hE]
  simp only [hker, true_and, completedEulerBridgeDefect]
  constructor
  · intro h
    have hm : max (‖completedEulerRelativeDensity D E‖ - 1) 0 ≤ 0 := h.le
    have := (max_le_iff.mp hm).1
    linarith
  · intro h
    exact max_eq_right (by linarith)

end CompletedEulerSingularSupport
end NCG
