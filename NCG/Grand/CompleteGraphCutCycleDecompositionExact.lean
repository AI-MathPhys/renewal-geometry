/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionCutCycle

/-!
# Exact cut--cycle decomposition of the complete relational cell

This supplies the decomposition and kernel clauses omitted by the original
signed-matrix rendering of `thm:dimension-cut-cycle`.  Every skew edge current
is split canonically into its normalized endpoint wedge and a boundary-free
cycle current; the two pieces are Frobenius-orthogonal, and vanishing boundary
is equivalent to vanishing cut part.
-/

open Matrix Finset

namespace NCG
namespace CompleteGraphCutCycle


variable {N : ℕ}

/-- The signed edge current `x wedge y`. -/
def wedge (x y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.vecMulVec x y - Matrix.vecMulVec y x

/-- Boundary of a signed edge current. -/
def boundary (A : Matrix (Fin N) (Fin N) ℝ) : Fin N → ℝ :=
  A *ᵥ (fun _ => 1)

/-- Normalized constant vector. -/
noncomputable def u0 : Fin N → ℝ := fun _ => (Real.sqrt N)⁻¹

/-- Endpoint coordinate extracted from a signed current. -/
noncomputable def cutVector (A : Matrix (Fin N) (Fin N) ℝ) : Fin N → ℝ :=
  -(Real.sqrt N)⁻¹ • boundary A

/-- Canonical endpoint/cut current. -/
noncomputable def cutPart (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := wedge u0 (cutVector A)

/-- Canonical boundary-free cycle current. -/
noncomputable def cyclePart (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := A - cutPart A

/-- Frobenius pairing on signed edge currents. -/
def edgeInner (A B : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

theorem wedge_transpose (x y : Fin N → ℝ) :
    (wedge x y)ᵀ = -wedge x y := by
  ext i j
  simp [wedge, Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

/-- A normalized cut wedge has the prescribed boundary. -/
theorem boundary_cutPart {A : Matrix (Fin N) (Fin N) ℝ}
    (hN : 1 ≤ N) (hA : Aᵀ = -A) : boundary (cutPart A) = boundary A := by
  have hmean : ∑ i, boundary A i = 0 :=
    (dimension_cut_cycle hN).2.2.1 A hA
  have hcutMean : ∑ i, cutVector A i = 0 := by
    change ∑ i, (-(Real.sqrt N)⁻¹) * boundary A i = 0
    rw [← Finset.mul_sum, hmean, mul_zero]
  have hformula := (dimension_cut_cycle hN).2.1 (cutVector A) hcutMean
  rw [cutPart, wedge]
  change (Matrix.vecMulVec (fun _ => (Real.sqrt N)⁻¹) (cutVector A) -
      Matrix.vecMulVec (cutVector A) (fun _ => (Real.sqrt N)⁻¹))
        *ᵥ (fun _ => 1) = boundary A
  rw [hformula]
  funext i
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  simp only [cutVector, Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg]
  field_simp

/-- A cycle current is Frobenius-orthogonal to every normalized cut wedge. -/
theorem wedge_orthogonal_cycle (hN : 1 ≤ N)
    (w : Fin N → ℝ) (C : Matrix (Fin N) (Fin N) ℝ)
    (hC : Cᵀ = -C) (hCb : boundary C = 0) :
    edgeInner (wedge u0 w) C = 0 := by
  have hrow : ∀ i, ∑ j, C i j = 0 := by
    intro i
    have hi := congrFun hCb i
    simpa [boundary, Matrix.mulVec, dotProduct] using hi
  have hcol : ∀ j, ∑ i, C i j = 0 := by
    intro j
    calc
      ∑ i, C i j = ∑ i, -C j i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij := congrFun (congrFun hC j) i
        simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
        linarith
      _ = -∑ i, C j i := by rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [hrow j, neg_zero]
  have hfirst :
      ∑ i, ∑ j, (Real.sqrt N)⁻¹ * w j * C i j = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    calc
      ∑ i, (Real.sqrt N)⁻¹ * w j * C i j =
          ((Real.sqrt N)⁻¹ * w j) * ∑ i, C i j := by
            rw [Finset.mul_sum]
      _ = 0 := by rw [hcol j, mul_zero]
  have hsecond :
      ∑ i, ∑ j, w i * (Real.sqrt N)⁻¹ * C i j = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    calc
      ∑ j, w i * (Real.sqrt N)⁻¹ * C i j =
          (w i * (Real.sqrt N)⁻¹) * ∑ j, C i j := by
            rw [Finset.mul_sum]
      _ = 0 := by rw [hrow i, mul_zero]
  simp only [edgeInner, wedge, Matrix.sub_apply, Matrix.vecMulVec_apply, u0]
  calc
    ∑ i, ∑ j, ((Real.sqrt N)⁻¹ * w j - w i * (Real.sqrt N)⁻¹) * C i j =
        (∑ i, ∑ j, (Real.sqrt N)⁻¹ * w j * C i j) -
          ∑ i, ∑ j, w i * (Real.sqrt N)⁻¹ * C i j := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = 0 := by rw [hfirst, hsecond, sub_self]
/-- `thm:dimension-cut-cycle`, exact canonical decomposition and kernel
identification in the signed-edge realization. -/
theorem dimension_cut_cycle_decomposition_exact (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : Aᵀ = -A) :
    (∑ i, cutVector A i = 0)
      ∧ (cutPart A)ᵀ = -cutPart A
      ∧ (cyclePart A)ᵀ = -cyclePart A
      ∧ boundary (cyclePart A) = 0
      ∧ A = cutPart A + cyclePart A
      ∧ edgeInner (cutPart A) (cyclePart A) = 0
      ∧ (boundary A = 0 ↔ cutPart A = 0) := by
  have hmean : ∑ i, boundary A i = 0 :=
    (dimension_cut_cycle hN).2.2.1 A hA
  have hcutMean : ∑ i, cutVector A i = 0 := by
    change ∑ i, (-(Real.sqrt N)⁻¹) * boundary A i = 0
    rw [← Finset.mul_sum, hmean, mul_zero]
  have hcutSkew : (cutPart A)ᵀ = -cutPart A :=
    wedge_transpose u0 (cutVector A)
  have hcycleSkew : (cyclePart A)ᵀ = -cyclePart A := by
    rw [cyclePart, Matrix.transpose_sub, hA, hcutSkew]
    abel
  have hcutBoundary := boundary_cutPart hN hA
  have hcycleBoundary : boundary (cyclePart A) = 0 := by
    funext i
    change ((A - cutPart A) *ᵥ (fun _ => 1)) i = 0
    rw [Matrix.sub_mulVec]
    change boundary A i - boundary (cutPart A) i = 0
    rw [congrFun hcutBoundary i]
    exact sub_self _
  refine ⟨hcutMean, hcutSkew, hcycleSkew, hcycleBoundary, ?_, ?_, ?_⟩
  · simp [cyclePart]
  · exact wedge_orthogonal_cycle hN (cutVector A) (cyclePart A)
      hcycleSkew hcycleBoundary
  · constructor
    · intro hb
      have hcv : cutVector A = 0 := by simp [cutVector, hb]
      simp [cutPart, hcv, wedge]
    · intro hc
      rw [← boundary_cutPart hN hA, hc]
      simp [boundary, Matrix.mulVec]

end CompleteGraphCutCycle
end NCG
